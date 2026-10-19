# fyp\_scheduling\_algorithms

## Generating the sample schedules

`SampleSchedules/` holds CSV traces of each scheduler on the sample process sets in
`FypSchedulingAlgorithms/SampleSchedules.lean`, so you can read what the schedulers actually do.
`lake build` keeps them up to date: besides the proof library it builds a second library,
`SampleSchedulesGen` (listed in `defaultTargets` in `lakefile.toml`), whose module
`SampleSchedulesGen.lean` writes every CSV while it is compiled. Lake only recompiles it when it
or something it imports changes (the schedulers, the sample data, the CSV rendering,
`Main.lean`), so a build rewrites the CSVs exactly when they could change and otherwise writes
nothing. The proof library does not import any of this, and `lake build` now also type-checks
the generator. The files always land in `SampleSchedules/` at the repository root (opening
`SampleSchedulesGen.lean` in an editor rewrites them too).

As a manual fallback (e.g. after editing or deleting a CSV by hand, which `lake build` does not
notice), run from the repository root

```
lake build && lake env lean --run Main.lean
```

`lean --run` uses the compiled library modules as they are, so always build first (otherwise it
runs a stale `SampleSchedules.olean`). It writes to `SampleSchedules/` relative to the current
directory. `Main.lean` runs in the Lean interpreter (a compiled `lake exe` would first have to
compile all of the imported Mathlib modules to native code). Both routes write the aperiodic
traces (`FCFSschedule.csv`, `SJFschedule.csv`, `SRTFschedule.csv`, `RRschedule_q3.csv`) to
`SampleSchedules/` and the periodic ones to `SampleSchedules/EDF/` and `SampleSchedules/RMS/`.
`.gitattributes` keeps the CSVs LF-only, as the generator writes them, so regenerating
unchanged CSVs leaves `git status` clean.

Each file has one row per step: the row with `time = k + 1` is the state after step `k`,
i.e. `runSteps arrivals step k` (`runStepsRR` for RR), after the jobs arriving at times
`0..k` have been added. Jobs are labelled by id; a periodic task releases a new job every
period, so periodic jobs are labelled `<id>@<release time>` (e.g. `2@7`) to tell the jobs of
one task apart. Columns:

- `time`: the clock after the step.
- `running`: the job on the CPU, or `0` when idle (the sample jobs have ids ≥ 1).
- `ready_queue`: the waiting jobs, in queue order.
- `completed`: the finished jobs, in completion order.
- `process_ticks` (`process_ticks with deadline` in the periodic files):
  `P<label>:<ticks run>/<burst>` for every job seen so far, sorted by id and then release time,
  separated by `|`; periodic jobs also show their absolute deadline as `d<deadline>`,
  e.g. `P2@7:1/4d14`.
- `missed_deadlines` (periodic only): the jobs that can no longer meet their deadline: still
  unfinished at or after it. A job with absolute deadline `D` must finish by time `D`, so it is
  listed from the row `time = D` on if it is still ready or running there. Same
  `P<label>:...` format, separated by `|`. Late jobs are not aborted, so one miss shows up on
  every row until the job finishes.

To add a scenario, define its arrival stream next to the others in `SampleSchedules.lean` (a
list of processes passed to `Process.convert_to_arrival_stream`), then add a `writeCSV` line for
it in `writeSampleSchedules` in `Main.lean` (the `subdir` argument picks the folder under
`SampleSchedules/`), and run `lake build`.

## TODO

Try to show optimality of EDF compared to RMS

## List of scheduling properties:

### Safety Properties (nothing bad ever happens)

#### Mutual exclusion on the CPU — at most one process runs at any tick. Sounds trivial but is the baseline sanity check your model needs before anything else.

#### No work conservation violation — if the ready queue is non-empty, the CPU is never idle. Some algorithms violate this subtly in corner cases.

#### No priority inversion — a high-priority process is never blocked waiting while a lower-priority process runs, unless some explicit protocol (Priority Ceiling, Priority Inheritance) permits it. This is the classic bug that caused the Mars Pathfinder reset in 1997.

#### Preemption consistency — if you model a non-preemptive scheduler, a running process is never evicted before its burst is done. Trivial to state, useful to check your step function doesn't accidentally preempt.

## Liveness Properties (something good eventually happens)

#### Starvation freedom — every arrived process is eventually scheduled. The interesting variant: show this fails for pure Priority scheduling with dynamic arrivals (a stream of high-priority jobs can block a low one forever).

#### Termination / finite completion — if no new processes arrive after time T, the system eventually drains the queue. You need a well-founded measure over total remaining burst time.

#### Bounded waiting — stronger than starvation freedom: every process is scheduled within f(n) time units of arrival, where n is queue length. For Round Robin this is (n-1) \* quantum; for FCFS it depends on burst sizes.

#### Response time guarantees — for periodic task models, every job meets its deadline. This is the core of real-time scheduling theory (Rate Monotonic, EDF). Proving the utilization bound U ≤ n(2^(1/n) - 1) for RM is a classic formalization target.

## Fairness Properties

#### Progress proportion — over any window of W ticks, process i gets CPU time proportional to its weight. This is the defining property of fair-share schedulers (CFS, WFQ). Hard to state precisely but very satisfying to prove.

#### Max-min fairness — no process gets more than its fair share while another gets less. You can prove CFS satisfies this and FCFS doesn't.

#### Jitter bounds — the variance in when a periodic process actually runs vs. when it was supposed to. Relevant for multimedia and networking schedulers.

## Algorithm-Specific Optimality Properties

#### FCFS has no starvation but has convoy effect — formally: every process completes (liveness ✓), but the expected waiting time of a short process behind a long one is unbounded relative to its own burst. You can quantify this as a ratio.

#### SJF minimizes average waiting time — among all non-preemptive algorithms with the same workload, SJF achieves the minimum sum of waiting times. This is an exchange argument proof — swap any two adjacent jobs out-of-SJF-order and show the sum decreases.

#### SRTF (preemptive SJF) minimizes average response time — same result for the preemptive case. Requires reasoning about preemption points.

#### EDF is optimal for single-processor deadline scheduling — if any algorithm can meet all deadlines, EDF can. The proof is a classic exchange argument; very doable to formalize.

#### Round Robin convergence — with quantum Q → 0, RR approaches Processor Sharing, where each process gets an equal instantaneous fraction of the CPU. A limit argument.

## Compositional / System-Level Properties

#### Work-conserving schedulers dominate non-work-conserving ones — for any metric (latency, throughput), a work-conserving variant of any algorithm is at least as good. Good exercise in building a simulation preorder.

#### Idempotency of scheduling decisions — running step twice from an idle state gives the same result as running it once (no phantom context switches). Checks your model doesn't have spurious state changes.

#### Monotonicity — adding a process to the ready queue never improves the waiting time of existing processes (expected, but fails for some feedback schedulers).

#### Simulation / refinement — your abstract model (pure state machine) refines to a more concrete model (with context-switch overhead, cache effects). A bisimulation proof connecting the two levels.

