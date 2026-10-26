# fyp\_scheduling\_algorithms

## Generating the sample schedules

`SampleSchedules/` holds CSV traces of each scheduler on the sample process sets in
`FypSchedulingAlgorithms/SampleSchedules.lean`, so you can read what the schedulers actually do.
`lake build` keeps them up to date: besides the proof library it builds a second library,
`SampleSchedulesGen` (listed in `defaultTargets` in `lakefile.toml`), whose module
`SampleSchedulesGen.lean` writes every CSV while it is compiled. Lake only recompiles it when it
or something it imports changes (the schedulers, the sample data, the CSV rendering), so a build
rewrites the CSVs exactly when they could change and otherwise writes nothing. The proof library
imports none of the CSV code, and the proofs do not depend on the CSVs; `lake build` also
type-checks the generator. The files always land in `SampleSchedules/` at the repository root
(opening `SampleSchedulesGen.lean` in an editor rewrites them too).

As a manual fallback (e.g. after editing or deleting a CSV by hand, which `lake build` does not
notice), run from the repository root

```
lake build && lake env lean SampleSchedulesGen.lean
```

This elaborates `SampleSchedulesGen.lean` directly, which writes the CSVs just as `lake build`
does. It uses the compiled library modules as they are, so always build first (otherwise it
uses a stale `SampleSchedules.olean`). It runs in the Lean interpreter (a compiled `lake exe`
would first have to compile all of the imported Mathlib modules to native code). Both routes
write the aperiodic traces (`FCFSschedule.csv`, `SJFschedule.csv`, `SRTFschedule.csv`,
`RRschedule_q3.csv`) to `SampleSchedules/` and the periodic ones to `SampleSchedules/EDF/` and
`SampleSchedules/RMS/`.
`.gitattributes` keeps the CSVs LF-only, as the generator writes them, so regenerating
unchanged CSVs leaves `git status` clean. In a checkout made before `.gitattributes` existed,
the first regeneration may still show the CSVs as modified although their content is
unchanged; a one-off `git add -- SampleSchedules` clears this and stages nothing.

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
- `missed_deadlines` (periodic only): the jobs that have missed their deadline. A job released
  at time `r` is not ticked before step `r+1` (one tick of dispatch latency, see the tick
  convention in `Step.lean`), so a job with absolute deadline `d = r + D` gets the `D` ticks of
  steps `r+1 … d` and must be finished in the row `time = d + 1`, the state after step `d`. It
  is listed from that row on if it is still ready or running there, i.e. on every row with
  `time > d`. Same `P<label>:...` format, separated by `|`. Late jobs are not aborted, so one
  miss shows up on every row until the job finishes.

To add a scenario, define its arrival stream next to the others in `SampleSchedules.lean` (a
list of processes passed to `Process.convert_to_arrival_stream`; periodic task lists go in
`PeriodicSchedulers/SampleTaskSets.lean`, in the proof library, so theorems can use them), then add a `writeCSV` line for
it in `writeSampleSchedules` in `SampleSchedulesGen.lean` (the `subdir` argument picks the
folder under `SampleSchedules/`), and run `lake build`.

## Periodic results at a glance

EDF is optimal (`Periodic.edf_optimal`), Deadline Monotonic and Rate Monotonic are optimal
among fixed-priority assignments with distinct priorities per task
(`Periodic.fixedPriority_optimal`, `Periodic.dm_optimal`, `Periodic.rm_optimal`), and EDF
dominates every preemptive priority scheduler, strictly on `rmsFailsEdfSucceeds`
(`Periodic.edf_dominates`, `Periodic.edf_beats_rms_rmsFails`). Details under
"Algorithm-Specific Optimality Properties" below. All of them use the miss rule of the CSVs
above: a job released at `r` with relative deadline `D` gets the `D` ticks of steps
`r+1 … r+D`, and is late iff it is still unfinished after step `r + D`
(`PeriodicProcess.missedDeadlines`).

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

Proved for batches (`IsBatch`: fresh jobs with distinct ids, all released at time 0), against every online non-preemptive policy and at every horizon: `ConvoyEffect.runWait_sjf_le_online_batch` (OnlineOptimality.lean). With later arrivals the claim fails: no online non-preemptive policy is optimal on every stream (`ConvoyEffect.no_optimal_online_nonPreemptive`, OnlineImpossibility.lean). What does hold is optimality given only the past: on the jobs known at any time `t`, SJF waits no longer than any online non-preemptive policy whose run agrees with SJF's before `t` (`ConvoyEffect.runWait_sjf_le_knownAt`, OnlineOptimality.lean).

#### SRTF (preemptive SJF) minimizes average waiting time — same result for the preemptive case. Requires reasoning about preemption points.

Proved: `ConvoyEffect.srtfMinimisesWait` (SRTFOptimality.lean). On every well-formed stream without repeats (`NoRepeats`), at every horizon, SRTF's total waiting time is at most that of any admissible schedule, preemptive or not, online or clairvoyant. This is in the discrete tick model with no context-switch cost, and optimality is weak (`≤`). Corollaries: SRTF waits no longer than any online non-preemptive policy (`ConvoyEffect.srtf_le_onlineRun`) or any job-conserving step function (`ConvoyEffect.srtf_le_runWait_of_conservesJobs`); Round Robin is not covered.

#### EDF is optimal for single-processor deadline scheduling — if any algorithm can meet all deadlines, EDF can. The proof is a classic exchange argument; very doable to formalize.

Proved: `Periodic.edf_optimal` (PeriodicSchedulers/EDFOptimality.lean). On every periodic task set with distinct task ids, if the run of `stepEDF` lists a missed deadline after step `t`, then every admissible schedule (preemptive or not, idling or not, online or clairvoyant) is late at `t`; so if any admissible schedule meets every deadline, EDF does (`Periodic.edf_never_late_of_exists`). Deadlines may exceed periods. The proof is not an exchange argument but a majorisation of the work still owed by jobs with deadline at most `d`, as for SRTF. It is in the discrete tick model with no context-switch cost and the miss rule above (the textbook discrete model shifted by one tick of dispatch latency). Corollaries (PeriodicSchedulers/PeriodicWitnesses.lean): EDF dominates every preemptive priority scheduler, fixed or not (`Periodic.edf_dominates`; `Periodic.edf_dominates_rms`, `Periodic.edf_dominates_dm`). The gap is strict on `SampleTaskSets.rmsFailsEdfSucceeds`: `stepRMS` misses a deadline after step 7 (`Periodic.rms_misses_rmsFails`), `stepEDF` never misses at any step (`Periodic.edf_never_misses_rmsFails`; one hyperperiod checked by `decide`, after which the run repeats, PeriodicSchedulers/Hyperperiod.lean), and no fixed-priority assignment with distinct priorities per task meets every deadline there (`Periodic.no_strict_fixedPriority_rmsFails`).

#### Deadline Monotonic and Rate Monotonic are optimal among fixed-priority assignments — for synchronous tasks with constrained deadlines (D ≤ T), if some fixed-priority assignment with distinct priorities per task meets every deadline, DM does; with D = T, RM does.

Proved: `Periodic.fixedPriority_optimal` (PeriodicSchedulers/FixedPriorityOptimality.lean; Leung and Whitehead 1982). Let `f` and `g` be fixed priorities (`Periodic.FixedPriority`: a job's priority is its task's), `f` strict on the tasks (distinct priorities per task), `g`'s level sets deadline-closed, and `D ≤ T` for every task with a positive period (a task with period 0 releases one job). If the run of `stepPreemptive f` never lists a missed deadline, neither does the run of `stepPreemptive g`. Corollaries: `Periodic.dm_optimal` for `stepDM`, and `Periodic.rm_optimal` for `stepRMS` when `D = T` (Liu and Layland 1973). First-job tests: with distinct relative deadlines (resp. distinct periods and `D = T`), `stepDM` (resp. `stepRMS`) never misses a deadline iff every task's first job meets its deadline (`Periodic.dm_firstJob_test`, `Periodic.rm_firstJob_test`); for example RMS never misses on `rmsSucceedsEdfSucceeds` (`Periodic.rms_never_misses_rmsSucceeds`). The proof goes through the level backlog of a set of tasks (PeriodicSchedulers/FixedPriorityBacklog.lean) and a busy-period bound: the synchronous busy period from time 0 dominates every other; there is no swap argument and no general critical-instant theorem. Scope: `stepPreemptive` breaks priority ties dynamically (the running job keeps the CPU, the queue is FIFO), so a priority function with ties is not a classical fixed-priority assignment and can do better. On `rmsFailsEdfSucceeds` both strict orders miss a deadline while the constant priority never does (`Periodic.tied_priority_never_misses_rmsFails`); hence the "distinct priorities per task" in the comparison class, and the distinct-deadline / distinct-period hypotheses of the first-job tests.

#### Round Robin convergence — with quantum Q → 0, RR approaches Processor Sharing, where each process gets an equal instantaneous fraction of the CPU. A limit argument.

## Compositional / System-Level Properties

#### Work-conserving schedulers dominate non-work-conserving ones — for any metric (latency, throughput), a work-conserving variant of any algorithm is at least as good. Good exercise in building a simulation preorder.

#### Idempotency of scheduling decisions — running step twice from an idle state gives the same result as running it once (no phantom context switches). Checks your model doesn't have spurious state changes.

#### Monotonicity — adding a process to the ready queue never improves the waiting time of existing processes (expected, but fails for some feedback schedulers).

#### Simulation / refinement — your abstract model (pure state machine) refines to a more concrete model (with context-switch overhead, cache effects). A bisimulation proof connecting the two levels.

