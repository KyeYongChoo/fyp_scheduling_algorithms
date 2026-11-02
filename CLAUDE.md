# fyp_scheduling_algorithms

Lean 4 + Mathlib formalisation of CPU scheduling (FCFS, SJF, SRTF, RR, RMS, DM, EDF).
`GLOSSARY.md` explains the terms and points to their definitions; read it before working on
the proofs. Build with `lake build`.

## Open follow-up: SJF is optimal at horizons `T ≤ 3`

`no_optimal_online_nonPreemptive` (`ConvoyEffect/OnlineImpossibility.lean`) says that at every
horizon `T ≥ 4`, no online non-preemptive policy (`DrawsFromReadyQueue`) is optimal on every
well-formed stream. The `4` is sharp: at every `T ≤ 3`, SJF *is* optimal. The goal is to prove
that and close the chapter with an iff:

```lean
theorem sjf_optimal_of_le_three {T : ℕ} (hT : T ≤ 3)
    (select : SchedState → Option AperiodicProcess) (h : DrawsFromReadyQueue select)
    (arrival_stream : ℕ → List AperiodicProcess) (h_wf : WellFormedStream arrival_stream) :
    runWait (runSteps · stepSJF) arrival_stream T ≤ runWait (onlineRun select) arrival_stream T

theorem exists_optimal_online_iff (T : ℕ) :
    (∃ select, DrawsFromReadyQueue select ∧ ∀ select', DrawsFromReadyQueue select' →
      ∀ arrival_stream, WellFormedStream arrival_stream →
        runWait (onlineRun select) arrival_stream T ≤ runWait (onlineRun select') arrival_stream T) ↔ T ≤ 3
```

`←` is `sjf_optimal_of_le_three` (SJF is online via `onlineRun_ready`); `→` is the existing
`no_optimal_online_nonPreemptive`.

**Evidence (not a proof).** A Python brute force mirroring `stepNonPreemptiveOnline` /
`runSteps` / `runWait`. Each step appends that time's arrivals, then ticks the running job,
and asks the policy on idle or completion; the policy may idle or pick any ready job; cost is
the sum over `t < T` of `len(ready after step t)`. On one stream an online policy can make
any decision sequence, so SJF is optimal at `T` iff it matches the minimum over all decision
sequences on every stream. Result: SJF is optimal on every stream for `T = 0..3` (42,875
streams at `T = 3`: arrivals at times 0–2, ≤ 3 jobs per time, bursts 1–4). From `T = 4` it
fails, and the smallest counterexample is `{0: [4], 1: [1]}`, which is exactly `streamB`.

**Why (hand proof).**
- Non-preemptive, so a dispatched job never returns to `ready`:
  `ready_t = N_t − D_t`, where `N_t` = jobs arrived by `t` (the same for every policy) and
  `D_t` = jobs dispatched by step `t`.
- So `runWait T = Σ N_t − Σ_{t<T} D_t`. Minimising waiting = maximising
  `D_0 + … + D_{T−1}`: dispatch as many jobs as early as possible.
- Idling at step 0 while a job waits costs 1 (in `D_0`). The only payback is that a short job
  arriving at time 1 is dispatched at step 1 and completes at step 2 at the earliest, so later
  dispatches come earlier. That gain counts once for each horizon step from 2 on: ≤ 1 at
  `T = 3`, a tie at best; 2 at `T = 4`, so idling wins (`streamB`).
- Cases on step 0 at `T = 3`:
  - Idling: `D_0 = 0`, `D_1 ≤ 1`, `D_2 ≤ 2`; dispatching and never idling already reaches
    that.
  - A unit job waits: SJF dispatches it, which is the only way to free the CPU at step 1, and
    at step 1 again picks the shortest job.
  - No unit job waits: the job dispatched at 0 holds the CPU through step 1, and only the
    shortest can finish by step 2.
  - Nothing at time 0: the `T = 2` argument shifted by one step.
  - Only "burst = 1, = 2 or ≥ 3" matters.

**Lean plan.**
1. Reduce to arrivals at times 0–2 via `runSteps_knownAt` (`RunStepsLemmas.lean`): replace
   `arrival_stream` by `knownAt arrival_stream 2`.
2. Accounting lemma: in a non-preemptive run, `ready.length` = arrived − (completed + busy).
   It is probably cheapest via `runWait_eq_schedWait`, `inSystem_perm` and `length_waiting`
   (`ConvoyEffect/Schedules.lean`), rather than from scratch.
3. Case analysis with the one-step lemmas in `NonPreemptiveLemmas.lean`
   (`stepNonPreemptiveOnline_tick`, `_dispatch`, `_complete_dispatch`, `_complete_idle`,
   `_idle`) and `selectSJF_min`. This is the long part: finite but mechanical.
4. `T < 3` the same way, or directly (they are small).

Estimated a few hundred lines, mostly step 3. Put it in a new file (e.g.
`ConvoyEffect/ShortHorizon.lean`) importing `OnlineImpossibility`. Then update the README
and the `OnlineImpossibility` module doc, which already says 4 is the least horizon for these
two streams.
