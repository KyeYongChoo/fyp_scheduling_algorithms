/-
Copyright (c) 2026 Choo Kye Yong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Choo Kye Yong
-/
import FypSchedulingAlgorithms.Process
import FypSchedulingAlgorithms.Step
import FypSchedulingAlgorithms.AperiodicSchedulers.ConvoyEffect.TotalWait
import FypSchedulingAlgorithms.ProcessSimpLemmas
import FypSchedulingAlgorithms.SchedStateSimpLemmas
import Mathlib.Data.List.Nodup

/-!
# The convoy effect

The convoy effect is the textbook observation that a long job put on the CPU
ahead of shorter ones that are already waiting inflates the total waiting time:
every job behind it pays for its full burst.

**The definition** (`HasConvoyEffectAtSomeDispatchRun`, `HasConvoyEffectAtSomeDispatch`)
watches real runs on well-formed arrival streams, with no restriction on when jobs
arrive.  A scheduler has the convoy effect at some dispatch when, at some *dispatch
moment* -- a step at which a job is put on the CPU that was not on it the step before
(`DispatchesAt`) -- a job with strictly less work left is waiting in `ready`.  Its
negation, the good property, is `ShortestAtEveryDispatchRun`.
Like `StarvationFreeRun`, it is stated over a run function, so it applies to
non-preemptive, preemptive and Round Robin schedulers alike.

* FCFS and RR have it (`fcfs_hasConvoyEffectAtSomeDispatch`, `rr_hasConvoyEffectAtSomeDispatch`).
* SJF and SRTF do not (`sjf_not_hasConvoyEffectAtSomeDispatch`,
  `srtf_not_hasConvoyEffectAtSomeDispatch`). In particular a short job arriving *after*
  non-preemptive SJF has committed to a long one is not a convoy: it was not in `ready` when the
  choice was made (`sjf_late_convoy_shortestAtEveryDispatch`).  It is the cost of non-preemption,
  which SRTF removes, and `NoOptimalNonPreemptiveOnEveryStream` shows that no non-preemptive
  state-select policy can avoid it on every stream.

Two related notions:

* The **convoy effect on all arrivals at zero** (`HasConvoyEffectAllArrivalsAtZero`) judges a
  selection policy's decision on a single *batch* (jobs all present at time 0).  It is the
  special case of the definition at step 0 of a batch run
  (`hasConvoyEffectAllArrivalsAtZero_imp_hasConvoyEffectAtSomeDispatch`), and it is the form in
  which the cost is visible: for a batch, swapping the two jobs strictly lowers total
  waiting time (`hasConvoyEffectAllArrivalsAtZero_iff_swap_improves`), and in `RunWait` a
  policy has the convoy effect on all arrivals at zero exactly when its run waits strictly longer
  than SJF's on some batch (`hasConvoyEffectAllArrivalsAtZero_iff_runWait`).  Off batches
  the cost is in `SJFOptimalityGivenSamePast`: at a convoy dispatch of any non-preemptive
  state-select run, switching to SJF strictly lowers the wait on the instance
  known at that moment, over every horizon that outlasts the shorter waiting
  job's work (`runWait_switchToSJF_lt_of_convoy`).
* The **convoy effect at some step** (`HasConvoyEffectAtSomeStep`) is a competing,
  weaker definition: a shorter job waits behind the running one at *some step*, not
  necessarily at a dispatch.  Every dispatch is a step, so the convoy effect at some
  dispatch implies it (`hasConvoyEffectAtSomeDispatchRun_imp_atSomeStep`), but not
  conversely: SJF has the convoy effect at some step without the convoy effect at some
  dispatch (`atSomeStep_not_imp_atSomeDispatch`).  Its negation, the good property, is
  `ShortestAtEveryStepRun`, which is stronger than `ShortestAtEveryDispatchRun`.

`remaining` rather than `burst` is the right measure in the run-based notions,
because a preempted job re-enters the queue with part of its burst done.
Starvation is an independent liveness property (`StarvationSpec`): SJF is
convoy-free yet starves.
-/

/-!
## Layout

This file only states the properties and connects them; the per-scheduler
results live in `FCFSConvoy`, `SJFConvoy`, `SRTFConvoy` and `RRConvoy`, sharing
the arrival streams in `ConvoyWitnesses`.  The cost side is in `TotalWait`, and
`RunWait` ties it to actual runs: there `runWait` measures a run's waiting time,
a batch run of a non-preemptive policy waits exactly `totalWait` of its dispatch
order, and `hasConvoyEffectAllArrivalsAtZero_iff_runWait` restates
`HasConvoyEffectAllArrivalsAtZero` as "on some batch, the run waits strictly longer than SJF's".
`NoOptimalNonPreemptiveOnEveryStream` shows that no non-preemptive state-select policy waits least
on every stream, and `SJFOptimalityGivenSamePast` that SJF nevertheless waits least given the same
past (on the instance known so far, against policies that made the same earlier decisions).
-/

namespace ConvoyEffect

/-! ## The convoy effect at dispatch moments -/

/-- In run `run` on stream `arrival_stream`, job `p` is **dispatched at step
`t`**: it holds the CPU after step `t`, and (if `t > 0`) the job on the CPU
after step `t - 1` had a different id.  This covers a dispatch into an idle CPU,
after a completion, and by preemption; a job that simply keeps the CPU is not
dispatched again. -/
def DispatchesAt (run : (ℕ → List AperiodicProcess) → ℕ → SchedState)
    (arrival_stream : ℕ → List AperiodicProcess) (t : ℕ) (p : AperiodicProcess) : Prop :=
  (run arrival_stream t).running = some p ∧
    ∀ t', t = t' + 1 → (run arrival_stream t').running.map (·.id) ≠ some p.id

/-- A scheduler, presented as `run arrival_stream t`, **runs the shortest job at
every dispatch**: on every well-formed stream, whenever it puts a job on the
CPU, no job waiting in `ready` has strictly less work left. -/
def ShortestAtEveryDispatchRun (run : (ℕ → List AperiodicProcess) → ℕ → SchedState) : Prop :=
  ∀ arrival_stream : ℕ → List AperiodicProcess,
    WellFormedStream arrival_stream →
    ∀ (t : ℕ) (p : AperiodicProcess), DispatchesAt run arrival_stream t p →
      ∀ q ∈ (run arrival_stream t).ready, p.remaining ≤ q.remaining

/-- A scheduler has the **convoy effect at some dispatch** when, on some well-formed
stream, it puts a job on the CPU while a job with strictly less work left is waiting. -/
def HasConvoyEffectAtSomeDispatchRun (run : (ℕ → List AperiodicProcess) → ℕ → SchedState) : Prop :=
  ¬ ShortestAtEveryDispatchRun run

/-- The convoy effect at some dispatch, for a one-step scheduler iterated with `runSteps`; every
scheduler except Round Robin has this form. -/
def HasConvoyEffectAtSomeDispatch (step : SchedState → SchedState) : Prop :=
  HasConvoyEffectAtSomeDispatchRun (fun arrival_stream => runSteps arrival_stream step)

/-- Unfolded form of `HasConvoyEffectAtSomeDispatchRun`: an explicit stream, dispatch moment,
dispatched job, and shorter waiting job. -/
theorem hasConvoyEffectAtSomeDispatchRun_iff (run : (ℕ → List AperiodicProcess) → ℕ → SchedState) :
    HasConvoyEffectAtSomeDispatchRun run ↔
      ∃ arrival_stream, WellFormedStream arrival_stream ∧
        ∃ (t : ℕ) (p : AperiodicProcess), DispatchesAt run arrival_stream t p ∧
          ∃ q ∈ (run arrival_stream t).ready, q.remaining < p.remaining := by
  unfold HasConvoyEffectAtSomeDispatchRun ShortestAtEveryDispatchRun
  push Not
  rfl

/-- Whatever holds the CPU after step 0 was dispatched at step 0. -/
theorem dispatchesAt_zero {run : (ℕ → List AperiodicProcess) → ℕ → SchedState}
    {arrival_stream : ℕ → List AperiodicProcess} {p : AperiodicProcess}
    (h : (run arrival_stream 0).running = some p) : DispatchesAt run arrival_stream 0 p :=
  ⟨h, fun t' ht' => by omega⟩

/-! ## The convoy effect on all arrivals at zero -/

/-- A **batch**: jobs that all arrive at time 0, untouched (`remaining = burst`),
with distinct ids.  These are the ready queues a scheduler can actually face at
the start of a well-formed run (`allArrivalsAtZeroStream_wf`). -/
def AllArrivalsAtZero (ready : List AperiodicProcess) : Prop :=
  (∀ p ∈ ready, p.arrival = 0 ∧ p.remaining = p.burst) ∧ (ready.map (·.id)).Nodup

/-- A selection policy never dispatches a job from a batch while a strictly
shorter job of the batch is waiting.  (Only jobs *from* the batch count: a
`select` returning some job outside the queue is not judged here.) -/
def RunsShortestAllArrivalsAtZero (select : List AperiodicProcess → Option AperiodicProcess) :
    Prop :=
  ∀ ready, AllArrivalsAtZero ready → ∀ p ∈ ready, select ready = some p →
    ∀ q ∈ ready, p.burst ≤ q.burst

/-- A selection policy has the **convoy effect on all arrivals at zero** when, for some batch, it
dispatches a job ahead of a strictly shorter one that is already waiting. -/
def HasConvoyEffectAllArrivalsAtZero
    (select : List AperiodicProcess → Option AperiodicProcess) : Prop :=
  ¬ RunsShortestAllArrivalsAtZero select

/-- Unfolded form of `HasConvoyEffectAllArrivalsAtZero`: an explicit batch and an explicit
shorter job that the policy passes over. -/
theorem hasConvoyEffectAllArrivalsAtZero_iff
    (select : List AperiodicProcess → Option AperiodicProcess) :
    HasConvoyEffectAllArrivalsAtZero select ↔
      ∃ ready, AllArrivalsAtZero ready ∧ ∃ p ∈ ready, select ready = some p ∧
        ∃ q ∈ ready, q.burst < p.burst := by
  unfold HasConvoyEffectAllArrivalsAtZero RunsShortestAllArrivalsAtZero
  push Not
  rfl

/-! ### Why "not running the shortest process" is the right definition

`HasConvoyEffectAllArrivalsAtZero` is a property of single decisions, while `totalWait`
measures a whole batch.  They are linked by a non-adjacent version of the
exchange lemma: if the policy dispatches `p` while a strictly shorter `q` is
waiting, then *whatever* order the remaining jobs run in afterwards -- `q` sits
somewhere in it, as `mid ++ q :: post` -- swapping `p` and `q` strictly lowers
total waiting time.  Conversely, if every such swap helps, `q` really was
shorter.

So `hasConvoyEffectAllArrivalsAtZero_iff_swap_improves` says: a policy has the batch convoy
effect exactly when one of its dispatch decisions is provably wasteful,
independently of everything the scheduler does later.
-/

/-- **Convoy effect on all arrivals at zero = a provably wasteful dispatch.** A policy has the
convoy effect on all arrivals at zero iff, for some batch, it dispatches `p` while some other
waiting job `q` exists such that swapping `p` and `q` strictly lowers total
waiting time in *every* continuation `mid ++ q :: post`. -/
theorem hasConvoyEffectAllArrivalsAtZero_iff_swap_improves
    (select : List AperiodicProcess → Option AperiodicProcess) :
    HasConvoyEffectAllArrivalsAtZero select ↔
      ∃ ready, AllArrivalsAtZero ready ∧ ∃ p ∈ ready, select ready = some p ∧
        ∃ q ∈ ready.erase p, ∀ mid post : List ℕ,
        totalWait (q.burst :: (mid ++ p.burst :: post)) <
          totalWait (p.burst :: (mid ++ q.burst :: post)) := by
  rw [hasConvoyEffectAllArrivalsAtZero_iff]
  constructor
  · rintro ⟨ready, h_atZero, p, hp, h_sel, q, hq, h_lt⟩
    have h_ne : q ≠ p := fun h_eq => by subst h_eq; omega
    exact ⟨ready, h_atZero, p, hp, h_sel, q, List.mem_erase_of_ne h_ne |>.mpr hq,
      fun mid post => totalWait_swap_far_lt mid post h_lt⟩
  · rintro ⟨ready, h_atZero, p, hp, h_sel, q, hq, h_swap⟩
    -- the two-job continuation already pins down `q.burst < p.burst`
    have h_lt := h_swap [] []
    simp only [List.nil_append, totalWait_cons, List.length_cons, List.length_nil,
      totalWait_nil] at h_lt
    exact ⟨ready, h_atZero, p, hp, h_sel, q, List.mem_of_mem_erase hq, by omega⟩

/-! ## The convoy effect at some step

The convoy effect at some step watches every step, not just dispatches: at some step
of some well-formed arrival stream, a job is waiting in `ready` with strictly
less work left than the job holding the CPU.

* FCFS and RR have it on `convoyArrivalStream`, where both jobs are present
  from the start.
* Non-preemptive SJF has it on `lateConvoyArrivalStream`, where the short job
  arrives after the long one has been dispatched -- even though SJF has no
  convoy effect at some dispatch.
* SRTF never has it: preemption always hands the CPU to the job with least
  remaining work.
-/

/-- A scheduler, presented as `run arrival_stream t`, always **runs the job with
the least remaining work**: whenever a job is on the CPU, no waiting job has
strictly less work left. -/
def ShortestAtEveryStepRun (run : (ℕ → List AperiodicProcess) → ℕ → SchedState) : Prop :=
  ∀ arrival_stream : ℕ → List AperiodicProcess,
    WellFormedStream arrival_stream →
    ∀ (t : ℕ) (p : AperiodicProcess), (run arrival_stream t).running = some p →
      ∀ q ∈ (run arrival_stream t).ready, p.remaining ≤ q.remaining

/-- A scheduler has the **convoy effect at some step** when, on some well-formed
arrival stream, a job with strictly less work left waits behind the running
job. -/
def HasConvoyEffectAtSomeStepRun (run : (ℕ → List AperiodicProcess) → ℕ → SchedState) : Prop :=
  ¬ ShortestAtEveryStepRun run

/-- The convoy effect at some step for a one-step scheduler iterated with `runSteps`;
every scheduler except Round Robin has this form. -/
def HasConvoyEffectAtSomeStep (step : SchedState → SchedState) : Prop :=
  HasConvoyEffectAtSomeStepRun (fun arrival_stream => runSteps arrival_stream step)

/-- Unfolded form of `HasConvoyEffectAtSomeStepRun`: an explicit stream, step,
running job, and shorter waiting job. -/
theorem hasConvoyEffectAtSomeStepRun_iff (run : (ℕ → List AperiodicProcess) → ℕ → SchedState) :
    HasConvoyEffectAtSomeStepRun run ↔
      ∃ arrival_stream, WellFormedStream arrival_stream ∧
        ∃ (t : ℕ) (p : AperiodicProcess), (run arrival_stream t).running = some p ∧
          ∃ q ∈ (run arrival_stream t).ready, q.remaining < p.remaining := by
  unfold HasConvoyEffectAtSomeStepRun ShortestAtEveryStepRun
  push Not
  rfl

/-! ## How the three notions relate -/

/-- Running the shortest job at every step in particular runs it at every
dispatch. -/
theorem shortestAtEveryStepRun_imp_atEveryDispatch
    {run : (ℕ → List AperiodicProcess) → ℕ → SchedState} (h : ShortestAtEveryStepRun run) :
    ShortestAtEveryDispatchRun run :=
  fun arrival_stream h_wf t p h_disp => h arrival_stream h_wf t p h_disp.1

/-- **The convoy effect implies the convoy effect at some step.** -/
theorem hasConvoyEffectAtSomeDispatchRun_imp_atSomeStep
    {run : (ℕ → List AperiodicProcess) → ℕ → SchedState}
    (h : HasConvoyEffectAtSomeDispatchRun run) : HasConvoyEffectAtSomeStepRun run :=
  fun h_short => h (shortestAtEveryStepRun_imp_atEveryDispatch h_short)

/-- The arrival stream that releases `ready` at time 0 and nothing afterwards. -/
def allArrivalsAtZeroStream (ready : List AperiodicProcess) : ℕ → List AperiodicProcess
  | 0 => ready
  | _ => []

theorem mem_allArrivalsAtZeroStream {ready : List AperiodicProcess} {p : AperiodicProcess} {t : ℕ}
    (h : p ∈ allArrivalsAtZeroStream ready t) : t = 0 ∧ p ∈ ready := by
  rcases t with _ | t <;> simp_all [allArrivalsAtZeroStream]

/-- Releasing a batch at time 0 is a well-formed arrival stream. -/
theorem allArrivalsAtZeroStream_wf {ready : List AperiodicProcess}
    (h_atZero : AllArrivalsAtZero ready) :
    WellFormedStream (allArrivalsAtZeroStream ready) where
  consistent p t h := by
    obtain ⟨rfl, hp⟩ := mem_allArrivalsAtZeroStream h
    exact (h_atZero.1 p hp).1
  fresh p t h := (h_atZero.1 p (mem_allArrivalsAtZeroStream h).2).2
  unique p1 p2 t1 t2 h1 h2 h_id := by
    obtain ⟨rfl, hp1⟩ := mem_allArrivalsAtZeroStream h1
    obtain ⟨rfl, hp2⟩ := mem_allArrivalsAtZeroStream h2
    exact ⟨rfl, List.inj_on_of_nodup_map h_atZero.2 hp1 hp2 h_id⟩

/-- **The convoy effect on all arrivals at zero is the convoy effect at step 0.** If a
non-preemptive policy passes over a shorter job in some batch, then releasing
that batch at time 0 makes it do so in a real run: at step 0 it dispatches the
chosen job while the shorter one waits. -/
theorem hasConvoyEffectAllArrivalsAtZero_imp_hasConvoyEffectAtSomeDispatch
    (select : List AperiodicProcess → Option AperiodicProcess)
    (h : HasConvoyEffectAllArrivalsAtZero select) :
    HasConvoyEffectAtSomeDispatch (stepNonPreemptive select) := by
  obtain ⟨ready, h_atZero, p, hp, h_sel, q, hq, h_lt⟩ :=
    (hasConvoyEffectAllArrivalsAtZero_iff select).mp h
  have h_ne : q ≠ p := fun h_eq => by subst h_eq; omega
  rw [HasConvoyEffectAtSomeDispatch, hasConvoyEffectAtSomeDispatchRun_iff]
  refine ⟨allArrivalsAtZeroStream ready, allArrivalsAtZeroStream_wf h_atZero, 0, p,
    dispatchesAt_zero ?_, q, ?_, ?_⟩
  · simp [runSteps, stepNonPreemptive, allArrivalsAtZeroStream, h_sel]
  · simpa [runSteps, stepNonPreemptive, allArrivalsAtZeroStream, h_sel] using
      (List.mem_erase_of_ne h_ne).mpr hq
  · -- in a batch nothing has run yet, so `remaining` is the burst
    rw [(h_atZero.1 q hq).2, (h_atZero.1 p hp).2]
    exact h_lt

/-- **The convoy effect on all arrivals at zero implies the convoy effect at some step.** -/
theorem hasConvoyEffectAllArrivalsAtZero_imp_atSomeStep
    (select : List AperiodicProcess → Option AperiodicProcess)
    (h : HasConvoyEffectAllArrivalsAtZero select) :
    HasConvoyEffectAtSomeStep (stepNonPreemptive select) :=
  hasConvoyEffectAtSomeDispatchRun_imp_atSomeStep
    (hasConvoyEffectAllArrivalsAtZero_imp_hasConvoyEffectAtSomeDispatch select h)

end ConvoyEffect
