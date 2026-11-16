/-
Copyright (c) 2026 Choo Kye Yong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Choo Kye Yong
-/
import FypSchedulingAlgorithms.AperiodicSchedulers.ConvoyEffect.Optimality.NoOptimalNonPreemptiveOnEveryStream
import FypSchedulingAlgorithms.AperiodicSchedulers.PreemptiveLemmas
import FypSchedulingAlgorithms.AperiodicSchedulers.Schedule
import FypSchedulingAlgorithms.PreemptiveRuns
import FypSchedulingAlgorithms.ListLemmas
import Mathlib.Data.List.Nodup

/-!
# Admissible schedules

To compare a scheduler with *every* possible way of running the jobs --
preemptive or not, clairvoyant or not -- this file uses runs without a
step function: a **schedule** `σ : ℕ → Option ℕ` (`Schedule`, defined in
`AperiodicSchedulers/Schedule` with `ticksBefore`, `scheduleOfRun` and `runSchedule`)
names, for each step `t`, the job (by id) that holds the CPU after step `t`.  As in
`runSteps` (see the tick convention in `Step`), that job receives the tick of step `t + 1`;
the jobs after step `t` are those released at times `0, …, t`
(`arrivedBy`), and job `i` has had `ticksBefore σ i t` ticks by then.

**The class** (`IsAdmissible`): whenever `σ` puts job `i` on the CPU after step
`t`, a job with id `i` has been released by time `t` and has had fewer ticks than
its burst.  So:

* *at most one job per tick* (`σ t` is a single option);
* *no job runs before it is released*, and *none runs more than its burst*;
* *nothing is invented or lost*: `unfinished` and `waiting` are computed from
  the stream, not from `σ`, so every released job counts until it has had its
  burst, whether `σ` ever runs it or not.

Everything else is allowed: preempting at any step, idling while jobs wait,
any order, and *clairvoyance* -- `σ` is an arbitrary function and may be chosen
knowing the whole stream.  Like every run of the model, a schedule cannot tick
a job in the step that releases it (a job newly put on the CPU is ticked from
the next step on); this holds for the whole class alike, it is a shift of the
time axis, not a handicap of some schedules.  There are no context-switch
costs, as in the step functions.

**The cost** (`schedWait`): at each step every unfinished job that is not on the
CPU waits one tick.  It is `runWait` for schedules, for every run that neither
invents nor loses jobs at any step (`ConservesJobsAtEveryStep`): the run's schedule
(`scheduleOfRun`) is admissible (`ConservesJobsAtEveryStep.scheduleOfRun_isAdmissible`)
and the run waits exactly what its schedule waits, at every horizon
(`ConservesJobsAtEveryStep.runWait_eq_schedWait`).  The bridge rests on the run
invariant `ConservesJobsAtEveryStep.inSystem_perm`: after every step the jobs in
`ready` and on the CPU are exactly the released, unfinished jobs, each with its burst
less the ticks the schedule gave it.

**Which runs.**  The predicate is stated about the run, not the step, so it covers:

* the run of every step function that neither invents nor loses jobs (`ConservesJobs`,
  `runSteps_conservesJobsAtEveryStep`) -- every preemptive priority scheduler
  (`stepPreemptive_conservesJobs`, SRTF included) and every non-preemptive state-select
  policy (`stepNonPreemptiveStateSelect_conservesJobs`: FCFS, SJF, policies that idle).
  For these the step-level names keep their statements: `inSystem_perm`,
  `runSchedule_isAdmissible`, `ready_length_eq_waiting`, `runWait_eq_schedWait`, all about
  `runSchedule` (defined in `AperiodicSchedulers/Schedule`);
* Round Robin, for every quantum, through its run `runRR` (`runRR_conservesJobsAtEveryStep`,
  `scheduleOfRun_runRR_isAdmissible`, `runWait_runRR_eq_schedWait`).  `stepRR` acts on an
  `RRState` and its choice depends on the slice counter `ticksUsed`, so it is not a
  `SchedState → SchedState`; for each fixed counter its step conserves jobs
  (`stepRR_conservesJobs`), and that is all the run needs.

The run-level predicate is the hook for any other scheduler that carries extra state
from step to step, such as a multilevel feedback queue (queue levels) or aging
(waiting counters): proving its run conserves jobs at every step is enough for the
bridge.  The extra state may record levels or counters, but every waiting job must sit
in `ready` (`runWait` counts only `ready`); an MLFQ whose queues live in the extra state
would have to keep `ready` as their concatenation.  No such scheduler is formalised
here.

**Assumptions.**  Streams are well formed (`WellFormedStream`).  In particular no
id is released twice (`WellFormedStream.ids_nodup`): were a job listed twice, a run
would hold two copies of it that a schedule, which names jobs by id, cannot tell
apart.
-/

namespace ConvoyEffect

open scoped List
open Preemptive

/-! ## Admissible schedules -/

/-- **Admissible schedules.** Whenever `σ` puts job `i` on the CPU after step `t`,
a job with id `i` has been released by time `t` and still has work left: it has
had fewer ticks than its burst. -/
def IsAdmissible (arrival_stream : ℕ → List AperiodicProcess) (σ : Schedule) : Prop :=
  ∀ t i, σ t = some i → ∃ p ∈ arrivedBy arrival_stream t, p.id = i ∧ ticksBefore σ i t < p.burst

/-- The jobs released by time `t` that `σ` has not finished before step `t`. -/
def unfinished (arrival_stream : ℕ → List AperiodicProcess) (σ : Schedule) (t : ℕ) :
    List AperiodicProcess :=
  (arrivedBy arrival_stream t).filter fun p => ticksBefore σ p.id t < p.burst

/-- The jobs waiting after step `t`: unfinished, and not on the CPU. -/
def waiting (arrival_stream : ℕ → List AperiodicProcess) (σ : Schedule) (t : ℕ) :
    List AperiodicProcess :=
  (unfinished arrival_stream σ t).filter fun p => σ t ≠ some p.id

/-- **Waiting time of a schedule** over its first `T` steps: at each step every
waiting job waits one tick.  This is `runWait` for schedules
(`runWait_eq_schedWait`). -/
def schedWait (arrival_stream : ℕ → List AperiodicProcess) (σ : Schedule) (T : ℕ) : ℕ :=
  ((List.range T).map fun t => (waiting arrival_stream σ t).length).sum

/-! ## Steps that neither invent nor lose jobs -/

/-- A step **conserves jobs** if the jobs in the system after it (ready or on
the CPU) are those before it, with the running job ticked, and dropped exactly
when that tick finished it.  The step may reorder `ready` and swap the job on
the CPU, but it adds and loses nothing.  This is `PreemptiveRuns.ConservesJobs`
spelled with the `AperiodicProcess` record update (`conservesJobs_iff`). -/
def ConservesJobs (step : SchedState → SchedState) : Prop :=
  ∀ s : SchedState,
    (step s).ready ++ (step s).running.toList ~
      s.ready ++ (s.running.toList.map fun b => { b with remaining := b.remaining - 1 }).filter
        fun b => 0 < b.remaining

/-- `ConservesJobs` is the job-type-generic `PreemptiveRuns.ConservesJobs`, by
definition. -/
theorem conservesJobs_iff (step : SchedState → SchedState) :
    ConservesJobs step ↔ PreemptiveRuns.ConservesJobs step :=
  Iff.rfl

/-- Dispatching a member of the queue keeps the jobs in the system (the
`AperiodicProcess` case of `PreemptiveRuns.erase_append_singleton_perm`). -/
theorem erase_append_singleton_perm {l : List AperiodicProcess} {p : AperiodicProcess}
    (h : p ∈ l) : l.erase p ++ [p] ~ l :=
  PreemptiveRuns.erase_append_singleton_perm h

/-- **Every preemptive scheduler conserves jobs**, whatever its priority function
(the `AperiodicProcess` case of `PreemptiveRuns.stepPreemptive_conservesJobs`). -/
theorem stepPreemptive_conservesJobs (f : AperiodicProcess → ℤ) :
    ConservesJobs (stepPreemptive AperiodicProcess f) :=
  PreemptiveRuns.stepPreemptive_conservesJobs f

/-- **Every non-preemptive state-select policy conserves jobs** (it only ever
dispatches a waiting job). -/
theorem stepNonPreemptiveStateSelect_conservesJobs {select : SchedState → Option AperiodicProcess}
    (h_mem : DrawsFromReadyQueue select) : ConservesJobs (stepNonPreemptiveStateSelect select) := by
  intro s
  unfold stepNonPreemptiveStateSelect
  rcases hr : s.running with _ | b
  · simp only [Option.toList_none, List.map_nil, List.filter_nil, List.append_nil]
    split
    · simp
    · rename_i p h_sel
      exact erase_append_singleton_perm (h_mem s p h_sel)
  · simp only [AperiodicProcess.process_tick, AperiodicProcess.process_remaining,
      Option.toList_some, List.map_cons, List.map_nil]
    split_ifs with h_done
    · have h0 : ¬ (0 < b.remaining - 1) := by omega
      simp only [List.filter_cons, List.filter_nil, h0, decide_false, Bool.false_eq_true,
        ↓reduceIte, List.append_nil]
      split
      · simp
      · rename_i p h_sel
        exact erase_append_singleton_perm (h_mem s p h_sel)
    · have h0 : 0 < b.remaining - 1 := by omega
      simp [h0]

/-! ## Facts about schedules -/

/-- On a well-formed stream, two jobs released by time `t` with the same id are
the same job. -/
theorem arrivedBy_id_inj {arrival_stream : ℕ → List AperiodicProcess}
    (h_wf : WellFormedStream arrival_stream) {t : ℕ} {p q : AperiodicProcess}
    (hp : p ∈ arrivedBy arrival_stream t) (hq : q ∈ arrivedBy arrival_stream t)
    (h_id : p.id = q.id) : p = q := by
  obtain ⟨t1, -, hp⟩ := mem_arrivedBy.mp hp
  obtain ⟨t2, -, hq⟩ := mem_arrivedBy.mp hq
  exact (h_wf.unique p q t1 t2 hp hq h_id).2

/-- In a list in which no two jobs share an id, exactly one job has the id of
`q`, if `q` is in it. -/
theorem length_filter_id_ne {l : List AperiodicProcess} (h_nodup : l.Nodup)
    (h_inj : ∀ p ∈ l, ∀ q ∈ l, p.id = q.id → p = q) {q : AperiodicProcess} (hq : q ∈ l) :
    (l.filter fun p => some q.id ≠ some p.id).length + 1 = l.length := by
  have h_perm := List.perm_cons_erase hq
  rw [(h_perm.filter _).length_eq, h_perm.length_eq, List.filter_cons]
  simp only [ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte,
    List.length_cons, Nat.add_right_cancel_iff]
  rw [List.filter_eq_self.mpr]
  intro p hp
  have h_ne : p ≠ q := ((h_nodup.mem_erase_iff).mp hp).1
  have hp' : p ∈ l := List.mem_of_mem_erase hp
  simpa [Option.some.injEq] using fun h_id => h_ne (h_inj p hp' q hq h_id.symm)

/-- **What waiting looks like.** For an admissible schedule on a well-formed
stream, the waiting jobs are the unfinished ones less the one on the CPU, if any. -/
theorem length_waiting {arrival_stream : ℕ → List AperiodicProcess}
    (h_wf : WellFormedStream arrival_stream)
    {σ : Schedule} (h_adm : IsAdmissible arrival_stream σ) (t : ℕ) :
    (waiting arrival_stream σ t).length =
      (unfinished arrival_stream σ t).length - (σ t).toList.length := by
  unfold waiting
  rcases h : σ t with _ | i
  · simp
  · obtain ⟨q, hq, rfl, h_lt⟩ := h_adm t _ h
    have hq' : q ∈ unfinished arrival_stream σ t := List.mem_filter.mpr ⟨hq, by simpa using h_lt⟩
    have := length_filter_id_ne (l := unfinished arrival_stream σ t)
      ((h_wf.arrivedBy_nodup t).filter _)
      (fun p hp q hq => arrivedBy_id_inj h_wf (List.mem_of_mem_filter hp)
        (List.mem_of_mem_filter hq)) hq'
    simp only [Option.toList_some, List.length_singleton]
    omega

/-- **Every admissible schedule leaves all but at most one unfinished job
waiting.** -/
theorem length_unfinished_sub_one_le {arrival_stream : ℕ → List AperiodicProcess}
    (h_wf : WellFormedStream arrival_stream)
    {σ : Schedule} (h_adm : IsAdmissible arrival_stream σ) (t : ℕ) :
    (unfinished arrival_stream σ t).length - 1 ≤ (waiting arrival_stream σ t).length := by
  rw [length_waiting h_wf h_adm]
  rcases σ t <;> simp

/-- Waiting can only grow with the horizon. -/
theorem schedWait_mono (arrival_stream : ℕ → List AperiodicProcess) (σ : Schedule) {T T' : ℕ}
    (h : T ≤ T') : schedWait arrival_stream σ T ≤ schedWait arrival_stream σ T' := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  unfold schedWait
  rw [List.range_add, List.map_append, List.sum_append]
  exact Nat.le_add_right _ _

/-! ## Runs that neither invent nor lose jobs -/

/-- The jobs in the system: waiting, or on the CPU. -/
def inSystem (s : SchedState) : List AperiodicProcess := s.ready ++ s.running.toList

/-- A run **conserves jobs at every step** if none of its steps invents or loses a job.  After
step 0 the jobs in the system (`inSystem`) are the arrivals of time 0.  After step `t + 1` they
are the jobs waiting after step `t`, the arrivals of time `t + 1`, and the job on the CPU after
step `t`, ticked, kept exactly when that tick left it work.  As with `ConservesJobs`, a step may
reorder the queue and swap the job on the CPU, but it adds and loses nothing.

This is `ConservesJobs` asked of a run instead of a step function
(`runSteps_conservesJobsAtEveryStep`), and it is all the bridge to schedules needs
(`ConservesJobsAtEveryStep.runWait_eq_schedWait`).  Since it only looks at the
`SchedState` after each step, it also covers schedulers that carry extra state from step to
step and so are not a `SchedState → SchedState`: Round Robin's slice counter
(`runRR_conservesJobsAtEveryStep`), and in the same way the queue levels of a multilevel
feedback queue or the counters of an aging scheme, which are not formalised here.  The extra
state may record levels or counters, but every waiting job must sit in `ready` (`runWait`
counts only `ready`); an MLFQ whose queues live in the extra state would have to keep `ready`
as their concatenation. -/
def ConservesJobsAtEveryStep (arrival_stream : ℕ → List AperiodicProcess)
    (run : ℕ → SchedState) : Prop :=
  inSystem (run 0) ~ arrival_stream 0 ∧
    ∀ t, inSystem (run (t + 1)) ~
      ((run t).ready ++ arrival_stream (t + 1)) ++
        ((run t).running.toList.map fun b => { b with remaining := b.remaining - 1 }).filter
          fun b => 0 < b.remaining

/-- **The run of a job-conserving step conserves jobs at every step**, on every stream. -/
theorem runSteps_conservesJobsAtEveryStep {step : SchedState → SchedState}
    (h_step : ConservesJobs step) (arrival_stream : ℕ → List AperiodicProcess) :
    ConservesJobsAtEveryStep arrival_stream (runSteps arrival_stream step) := by
  refine ⟨?_, fun t => h_step _⟩
  simpa [inSystem, runSteps] using h_step { SchedStateMethods.init with ready := arrival_stream 0 }

/-- **A Round Robin step conserves jobs**, whatever the quantum and the slice counter: on the
`SchedState` inside its `RRState`, for each fixed `ticksUsed`, `stepRR` is a job-conserving
step.  (`stepRR` itself is not a `SchedState → SchedState`, since its choice depends on
`ticksUsed`.) -/
theorem stepRR_conservesJobs (quantum ticksUsed : ℕ) :
    ConservesJobs fun s => (stepRR quantum { sched := s, ticksUsed := ticksUsed }).sched := by
  intro s
  unfold stepRR
  rcases hr : s.running with _ | p
  · rcases hq : s.ready with _ | ⟨nx, ps⟩ <;> simp [hr, hq]
  · by_cases h_done : p.remaining ≤ 1
    · rcases hq : s.ready with _ | ⟨nx, ps⟩ <;> simp [hr, hq, h_done]
    · have h0 : 0 < p.remaining - 1 := by omega
      by_cases h_slice : ticksUsed ≥ quantum - 1
      · rcases hq : s.ready with _ | ⟨nx, ps⟩
        · simp [hr, hq, h_done, h0, h_slice]
        · simp [hr, hq, h_done, h0, h_slice]
          have := List.perm_append_singleton nx (ps ++ [{ p with remaining := p.remaining - 1 }])
          rwa [List.append_assoc, List.singleton_append] at this
      · simp [hr, h_done, h0, h_slice]

/-- **Every Round Robin run conserves jobs at every step**, for every quantum (quantum 0
behaves as 1) and on every stream. -/
theorem runRR_conservesJobsAtEveryStep (quantum : ℕ)
    (arrival_stream : ℕ → List AperiodicProcess) :
    ConservesJobsAtEveryStep arrival_stream (runRR quantum arrival_stream) := by
  refine ⟨?_, fun t =>
    stepRR_conservesJobs quantum (runStepsRR quantum arrival_stream t).ticksUsed _⟩
  simpa [inSystem, runStepsRR] using
    stepRR_conservesJobs quantum 0 { SchedStateMethods.init with ready := arrival_stream 0 }

/-! ## Jobs as a schedule leaves them -/

/-- Job `p` as it stands after step `t` of `σ`: its burst less the ticks it has had. -/
def jobAt (σ : Schedule) (t : ℕ) (p : AperiodicProcess) : AperiodicProcess :=
  { p with remaining := p.burst - ticksBefore σ p.id t }

/-- A fresh job, as it stands before its first tick, is itself. -/
theorem jobAt_fresh {σ : Schedule} {t : ℕ} {p : AperiodicProcess}
    (h_fresh : p.remaining = p.burst) (h_zero : ticksBefore σ p.id t = 0) : jobAt σ t p = p := by
  cases p
  simp_all [jobAt]

/-! ## The bridge, for runs -/

section RunBridge

variable {arrival_stream : ℕ → List AperiodicProcess}

/-- **The run invariant.** After every step of a run that conserves jobs at every step, the
jobs in the system are exactly the jobs its schedule has released and not finished, each with
its burst less the ticks the schedule gave it. -/
theorem ConservesJobsAtEveryStep.inSystem_perm {run : ℕ → SchedState}
    (h_run : ConservesJobsAtEveryStep arrival_stream run)
    (h_wf : WellFormedStream arrival_stream) (t : ℕ) :
    inSystem (run t) ~
      (unfinished arrival_stream (scheduleOfRun run) t).map (jobAt (scheduleOfRun run) t) := by
  set σ := scheduleOfRun run with hσ
  induction t using Nat.strong_induction_on with
  | _ t ih =>
  -- a job on the CPU after an earlier step was released by then
  have h_src : ∀ t' < t, ∀ i, σ t' = some i → ∃ q ∈ arrivedBy arrival_stream t', q.id = i := by
    intro t' ht' i hi
    obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp hi
    have hb' : b ∈ inSystem (run t') := by simp [inSystem, hb]
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ((ih t' ht').subset hb')
    exact ⟨q, List.mem_of_mem_filter hq, rfl⟩
  -- so a job released at time `t` has had no ticks before step `t`
  have h_new : ∀ p ∈ arrival_stream t, ticksBefore σ p.id t = 0 := by
    intro p hp
    refine ticksBefore_eq_zero fun t' ht' h_eq => ?_
    obtain ⟨q, hq, h_id⟩ := h_src t' ht' _ h_eq
    obtain ⟨t'', ht'', hq⟩ := mem_arrivedBy.mp hq
    have := (h_wf.unique q p t'' t hq hp h_id).1
    omega
  have h_fresh : ∀ p ∈ arrival_stream t, p.burst - ticksBefore σ p.id t = p.burst ∧
      jobAt σ t p = p := fun p hp =>
    ⟨by rw [h_new p hp]; rfl, jobAt_fresh (h_wf.fresh p t hp) (h_new p hp)⟩
  have h_arr : ((arrival_stream t).filter fun p => ticksBefore σ p.id t < p.burst).map
      (jobAt σ t) = arrival_stream t := by
    rw [List.filter_eq_self.mpr fun p hp => by simp [h_new p hp, p.burst_exceed_zero]]
    exact (List.map_congr_left fun p hp => (h_fresh p hp).2).trans (List.map_id _)
  cases t with
  | zero =>
    unfold unfinished
    rw [arrivedBy_zero, h_arr]
    exact h_run.1
  | succ t =>
    set S := run t with hS
    refine (h_run.2 t).trans ?_
    have ih_t := ih t (by omega)
    rw [← hS] at ih_t
    unfold unfinished
    rw [arrivedBy_succ, List.filter_append, List.map_append, h_arr]
    -- the jobs released earlier: only the one on the CPU has changed
    suffices h : S.ready ++
        (S.running.toList.map fun b => { b with remaining := b.remaining - 1 }).filter
          (fun b => 0 < b.remaining) ~ ((arrivedBy arrival_stream t).filter
          fun p => ticksBefore σ p.id (t + 1) < p.burst).map (jobAt σ (t + 1)) by
      rw [List.append_assoc]
      exact (List.Perm.append_left _ List.perm_append_comm).trans
        (by rw [← List.append_assoc]; exact h.append_right _)
    rcases hr : S.running with _ | b
    · -- an idle CPU: nobody was ticked
      have hσt : σ t = none := by simp [hσ, scheduleOfRun, ← hS, hr]
      have h_same : ∀ p : AperiodicProcess, ticksBefore σ p.id (t + 1) = ticksBefore σ p.id t :=
        fun p => ticksBefore_succ_of_ne (by simp [hσt])
      have hJ : jobAt σ (t + 1) = jobAt σ t := funext fun p => by simp [jobAt, h_same]
      simp only [h_same, hJ, Option.toList_none, List.map_nil, List.filter_nil, List.append_nil]
      simpa [inSystem, hr, unfinished] using ih_t
    · -- `b` was on the CPU: it is some released job `q`, which receives the tick
      have hσt : σ t = some b.id := by simp [hσ, scheduleOfRun, ← hS, hr]
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp
        (ih_t.subset (show b ∈ inSystem S by simp [inSystem, hr]))
      have hqL := List.mem_of_mem_filter hq
      have hq_lt : ticksBefore σ q.id t < q.burst := by simpa using (List.mem_filter.mp hq).2
      have h_tick : ticksBefore σ q.id (t + 1) = ticksBefore σ q.id t + 1 := by
        simp [ticksBefore_succ, hσt, jobAt]
      obtain ⟨rest, h_old, h_upd⟩ := filter_map_update (h_wf.arrivedBy_nodup t) hqL
        (fun p => decide (ticksBefore σ p.id t < p.burst))
        (fun p => decide (ticksBefore σ p.id (t + 1) < p.burst)) (jobAt σ t) (jobAt σ (t + 1))
        (fun p hp h_ne => by
          have h_id : p.id ≠ q.id := fun h => h_ne (arrivedBy_id_inj h_wf hp hqL h)
          have h_same : ticksBefore σ p.id (t + 1) = ticksBefore σ p.id t :=
            ticksBefore_succ_of_ne (by simp [hσt, jobAt, Ne.symm h_id])
          exact ⟨by simp [h_same], by simp [jobAt, h_same]⟩)
      refine List.Perm.trans ?_ h_upd.symm
      simp only [hq_lt, decide_true, ↓reduceIte, List.singleton_append] at h_old
      have h_ready : S.ready ~ rest := by
        have := (ih_t.trans h_old)
        simp only [inSystem, hr, Option.toList_some] at this
        exact ((List.perm_append_singleton _ _).symm.trans this).cons_inv
      have h_tf : ([jobAt σ t q].map fun b => { b with remaining := b.remaining - 1 }).filter
          (fun b => 0 < b.remaining) =
          if decide (ticksBefore σ q.id (t + 1) < q.burst) then [jobAt σ (t + 1) q] else [] := by
        simp only [List.map_cons, List.map_nil, List.filter_cons, List.filter_nil, jobAt, h_tick]
        by_cases h : ticksBefore σ q.id t + 1 < q.burst
        · simp only [show 0 < q.burst - ticksBefore σ q.id t - 1 by omega, decide_true,
            ↓reduceIte, h]
          congr 2
        · simp only [show ¬ 0 < q.burst - ticksBefore σ q.id t - 1 by omega, decide_false,
            Bool.false_eq_true, ↓reduceIte, h]
      simp only [Option.toList_some]
      rw [h_tf]
      exact List.perm_append_comm.trans (h_ready.append_left _)

/-- **A run that conserves jobs at every step is an admissible schedule**: it only ever runs a
released job with work left. -/
theorem ConservesJobsAtEveryStep.scheduleOfRun_isAdmissible {run : ℕ → SchedState}
    (h_run : ConservesJobsAtEveryStep arrival_stream run)
    (h_wf : WellFormedStream arrival_stream) :
    IsAdmissible arrival_stream (scheduleOfRun run) := by
  intro t i h
  obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ((h_run.inSystem_perm h_wf t).subset
    (show b ∈ inSystem _ by simp [inSystem, hb]))
  exact ⟨q, List.mem_of_mem_filter hq, rfl, by simpa [jobAt] using (List.mem_filter.mp hq).2⟩

/-- After each step of a run that conserves jobs at every step, the ready queue holds exactly
the jobs its schedule leaves waiting. -/
theorem ConservesJobsAtEveryStep.ready_length_eq_waiting {run : ℕ → SchedState}
    (h_run : ConservesJobsAtEveryStep arrival_stream run)
    (h_wf : WellFormedStream arrival_stream) (t : ℕ) :
    (run t).ready.length = (waiting arrival_stream (scheduleOfRun run) t).length := by
  rw [length_waiting h_wf (h_run.scheduleOfRun_isAdmissible h_wf)]
  have := (h_run.inSystem_perm h_wf t).length_eq
  simp only [inSystem, List.length_append, List.length_map] at this
  cases h : (run t).running
  · simp_all [scheduleOfRun]
  · simp_all [scheduleOfRun]
    omega

/-- **The bridge, for runs: a run waits what its schedule waits.** For every run function
whose run on a well-formed stream conserves jobs at every step (the run of every job-conserving
step function, every Round Robin run), `runWait` of the run is `schedWait` of the schedule it
follows, at every horizon. -/
theorem ConservesJobsAtEveryStep.runWait_eq_schedWait
    {run : (ℕ → List AperiodicProcess) → ℕ → SchedState}
    (h_run : ConservesJobsAtEveryStep arrival_stream (run arrival_stream))
    (h_wf : WellFormedStream arrival_stream) (T : ℕ) :
    runWait run arrival_stream T =
      schedWait arrival_stream (scheduleOfRun (run arrival_stream)) T := by
  unfold runWait schedWait
  congr 1
  exact List.map_congr_left fun t _ => h_run.ready_length_eq_waiting h_wf t

end RunBridge

/-! ## The bridge, for step functions -/

section Bridge

variable {step : SchedState → SchedState} (h_step : ConservesJobs step)
  {arrival_stream : ℕ → List AperiodicProcess} (h_wf : WellFormedStream arrival_stream)
include h_step h_wf

/-- **The run invariant.** After every step of a job-conserving run, the jobs in
the system are exactly the jobs its schedule has released and not finished,
each with its burst less the ticks the schedule gave it. -/
theorem inSystem_perm (t : ℕ) :
    inSystem (runSteps arrival_stream step t) ~
      (unfinished arrival_stream (runSchedule step arrival_stream) t).map
        (jobAt (runSchedule step arrival_stream) t) :=
  (runSteps_conservesJobsAtEveryStep h_step arrival_stream).inSystem_perm h_wf t

/-- **A run is an admissible schedule**: it only ever runs a released job with
work left. -/
theorem runSchedule_isAdmissible :
    IsAdmissible arrival_stream (runSchedule step arrival_stream) :=
  (runSteps_conservesJobsAtEveryStep h_step arrival_stream).scheduleOfRun_isAdmissible h_wf

/-- After each step of a run, the ready queue holds exactly the jobs its
schedule leaves waiting. -/
theorem ready_length_eq_waiting (t : ℕ) :
    (runSteps arrival_stream step t).ready.length =
      (waiting arrival_stream (runSchedule step arrival_stream) t).length :=
  (runSteps_conservesJobsAtEveryStep h_step arrival_stream).ready_length_eq_waiting h_wf t

/-- **The bridge: a run waits what its schedule waits.** For every
job-conserving step (every preemptive scheduler, every non-preemptive state-select
policy), on every well-formed stream, `runWait` of the run is `schedWait` of the
schedule it follows, at every horizon. -/
theorem runWait_eq_schedWait (T : ℕ) :
    runWait (runSteps · step) arrival_stream T =
      schedWait arrival_stream (runSchedule step arrival_stream) T :=
  (runSteps_conservesJobsAtEveryStep h_step arrival_stream).runWait_eq_schedWait
    (run := (runSteps · step)) h_wf T

end Bridge

/-! ## Round Robin -/

/-- **A Round Robin run is an admissible schedule** (the schedule it follows is admissible),
for every quantum, on every well-formed stream. -/
theorem scheduleOfRun_runRR_isAdmissible (quantum : ℕ)
    {arrival_stream : ℕ → List AperiodicProcess} (h_wf : WellFormedStream arrival_stream) :
    IsAdmissible arrival_stream (scheduleOfRun (runRR quantum arrival_stream)) :=
  (runRR_conservesJobsAtEveryStep quantum arrival_stream).scheduleOfRun_isAdmissible h_wf

/-- **A Round Robin run waits what its schedule waits**, for every quantum, on every
well-formed stream, at every horizon. -/
theorem runWait_runRR_eq_schedWait (quantum : ℕ)
    {arrival_stream : ℕ → List AperiodicProcess} (h_wf : WellFormedStream arrival_stream)
    (T : ℕ) :
    runWait (runRR quantum) arrival_stream T =
      schedWait arrival_stream (scheduleOfRun (runRR quantum arrival_stream)) T :=
  (runRR_conservesJobsAtEveryStep quantum arrival_stream).runWait_eq_schedWait
    (run := runRR quantum) h_wf T

end ConvoyEffect
