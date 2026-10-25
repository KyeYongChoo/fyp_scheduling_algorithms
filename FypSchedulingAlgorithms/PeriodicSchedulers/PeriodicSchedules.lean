/-
Copyright (c) 2026 Choo Kye Yong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Choo Kye Yong
-/
import FypSchedulingAlgorithms.PeriodicSchedulers.PeriodicStep
import FypSchedulingAlgorithms.PreemptiveRuns
import FypSchedulingAlgorithms.ListLemmas
import FypSchedulingAlgorithms.ProcessSimpLemmas
import FypSchedulingAlgorithms.SchedStateSimpLemmas
import Mathlib.Data.List.Nodup

/-!
# Admissible schedules for periodic jobs

The periodic counterpart of `ConvoyEffect/Schedules.lean`.  A **schedule**
`σ : PSchedule = ℕ → Option (ℕ × ℕ)` names, for each step `t`, the job that holds the
CPU in the state after step `t`.  As in `runSteps` (tick convention in `Step`), that job
receives the tick of step `t + 1`.  All jobs of a periodic task share the task's `id`,
so a job is named by its **key** `(id, arrival)` (`key`).

The jobs of a task set `tasks` are those of `PeriodicProcess.releasesAt tasks`, which is
synchronous: every task releases a fresh job at time 0 and then every `period`.  The
jobs released by time `t` are `jobsBy tasks t`, and job `k` has had `ticksBefore σ k t`
ticks by the state after step `t`.

* `IsAdmissible tasks σ`: whenever `σ` puts job `k` on the CPU after step `t`, a job with
  key `k` has been released by time `t` and has had fewer ticks than its burst.
  Everything else is allowed, clairvoyance included (see `Schedules.lean`).
* `unfinished tasks σ t`: the released jobs that `σ` has not finished by the state after
  step `t`.
* `LateAt tasks σ t`: some unfinished job has absolute deadline `absDeadline p ≤ t`.  A
  job released at `r` with relative deadline `D` gets the `D` usable ticks of steps
  `r+1 … r+D`, so it is late at `t` iff `r + D ≤ t` and it is still unfinished after
  step `t` (the miss rule of `PeriodicProcess.missedDeadlines`).

Sums over the released jobs, such as the work still owed by jobs with deadline at most
`d`, are written as filtered sums over `jobsBy tasks t` with
`p.burst - ticksBefore σ (key p) t`.

**The bridge.**  For any step function that conserves jobs
(`PreemptiveRuns.ConservesJobs`; every `stepPreemptive f`, so `stepRMS` and `stepEDF`),
a run is described by its schedule `runSchedule step tasks`:

* `inSystem_perm`: after every step, the ready and running jobs are exactly the
  released, unfinished jobs, each with its burst less the ticks the schedule gave it;
* `runSchedule_isAdmissible`: the run's schedule is admissible;
* `missedDeadlines_ne_nil_iff`: the run lists a missed deadline after step `t` iff its
  schedule is late at `t` (for steps that advance the clock by one, as every
  `stepPreemptive f` does: `missedDeadlines_ne_nil_iff_preemptive`).

Facts used by the optimality proofs: an admissible schedule gives a job no tick before
its release (`ticksBefore_of_mem_releasesAt`) and never more ticks than its burst
(`ticksBefore_le_burst`); a preemptive scheduler idles only when every released job is
finished (`unfinished_eq_nil_of_idle`) and runs an unfinished job of highest priority
(`runSchedule_stepPreemptive_max`).

**Assumption.**  Task ids are distinct (`(tasks.map PeriodicProcess.id).Nodup`).  Then
keys are unique among released jobs (`key_injective`, `jobsBy_nodup`).  `TaskSet`
bundles this with positive periods, which the bridge does not need.
-/

namespace Periodic

open scoped List
open PreemptiveRuns

/-! ## Task sets and their jobs -/

/-- The usual hypotheses on a periodic task set: distinct task ids and positive
periods.  The bridge in this file only needs `ids_nodup`. -/
structure TaskSet (tasks : List PeriodicProcess) : Prop where
  ids_nodup : (tasks.map PeriodicProcess.id).Nodup
  period_pos : ∀ τ ∈ tasks, 0 < τ.period

/-- The key of a periodic job: its task id and its release time. -/
def key (p : PeriodicProcess) : ℕ × ℕ := (p.id, p.arrival)

/-- The absolute deadline of a job: release time plus relative deadline. -/
def absDeadline (p : PeriodicProcess) : ℕ := p.arrival + p.deadline

/-- The jobs released by time `t`, in order of release. -/
def jobsBy (tasks : List PeriodicProcess) (t : ℕ) : List PeriodicProcess :=
  (List.range (t + 1)).flatMap (PeriodicProcess.releasesAt tasks)

/-- What a release is: a fresh copy of a task whose period divides the time, stamped
with that time. -/
theorem mem_releasesAt {tasks : List PeriodicProcess} {t : ℕ} {p : PeriodicProcess} :
    p ∈ PeriodicProcess.releasesAt tasks t ↔
      ∃ τ ∈ tasks, t % τ.period = 0 ∧ { τ with arrival := t, remaining := τ.burst } = p := by
  simp [PeriodicProcess.releasesAt, and_assoc]

/-- A job released at time `t` carries `t` as its release time. -/
theorem arrival_of_mem_releasesAt {tasks : List PeriodicProcess} {t : ℕ} {p : PeriodicProcess}
    (h : p ∈ PeriodicProcess.releasesAt tasks t) : p.arrival = t := by
  obtain ⟨τ, -, -, rfl⟩ := mem_releasesAt.mp h
  rfl

/-- A released job is fresh: it has all its burst left. -/
theorem remaining_of_mem_releasesAt {tasks : List PeriodicProcess} {t : ℕ}
    {p : PeriodicProcess} (h : p ∈ PeriodicProcess.releasesAt tasks t) :
    p.remaining = p.burst := by
  obtain ⟨τ, -, -, rfl⟩ := mem_releasesAt.mp h
  rfl

/-- Two tasks with the same id are the same task. -/
theorem task_eq_of_id_eq {tasks : List PeriodicProcess}
    (h_ids : (tasks.map PeriodicProcess.id).Nodup) {τ τ' : PeriodicProcess}
    (hτ : τ ∈ tasks) (hτ' : τ' ∈ tasks) (h : τ.id = τ'.id) : τ = τ' :=
  List.inj_on_of_nodup_map h_ids hτ hτ' h

/-- **Keys name released jobs uniquely**: two released jobs with the same key are
the same job. -/
theorem key_injective_releasesAt {tasks : List PeriodicProcess}
    (h_ids : (tasks.map PeriodicProcess.id).Nodup) {t t' : ℕ} {p q : PeriodicProcess}
    (hp : p ∈ PeriodicProcess.releasesAt tasks t) (hq : q ∈ PeriodicProcess.releasesAt tasks t')
    (h : key p = key q) : p = q := by
  obtain ⟨τ, hτ, -, rfl⟩ := mem_releasesAt.mp hp
  obtain ⟨τ', hτ', -, rfl⟩ := mem_releasesAt.mp hq
  simp only [key, Prod.mk.injEq] at h
  obtain ⟨h_id, rfl⟩ := h
  rw [task_eq_of_id_eq h_ids hτ hτ' h_id]

/-- One release lists no job twice. -/
theorem releasesAt_nodup {tasks : List PeriodicProcess}
    (h_ids : (tasks.map PeriodicProcess.id).Nodup) (t : ℕ) :
    (PeriodicProcess.releasesAt tasks t).Nodup := by
  refine List.Nodup.map_on (fun τ hτ τ' hτ' h => ?_) ((h_ids.of_map _).filter _)
  exact task_eq_of_id_eq h_ids (List.mem_of_mem_filter hτ) (List.mem_of_mem_filter hτ')
    (by simpa using congrArg PeriodicProcess.id h)

/-- Step 0 has seen the releases of time 0. -/
@[simp] theorem jobsBy_zero (tasks : List PeriodicProcess) :
    jobsBy tasks 0 = PeriodicProcess.releasesAt tasks 0 := by
  simp [jobsBy]

/-- One more step, one more release. -/
theorem jobsBy_succ (tasks : List PeriodicProcess) (t : ℕ) :
    jobsBy tasks (t + 1) = jobsBy tasks t ++ PeriodicProcess.releasesAt tasks (t + 1) := by
  simp [jobsBy, List.range_succ, List.flatMap_append]

/-- The jobs released by time `t` are those of the releases at times `t' ≤ t`. -/
theorem mem_jobsBy {tasks : List PeriodicProcess} {t : ℕ} {p : PeriodicProcess} :
    p ∈ jobsBy tasks t ↔ ∃ t' ≤ t, p ∈ PeriodicProcess.releasesAt tasks t' := by
  simp [jobsBy, Nat.lt_succ_iff]

/-- A job released by time `t` was released at a time `≤ t`. -/
theorem arrival_le_of_mem_jobsBy {tasks : List PeriodicProcess} {t : ℕ} {p : PeriodicProcess}
    (h : p ∈ jobsBy tasks t) : p.arrival ≤ t := by
  obtain ⟨t', ht', hp⟩ := mem_jobsBy.mp h
  rw [arrival_of_mem_releasesAt hp]
  exact ht'

/-- **Keys name the released jobs uniquely**, across any two horizons. -/
theorem key_injective {tasks : List PeriodicProcess}
    (h_ids : (tasks.map PeriodicProcess.id).Nodup) {t t' : ℕ} {p q : PeriodicProcess}
    (hp : p ∈ jobsBy tasks t) (hq : q ∈ jobsBy tasks t') (h : key p = key q) : p = q := by
  obtain ⟨_, -, hp⟩ := mem_jobsBy.mp hp
  obtain ⟨_, -, hq⟩ := mem_jobsBy.mp hq
  exact key_injective_releasesAt h_ids hp hq h

/-- No job is released twice. -/
theorem jobsBy_nodup {tasks : List PeriodicProcess}
    (h_ids : (tasks.map PeriodicProcess.id).Nodup) (t : ℕ) : (jobsBy tasks t).Nodup := by
  induction t with
  | zero => simpa using releasesAt_nodup h_ids 0
  | succ t ih =>
    rw [jobsBy_succ]
    refine List.nodup_append.mpr ⟨ih, releasesAt_nodup h_ids _, fun p hp q hq h_eq => ?_⟩
    subst h_eq
    have h1 := arrival_le_of_mem_jobsBy hp
    have h2 := arrival_of_mem_releasesAt hq
    omega

/-! ## Schedules -/

/-- A **schedule** says, for each step `t`, which job (by key) holds the CPU in the state
after step `t`, if any.  That job receives the tick of step `t + 1`. -/
abbrev PSchedule := ℕ → Option (ℕ × ℕ)

/-- The ticks job `k` has received from schedule `σ` by the state after step `t`: one for
each earlier step `t' < t` in which it held the CPU. -/
def ticksBefore (σ : PSchedule) (k : ℕ × ℕ) (t : ℕ) : ℕ :=
  (List.range t).countP fun t' => σ t' = some k

/-- **Admissible schedules.** Whenever `σ` puts job `k` on the CPU after step `t`, a job
with key `k` has been released by time `t` and still has work left. -/
def IsAdmissible (tasks : List PeriodicProcess) (σ : PSchedule) : Prop :=
  ∀ t k, σ t = some k → ∃ p ∈ jobsBy tasks t, key p = k ∧ ticksBefore σ k t < p.burst

/-- The jobs released by time `t` that `σ` has not finished by the state after step `t`. -/
def unfinished (tasks : List PeriodicProcess) (σ : PSchedule) (t : ℕ) :
    List PeriodicProcess :=
  (jobsBy tasks t).filter fun p => ticksBefore σ (key p) t < p.burst

/-- **Lateness.** `σ` is late at `t` if some job released by `t` with absolute deadline
`≤ t` is unfinished after step `t`: its `D` usable ticks, steps `r+1 … r+D`, are over. -/
def LateAt (tasks : List PeriodicProcess) (σ : PSchedule) (t : ℕ) : Prop :=
  ∃ p ∈ unfinished tasks σ t, absDeadline p ≤ t

instance (tasks : List PeriodicProcess) (σ : PSchedule) (t : ℕ) :
    Decidable (LateAt tasks σ t) :=
  inferInstanceAs (Decidable (∃ p ∈ unfinished tasks σ t, absDeadline p ≤ t))

@[simp] theorem mem_unfinished {tasks : List PeriodicProcess} {σ : PSchedule} {t : ℕ}
    {p : PeriodicProcess} :
    p ∈ unfinished tasks σ t ↔ p ∈ jobsBy tasks t ∧ ticksBefore σ (key p) t < p.burst := by
  simp [unfinished]

/-- No ticks before step 0. -/
@[simp] theorem ticksBefore_zero (σ : PSchedule) (k : ℕ × ℕ) : ticksBefore σ k 0 = 0 := rfl

/-- Step `t` adds a tick to the job on the CPU after it. -/
theorem ticksBefore_succ (σ : PSchedule) (k : ℕ × ℕ) (t : ℕ) :
    ticksBefore σ k (t + 1) = ticksBefore σ k t + if σ t = some k then 1 else 0 := by
  simp [ticksBefore, List.range_succ, List.countP_append]

/-- A job that never held the CPU before step `t` has had no ticks. -/
theorem ticksBefore_eq_zero {σ : PSchedule} {k : ℕ × ℕ} {t : ℕ}
    (h : ∀ t' < t, σ t' ≠ some k) : ticksBefore σ k t = 0 := by
  unfold ticksBefore
  rw [List.countP_eq_zero]
  intro t' ht'
  simpa using h t' (List.mem_range.mp ht')

/-- Ticks only accumulate. -/
theorem ticksBefore_mono (σ : PSchedule) (k : ℕ × ℕ) {t t' : ℕ} (h : t ≤ t') :
    ticksBefore σ k t ≤ ticksBefore σ k t' := by
  induction t', h using Nat.le_induction with
  | base => exact le_rfl
  | succ n _ ih => rw [ticksBefore_succ]; omega

/-- Only the job on the CPU after step `t` gains a tick from step `t` to `t + 1`. -/
theorem ticksBefore_succ_of_ne {σ : PSchedule} {k : ℕ × ℕ} {t : ℕ} (h : σ t ≠ some k) :
    ticksBefore σ k (t + 1) = ticksBefore σ k t := by
  simp [ticksBefore_succ, h]

/-- An admissible schedule has not run a job before its release. -/
theorem ticksBefore_of_mem_releasesAt {tasks : List PeriodicProcess} {σ : PSchedule}
    (h_adm : IsAdmissible tasks σ) {t : ℕ} {p : PeriodicProcess}
    (hp : p ∈ PeriodicProcess.releasesAt tasks t) : ticksBefore σ (key p) t = 0 := by
  refine ticksBefore_eq_zero fun t' ht' h_eq => ?_
  obtain ⟨q, hq, h_key, -⟩ := h_adm t' _ h_eq
  have h1 := arrival_le_of_mem_jobsBy hq
  have h2 := arrival_of_mem_releasesAt hp
  have h3 : q.arrival = p.arrival := congrArg Prod.snd h_key
  omega

/-- **An admissible schedule never over-ticks a released job**, so
`p.burst - ticksBefore σ (key p) t` is exactly the work `p` still owes. -/
theorem ticksBefore_le_burst {tasks : List PeriodicProcess}
    (h_ids : (tasks.map PeriodicProcess.id).Nodup) {σ : PSchedule}
    (h_adm : IsAdmissible tasks σ) {p : PeriodicProcess} {t : ℕ} (hp : p ∈ jobsBy tasks t) :
    ticksBefore σ (key p) t ≤ p.burst := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [ticksBefore_succ]
    by_cases h : σ t = some (key p)
    · obtain ⟨q, hq, h_key, h_lt⟩ := h_adm t _ h
      obtain rfl := key_injective h_ids hq hp h_key
      simp only [h, ↓reduceIte]
      omega
    · simp only [h, ↓reduceIte, Nat.add_zero]
      by_cases hpt : p ∈ jobsBy tasks t
      · exact ih hpt
      · have hp' : p ∈ PeriodicProcess.releasesAt tasks (t + 1) := by
          rw [jobsBy_succ] at hp
          exact (List.mem_append.mp hp).resolve_left hpt
        have h0 := ticksBefore_of_mem_releasesAt h_adm hp'
        have hm := ticksBefore_mono σ (key p) (show t ≤ t + 1 by omega)
        omega

/-! ## Runs as schedules -/

/-- The schedule a run of `step` on the task set follows: the key of the job on the CPU
after each step. -/
def runSchedule (step : PeriodicSchedState → PeriodicSchedState)
    (tasks : List PeriodicProcess) : PSchedule :=
  fun t => (runSteps (PeriodicProcess.releasesAt tasks) step t).running.map key

/-- The jobs in the system: waiting, or on the CPU. -/
def inSystem (s : PeriodicSchedState) : List PeriodicProcess := s.ready ++ s.running.toList

/-- Job `p` as it stands after step `t` of `σ`: its burst less the ticks it has had. -/
def jobAt (σ : PSchedule) (t : ℕ) (p : PeriodicProcess) : PeriodicProcess :=
  { p with remaining := p.burst - ticksBefore σ (key p) t }

@[simp] theorem key_jobAt (σ : PSchedule) (t : ℕ) (p : PeriodicProcess) :
    key (jobAt σ t p) = key p := rfl

@[simp] theorem absDeadline_jobAt (σ : PSchedule) (t : ℕ) (p : PeriodicProcess) :
    absDeadline (jobAt σ t p) = absDeadline p := rfl

/-- A fresh job, as it stands before its first tick, is itself. -/
theorem jobAt_fresh {σ : PSchedule} {t : ℕ} {p : PeriodicProcess}
    (h_fresh : p.remaining = p.burst) (h_zero : ticksBefore σ (key p) t = 0) :
    jobAt σ t p = p := by
  cases p
  simp_all [jobAt]

/-- After step `t` of a run whose steps each advance the clock by one, the clock reads
`t + 1`. -/
theorem runSteps_time {step : PeriodicSchedState → PeriodicSchedState}
    (h_time : ∀ s, (step s).time = s.time + 1) (tasks : List PeriodicProcess) (t : ℕ) :
    (runSteps (PeriodicProcess.releasesAt tasks) step t).time = t + 1 := by
  induction t with
  | zero => simp [runSteps, h_time]
  | succ t ih => simp [runSteps, h_time, ih]

section Bridge

variable {step : PeriodicSchedState → PeriodicSchedState} (h_step : ConservesJobs step)
  {tasks : List PeriodicProcess} (h_ids : (tasks.map PeriodicProcess.id).Nodup)
include h_step h_ids

/-- **The run invariant.** After every step of a job-conserving run, the jobs in the
system are exactly the released jobs its schedule has not finished, each with its burst
less the ticks the schedule gave it. -/
theorem inSystem_perm (t : ℕ) :
    inSystem (runSteps (PeriodicProcess.releasesAt tasks) step t) ~
      (unfinished tasks (runSchedule step tasks) t).map (jobAt (runSchedule step tasks) t) := by
  set σ := runSchedule step tasks with hσ
  induction t using Nat.strong_induction_on with
  | _ t ih =>
  -- a job on the CPU after an earlier step was released by then
  have h_src : ∀ t' < t, ∀ k, σ t' = some k → ∃ q ∈ jobsBy tasks t', key q = k := by
    intro t' ht' k hk
    obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp hk
    have hb' : b ∈ inSystem (runSteps (PeriodicProcess.releasesAt tasks) step t') := by
      simp [inSystem, hb]
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ((ih t' ht').subset hb')
    exact ⟨q, List.mem_of_mem_filter hq, rfl⟩
  -- so a job released at time `t` has had no ticks before step `t`
  have h_new : ∀ p ∈ PeriodicProcess.releasesAt tasks t, ticksBefore σ (key p) t = 0 := by
    intro p hp
    refine ticksBefore_eq_zero fun t' ht' h_eq => ?_
    obtain ⟨q, hq, h_key⟩ := h_src t' ht' _ h_eq
    have h1 := arrival_le_of_mem_jobsBy hq
    have h2 := arrival_of_mem_releasesAt hp
    have h3 : q.arrival = p.arrival := congrArg Prod.snd h_key
    omega
  have h_arr : ((PeriodicProcess.releasesAt tasks t).filter
      fun p => ticksBefore σ (key p) t < p.burst).map (jobAt σ t) =
        PeriodicProcess.releasesAt tasks t := by
    rw [List.filter_eq_self.mpr fun p hp => by simp [h_new p hp, p.burst_exceed_zero]]
    exact (List.map_congr_left fun p hp =>
      jobAt_fresh (remaining_of_mem_releasesAt hp) (h_new p hp)).trans (List.map_id _)
  cases t with
  | zero =>
    have h0 := h_step { SchedStateMethods.init with ready := PeriodicProcess.releasesAt tasks 0 }
    simp only [SchedStateG.init_periodic, Option.toList_none, List.map_nil, List.filter_nil,
      List.append_nil] at h0
    unfold unfinished
    rw [jobsBy_zero, h_arr]
    simpa [inSystem, runSteps] using h0
  | succ t =>
    set S := runSteps (PeriodicProcess.releasesAt tasks) step t with hS
    have h1 := h_step { S with ready := S.ready ++ PeriodicProcess.releasesAt tasks (t + 1) }
    simp only [PeriodicProcess.process_remaining] at h1
    change inSystem (runSteps (PeriodicProcess.releasesAt tasks) step (t + 1)) ~ _ at h1 ⊢
    refine h1.trans ?_
    have ih_t := ih t (by omega)
    rw [← hS] at ih_t
    unfold unfinished
    rw [jobsBy_succ, List.filter_append, List.map_append, h_arr]
    -- the jobs released earlier: only the one on the CPU has changed
    suffices h : S.ready ++
        (S.running.toList.map fun b => { b with remaining := b.remaining - 1 }).filter
          (fun b => 0 < b.remaining) ~ ((jobsBy tasks t).filter
          fun p => ticksBefore σ (key p) (t + 1) < p.burst).map (jobAt σ (t + 1)) by
      rw [List.append_assoc]
      exact (List.Perm.append_left _ List.perm_append_comm).trans
        (by rw [← List.append_assoc]; exact h.append_right _)
    rcases hr : S.running with _ | b
    · -- an idle CPU: nobody was ticked
      have hσt : σ t = none := by simp [hσ, runSchedule, ← hS, hr]
      have h_same : ∀ p : PeriodicProcess,
          ticksBefore σ (key p) (t + 1) = ticksBefore σ (key p) t :=
        fun p => ticksBefore_succ_of_ne (by simp [hσt])
      have hJ : jobAt σ (t + 1) = jobAt σ t := funext fun p => by simp [jobAt, h_same]
      simp only [h_same, hJ, Option.toList_none, List.map_nil, List.filter_nil, List.append_nil]
      simpa [inSystem, hr, unfinished] using ih_t
    · -- `b` was on the CPU: it is some released job `q`, which receives the tick
      have hσt : σ t = some (key b) := by simp [hσ, runSchedule, ← hS, hr]
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp
        (ih_t.subset (show b ∈ inSystem S by simp [inSystem, hr]))
      have hqL := List.mem_of_mem_filter hq
      have hq_lt : ticksBefore σ (key q) t < q.burst := by simpa using (List.mem_filter.mp hq).2
      have h_tick : ticksBefore σ (key q) (t + 1) = ticksBefore σ (key q) t + 1 := by
        simp [ticksBefore_succ, hσt]
      obtain ⟨rest, h_old, h_upd⟩ := filter_map_update (jobsBy_nodup h_ids t) hqL
        (fun p => decide (ticksBefore σ (key p) t < p.burst))
        (fun p => decide (ticksBefore σ (key p) (t + 1) < p.burst)) (jobAt σ t) (jobAt σ (t + 1))
        (fun p hp h_ne => by
          have h_key : key p ≠ key q := fun h => h_ne (key_injective h_ids hp hqL h)
          have h_same : ticksBefore σ (key p) (t + 1) = ticksBefore σ (key p) t :=
            ticksBefore_succ_of_ne (by simp [hσt, Ne.symm h_key])
          exact ⟨by simp [h_same], by simp [jobAt, h_same]⟩)
      refine List.Perm.trans ?_ h_upd.symm
      simp only [hq_lt, decide_true, ↓reduceIte, List.singleton_append] at h_old
      have h_ready : S.ready ~ rest := by
        have := (ih_t.trans h_old)
        simp only [inSystem, hr, Option.toList_some] at this
        exact ((List.perm_append_singleton _ _).symm.trans this).cons_inv
      have h_tf : ([jobAt σ t q].map fun b => { b with remaining := b.remaining - 1 }).filter
          (fun b => 0 < b.remaining) =
          if decide (ticksBefore σ (key q) (t + 1) < q.burst) then [jobAt σ (t + 1) q]
          else [] := by
        simp only [List.map_cons, List.map_nil, List.filter_cons, List.filter_nil, jobAt, h_tick]
        by_cases h : ticksBefore σ (key q) t + 1 < q.burst
        · simp only [show 0 < q.burst - ticksBefore σ (key q) t - 1 by omega, decide_true,
            ↓reduceIte, h]
          congr 2
        · simp only [show ¬ 0 < q.burst - ticksBefore σ (key q) t - 1 by omega, decide_false,
            Bool.false_eq_true, ↓reduceIte, h]
      simp only [Option.toList_some]
      rw [h_tf]
      exact List.perm_append_comm.trans (h_ready.append_left _)

/-- **A run is an admissible schedule**: it only ever runs a released job with work
left. -/
theorem runSchedule_isAdmissible : IsAdmissible tasks (runSchedule step tasks) := by
  intro t k h
  obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ((inSystem_perm h_step h_ids t).subset
    (show b ∈ inSystem _ by simp [inSystem, hb]))
  exact ⟨q, List.mem_of_mem_filter hq, rfl, by simpa using (List.mem_filter.mp hq).2⟩

/-- **The miss bridge.** For a job-conserving step that advances the clock by one, the
run lists a missed deadline after step `t` iff its schedule is late at `t`: some
released job with absolute deadline `≤ t` is unfinished. -/
theorem missedDeadlines_ne_nil_iff (h_time : ∀ s, (step s).time = s.time + 1) (t : ℕ) :
    PeriodicProcess.missedDeadlines (runSteps (PeriodicProcess.releasesAt tasks) step t) ≠ [] ↔
      LateAt tasks (runSchedule step tasks) t := by
  have h_perm := inSystem_perm h_step h_ids t
  unfold PeriodicProcess.missedDeadlines
  rw [runSteps_time h_time, Ne, List.eq_nil_iff_forall_not_mem, not_forall_not]
  change (∃ p, p ∈ (inSystem _).filter _) ↔ _
  simp only [List.mem_filter, h_perm.mem_iff, List.mem_map, decide_eq_true_eq]
  constructor
  · rintro ⟨_, ⟨q, hq, rfl⟩, h_late⟩
    exact ⟨q, hq, by simpa [absDeadline, jobAt] using Nat.lt_succ_iff.mp h_late⟩
  · rintro ⟨q, hq, h_late⟩
    exact ⟨_, ⟨q, hq, rfl⟩, by simpa [absDeadline, jobAt] using Nat.lt_succ_of_le h_late⟩

end Bridge

/-! ## Preemptive schedulers -/

/-- The run of a preemptive scheduler (`stepRMS`, `stepEDF`, …) is an admissible
schedule. -/
theorem runSchedule_stepPreemptive_isAdmissible (f : PeriodicProcess → ℤ)
    {tasks : List PeriodicProcess} (h_ids : (tasks.map PeriodicProcess.id).Nodup) :
    IsAdmissible tasks (runSchedule (stepPreemptive PeriodicProcess f) tasks) :=
  runSchedule_isAdmissible (stepPreemptive_conservesJobs f) h_ids

/-- **The miss bridge for preemptive schedulers.** A run of `stepPreemptive f` (for
instance `stepRMS` or `stepEDF`) lists a missed deadline after step `t` iff its schedule
is late at `t`. -/
theorem missedDeadlines_ne_nil_iff_preemptive (f : PeriodicProcess → ℤ)
    {tasks : List PeriodicProcess} (h_ids : (tasks.map PeriodicProcess.id).Nodup) (t : ℕ) :
    PeriodicProcess.missedDeadlines
        (runSteps (PeriodicProcess.releasesAt tasks) (stepPreemptive PeriodicProcess f) t) ≠ [] ↔
      LateAt tasks (runSchedule (stepPreemptive PeriodicProcess f) tasks) t :=
  missedDeadlines_ne_nil_iff (stepPreemptive_conservesJobs f) h_ids
    (stepPreemptive_time f) t

/-- **A preemptive scheduler idles only when every released job is finished.** -/
theorem unfinished_eq_nil_of_idle (f : PeriodicProcess → ℤ) {tasks : List PeriodicProcess}
    (h_ids : (tasks.map PeriodicProcess.id).Nodup) {t : ℕ}
    (h : runSchedule (stepPreemptive PeriodicProcess f) tasks t = none) :
    unfinished tasks (runSchedule (stepPreemptive PeriodicProcess f) tasks) t = [] := by
  have h_run :
      (runSteps (PeriodicProcess.releasesAt tasks) (stepPreemptive PeriodicProcess f) t).running =
        none := by
    simpa [runSchedule] using h
  have h_sys := inSystem_perm (stepPreemptive_conservesJobs f) h_ids t
  rw [inSystem, runSteps_ready_nil_of_idle f _ t h_run, h_run] at h_sys
  simpa using h_sys.symm

/-- **A preemptive scheduler runs an unfinished job of highest priority.** If the run of
`stepPreemptive f` has job `k` on the CPU after step `t`, then `k` is the key of an
unfinished job `p0`, and no unfinished job, as it stands after step `t`, has a higher
`f`-value than `p0`. -/
theorem runSchedule_stepPreemptive_max (f : PeriodicProcess → ℤ) {tasks : List PeriodicProcess}
    (h_ids : (tasks.map PeriodicProcess.id).Nodup) {t : ℕ} {k : ℕ × ℕ}
    (h : runSchedule (stepPreemptive PeriodicProcess f) tasks t = some k) :
    ∃ p0 ∈ unfinished tasks (runSchedule (stepPreemptive PeriodicProcess f) tasks) t,
      key p0 = k ∧ ∀ p ∈ unfinished tasks (runSchedule (stepPreemptive PeriodicProcess f) tasks) t,
        f (jobAt (runSchedule (stepPreemptive PeriodicProcess f) tasks) t p) ≤
          f (jobAt (runSchedule (stepPreemptive PeriodicProcess f) tasks) t p0) := by
  set σ := runSchedule (stepPreemptive PeriodicProcess f) tasks
  obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp h
  have h_sys := inSystem_perm (stepPreemptive_conservesJobs f) h_ids t
  obtain ⟨p0, hp0, rfl⟩ := List.mem_map.mp
    (h_sys.subset (show b ∈ inSystem _ by simp [inSystem, hb]))
  refine ⟨p0, hp0, rfl, fun p hp => ?_⟩
  by_cases h_eq : p = p0
  · subst h_eq
    exact le_rfl
  · have hp_sys : jobAt σ t p ∈ inSystem _ := h_sys.symm.subset (List.mem_map_of_mem hp)
    have hp_ready : jobAt σ t p ∈
        (runSteps (PeriodicProcess.releasesAt tasks) (stepPreemptive PeriodicProcess f) t).ready := by
      simp only [inSystem, hb, Option.toList_some, List.mem_append, List.mem_singleton] at hp_sys
      refine hp_sys.resolve_right fun h' => h_eq ?_
      exact key_injective h_ids (mem_unfinished.mp hp).1 (mem_unfinished.mp hp0).1
        (by simpa using congrArg key h')
    exact runSteps_running_max f _ t _ hb _ hp_ready

end Periodic
