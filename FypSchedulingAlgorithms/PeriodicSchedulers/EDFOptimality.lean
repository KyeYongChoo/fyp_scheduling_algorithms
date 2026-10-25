/-
Copyright (c) 2026 Choo Kye Yong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Choo Kye Yong
-/
import FypSchedulingAlgorithms.PeriodicSchedulers.PeriodicSchedules

/-!
# EDF is optimal

Dertouzos (1974): if any schedule meets every deadline, so does Earliest Deadline First.
Here: on every periodic task set with distinct task ids, if the run of `stepEDF` lists a
missed deadline after step `t`, then every admissible schedule (`PeriodicSchedules`) is
late at `t` (`edf_optimal`).  So if some admissible schedule is never late, EDF never
misses a deadline (`edf_never_late`, `edf_never_late_of_exists`).  The competing schedule
may be anything admissible: preemptive or not, idling or not, online or clairvoyant, with
fixed or dynamic priorities.

**Scope.**  The result holds inside the discrete model of `PeriodicSchedules`: the shared
tick convention of `Step`, no context-switch cost, and the miss rule of
`PeriodicProcess.missedDeadlines`, under which a job released at `r` with relative
deadline `D` gets the `D` ticks of steps `r+1 … r+D` and is late at `t` iff `r + D ≤ t`
and it is still unfinished after step `t`.  The only hypothesis is that task ids are
distinct, so that a job is named by its key `(id, arrival)`.  Periodicity is never used
beyond that: the jobs come from `PeriodicProcess.releasesAt`, but the proof only needs
them to be fresh at release, stamped with their release time, and uniquely named by
`(id, arrival)`.  Deadlines may exceed periods, and periods need not be positive.

**How.**  Compare the work still owed by the jobs with absolute deadline `≤ d`
(`workDue tasks σ t d`).  After every step and for every `d`, EDF's is no larger than
that of any admissible schedule (`edf_workDue_le`), by induction on the step:

* releases add the same fresh work to both sides (`workDue_succ`);
* any schedule's tick lowers `workDue` by at most 1 (`workDue_sub_one_le`);
* EDF's tick lowers it by exactly 1 while it is positive (`edf_workAfter_le`): then some
  unfinished job has deadline `≤ d`, so EDF does not idle (`unfinished_eq_nil_of_idle`),
  and the job it runs has the least absolute deadline among the unfinished jobs
  (`runSchedule_stepPreemptive_max`, from the priority run invariant), hence deadline
  `≤ d` too (`workAfter_add_one`).

A schedule is late at `t` iff `workDue _ σ t t > 0` (`workDue_pos_iff`), so lateness of
EDF forces lateness of every admissible schedule.  The miss bridge
(`missedDeadlines_ne_nil_iff_preemptive`) turns this into a statement about the run.
-/

namespace Periodic

open scoped List
open PreemptiveRuns

/-! ## Work due under a schedule

`workDue`, `workAfter` and `workReleased` are `workOf`, `workOfAfter` and `releasedOf`
(`PeriodicSchedules`) for the jobs with absolute deadline `≤ d`, and their lemmas are
those of `workOf`.
-/

/-- Work still owed, after step `t` of `σ`, by the jobs released by time `t` with
absolute deadline `≤ d`. -/
def workDue (tasks : List PeriodicProcess) (σ : PSchedule) (t d : ℕ) : ℕ :=
  workOf tasks σ (absDeadline · ≤ d) t

/-- The work the same jobs still owe once step `t + 1` has ticked `σ`'s job of step `t`,
before the releases of time `t + 1`. -/
def workAfter (tasks : List PeriodicProcess) (σ : PSchedule) (t d : ℕ) : ℕ :=
  workOfAfter tasks σ (absDeadline · ≤ d) t

/-- The work released at time `t` with absolute deadline `≤ d`. -/
def workReleased (tasks : List PeriodicProcess) (t d : ℕ) : ℕ :=
  releasedOf tasks (absDeadline · ≤ d) t

/-- **Work is due iff a job with deadline `≤ d` is unfinished.** -/
theorem workDue_pos_iff {tasks : List PeriodicProcess} {σ : PSchedule} {t d : ℕ} :
    0 < workDue tasks σ t d ↔ ∃ p ∈ unfinished tasks σ t, absDeadline p ≤ d :=
  workOf_pos_iff

/-- **Lateness is work due by now**: `σ` is late at `t` iff the jobs with deadline `≤ t`
still owe work after step `t`. -/
theorem lateAt_iff_workDue_pos {tasks : List PeriodicProcess} {σ : PSchedule} {t : ℕ} :
    LateAt tasks σ t ↔ 0 < workDue tasks σ t t :=
  workDue_pos_iff.symm

/-- Before any tick, every schedule owes the same work. -/
theorem workDue_zero (tasks : List PeriodicProcess) (σ σ' : PSchedule) (d : ℕ) :
    workDue tasks σ 0 d = workDue tasks σ' 0 d :=
  workOf_zero.trans workOf_zero.symm

/-- **One step of work due**: the tick, then the releases, fresh. -/
theorem workDue_succ {tasks : List PeriodicProcess} {σ : PSchedule}
    (h_adm : IsAdmissible tasks σ) (t d : ℕ) :
    workDue tasks σ (t + 1) d = workAfter tasks σ t d + workReleased tasks (t + 1) d :=
  workOf_succ h_adm t

/-- A tick never adds work. -/
theorem workAfter_le (tasks : List PeriodicProcess) (σ : PSchedule) (t d : ℕ) :
    workAfter tasks σ t d ≤ workDue tasks σ t d :=
  workOfAfter_le t

/-- If `σ` runs none of the jobs with deadline `≤ d` after step `t`, their work stays
the same. -/
theorem workAfter_eq_of_forall_ne {tasks : List PeriodicProcess} {σ : PSchedule} {t d : ℕ}
    (h : ∀ p ∈ (jobsBy tasks t).filter (absDeadline · ≤ d), σ t ≠ some (key p)) :
    workAfter tasks σ t d = workDue tasks σ t d :=
  workOfAfter_eq_of_forall_ne h

/-- **A tick on a job with deadline `≤ d`**: if `σ` runs `p0` after step `t`, `p0` takes
the whole change in work, a drop of one unless `p0` is already finished. -/
theorem workAfter_tick {tasks : List PeriodicProcess}
    (h_ids : (tasks.map PeriodicProcess.id).Nodup) {σ : PSchedule} {t d : ℕ}
    {p0 : PeriodicProcess} (hσ : σ t = some (key p0))
    (hp0 : p0 ∈ (jobsBy tasks t).filter (absDeadline · ≤ d)) :
    workDue tasks σ t d + (p0.burst - ticksBefore σ (key p0) t - 1) =
      workAfter tasks σ t d + (p0.burst - ticksBefore σ (key p0) t) :=
  workOf_tick h_ids hσ hp0

/-- **A tick lowers work due by at most one**, for any schedule. -/
theorem workDue_sub_one_le {tasks : List PeriodicProcess}
    (h_ids : (tasks.map PeriodicProcess.id).Nodup) (σ : PSchedule) (t d : ℕ) :
    workDue tasks σ t d - 1 ≤ workAfter tasks σ t d :=
  workOf_sub_one_le h_ids t

/-- **A tick on an unfinished job with deadline `≤ d` lowers work due by exactly one.** -/
theorem workAfter_add_one {tasks : List PeriodicProcess}
    (h_ids : (tasks.map PeriodicProcess.id).Nodup) {σ : PSchedule} {t d : ℕ}
    {p0 : PeriodicProcess} (hσ : σ t = some (key p0)) (hp0 : p0 ∈ jobsBy tasks t)
    (hd : absDeadline p0 ≤ d) (h_pos : ticksBefore σ (key p0) t < p0.burst) :
    workAfter tasks σ t d + 1 = workDue tasks σ t d :=
  workOfAfter_add_one h_ids hσ hp0 hd h_pos

/-! ## EDF's ticks -/

/-- **EDF's tick lowers work due by one while any is due**, for every `d`.  If a job with
deadline `≤ d` is unfinished, EDF does not idle, and the job it runs has the least
absolute deadline among the unfinished jobs, so its deadline is `≤ d` too. -/
theorem edf_workAfter_le {tasks : List PeriodicProcess}
    (h_ids : (tasks.map PeriodicProcess.id).Nodup) (t d : ℕ) :
    workAfter tasks (runSchedule stepEDF tasks) t d ≤
      workDue tasks (runSchedule stepEDF tasks) t d - 1 := by
  by_cases h0 : workDue tasks (runSchedule stepEDF tasks) t d = 0
  · have := workAfter_le tasks (runSchedule stepEDF tasks) t d
    omega
  obtain ⟨p, hp, hpd⟩ := workDue_pos_iff.mp (Nat.pos_of_ne_zero h0)
  cases hE : runSchedule stepEDF tasks t with
  | none =>
    have h_nil := unfinished_eq_nil_of_idle _ h_ids hE
    rw [stepEDF, h_nil] at hp
    exact absurd hp List.not_mem_nil
  | some k =>
    obtain ⟨p0, hp0, rfl, h_max⟩ := runSchedule_stepPreemptive_max _ h_ids hE
    have h_le := h_max p hp
    simp only [jobAt] at h_le
    have hd : absDeadline p0 ≤ d := by
      unfold absDeadline at hpd ⊢
      omega
    have := workAfter_add_one h_ids hE (mem_unfinished.mp hp0).1 hd (mem_unfinished.mp hp0).2
    omega

/-! ## EDF is optimal -/

/-- **The majorisation invariant.** After every step and for every `d`, EDF's schedule
owes no more work with deadline `≤ d` than any admissible schedule. -/
theorem edf_workDue_le {tasks : List PeriodicProcess}
    (h_ids : (tasks.map PeriodicProcess.id).Nodup) {σ : PSchedule}
    (h_adm : IsAdmissible tasks σ) (t d : ℕ) :
    workDue tasks (runSchedule stepEDF tasks) t d ≤ workDue tasks σ t d := by
  have h_admE : IsAdmissible tasks (runSchedule stepEDF tasks) :=
    runSchedule_stepPreemptive_isAdmissible _ h_ids
  induction t with
  | zero => exact (workDue_zero tasks _ σ d).le
  | succ t ih =>
    rw [workDue_succ h_admE, workDue_succ h_adm]
    have h1 := edf_workAfter_le h_ids t d
    have h2 := workDue_sub_one_le h_ids σ t d
    omega

/-- **If EDF is late, every admissible schedule is late**, at the same step. -/
theorem edf_lateAt_imp {tasks : List PeriodicProcess}
    (h_ids : (tasks.map PeriodicProcess.id).Nodup) {σ : PSchedule}
    (h_adm : IsAdmissible tasks σ) {t : ℕ} (h : LateAt tasks (runSchedule stepEDF tasks) t) :
    LateAt tasks σ t :=
  lateAt_iff_workDue_pos.mpr
    (lt_of_lt_of_le (lateAt_iff_workDue_pos.mp h) (edf_workDue_le h_ids h_adm t t))

/-- **EDF is optimal** (Dertouzos 1974).  If the run of `stepEDF` lists a missed deadline
after step `t`, every admissible schedule is late at `t`: some job with absolute deadline
`≤ t` is unfinished after step `t`. -/
theorem edf_optimal {tasks : List PeriodicProcess}
    (h_ids : (tasks.map PeriodicProcess.id).Nodup) {σ : PSchedule}
    (h_adm : IsAdmissible tasks σ) (t : ℕ)
    (h : PeriodicProcess.missedDeadlines (runSteps (PeriodicProcess.releasesAt tasks) stepEDF t) ≠
      []) :
    LateAt tasks σ t :=
  edf_lateAt_imp h_ids h_adm ((missedDeadlines_ne_nil_iff_preemptive _ h_ids t).mp h)

/-- **If some admissible schedule is never late, EDF never misses a deadline.** -/
theorem edf_never_late {tasks : List PeriodicProcess}
    (h_ids : (tasks.map PeriodicProcess.id).Nodup) {σ : PSchedule}
    (h_adm : IsAdmissible tasks σ) (h_never : ∀ t, ¬ LateAt tasks σ t) (t : ℕ) :
    PeriodicProcess.missedDeadlines (runSteps (PeriodicProcess.releasesAt tasks) stepEDF t) =
      [] := by
  by_contra h
  exact h_never t (edf_optimal h_ids h_adm t h)

/-- **Feasible task sets are EDF-schedulable**: if any admissible schedule meets every
deadline, `stepEDF` lists no missed deadline at any step. -/
theorem edf_never_late_of_exists {tasks : List PeriodicProcess}
    (h_ids : (tasks.map PeriodicProcess.id).Nodup)
    (h : ∃ σ, IsAdmissible tasks σ ∧ ∀ t, ¬ LateAt tasks σ t) (t : ℕ) :
    PeriodicProcess.missedDeadlines (runSteps (PeriodicProcess.releasesAt tasks) stepEDF t) =
      [] := by
  obtain ⟨σ, h_adm, h_never⟩ := h
  exact edf_never_late h_ids h_adm h_never t

end Periodic
