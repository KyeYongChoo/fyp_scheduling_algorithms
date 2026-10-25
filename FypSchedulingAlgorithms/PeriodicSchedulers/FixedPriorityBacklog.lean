/-
Copyright (c) 2026 Choo Kye Yong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Choo Kye Yong
-/
import FypSchedulingAlgorithms.PeriodicSchedulers.PeriodicSchedules

/-!
# Fixed priorities and the level backlog

A priority function `f` is **fixed** (`FixedPriority f`) if a job's priority is that of
its task: it does not depend on the release time or on the work left.  `stepRMS`
(`-period`), `stepDM` (`-deadline`) and any `fun p => π p.id` are fixed-priority
schedulers; `stepEDF` is not (`not_fixedPriority_edf`).

For a set `S` of task ids (a decidable predicate on ids), the **level backlog** is pure
arithmetic on the releases, with no schedule in it:

* `levelRel tasks S t`: the work released by the tasks in `S` at time `t`;
* `levelBacklog tasks S t`: `levelRel` at 0, then one less (down to 0) per step plus the
  new releases;
* `pre tasks S e = levelBacklog tasks S e - levelRel tasks S e`: the backlog of jobs
  released *before* `e`.  `pre S 0 = 0` and `pre S (t + 1) = levelBacklog S t - 1`.  `e`
  is a **drain point** of `S` when `pre S e = 0`.

**Results.**

* **R1, the bridge** (`workOf_eq_levelBacklog`).  Let `f` be fixed and `S` upward-closed
  under `f` among the tasks (`UpClosed`: a task with priority at least that of a member
  of `S` is in `S`).  Then in the run of `stepPreemptive f`, the work the jobs of `S`
  still owe after step `t` is `levelBacklog tasks S t`.  Ties are allowed.  The reason:
  while some job of `S` is unfinished, the scheduler runs a job of highest priority among
  the unfinished jobs (`runSchedule_stepPreemptive_max`), and upward closure puts that
  job in `S`, so `S`'s work drops by exactly one per step.
* **R2, monotonicity** (`levelBacklog_mono`, `pre_mono`): a larger set of tasks has a
  larger backlog.
* **R3, sufficiency** (`ticksBefore_eq_burst_of_pre_eq_zero`,
  `meetsDeadline_of_drainPoint`): under R1's hypotheses, at a drain point `e` every job
  of `S` released before `e` is finished in the state after step `e`.  So a job of a task
  in `S` released at `r` meets its deadline if `S` has a drain point `e` with
  `r < e ≤ r + D`; it is then never late (`not_mem_unfinished_of_drainPoint`).

R1 is stated for the schedule (`workOf` over `jobsBy`, with `runSchedule`'s ticks) rather
than for the run's state, because R3 and the first-job argument of the DM/RM optimality
proof speak about the ticks of individual jobs, as the lateness of `PeriodicSchedules`
does.
-/

namespace Periodic

open PreemptiveRuns

/-! ## Fixed priorities -/

/-- A priority function is **fixed** if a job's priority is that of its task: changing
its release time or its work left does not change it. -/
def FixedPriority (f : PeriodicProcess → ℤ) : Prop :=
  ∀ p a r, f { p with arrival := a, remaining := r } = f p

/-- Rate Monotonic priorities are fixed. -/
theorem fixedPriority_rms : FixedPriority (fun p => -(p.period : ℤ)) := fun _ _ _ => rfl

/-- Deadline Monotonic priorities are fixed. -/
theorem fixedPriority_dm : FixedPriority (fun p => -(p.deadline : ℤ)) := fun _ _ _ => rfl

/-- Any priority given per task id is fixed. -/
theorem fixedPriority_of_id (π : ℕ → ℤ) : FixedPriority (fun p => π p.id) := fun _ _ _ => rfl

/-- EDF priorities are not fixed: they depend on the release time. -/
theorem not_fixedPriority_edf :
    ¬ FixedPriority (fun p => -((p.arrival + p.deadline : ℕ) : ℤ)) := by
  intro h
  have := h ⟨0, 0, 1, 1, 0, 1, by omega⟩ 1 1
  simp at this

/-- A released job has the priority of its task, under a fixed priority. -/
theorem exists_task_of_mem_jobsBy {f : PeriodicProcess → ℤ} (hf : FixedPriority f)
    {tasks : List PeriodicProcess} {t : ℕ} {p : PeriodicProcess} (hp : p ∈ jobsBy tasks t) :
    ∃ τ ∈ tasks, τ.id = p.id ∧ f τ = f p := by
  obtain ⟨t', -, hp⟩ := mem_jobsBy.mp hp
  obtain ⟨τ, hτ, -, rfl⟩ := mem_releasesAt.mp hp
  exact ⟨τ, hτ, rfl, (hf τ t' τ.burst).symm⟩

/-- A set of task ids is **upward-closed** under `f` among the tasks if every task with
priority at least that of a member is a member. -/
def UpClosed (tasks : List PeriodicProcess) (f : PeriodicProcess → ℤ) (S : ℕ → Prop) : Prop :=
  ∀ τ ∈ tasks, ∀ τ' ∈ tasks, S τ.id → f τ ≤ f τ' → S τ'.id

/-! ## The level backlog -/

section Backlog

variable (tasks : List PeriodicProcess) (S : ℕ → Prop) [DecidablePred S]

/-- The work released by the tasks in `S` at time `t`. -/
def levelRel (t : ℕ) : ℕ :=
  releasedOf tasks (fun p => S p.id) t

/-- The **level backlog** of `S`: the work released by the tasks in `S` at time 0, then
one less (down to 0) per step plus the new releases. -/
def levelBacklog : ℕ → ℕ
  | 0 => levelRel tasks S 0
  | t + 1 => (levelBacklog t - 1) + levelRel tasks S (t + 1)

/-- The backlog of the jobs of `S` released before `e`.  `e` is a drain point of `S`
when it is 0. -/
def pre (e : ℕ) : ℕ :=
  levelBacklog tasks S e - levelRel tasks S e

/-- Nothing is released before time 0. -/
@[simp] theorem pre_zero : pre tasks S 0 = 0 := by
  simp [pre, levelBacklog]

/-- The backlog before `t + 1` is the backlog after step `t` less the tick of step
`t + 1`. -/
theorem pre_succ (t : ℕ) : pre tasks S (t + 1) = levelBacklog tasks S t - 1 := by
  simp [pre, levelBacklog]

/-- The backlog is the backlog before `e` plus the releases at `e`. -/
theorem levelBacklog_eq_pre_add (e : ℕ) :
    levelBacklog tasks S e = pre tasks S e + levelRel tasks S e := by
  cases e <;> simp [pre, levelBacklog]

end Backlog

/-! ## R2: monotonicity -/

section Mono

variable {tasks : List PeriodicProcess} {S S' : ℕ → Prop} [DecidablePred S] [DecidablePred S']

/-- **More tasks, more released work.** -/
theorem levelRel_mono (h : ∀ i, S i → S' i) (t : ℕ) :
    levelRel tasks S t ≤ levelRel tasks S' t :=
  sum_map_filter_le_of_imp _ _ fun p => h p.id

/-- **R2: more tasks, more backlog.** -/
theorem levelBacklog_mono (h : ∀ i, S i → S' i) (t : ℕ) :
    levelBacklog tasks S t ≤ levelBacklog tasks S' t := by
  induction t with
  | zero => exact levelRel_mono h 0
  | succ t ih =>
    have := levelRel_mono (tasks := tasks) h (t + 1)
    simp only [levelBacklog]
    omega

/-- **R2 for the backlog before `e`**: a drain point of a larger set of tasks is a drain
point of a smaller one. -/
theorem pre_mono (h : ∀ i, S i → S' i) (e : ℕ) : pre tasks S e ≤ pre tasks S' e := by
  cases e with
  | zero => simp
  | succ t =>
    rw [pre_succ, pre_succ]
    have := levelBacklog_mono (tasks := tasks) h t
    omega

end Mono

/-! ## R1: the bridge -/

section Bridge

variable {f : PeriodicProcess → ℤ} (hf : FixedPriority f) {tasks : List PeriodicProcess}
  (h_ids : (tasks.map PeriodicProcess.id).Nodup) {S : ℕ → Prop} [DecidablePred S]
  (hS : UpClosed tasks f S)
include hf h_ids hS

/-- **R1.**  In the run of a fixed-priority scheduler, the work the jobs of an
upward-closed set of tasks still owe after step `t` is the level backlog. -/
theorem workOf_eq_levelBacklog (t : ℕ) :
    workOf tasks (runSchedule (stepPreemptive PeriodicProcess f) tasks) (fun p => S p.id) t =
      levelBacklog tasks S t := by
  set σ := runSchedule (stepPreemptive PeriodicProcess f) tasks
  have h_adm : IsAdmissible tasks σ := runSchedule_stepPreemptive_isAdmissible f h_ids
  induction t with
  | zero => exact workOf_zero
  | succ t ih =>
    rw [workOf_succ h_adm, levelBacklog]
    change _ + levelRel tasks S (t + 1) = _
    -- the tick of step `t + 1` lowers `S`'s work by one while any is owed
    suffices h : workOfAfter tasks σ (fun p => S p.id) t =
        workOf tasks σ (fun p => S p.id) t - 1 by rw [h, ih]
    by_cases h0 : workOf tasks σ (fun p => S p.id) t = 0
    · have := workOfAfter_le (tasks := tasks) (σ := σ) (P := fun p => S p.id) t
      omega
    obtain ⟨p, hp, hpS⟩ := workOf_pos_iff.mp (Nat.pos_of_ne_zero h0)
    cases hσ : σ t with
    | none =>
      have h_nil := unfinished_eq_nil_of_idle f h_ids hσ
      rw [h_nil] at hp
      exact absurd hp List.not_mem_nil
    | some k =>
      obtain ⟨p0, hp0, rfl, h_max⟩ := runSchedule_stepPreemptive_max f h_ids hσ
      have hp0' := mem_unfinished.mp hp0
      -- `p0` has priority at least that of `p`, so its task is in `S`
      have h_le : f p ≤ f p0 := by
        have h1 : f (jobAt σ t p) = f p := hf p p.arrival _
        have h2 : f (jobAt σ t p0) = f p0 := hf p0 p0.arrival _
        have := h_max p hp
        rwa [h1, h2] at this
      obtain ⟨τ, hτ, hτ_id, hτ_f⟩ := exists_task_of_mem_jobsBy hf (mem_unfinished.mp hp).1
      obtain ⟨τ0, hτ0, hτ0_id, hτ0_f⟩ := exists_task_of_mem_jobsBy hf hp0'.1
      have hS0 : S p0.id := by
        rw [← hτ0_id]
        exact hS τ hτ τ0 hτ0 (by rwa [hτ_id]) (by rw [hτ_f, hτ0_f]; exact h_le)
      have := workOfAfter_add_one h_ids hσ hp0'.1 (P := fun p => S p.id) hS0 hp0'.2
      omega

/-- **The backlog before `t + 1` is what is left after the tick of step `t + 1`**: the
work the jobs of `S` released by `t` still owe in the state after step `t + 1`. -/
theorem pre_succ_eq_workOfAfter (t : ℕ) :
    pre tasks S (t + 1) =
      workOfAfter tasks (runSchedule (stepPreemptive PeriodicProcess f) tasks)
        (fun p => S p.id) t := by
  have h1 := workOf_succ (P := fun p => S p.id)
    (runSchedule_stepPreemptive_isAdmissible f h_ids) t
  rw [workOf_eq_levelBacklog hf h_ids hS, levelBacklog_eq_pre_add] at h1
  change _ + levelRel tasks S (t + 1) = _ + levelRel tasks S (t + 1) at h1
  omega

/-! ## R3: sufficiency -/

/-- **R3.**  At a drain point `e` of `S`, every job of `S` released before `e` is finished
in the state after step `e`. -/
theorem ticksBefore_eq_burst_of_pre_eq_zero {e : ℕ} (h_pre : pre tasks S e = 0)
    {p : PeriodicProcess} (hp : p ∈ jobsBy tasks e) (hpS : S p.id) (h_arr : p.arrival < e) :
    ticksBefore (runSchedule (stepPreemptive PeriodicProcess f) tasks) (key p) e = p.burst := by
  set σ := runSchedule (stepPreemptive PeriodicProcess f) tasks
  have h_adm : IsAdmissible tasks σ := runSchedule_stepPreemptive_isAdmissible f h_ids
  cases e with
  | zero => omega
  | succ t =>
    -- the work left after the tick of step `t + 1` is the backlog before `t + 1`
    have h_after : workOfAfter tasks σ (fun p => S p.id) t = 0 := by
      rw [← pre_succ_eq_workOfAfter hf h_ids hS]
      exact h_pre
    have hp_t : p ∈ jobsBy tasks t := by
      rw [jobsBy_succ] at hp
      refine (List.mem_append.mp hp).resolve_right fun h => ?_
      have := arrival_of_mem_releasesAt h
      omega
    have h_ge := burst_le_ticksBefore_of_workOfAfter_eq_zero h_after hp_t hpS
    have h_le := ticksBefore_le_burst h_ids h_adm hp
    omega

/-- **R3, for deadlines.**  A job of `S` released at `r` meets its deadline if `S` has a
drain point `e` with `r < e ≤ r + D`: it is finished in the state after step `r + D`. -/
theorem meetsDeadline_of_drainPoint {p : PeriodicProcess} {t : ℕ} (hp : p ∈ jobsBy tasks t)
    (hpS : S p.id) {e : ℕ} (h_pre : pre tasks S e = 0) (h_lt : p.arrival < e)
    (h_le : e ≤ absDeadline p) :
    ticksBefore (runSchedule (stepPreemptive PeriodicProcess f) tasks) (key p) (absDeadline p) =
      p.burst := by
  have h_adm := runSchedule_stepPreemptive_isAdmissible f h_ids (tasks := tasks)
  have hp_e : p ∈ jobsBy tasks e := by
    obtain ⟨t', ht', hp'⟩ := mem_jobsBy.mp hp
    exact mem_jobsBy.mpr ⟨t', by rw [← arrival_of_mem_releasesAt hp']; omega, hp'⟩
  have h_e := ticksBefore_eq_burst_of_pre_eq_zero hf h_ids hS h_pre hp_e hpS h_lt
  have h_mono := ticksBefore_mono (runSchedule (stepPreemptive PeriodicProcess f) tasks) (key p) h_le
  have h_burst := ticksBefore_le_burst h_ids h_adm (t := absDeadline p)
    (by
      obtain ⟨t', ht', hp'⟩ := mem_jobsBy.mp hp
      exact mem_jobsBy.mpr ⟨t', by rw [← arrival_of_mem_releasesAt hp']; unfold absDeadline; omega,
        hp'⟩)
  omega

/-- **A job that meets its deadline is never late**: under the hypotheses of
`meetsDeadline_of_drainPoint`, the job is not unfinished at any `t' ≥ absDeadline p`. -/
theorem not_mem_unfinished_of_drainPoint {p : PeriodicProcess} {t : ℕ} (hp : p ∈ jobsBy tasks t)
    (hpS : S p.id) {e : ℕ} (h_pre : pre tasks S e = 0) (h_lt : p.arrival < e)
    (h_le : e ≤ absDeadline p) {t' : ℕ} (ht' : absDeadline p ≤ t') :
    p ∉ unfinished tasks (runSchedule (stepPreemptive PeriodicProcess f) tasks) t' := by
  intro h
  have h_d := meetsDeadline_of_drainPoint hf h_ids hS hp hpS h_pre h_lt h_le
  have h_mono := ticksBefore_mono (runSchedule (stepPreemptive PeriodicProcess f) tasks)
    (key p) ht'
  have := (mem_unfinished.mp h).2
  omega

end Bridge

end Periodic
