/-
Copyright (c) 2026 Choo Kye Yong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Choo Kye Yong
-/
import FypSchedulingAlgorithms.PeriodicSchedulers.FixedPriorityBacklog

/-!
# Deadline Monotonic and Rate Monotonic are optimal among fixed-priority assignments

Leung and Whitehead (1982): for synchronous periodic tasks with constrained deadlines
(`D ≤ T`), if some fixed-priority assignment (distinct priorities per task) meets every
deadline, Deadline Monotonic does.  Liu and Layland (1973): with `D = T`, Rate Monotonic
does.

**Statement.**  Let `f` and `g` be fixed priorities (`FixedPriority`), with `f` strict on
the tasks (distinct tasks have distinct priorities) and `g`'s level sets deadline-closed
(a task at least as urgent under `g` has a deadline no longer).  If every task's first job
meets its deadline under `stepPreemptive f`, then `stepPreemptive g` is never late
(`never_late_of_firstJobs`); on runs, if `stepPreemptive f` never lists a missed deadline,
neither does `stepPreemptive g` (`fixedPriority_optimal`).  DM has deadline-closed level
sets (`dm_optimal`), and so does RM when `D = T` (`rm_optimal`).  The **first-job test**:
with distinct deadlines (resp. periods, and `D = T`), `stepDM` (resp. `stepRMS`) never
misses iff every task's first job meets its deadline (`dm_firstJob_test`,
`rm_firstJob_test`).  DM and RM need not be strict where they play `g`; the tests need
strictness because they apply R4 to DM and RM themselves.

**Scope.**  The discrete model of `PeriodicSchedules`, with the miss rule of
`PeriodicProcess.missedDeadlines` (a job released at `r` with relative deadline `D` gets
the `D` ticks of steps `r+1 … r+D`).  Synchronous releases (`PeriodicProcess.releasesAt`),
distinct task ids, `f` strict, and `D ≤ T` for every task with a positive period.  A task
with period 0 releases a single job at time 0 and needs no bound on its deadline; positive
periods are not needed anywhere.

**Ties.**  The comparison class is the strict fixed priorities: distinct priorities per
task (`h_strict`).  `stepPreemptive` breaks ties dynamically (the running job keeps the
CPU, the ready queue is FIFO), so a priority function with ties satisfies
`FixedPriority` but is not a classical fixed-priority assignment, and it can do better:
on `SampleTaskSets.rmsFailsEdfSucceeds` both strict orders miss a deadline, while the
constant priority never does (`tied_priority_never_misses_rmsFails`, in
`PeriodicWitnesses`).  DM and RM themselves may have ties where they play `g`.

**How.**  Everything goes through the level backlog of `FixedPriorityBacklog` (R1–R3) and
two more facts:

* **R4** (`exists_drainPoint_of_firstJob`): if `m`'s first job meets its deadline under a
  strict fixed `f`, then `m`'s level set has a drain point in `(0, D_m]`;
* **R5** (`exists_pre_eq_zero_of_window`): if `u` is a drain point and the synchronous busy
  period from 0 has a drain point `e > 0`, there is a drain point in `(u, u + e]`.  No
  window of length `e` releases more than `[0, e)` (`window_le_window_zero`, from counting
  multiples of each period, `wsum_le_wsum_zero`), and the backlog falls by exactly one per
  step while it stays positive (`levelBacklog_add_eq`).

For a job of task `k` released at `r`, let `S` be the tasks at least as urgent as `k`
under `g`, and `m` the least urgent of them under `f`.  Then `S` lies in `m`'s level set
under `f` and `D_m ≤ D_k`, so R4 and R2 give a drain point of `S` in `(0, D_k]`.  From the
last drain point of `S` at or before `r`, R5 gives one in `(r, r + D_k]`, and R3 says the
job is finished by then.

This route uses no swap argument and no general critical-instant theorem: the synchronous
busy period from 0 dominates every other busy period (R5).
-/

namespace Periodic

open PreemptiveRuns

/-! ## Releases in a window -/

/-- The work a task with period `T` and burst `C` releases at the times `a, …, a + n - 1`:
`C` at every multiple of `T` (only at 0 when `T = 0`). -/
def wsum (T C a n : ℕ) : ℕ :=
  ((List.range n).map fun i => if (a + i) % T = 0 then C else 0).sum

theorem wsum_zero_len (T C a : ℕ) : wsum T C a 0 = 0 := rfl

theorem wsum_succ (T C a n : ℕ) :
    wsum T C a (n + 1) = wsum T C a n + if (a + n) % T = 0 then C else 0 := by
  simp [wsum, List.range_succ]

theorem wsum_add (T C a m k : ℕ) : wsum T C a (m + k) = wsum T C a m + wsum T C (a + m) k := by
  induction k with
  | zero => simp [wsum_zero_len]
  | succ k ih =>
    rw [← Nat.add_assoc, wsum_succ, ih, wsum_succ, Nat.add_assoc a m k]
    omega

/-- Releases repeat with the period. -/
theorem wsum_add_period (T C a n : ℕ) : wsum T C (a + T) n = wsum T C a n := by
  unfold wsum
  congr 1
  refine List.map_congr_left fun i _ => ?_
  rw [Nat.add_right_comm, Nat.add_mod_right]

/-- No release in the window: no work. -/
theorem wsum_eq_zero_of_forall {T C a n : ℕ} (h : ∀ i < n, (a + i) % T ≠ 0) :
    wsum T C a n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [wsum_succ, ih fun i hi => h i (by omega), if_neg (h n (by omega))]

/-- A window no longer than the period holds at most one release. -/
theorem wsum_le_of_le_period {T C a n : ℕ} (hn : n ≤ T) : wsum T C a n ≤ C := by
  induction n with
  | zero => simp [wsum_zero_len]
  | succ n ih =>
    rw [wsum_succ]
    by_cases h : (a + n) % T = 0
    · rw [if_pos h, wsum_eq_zero_of_forall fun i hi h' => ?_]
      · omega
      -- two releases `i < n` less than a period apart
      have h_eq : (a + n) % T = (a + i) % T := by rw [h, h']
      have h_sub := Nat.sub_mod_eq_zero_of_mod_eq h_eq
      rw [show a + n - (a + i) = n - i by omega, Nat.mod_eq_of_lt (by omega)] at h_sub
      omega
    · rw [if_neg h]
      exact Nat.add_zero _ ▸ ih (by omega)

/-- The synchronous window `[0, n)` holds a release at 0. -/
theorem le_wsum_zero {T C n : ℕ} (hn : 0 < n) : C ≤ wsum T C 0 n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hn
  rw [show 0 + k + 1 = 1 + k by omega, wsum_add]
  simp [wsum]

/-- **The synchronous window releases the most**: no window of length `n` releases more
than `[0, n)`. -/
theorem wsum_le_wsum_zero (T C a n : ℕ) : wsum T C a n ≤ wsum T C 0 n := by
  rcases Nat.eq_zero_or_pos T with rfl | hT
  · -- period 0: one release, at time 0
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · exact le_rfl
    · rw [wsum_eq_zero_of_forall fun i _ => by simp; omega]
      exact Nat.zero_le _
  induction n using Nat.strong_induction_on generalizing a with
  | _ n ih =>
  by_cases hn : n ≤ T
  · rcases Nat.eq_zero_or_pos n with rfl | hn0
    · exact le_rfl
    · exact (wsum_le_of_le_period hn).trans (le_wsum_zero hn0)
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt (not_le.mp hn)
    rw [show T + k + 1 = T + (k + 1) by omega, wsum_add T C a T (k + 1), wsum_add_period,
      wsum_add T C 0 T (k + 1), wsum_add_period]
    have h1 := wsum_le_of_le_period (C := C) (a := a) (le_refl T)
    have h2 := le_wsum_zero (T := T) (C := C) hT
    have h3 := ih (k + 1) (by omega) a
    omega

/-! ## The level backlog in a window -/

section Window

variable (tasks : List PeriodicProcess) (S : ℕ → Prop) [DecidablePred S]

/-- The work released by `S` at time `t`, task by task. -/
theorem levelRel_eq (t : ℕ) :
    levelRel tasks S t =
      ((tasks.filter (S ·.id)).map fun τ => if t % τ.period = 0 then τ.burst else 0).sum := by
  unfold levelRel releasedOf PeriodicProcess.releasesAt
  induction tasks with
  | nil => rfl
  | cons τ L ih =>
    by_cases h1 : t % τ.period = 0 <;> by_cases h2 : S τ.id <;>
      simp_all

/-- The work released by `S` at the times `a, …, a + n - 1`. -/
def window (a n : ℕ) : ℕ :=
  ((List.range n).map fun i => levelRel tasks S (a + i)).sum

theorem window_succ (a n : ℕ) :
    window tasks S a (n + 1) = window tasks S a n + levelRel tasks S (a + n) := by
  simp [window, List.range_succ]

/-- The window, task by task. -/
theorem window_eq (a n : ℕ) :
    window tasks S a n =
      ((tasks.filter (S ·.id)).map fun τ => wsum τ.period τ.burst a n).sum := by
  induction n with
  | zero => simp [window, wsum]
  | succ n ih =>
    rw [window_succ, ih, levelRel_eq]
    simp only [wsum_succ]
    exact (sum_map_add_eq _ _ _).symm

/-- **R5's counting step: the synchronous window releases the most.** -/
theorem window_le_window_zero (a n : ℕ) : window tasks S a n ≤ window tasks S 0 n := by
  rw [window_eq, window_eq]
  exact sum_map_le_sum_map _ fun τ _ => wsum_le_wsum_zero _ _ _ _

/-- The backlog drops by at most one per step, so it is at least the work released so
far less the steps taken. -/
theorem window_le_levelBacklog_add (t : ℕ) :
    window tasks S 0 (t + 1) ≤ levelBacklog tasks S t + t := by
  induction t with
  | zero => simp [window, levelBacklog]
  | succ t ih =>
    rw [window_succ, levelBacklog]
    simp only [Nat.zero_add] at ih ⊢
    omega

/-- A drain point `e > 0` of the synchronous busy period bounds the work released before
it: `window 0 e ≤ e`. -/
theorem window_le_of_pre_eq_zero {e : ℕ} (he : 0 < e) (h : pre tasks S e = 0) :
    window tasks S 0 e ≤ e := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_lt he
  rw [Nat.zero_add, pre_succ] at *
  have := window_le_levelBacklog_add tasks S t
  omega

/-- While the backlog stays positive, it is exactly the released work less the steps
taken. -/
theorem levelBacklog_add_eq {u k : ℕ} (h : ∀ j < k, 1 ≤ levelBacklog tasks S (u + j)) :
    levelBacklog tasks S (u + k) + k = pre tasks S u + window tasks S u (k + 1) := by
  induction k with
  | zero => simp [window, levelBacklog_eq_pre_add]
  | succ k ih =>
    have ih' := ih fun j hj => h j (by omega)
    have hk := h k (by omega)
    have h_step : levelBacklog tasks S (u + (k + 1)) =
        (levelBacklog tasks S (u + k) - 1) + levelRel tasks S (u + (k + 1)) := rfl
    rw [h_step, window_succ]
    omega

/-- **R5, the busy-period bound.**  If `u` is a drain point of `S` and `S`'s synchronous
busy period from 0 has a drain point `e > 0`, then `S` has a drain point in
`(u, u + e]`. -/
theorem exists_pre_eq_zero_of_window {u e : ℕ} (hu : pre tasks S u = 0) (he : 0 < e)
    (h_e : pre tasks S e = 0) :
    ∃ e' : ℕ, u < e' ∧ e' ≤ u + e ∧ pre tasks S e' = 0 := by
  by_contra h_none
  push Not at h_none
  -- no drain point in `(u, u + e]`: the backlog stays positive from `u` to `u + e - 1`
  have h_pos : ∀ j < e, 2 ≤ levelBacklog tasks S (u + j) := by
    intro j hj
    have := h_none (u + j + 1) (by omega) (by omega)
    rw [pre_succ] at this
    omega
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt he
  have h_eq := levelBacklog_add_eq tasks S (u := u) (k := k) fun j hj => by
    have := h_pos j (by omega)
    omega
  have h_last := h_pos k (by omega)
  have h_win := window_le_window_zero tasks S u (k + 1)
  have h_zero := window_le_of_pre_eq_zero tasks S he h_e
  simp only [Nat.zero_add] at h_zero
  omega

end Window

/-! ## R4: a first job that meets its deadline drains its level -/

/-- The **level set** of task `m` under `f`: the ids of the tasks with priority at least
`f m`. -/
def levelSet (tasks : List PeriodicProcess) (f : PeriodicProcess → ℤ) (m : PeriodicProcess)
    (i : ℕ) : Prop :=
  ∃ τ ∈ tasks, τ.id = i ∧ f m ≤ f τ

instance (tasks : List PeriodicProcess) (f : PeriodicProcess → ℤ) (m : PeriodicProcess) :
    DecidablePred (levelSet tasks f m) :=
  fun i => inferInstanceAs (Decidable (∃ τ ∈ tasks, τ.id = i ∧ f m ≤ f τ))

/-- A level set is upward-closed. -/
theorem upClosed_levelSet {tasks : List PeriodicProcess}
    (h_ids : (tasks.map PeriodicProcess.id).Nodup) (f : PeriodicProcess → ℤ)
    (m : PeriodicProcess) : UpClosed tasks f (levelSet tasks f m) := by
  rintro τ hτ τ' hτ' ⟨τ'', hτ'', h_id, h_le⟩ h_f
  obtain rfl := task_eq_of_id_eq h_ids hτ'' hτ h_id
  exact ⟨τ', hτ', rfl, h_le.trans h_f⟩

/-- **R4.**  Let `f` be fixed and strict on the tasks, and let `m` be a task with
`D_m ≤ T_m` (or `T_m = 0`: a single job).  If `m`'s first job meets its deadline under
`stepPreemptive f`, then `m`'s level set has a drain point in `(0, D_m]`: the first step
`F` after which the job is finished.  After step `F - 1` the job holds the CPU with one
tick left; by strictness and the priority run invariant no other job of the level set
is unfinished then (`m`'s next job comes at `T_m ≥ D_m ≥ F`), so the backlog before `F`
is zero. -/
theorem exists_drainPoint_of_firstJob {f : PeriodicProcess → ℤ} (hf : FixedPriority f)
    {tasks : List PeriodicProcess} (h_ids : (tasks.map PeriodicProcess.id).Nodup)
    (h_strict : ∀ τ ∈ tasks, ∀ τ' ∈ tasks, f τ = f τ' → τ = τ')
    {m : PeriodicProcess} (hm : m ∈ tasks) (h_DT : 0 < m.period → m.deadline ≤ m.period)
    (h_first : MeetsDeadline (runSchedule (stepPreemptive PeriodicProcess f) tasks) (firstJob m)) :
    ∃ e, 0 < e ∧ e ≤ m.deadline ∧ pre tasks (levelSet tasks f m) e = 0 := by
  classical
  set σ := runSchedule (stepPreemptive PeriodicProcess f) tasks with hσ
  have hS := upClosed_levelSet h_ids f m
  have hj0_by := firstJob_mem_jobsBy hm
  -- `F = G + 1`: the first step after which the first job is finished
  have h_ex : ∃ t, m.burst ≤ ticksBefore σ (m.id, 0) t :=
    ⟨m.deadline, by simpa [MeetsDeadline] using h_first.ge⟩
  have hF_le : Nat.find h_ex ≤ m.deadline :=
    Nat.find_min' h_ex (by simpa [MeetsDeadline] using h_first.ge)
  have hF_spec := Nat.find_spec h_ex
  obtain ⟨G, hG⟩ : ∃ G, Nat.find h_ex = G + 1 := by
    refine ⟨Nat.find h_ex - 1, ?_⟩
    rcases Nat.eq_zero_or_pos (Nat.find h_ex) with h | h
    · rw [h, ticksBefore_zero] at hF_spec
      have := m.burst_exceed_zero
      omega
    · omega
  have hG_lt : ticksBefore σ (m.id, 0) G < m.burst := by
    have := Nat.find_min h_ex (show G < Nat.find h_ex by omega)
    omega
  rw [hG] at hF_spec hF_le
  -- the first job held the CPU after step `G`
  have hσG : σ G = some (m.id, 0) := by
    by_contra h
    rw [ticksBefore_succ_of_ne h] at hF_spec
    omega
  refine ⟨G + 1, by omega, hF_le, ?_⟩
  rw [pre_succ_eq_workOfAfter hf h_ids hS, workOfAfter_eq_zero_iff]
  -- after the tick of step `G + 1`, every job of the level set released by `G` is finished
  intro p hp_by hpS
  by_cases hpj : p = firstJob m
  · subst hpj
    simpa using hF_spec
  -- any other job of the level set was finished already after step `G`
  suffices h_fin : p.burst ≤ ticksBefore σ (key p) G from
    h_fin.trans (ticksBefore_mono σ (key p) (show G ≤ G + 1 by omega))
  by_contra h_lt
  push Not at h_lt
  obtain ⟨p0, hp0, hk, h_max⟩ := runSchedule_stepPreemptive_max f h_ids hσG
  obtain rfl : p0 = firstJob m :=
    key_injective h_ids (mem_unfinished.mp hp0).1 (hj0_by G) (by rw [hk, key_firstJob])
  have h_le : f p ≤ f m := by
    have h1 : f (jobAt σ G p) = f p := hf p p.arrival _
    have h2 : f (jobAt σ G (firstJob m)) = f m := hf m 0 _
    have := h_max p (mem_unfinished.mpr ⟨hp_by, h_lt⟩)
    rwa [h1, h2] at this
  -- so `p` is a job of `m`, released after 0 and before `G + 1 ≤ D_m ≤ T_m`
  obtain ⟨τ, hτ, hτ_id, hτ_f⟩ := hpS
  obtain ⟨r, hr, hp_rel⟩ := mem_jobsBy.mp hp_by
  obtain ⟨τp, hτp, h_mod, rfl⟩ := mem_releasesAt.mp hp_rel
  obtain rfl := task_eq_of_id_eq h_ids hτ hτp hτ_id
  have h_fp : f { τ with arrival := r, remaining := τ.burst } = f τ := hf τ r τ.burst
  obtain rfl := h_strict τ hτ m hm (by omega)
  have hr0 : r ≠ 0 := fun h => hpj (by subst h; rfl)
  rcases Nat.eq_zero_or_pos τ.period with h0 | h_pos
  · rw [h0, Nat.mod_zero] at h_mod
    exact hr0 h_mod
  · have := Nat.le_of_dvd (Nat.pos_of_ne_zero hr0) (Nat.dvd_of_mod_eq_zero h_mod)
    have := h_DT h_pos
    omega

/-! ## The main theorem -/

/-- **The main theorem, schedule form.**  Let `f` and `g` be fixed priorities, `f` strict
on the tasks, `g`'s level sets deadline-closed (a task at least as urgent under `g` has a
deadline no longer), and `D ≤ T` for every task with a positive period.  If every task's
first job meets its deadline under `stepPreemptive f`, then `stepPreemptive g` is never
late. -/
theorem never_late_of_firstJobs {f g : PeriodicProcess → ℤ} (hf : FixedPriority f)
    (hg : FixedPriority g) {tasks : List PeriodicProcess}
    (h_ids : (tasks.map PeriodicProcess.id).Nodup)
    (h_strict : ∀ τ ∈ tasks, ∀ τ' ∈ tasks, f τ = f τ' → τ = τ')
    (h_dc : ∀ τ ∈ tasks, ∀ τ' ∈ tasks, g τ ≤ g τ' → τ'.deadline ≤ τ.deadline)
    (h_DT : ∀ τ ∈ tasks, 0 < τ.period → τ.deadline ≤ τ.period)
    (h_first : ∀ m ∈ tasks,
      MeetsDeadline (runSchedule (stepPreemptive PeriodicProcess f) tasks) (firstJob m))
    (t : ℕ) : ¬ LateAt tasks (runSchedule (stepPreemptive PeriodicProcess g) tasks) t := by
  classical
  rintro ⟨p, hp, hpd⟩
  have hp' := mem_unfinished.mp hp
  obtain ⟨r, -, hp_rel⟩ := mem_jobsBy.mp hp'.1
  obtain ⟨k, hk, -, rfl⟩ := mem_releasesAt.mp hp_rel
  -- `S`: the tasks at least as urgent as `k` under `g`; `m`: its least urgent under `f`
  have hk_mem : k ∈ tasks.filter fun τ => g k ≤ g τ := List.mem_filter.mpr ⟨hk, by simp⟩
  obtain ⟨m, hm_mem, hm_min⟩ := exists_min_image_of_ne_nil _ f (List.ne_nil_of_mem hk_mem)
  obtain ⟨hm, hgm⟩ := List.mem_filter.mp hm_mem
  simp only [decide_eq_true_eq] at hgm
  have h_sub : ∀ i, levelSet tasks g k i → levelSet tasks f m i := by
    rintro i ⟨τ, hτ, h_id, h_le⟩
    exact ⟨τ, hτ, h_id, hm_min τ (List.mem_filter.mpr ⟨hτ, by simpa using h_le⟩)⟩
  have h_Dm : m.deadline ≤ k.deadline := h_dc k hk m hm hgm
  -- R4 and R2: `S` has a drain point `e1 ∈ (0, D_m]`
  obtain ⟨e1, he1_pos, he1_le, he1⟩ :=
    exists_drainPoint_of_firstJob hf h_ids h_strict hm (h_DT m hm) (h_first m hm)
  have hS_e1 : pre tasks (levelSet tasks g k) e1 = 0 :=
    Nat.eq_zero_of_le_zero ((pre_mono h_sub e1).trans he1.le)
  -- `u`: the last drain point of `S` at or before the release `r`
  have hu : pre tasks (levelSet tasks g k)
      (Nat.findGreatest (fun e => pre tasks (levelSet tasks g k) e = 0) r) = 0 :=
    Nat.findGreatest_spec (P := fun e => pre tasks (levelSet tasks g k) e = 0) (Nat.zero_le r)
      (pre_zero tasks _)
  have hu_le := Nat.findGreatest_le (P := fun e => pre tasks (levelSet tasks g k) e = 0) r
  -- R5: a drain point `e ∈ (u, u + e1]`, so `e ∈ (r, r + D_k]`
  obtain ⟨e, hue, he_le, he⟩ := exists_pre_eq_zero_of_window tasks _ hu he1_pos hS_e1
  have hre : r < e := by
    by_contra h
    exact Nat.findGreatest_is_greatest hue (by omega) he
  -- R3: the job meets its deadline
  exact not_mem_unfinished_of_drainPoint hg h_ids (upClosed_levelSet h_ids g k) hp'.1
    ⟨k, hk, rfl, le_rfl⟩ he hre (by simp only [absDeadline]; omega) hpd hp

/-- **The main theorem, on runs, from first jobs.**  Under the hypotheses of
`never_late_of_firstJobs`, the run of `stepPreemptive g` lists no missed deadline at any
step. -/
theorem fixedPriority_optimal_of_firstJobs {f g : PeriodicProcess → ℤ} (hf : FixedPriority f)
    (hg : FixedPriority g) {tasks : List PeriodicProcess}
    (h_ids : (tasks.map PeriodicProcess.id).Nodup)
    (h_strict : ∀ τ ∈ tasks, ∀ τ' ∈ tasks, f τ = f τ' → τ = τ')
    (h_dc : ∀ τ ∈ tasks, ∀ τ' ∈ tasks, g τ ≤ g τ' → τ'.deadline ≤ τ.deadline)
    (h_DT : ∀ τ ∈ tasks, 0 < τ.period → τ.deadline ≤ τ.period)
    (h_first : ∀ m ∈ tasks,
      MeetsDeadline (runSchedule (stepPreemptive PeriodicProcess f) tasks) (firstJob m))
    (t : ℕ) :
    PeriodicProcess.missedDeadlines
      (runSteps (PeriodicProcess.releasesAt tasks) (stepPreemptive PeriodicProcess g) t) = [] := by
  by_contra h
  exact never_late_of_firstJobs hf hg h_ids h_strict h_dc h_DT h_first t
    ((missedDeadlines_ne_nil_iff_preemptive g h_ids t).mp h)

/-- A preemptive run that never lists a missed deadline meets every task's first
deadline. -/
theorem firstJobs_of_never_late {f : PeriodicProcess → ℤ} {tasks : List PeriodicProcess}
    (h_ids : (tasks.map PeriodicProcess.id).Nodup)
    (h_f : ∀ t, PeriodicProcess.missedDeadlines
      (runSteps (PeriodicProcess.releasesAt tasks) (stepPreemptive PeriodicProcess f) t) = [])
    (m : PeriodicProcess) (hm : m ∈ tasks) :
    MeetsDeadline (runSchedule (stepPreemptive PeriodicProcess f) tasks) (firstJob m) :=
  meetsDeadline_of_not_lateAt h_ids (runSchedule_stepPreemptive_isAdmissible f h_ids)
    (firstJob_mem_jobsBy hm 0) fun h =>
      (missedDeadlines_ne_nil_iff_preemptive f h_ids _).mpr h (h_f _)

/-- **Fixed-priority optimality** (Leung and Whitehead 1982).  Let `f` and `g` be fixed
priorities, `f` strict on the tasks and `g`'s level sets deadline-closed, and `D ≤ T` for
every task with a positive period.  If the run of `stepPreemptive f` never lists a missed
deadline, neither does the run of `stepPreemptive g`. -/
theorem fixedPriority_optimal {f g : PeriodicProcess → ℤ} (hf : FixedPriority f)
    (hg : FixedPriority g) {tasks : List PeriodicProcess}
    (h_ids : (tasks.map PeriodicProcess.id).Nodup)
    (h_strict : ∀ τ ∈ tasks, ∀ τ' ∈ tasks, f τ = f τ' → τ = τ')
    (h_dc : ∀ τ ∈ tasks, ∀ τ' ∈ tasks, g τ ≤ g τ' → τ'.deadline ≤ τ.deadline)
    (h_DT : ∀ τ ∈ tasks, 0 < τ.period → τ.deadline ≤ τ.period)
    (h_f : ∀ t, PeriodicProcess.missedDeadlines
      (runSteps (PeriodicProcess.releasesAt tasks) (stepPreemptive PeriodicProcess f) t) = [])
    (t : ℕ) :
    PeriodicProcess.missedDeadlines
      (runSteps (PeriodicProcess.releasesAt tasks) (stepPreemptive PeriodicProcess g) t) = [] :=
  fixedPriority_optimal_of_firstJobs hf hg h_ids h_strict h_dc h_DT
    (firstJobs_of_never_late h_ids h_f) t

/-! ## Deadline Monotonic and Rate Monotonic -/

/-- DM's level sets are deadline-closed. -/
theorem deadlineClosed_dm (tasks : List PeriodicProcess) :
    ∀ τ ∈ tasks, ∀ τ' ∈ tasks, (fun p : PeriodicProcess => -(p.deadline : ℤ)) τ ≤
      (fun p : PeriodicProcess => -(p.deadline : ℤ)) τ' → τ'.deadline ≤ τ.deadline :=
  fun _ _ _ _ h => by simp only at h; omega

/-- With `D = T`, RM's level sets are deadline-closed. -/
theorem deadlineClosed_rm {tasks : List PeriodicProcess}
    (h_DT : ∀ τ ∈ tasks, τ.deadline = τ.period) :
    ∀ τ ∈ tasks, ∀ τ' ∈ tasks, (fun p : PeriodicProcess => -(p.period : ℤ)) τ ≤
      (fun p : PeriodicProcess => -(p.period : ℤ)) τ' → τ'.deadline ≤ τ.deadline :=
  fun τ hτ τ' hτ' h => by simp only at h; rw [h_DT τ hτ, h_DT τ' hτ']; omega

/-- **DM is optimal among fixed priorities** for constrained deadlines: if some strict
fixed-priority scheduler never misses a deadline, `stepDM` never does. -/
theorem dm_optimal {f : PeriodicProcess → ℤ} (hf : FixedPriority f)
    {tasks : List PeriodicProcess} (h_ids : (tasks.map PeriodicProcess.id).Nodup)
    (h_strict : ∀ τ ∈ tasks, ∀ τ' ∈ tasks, f τ = f τ' → τ = τ')
    (h_DT : ∀ τ ∈ tasks, 0 < τ.period → τ.deadline ≤ τ.period)
    (h_f : ∀ t, PeriodicProcess.missedDeadlines
      (runSteps (PeriodicProcess.releasesAt tasks) (stepPreemptive PeriodicProcess f) t) = [])
    (t : ℕ) :
    PeriodicProcess.missedDeadlines (runSteps (PeriodicProcess.releasesAt tasks) stepDM t) = [] :=
  fixedPriority_optimal hf fixedPriority_dm h_ids h_strict (deadlineClosed_dm tasks) h_DT h_f t

/-- **RM is optimal among fixed priorities** for implicit deadlines (`D = T`): if some
strict fixed-priority scheduler never misses a deadline, `stepRMS` never does. -/
theorem rm_optimal {f : PeriodicProcess → ℤ} (hf : FixedPriority f)
    {tasks : List PeriodicProcess} (h_ids : (tasks.map PeriodicProcess.id).Nodup)
    (h_strict : ∀ τ ∈ tasks, ∀ τ' ∈ tasks, f τ = f τ' → τ = τ')
    (h_DT : ∀ τ ∈ tasks, τ.deadline = τ.period)
    (h_f : ∀ t, PeriodicProcess.missedDeadlines
      (runSteps (PeriodicProcess.releasesAt tasks) (stepPreemptive PeriodicProcess f) t) = [])
    (t : ℕ) :
    PeriodicProcess.missedDeadlines (runSteps (PeriodicProcess.releasesAt tasks) stepRMS t) = [] :=
  fixedPriority_optimal hf fixedPriority_rms h_ids h_strict (deadlineClosed_rm h_DT)
    (fun τ hτ _ => (h_DT τ hτ).le) h_f t

/-- **The first-job test for DM.**  With distinct relative deadlines and `D ≤ T`, `stepDM`
never misses a deadline iff every task's first job meets its deadline under `stepDM`.
Distinct deadlines make DM strict, which R4 needs; with ties the test is not claimed
here. -/
theorem dm_firstJob_test {tasks : List PeriodicProcess}
    (h_ids : (tasks.map PeriodicProcess.id).Nodup)
    (h_distinct : ∀ τ ∈ tasks, ∀ τ' ∈ tasks, τ.deadline = τ'.deadline → τ = τ')
    (h_DT : ∀ τ ∈ tasks, 0 < τ.period → τ.deadline ≤ τ.period) :
    (∀ t, PeriodicProcess.missedDeadlines
        (runSteps (PeriodicProcess.releasesAt tasks) stepDM t) = []) ↔
      ∀ m ∈ tasks, MeetsDeadline (runSchedule stepDM tasks) (firstJob m) :=
  ⟨fun h => firstJobs_of_never_late h_ids h, fun h t =>
    fixedPriority_optimal_of_firstJobs fixedPriority_dm fixedPriority_dm h_ids
      (fun τ hτ τ' hτ' h_eq => h_distinct τ hτ τ' hτ' (by omega))
      (deadlineClosed_dm tasks) h_DT h t⟩

/-- **The first-job test for RM.**  With `D = T` and distinct periods, `stepRMS` never
misses a deadline iff every task's first job meets its deadline under `stepRMS`.
Distinct periods make RM strict, which R4 needs; with ties the test is not claimed
here. -/
theorem rm_firstJob_test {tasks : List PeriodicProcess}
    (h_ids : (tasks.map PeriodicProcess.id).Nodup)
    (h_distinct : ∀ τ ∈ tasks, ∀ τ' ∈ tasks, τ.period = τ'.period → τ = τ')
    (h_DT : ∀ τ ∈ tasks, τ.deadline = τ.period) :
    (∀ t, PeriodicProcess.missedDeadlines
        (runSteps (PeriodicProcess.releasesAt tasks) stepRMS t) = []) ↔
      ∀ m ∈ tasks, MeetsDeadline (runSchedule stepRMS tasks) (firstJob m) :=
  ⟨fun h => firstJobs_of_never_late h_ids h, fun h t =>
    fixedPriority_optimal_of_firstJobs fixedPriority_rms fixedPriority_rms h_ids
      (fun τ hτ τ' hτ' h_eq => h_distinct τ hτ τ' hτ' (by omega))
      (deadlineClosed_rm h_DT) (fun τ hτ _ => (h_DT τ hτ).le) h t⟩

end Periodic
