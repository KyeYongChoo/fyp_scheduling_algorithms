/-
Copyright (c) 2026 Choo Kye Yong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Choo Kye Yong
-/
import FypSchedulingAlgorithms.AperiodicSchedulers.ResponseTime.RRResponseTime
import FypSchedulingAlgorithms.AperiodicSchedulers.NonPreemptiveLemmas

/-! # FCFS response time on a batch, and RR with a large quantum

On a batch released at time 0, FCFS runs the jobs to completion in queue order, so job `i`
is first dispatched once every job ahead of it has run its whole burst, at step

  `sumOfBurstsAhead l i = Σ_{j < i} burst j`

(`fcfs_allArrivalsAtZero_isFirstDispatchAt`).

Round Robin's first round serves the same jobs in the same order, each for one slice
`min quantum burst` (`RRResponseTime`).  Once the quantum covers every burst, every slice is
a whole burst, and RR first dispatches every job of the batch exactly when FCFS does
(`rr_allArrivalsAtZero_isFirstDispatchAt_iff_fcfs_of_large_quantum`).  With a smaller
quantum RR's first dispatch step is no later (`rr_allArrivalsAtZero_firstDispatch_mono`).
-/

namespace ResponseTime

open NonPreemptive

/-- The sum of the bursts of the jobs ahead of index `i` of a batch: FCFS runs each of them
to completion before job `i`, so this is the step at which job `i` is first dispatched
(`fcfs_allArrivalsAtZero_isFirstDispatchAt`). -/
def sumOfBurstsAhead (l : List AperiodicProcess) (i : ℕ) : ℕ :=
  ((l.take i).map (·.burst)).sum

/-- One more job ahead, one more burst. -/
theorem sumOfBurstsAhead_succ (l : List AperiodicProcess) {i : ℕ} (hi : i < l.length) :
    sumOfBurstsAhead l (i + 1) = sumOfBurstsAhead l i + l[i].burst := by
  rw [sumOfBurstsAhead, sumOfBurstsAhead, List.take_add_one, List.getElem?_eq_getElem hi,
    Option.toList_some, List.map_append, List.sum_append, List.map_singleton,
    List.sum_singleton]

/-! ## FCFS on a batch, job by job -/

/-- FCFS on batch `l` at the `k`-th tick of job `i`: job `i` is on the CPU with `k` ticks
done, and the jobs after it wait in order. -/
def FCFSAllArrivalsAtZeroAt (l : List AperiodicProcess) (i : ℕ) (hi : i < l.length) (k : ℕ)
    (s : SchedState) : Prop :=
  s.running = some { l[i] with remaining := l[i].burst - k } ∧ s.ready = l.drop (i + 1)

/-- Step 0: FCFS dispatches the first job of the batch. -/
theorem fcfs_allArrivalsAtZero_start (l : List AperiodicProcess)
    (h_fresh : ∀ p ∈ l, p.remaining = p.burst) (hl : 0 < l.length) :
    FCFSAllArrivalsAtZeroAt l 0 hl 0 (runSteps (allArrivalsAtZeroStream l) stepFCFS 0) := by
  cases l with
  | nil => simp at hl
  | cons p rest =>
    obtain ⟨h_run, h_ready⟩ := stepNonPreemptive_dispatch selectFCFS
      { SchedStateMethods.init with ready := p :: rest } (q := p) rfl rfl
    refine ⟨?_, ?_⟩
    · rw [show runSteps (allArrivalsAtZeroStream (p :: rest)) stepFCFS 0 =
          stepNonPreemptive selectFCFS { SchedStateMethods.init with ready := p :: rest }
          from rfl, h_run, List.getElem_cons_zero,
        with_remaining_burst (h_fresh p (List.mem_cons_self ..))]
    · rw [show runSteps (allArrivalsAtZeroStream (p :: rest)) stepFCFS 0 =
          stepNonPreemptive selectFCFS { SchedStateMethods.init with ready := p :: rest }
          from rfl, h_ready]
      simp

/-- Before its last tick, FCFS ticks the running job and leaves the queue alone. -/
theorem fcfs_allArrivalsAtZero_tick (l : List AperiodicProcess) (i : ℕ) (hi : i < l.length) (k : ℕ)
    (s : SchedState) (h : FCFSAllArrivalsAtZeroAt l i hi k s) (hk : k + 1 < l[i].burst) :
    FCFSAllArrivalsAtZeroAt l i hi (k + 1) (stepFCFS s) := by
  obtain ⟨h_run, h_ready⟩ := h
  obtain ⟨h1, h2⟩ := stepNonPreemptive_tick selectFCFS s h_run (by simp; omega)
  refine ⟨?_, by rw [stepFCFS, h2, h_ready]⟩
  rw [stepFCFS, h1]
  simp [Nat.sub_sub]

/-- On job `i`'s last tick, FCFS completes it and dispatches job `i + 1`. -/
theorem fcfs_allArrivalsAtZero_next (l : List AperiodicProcess)
    (h_fresh : ∀ p ∈ l, p.remaining = p.burst) (i : ℕ) (hi : i < l.length)
    (hi1 : i + 1 < l.length) (s : SchedState)
    (h : FCFSAllArrivalsAtZeroAt l i hi (l[i].burst - 1) s) :
    FCFSAllArrivalsAtZeroAt l (i + 1) hi1 0 (stepFCFS s) := by
  obtain ⟨h_run, h_ready⟩ := h
  rw [List.drop_eq_getElem_cons hi1] at h_ready
  have h_pos := l[i].burst_exceed_zero
  obtain ⟨h1, h2⟩ := stepNonPreemptive_complete_dispatch selectFCFS s (q := l[i + 1]) h_run
    (by simp; omega) (by rw [h_ready]; rfl)
  refine ⟨?_, ?_⟩
  · rw [stepFCFS, h1, with_remaining_burst (h_fresh _ (List.getElem_mem hi1))]
  · rw [stepFCFS, h2, h_ready, List.erase_cons_head]

/-- **FCFS on a batch.** At step `sumOfBurstsAhead l i + k`, for `k` within job `i`'s burst,
FCFS is `k` ticks into job `i`. -/
theorem fcfs_allArrivalsAtZero_at (l : List AperiodicProcess)
    (h_fresh : ∀ p ∈ l, p.remaining = p.burst) :
    ∀ (i : ℕ) (hi : i < l.length) (k : ℕ), k < l[i].burst →
      FCFSAllArrivalsAtZeroAt l i hi k
        (runSteps (allArrivalsAtZeroStream l) stepFCFS (sumOfBurstsAhead l i + k)) := by
  intro i
  induction i with
  | zero =>
    intro hi k
    induction k with
    | zero =>
      intro _
      rw [show sumOfBurstsAhead l 0 + 0 = 0 by simp [sumOfBurstsAhead]]
      exact fcfs_allArrivalsAtZero_start l h_fresh hi
    | succ k ih =>
      intro hk
      rw [← Nat.add_assoc, runSteps_succ_of_nil stepFCFS _ _ rfl]
      exact fcfs_allArrivalsAtZero_tick l 0 hi k _ (ih (by omega)) hk
  | succ i ih =>
    intro hi k
    have hi' : i < l.length := by omega
    induction k with
    | zero =>
      intro _
      have h_pos := l[i].burst_exceed_zero
      have h_step : sumOfBurstsAhead l (i + 1) + 0 =
          sumOfBurstsAhead l i + (l[i].burst - 1) + 1 := by
        rw [sumOfBurstsAhead_succ l hi']
        omega
      rw [h_step, runSteps_succ_of_nil stepFCFS _ _ rfl]
      exact fcfs_allArrivalsAtZero_next l h_fresh i hi' hi _ (ih hi' _ (by omega))
    | succ k ihk =>
      intro hk
      rw [← Nat.add_assoc, runSteps_succ_of_nil stepFCFS _ _ rfl]
      exact fcfs_allArrivalsAtZero_tick l (i + 1) hi k _ (ihk (by omega)) hk

/-- Every step before `sumOfBurstsAhead l i` falls inside the burst of some earlier job. -/
theorem sumOfBurstsAhead_decompose (l : List AperiodicProcess) :
    ∀ (i : ℕ) (hi : i ≤ l.length), ∀ t, t < sumOfBurstsAhead l i →
      ∃ j, ∃ hj : j < i, ∃ k < (l[j]'(by omega)).burst, t = sumOfBurstsAhead l j + k := by
  intro i
  induction i with
  | zero => intro _ t ht; simp [sumOfBurstsAhead] at ht
  | succ i ih =>
    intro hi t ht
    rw [sumOfBurstsAhead_succ l (by omega)] at ht
    by_cases h : t < sumOfBurstsAhead l i
    · obtain ⟨j, hj, k, hk, rfl⟩ := ih (by omega) t h
      exact ⟨j, by omega, k, hk, rfl⟩
    · exact ⟨i, by omega, t - sumOfBurstsAhead l i, by omega, by omega⟩

/-! ## Response time -/

/-- **FCFS's first dispatch on a batch.** FCFS on a batch first puts job `i` on the CPU at
step `sumOfBurstsAhead l i`: after every job ahead of it has run its whole burst. -/
theorem fcfs_allArrivalsAtZero_isFirstDispatchAt {l : List AperiodicProcess}
    (h_atZero : AllArrivalsAtZero l) (i : ℕ) (hi : i < l.length) :
    IsFirstDispatchAt (runSchedule stepFCFS (allArrivalsAtZeroStream l)) l[i].id
      (sumOfBurstsAhead l i) := by
  have h_fresh : ∀ p ∈ l, p.remaining = p.burst := fun p hp => (h_atZero.1 p hp).2
  refine ⟨?_, fun t ht => ?_⟩
  · have h := (fcfs_allArrivalsAtZero_at l h_fresh i hi 0 l[i].burst_exceed_zero).1
    rw [Nat.add_zero, with_remaining_burst (h_fresh _ (List.getElem_mem hi))] at h
    simp [runSchedule, scheduleOfRun, h]
  · obtain ⟨j, hj, k, hk, rfl⟩ := sumOfBurstsAhead_decompose l i (Nat.le_of_lt hi) t ht
    simp only [runSchedule, scheduleOfRun,
      (fcfs_allArrivalsAtZero_at l h_fresh j (by omega) k hk).1, Option.map_some]
    intro h_id
    have := h_atZero.getElem_id_inj (i := j) (by omega) hi (by simpa using h_id)
    omega

/-- **FCFS's response time on a batch** is `sumOfBurstsAhead l i`. -/
theorem fcfs_allArrivalsAtZero_hasResponseTime {l : List AperiodicProcess}
    (h_atZero : AllArrivalsAtZero l) (i : ℕ) (hi : i < l.length) :
    HasResponseTime (runSchedule stepFCFS (allArrivalsAtZeroStream l)) l[i]
      (sumOfBurstsAhead l i) :=
  (hasResponseTime_iff_of_arrival_eq_zero _ (h_atZero.1 _ (List.getElem_mem hi)).1 _).mpr
    (fcfs_allArrivalsAtZero_isFirstDispatchAt h_atZero i hi)

/-! ## Round Robin with a large quantum -/

/-- **RR with a large quantum first dispatches like FCFS.** On a batch, once the quantum
covers every burst, Round Robin first puts job `i` on the CPU at step `t` exactly when FCFS
does. -/
theorem rr_allArrivalsAtZero_isFirstDispatchAt_iff_fcfs_of_large_quantum {quantum : ℕ}
    {l : List AperiodicProcess} (h_atZero : AllArrivalsAtZero l)
    (h_large : ∀ p ∈ l, p.burst ≤ quantum) (i : ℕ) (hi : i < l.length) (t : ℕ) :
    IsFirstDispatchAt (scheduleOfRun (runRR quantum (allArrivalsAtZeroStream l))) l[i].id t ↔
      IsFirstDispatchAt (runSchedule stepFCFS (allArrivalsAtZeroStream l)) l[i].id t := by
  have hq : 0 < quantum :=
    Nat.lt_of_lt_of_le l[i].burst_exceed_zero (h_large _ (List.getElem_mem hi))
  have h_rr := rr_allArrivalsAtZero_isFirstDispatchAt quantum hq h_atZero i hi
  have h_fcfs := fcfs_allArrivalsAtZero_isFirstDispatchAt h_atZero i hi
  rw [sumOfFirstSlicesAhead_of_large_quantum h_large] at h_rr
  constructor
  · intro h
    rw [h.unique h_rr]
    exact h_fcfs
  · intro h
    rw [h.unique h_fcfs]
    exact h_rr

end ResponseTime
