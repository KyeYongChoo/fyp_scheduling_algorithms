/-
Copyright (c) 2026 Choo Kye Yong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Choo Kye Yong
-/
import FypSchedulingAlgorithms.AperiodicSchedulers.ResponseTime.ResponseTimeSpec
import FypSchedulingAlgorithms.AperiodicSchedulers.AperiodicStep
import FypSchedulingAlgorithms.ProcessSimpLemmas
import FypSchedulingAlgorithms.SchedStateSimpLemmas
import Mathlib.Data.List.Nodup

/-! # Round Robin response time on a batch

Response time (`ResponseTimeSpec`) is the one metric a smaller quantum reliably improves:
total waiting and turnaround time are not monotone in the quantum
(`rr_smaller_quantum_not_better`), but response time is.

On a batch released at time 0, RR's first round serves the jobs in queue order,
and each job ahead of you holds the CPU for one slice, `firstSlice quantum p = min quantum
p.burst`.  So job `i` is first dispatched at step

  `sumOfFirstSlicesAhead quantum l i = Σ_{j < i} min quantum (burst j)`

(`rr_allArrivalsAtZero_isFirstDispatchAt`).  The run puts job `i` on the CPU then
(`rr_allArrivalsAtZero_dispatch`), and until then job `i` waits untouched in `ready`
(`rr_allArrivalsAtZero_waiting`) while the jobs ahead of it take their slices.  This is the
general form of `rr_convoy_dispatch`.

Two consequences:

* `rr_allArrivalsAtZero_firstDispatch_mono`: the first dispatch step is monotone in the
  quantum (from the formula-level `sumOfFirstSlicesAhead_mono`);
* `sumOfFirstSlicesAhead_of_large_quantum`: once the quantum covers every burst, the formula
  is the sum of the bursts ahead -- exactly FCFS's first dispatch step
  (`FCFSResponseTime`).

The quantum must be positive: `stepRR` treats quantum 0 like quantum 1.
-/

namespace ResponseTime

/-! ## Response time as a formula -/

/-- The slice job `p` gets in RR's first round. -/
def firstSlice (quantum : ℕ) (p : AperiodicProcess) : ℕ := min quantum p.burst

/-- The sum of the first-round slices of the jobs ahead of index `i` of a batch: in RR's
first round every job ahead of job `i` holds the CPU for one slice, so this is the step at
which job `i` is first dispatched (`rr_allArrivalsAtZero_isFirstDispatchAt`). -/
def sumOfFirstSlicesAhead (quantum : ℕ) (l : List AperiodicProcess) (i : ℕ) : ℕ :=
  ((l.take i).map (firstSlice quantum)).sum

/-- With a positive quantum every slice is at least one tick. -/
theorem firstSlice_pos {quantum : ℕ} (hq : 0 < quantum) (p : AperiodicProcess) :
    0 < firstSlice quantum p := by
  have := p.burst_exceed_zero
  simp only [firstSlice]
  omega

/-- One more job ahead, one more slice. -/
theorem sumOfFirstSlicesAhead_succ (quantum : ℕ) (l : List AperiodicProcess) {i : ℕ}
    (hi : i < l.length) :
    sumOfFirstSlicesAhead quantum l (i + 1) =
      sumOfFirstSlicesAhead quantum l i + firstSlice quantum l[i] := by
  rw [sumOfFirstSlicesAhead, sumOfFirstSlicesAhead, List.take_add_one,
    List.getElem?_eq_getElem hi, Option.toList_some, List.map_append, List.sum_append,
    List.map_singleton, List.sum_singleton]

/-- **The formula is monotone in the quantum.** -/
theorem sumOfFirstSlicesAhead_mono {quantum quantum' : ℕ} (h : quantum ≤ quantum')
    (l : List AperiodicProcess) (i : ℕ) :
    sumOfFirstSlicesAhead quantum l i ≤ sumOfFirstSlicesAhead quantum' l i := by
  unfold sumOfFirstSlicesAhead
  induction l.take i with
  | nil => simp
  | cons p ps ih =>
    simp only [List.map_cons, List.sum_cons, firstSlice] at ih ⊢
    omega

/-- **Large quantum = FCFS, as a formula.** Once the quantum covers every burst, the sum of
the first slices ahead of a job is the sum of the bursts ahead of it. -/
theorem sumOfFirstSlicesAhead_of_large_quantum {quantum : ℕ} {l : List AperiodicProcess}
    (h : ∀ p ∈ l, p.burst ≤ quantum) (i : ℕ) :
    sumOfFirstSlicesAhead quantum l i = ((l.take i).map (·.burst)).sum := by
  unfold sumOfFirstSlicesAhead
  congr 1
  apply List.map_congr_left
  intro p hp
  exact Nat.min_eq_right (h p (List.mem_of_mem_take hp))

/-! ## What one RR step does -/

/-- An idle CPU takes the head of the queue, unticked, with a fresh slice. -/
theorem stepRR_dispatch (quantum : ℕ) (rs : RRState) (nx : AperiodicProcess)
    (ps : List AperiodicProcess)
    (h_run : rs.sched.running = none) (h_ready : rs.sched.ready = nx :: ps) :
    (stepRR quantum rs).sched.running = some nx ∧ (stepRR quantum rs).sched.ready = ps ∧
      (stepRR quantum rs).ticksUsed = 0 := by
  simp [stepRR, h_run, h_ready]

/-- Within a slice, a job with work left after this tick is ticked and keeps the CPU. -/
theorem stepRR_tick (quantum : ℕ) (rs : RRState) (p : AperiodicProcess)
    (h_run : rs.sched.running = some p) (h_left : ¬ p.remaining ≤ 1)
    (h_quantum : ¬ rs.ticksUsed ≥ quantum - 1) :
    (stepRR quantum rs).sched.running = some { p with remaining := p.remaining - 1 } ∧
      (stepRR quantum rs).sched.ready = rs.sched.ready ∧
      (stepRR quantum rs).ticksUsed = rs.ticksUsed + 1 := by
  simp [stepRR, h_run, h_left, h_quantum]

/-- A job on its last tick completes, and the head of the queue is dispatched, unticked. -/
theorem stepRR_complete (quantum : ℕ) (rs : RRState) (p nx : AperiodicProcess)
    (ps : List AperiodicProcess)
    (h_run : rs.sched.running = some p) (h_done : p.remaining ≤ 1)
    (h_ready : rs.sched.ready = nx :: ps) :
    (stepRR quantum rs).sched.running = some nx ∧ (stepRR quantum rs).sched.ready = ps ∧
      (stepRR quantum rs).ticksUsed = 0 := by
  simp [stepRR, h_run, h_done, h_ready]

/-- The tick that uses up the quantum sends the ticked job to the back of the queue and
dispatches the head, unticked. -/
theorem stepRR_preempt (quantum : ℕ) (rs : RRState) (p nx : AperiodicProcess)
    (ps : List AperiodicProcess)
    (h_run : rs.sched.running = some p) (h_left : ¬ p.remaining ≤ 1)
    (h_quantum : rs.ticksUsed ≥ quantum - 1) (h_ready : rs.sched.ready = nx :: ps) :
    (stepRR quantum rs).sched.running = some nx ∧
      (stepRR quantum rs).sched.ready = ps ++ [{ p with remaining := p.remaining - 1 }] ∧
      (stepRR quantum rs).ticksUsed = 0 := by
  simp [stepRR, h_run, h_left, h_quantum, h_ready]

/-- On a batch nothing arrives after time 0, so each run step is one `stepRR`. -/
theorem runStepsRR_allArrivalsAtZero_succ (quantum : ℕ) (l : List AperiodicProcess) (t : ℕ) :
    runStepsRR quantum (allArrivalsAtZeroStream l) (t + 1) =
      stepRR quantum (runStepsRR quantum (allArrivalsAtZeroStream l) t) := by
  simp [runStepsRR, allArrivalsAtZeroStream]

/-! ## The first round, slice by slice -/

/-- The jobs of `pre` that did not finish within one slice, as they re-enter the
queue: preempted after exactly one quantum of work. -/
def leftovers (quantum : ℕ) (pre : List AperiodicProcess) : List AperiodicProcess :=
  (pre.filter (fun p => quantum < p.burst)).map
    (fun p => { p with remaining := p.burst - quantum })

/-- RR on batch `l` at the `k`-th tick of job `i`'s first slice: job `i` is on
the CPU with `k` ticks done, the jobs after it wait in order, and behind them
the earlier jobs that were preempted. -/
def RRFirstRoundAt (quantum : ℕ) (l : List AperiodicProcess) (i : ℕ) (hi : i < l.length)
    (k : ℕ) (rs : RRState) : Prop :=
  rs.sched.running = some { l[i] with remaining := l[i].burst - k } ∧
    rs.sched.ready = l.drop (i + 1) ++ leftovers quantum (l.take i) ∧
    rs.ticksUsed = k

/-- An untouched job is unchanged by "reset `remaining` to the full burst". -/
theorem with_remaining_burst {p : AperiodicProcess} (h : p.remaining = p.burst) :
    { p with remaining := p.burst - 0 } = p := by
  cases p
  simp_all

/-- Step 0: RR dispatches the first job of the batch. -/
theorem rr_first_round_start (quantum : ℕ) (l : List AperiodicProcess)
    (h_fresh : ∀ p ∈ l, p.remaining = p.burst) (hl : 0 < l.length) :
    RRFirstRoundAt quantum l 0 hl 0 (runStepsRR quantum (allArrivalsAtZeroStream l) 0) := by
  cases l with
  | nil => simp at hl
  | cons p rest =>
    rw [show runStepsRR quantum (allArrivalsAtZeroStream (p :: rest)) 0 =
        stepRR quantum ⟨{ SchedStateMethods.init with ready := p :: rest }, 0⟩ from rfl]
    obtain ⟨h_run, h_ready, h_ticks⟩ := stepRR_dispatch quantum
      ⟨{ SchedStateMethods.init with ready := p :: rest }, 0⟩ p rest rfl rfl
    refine ⟨?_, ?_, h_ticks⟩
    · rw [h_run, List.getElem_cons_zero,
        with_remaining_burst (h_fresh p (List.mem_cons_self ..))]
    · rw [h_ready]; simp [leftovers]

/-- Within a slice, RR ticks the running job and leaves the queue alone. -/
theorem rr_first_round_tick (quantum : ℕ) (l : List AperiodicProcess) (i : ℕ)
    (hi : i < l.length) (k : ℕ) (rs : RRState) (h : RRFirstRoundAt quantum l i hi k rs)
    (hk : k + 1 < firstSlice quantum l[i]) :
    RRFirstRoundAt quantum l i hi (k + 1) (stepRR quantum rs) := by
  obtain ⟨h_run, h_ready, h_ticks⟩ := h
  simp only [firstSlice] at hk
  obtain ⟨h1, h2, h3⟩ := stepRR_tick quantum rs _ h_run (by simp; omega)
    (by rw [h_ticks]; omega)
  refine ⟨?_, by rw [h2, h_ready], by rw [h3, h_ticks]⟩
  rw [h1]
  simp [Nat.sub_sub]

/-- At the end of job `i`'s slice, RR hands the CPU to job `i + 1`, whether job
`i` finished or was preempted to the back of the queue. -/
theorem rr_first_round_next (quantum : ℕ) (hq : 0 < quantum) (l : List AperiodicProcess)
    (h_fresh : ∀ p ∈ l, p.remaining = p.burst) (i : ℕ) (hi : i < l.length)
    (hi1 : i + 1 < l.length) (rs : RRState)
    (h : RRFirstRoundAt quantum l i hi (firstSlice quantum l[i] - 1) rs) :
    RRFirstRoundAt quantum l (i + 1) hi1 0 (stepRR quantum rs) := by
  obtain ⟨h_run, h_ready, h_ticks⟩ := h
  rw [List.drop_eq_getElem_cons hi1, List.cons_append] at h_ready
  have h_next : { l[i + 1] with remaining := l[i + 1].burst - 0 } = l[i + 1] :=
    with_remaining_burst (h_fresh _ (List.getElem_mem hi1))
  have h_take : l.take (i + 1) = l.take i ++ [l[i]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some]
  by_cases hb : l[i].burst ≤ quantum
  · -- job `i` finishes within its slice; it does not re-enter the queue
    have hs : firstSlice quantum l[i] = l[i].burst := Nat.min_eq_right hb
    obtain ⟨h1, h2, h3⟩ := stepRR_complete quantum rs _ _ _ h_run
      (by rw [hs]; simp; omega) h_ready
    refine ⟨by rw [h1, h_next], ?_, h3⟩
    rw [h2, h_take, leftovers, leftovers, List.filter_append, List.map_append]
    simp [show ¬ quantum < l[i].burst by omega]
  · -- job `i` is preempted after one quantum and goes to the back of the queue
    have hs : firstSlice quantum l[i] = quantum := Nat.min_eq_left (by omega)
    obtain ⟨h1, h2, h3⟩ := stepRR_preempt quantum rs _ _ _ h_run
      (by rw [hs]; simp; omega) (by omega) h_ready
    refine ⟨by rw [h1, h_next], ?_, h3⟩
    rw [h2, h_take, leftovers, leftovers, List.filter_append, List.map_append]
    simp [show quantum < l[i].burst by omega, hs]
    omega

/-- **RR's first round on a batch.** At step `sumOfFirstSlicesAhead quantum l i + k`, for
`k` within job `i`'s slice, RR is `k` ticks into job `i`'s first slice. -/
theorem rr_first_round (quantum : ℕ) (hq : 0 < quantum) (l : List AperiodicProcess)
    (h_fresh : ∀ p ∈ l, p.remaining = p.burst) :
    ∀ (i : ℕ) (hi : i < l.length) (k : ℕ), k < firstSlice quantum l[i] →
      RRFirstRoundAt quantum l i hi k
        (runStepsRR quantum (allArrivalsAtZeroStream l)
          (sumOfFirstSlicesAhead quantum l i + k)) := by
  intro i
  induction i with
  | zero =>
    intro hi k
    induction k with
    | zero =>
      intro _
      rw [show sumOfFirstSlicesAhead quantum l 0 + 0 = 0 by simp [sumOfFirstSlicesAhead]]
      exact rr_first_round_start quantum l h_fresh hi
    | succ k ih =>
      intro hk
      rw [← Nat.add_assoc, runStepsRR_allArrivalsAtZero_succ]
      exact rr_first_round_tick quantum l 0 hi k _ (ih (by omega)) hk
  | succ i ih =>
    intro hi k
    have hi' : i < l.length := by omega
    induction k with
    | zero =>
      intro _
      have hs := firstSlice_pos hq l[i]
      have h_step : sumOfFirstSlicesAhead quantum l (i + 1) + 0 =
          sumOfFirstSlicesAhead quantum l i + (firstSlice quantum l[i] - 1) + 1 := by
        rw [sumOfFirstSlicesAhead_succ quantum l hi']
        omega
      rw [h_step, runStepsRR_allArrivalsAtZero_succ]
      exact rr_first_round_next quantum hq l h_fresh i hi' hi _
        (ih hi' _ (by omega))
    | succ k ihk =>
      intro hk
      rw [← Nat.add_assoc, runStepsRR_allArrivalsAtZero_succ]
      exact rr_first_round_tick quantum l (i + 1) hi k _ (ihk (by omega)) hk

/-! ## The run, step by step -/

/-- **RR puts job `i` of a batch on the CPU at step `sumOfFirstSlicesAhead quantum l i`**,
untouched. -/
theorem rr_allArrivalsAtZero_dispatch (quantum : ℕ) (hq : 0 < quantum) (l : List AperiodicProcess)
    (h_fresh : ∀ p ∈ l, p.remaining = p.burst) (i : ℕ) (hi : i < l.length) :
    (runStepsRR quantum (allArrivalsAtZeroStream l)
        (sumOfFirstSlicesAhead quantum l i)).sched.running = some l[i] := by
  have h := (rr_first_round quantum hq l h_fresh i hi 0 (firstSlice_pos hq _)).1
  rw [Nat.add_zero] at h
  rw [h, with_remaining_burst (h_fresh _ (List.getElem_mem hi))]

/-- Every step before `sumOfFirstSlicesAhead quantum l i` falls inside the first slice of
some earlier job. -/
theorem sumOfFirstSlicesAhead_decompose (quantum : ℕ) (l : List AperiodicProcess) :
    ∀ (i : ℕ) (hi : i ≤ l.length), ∀ t, t < sumOfFirstSlicesAhead quantum l i →
      ∃ j, ∃ hj : j < i, ∃ k < firstSlice quantum (l[j]'(by omega)),
        t = sumOfFirstSlicesAhead quantum l j + k := by
  intro i
  induction i with
  | zero => intro _ t ht; simp [sumOfFirstSlicesAhead] at ht
  | succ i ih =>
    intro hi t ht
    rw [sumOfFirstSlicesAhead_succ quantum l (by omega)] at ht
    by_cases h : t < sumOfFirstSlicesAhead quantum l i
    · obtain ⟨j, hj, k, hk, rfl⟩ := ih (by omega) t h
      exact ⟨j, by omega, k, hk, rfl⟩
    · exact ⟨i, by omega, t - sumOfFirstSlicesAhead quantum l i, by omega, by omega⟩

/-- **Until its first dispatch, a job is waiting untouched.** Before step
`sumOfFirstSlicesAhead quantum l i`, job `i` sits in the ready queue exactly as it
arrived. -/
theorem rr_allArrivalsAtZero_waiting (quantum : ℕ) (hq : 0 < quantum) (l : List AperiodicProcess)
    (h_fresh : ∀ p ∈ l, p.remaining = p.burst) (i : ℕ) (hi : i < l.length) (t : ℕ)
    (ht : t < sumOfFirstSlicesAhead quantum l i) :
    l[i] ∈ (runStepsRR quantum (allArrivalsAtZeroStream l) t).sched.ready := by
  obtain ⟨j, hj, k, hk, rfl⟩ := sumOfFirstSlicesAhead_decompose quantum l i (Nat.le_of_lt hi) t ht
  rw [(rr_first_round quantum hq l h_fresh j (by omega) k hk).2.1]
  apply List.mem_append_left
  have h_get : (l.drop (j + 1))[i - (j + 1)]'(by simp; omega) = l[i] := by
    simp only [List.getElem_drop]
    congr 1
    omega
  rw [← h_get]
  exact List.getElem_mem _

/-- Before step `sumOfFirstSlicesAhead quantum l i`, the job on the CPU is an earlier job of
the batch, so with distinct ids it is not job `i`. -/
theorem rr_allArrivalsAtZero_running_ne (quantum : ℕ) (hq : 0 < quantum)
    {l : List AperiodicProcess} (h_atZero : AllArrivalsAtZero l) (i : ℕ) (hi : i < l.length)
    (t : ℕ) (ht : t < sumOfFirstSlicesAhead quantum l i) :
    (runRR quantum (allArrivalsAtZeroStream l) t).running.map (·.id) ≠ some l[i].id := by
  obtain ⟨j, hj, k, hk, rfl⟩ := sumOfFirstSlicesAhead_decompose quantum l i (Nat.le_of_lt hi) t ht
  rw [runRR_apply,
    (rr_first_round quantum hq l (fun p hp => (h_atZero.1 p hp).2) j (by omega) k hk).1]
  intro h_id
  simp only [Option.map_some, Option.some.injEq] at h_id
  have h_eq : (l.map (·.id))[j]'(by simp; omega) = (l.map (·.id))[i]'(by simp; omega) := by
    simpa using h_id
  have := (h_atZero.2.getElem_inj_iff).mp h_eq
  omega

/-! ## Response time -/

/-- **RR's first dispatch on a batch.** With a positive quantum, Round Robin on a batch
first puts job `i` on the CPU at step `sumOfFirstSlicesAhead quantum l i`: after every job
ahead of it has had one slice. -/
theorem rr_allArrivalsAtZero_isFirstDispatchAt (quantum : ℕ) (hq : 0 < quantum)
    {l : List AperiodicProcess} (h_atZero : AllArrivalsAtZero l) (i : ℕ) (hi : i < l.length) :
    IsFirstDispatchAt (scheduleOfRun (runRR quantum (allArrivalsAtZeroStream l))) l[i].id
      (sumOfFirstSlicesAhead quantum l i) := by
  refine ⟨?_, fun t ht => rr_allArrivalsAtZero_running_ne quantum hq h_atZero i hi t ht⟩
  simp only [scheduleOfRun, runRR_apply,
    rr_allArrivalsAtZero_dispatch quantum hq l (fun p hp => (h_atZero.1 p hp).2) i hi,
    Option.map_some]

/-- **RR's response time on a batch** is `sumOfFirstSlicesAhead quantum l i`: the jobs of a
batch arrive at time 0, so response time is the first dispatch step. -/
theorem rr_allArrivalsAtZero_hasResponseTime (quantum : ℕ) (hq : 0 < quantum)
    {l : List AperiodicProcess} (h_atZero : AllArrivalsAtZero l) (i : ℕ) (hi : i < l.length) :
    HasResponseTime (scheduleOfRun (runRR quantum (allArrivalsAtZeroStream l))) l[i]
      (sumOfFirstSlicesAhead quantum l i) :=
  (hasResponseTime_iff_of_arrival_eq_zero _ (h_atZero.1 _ (List.getElem_mem hi)).1 _).mpr
    (rr_allArrivalsAtZero_isFirstDispatchAt quantum hq h_atZero i hi)

/-- **Response time is monotone in the quantum.** On a batch, if Round Robin with quantum
`quantum` first dispatches job `i` at step `t` and Round Robin with a quantum
`quantum' ≥ quantum` first dispatches it at step `t'`, then `t ≤ t'`. -/
theorem rr_allArrivalsAtZero_firstDispatch_mono {quantum quantum' : ℕ} (hq : 0 < quantum)
    (h_le : quantum ≤ quantum') {l : List AperiodicProcess} (h_atZero : AllArrivalsAtZero l)
    (i : ℕ) (hi : i < l.length) {t t' : ℕ}
    (ht : IsFirstDispatchAt (scheduleOfRun (runRR quantum (allArrivalsAtZeroStream l)))
      l[i].id t)
    (ht' : IsFirstDispatchAt (scheduleOfRun (runRR quantum' (allArrivalsAtZeroStream l)))
      l[i].id t') :
    t ≤ t' := by
  rw [ht.unique (rr_allArrivalsAtZero_isFirstDispatchAt quantum hq h_atZero i hi),
    ht'.unique (rr_allArrivalsAtZero_isFirstDispatchAt quantum' (by omega) h_atZero i hi)]
  exact sumOfFirstSlicesAhead_mono h_le l i

end ResponseTime
