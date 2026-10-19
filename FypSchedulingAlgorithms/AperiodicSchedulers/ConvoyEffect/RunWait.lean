/-
Copyright (c) 2026 Choo Kye Yong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Choo Kye Yong
-/
import FypSchedulingAlgorithms.AperiodicSchedulers.ConvoyEffect.ConvoySpec
import FypSchedulingAlgorithms.AperiodicSchedulers.ConvoyEffect.SJFConvoy
import FypSchedulingAlgorithms.AperiodicSchedulers.AperiodicStep
import FypSchedulingAlgorithms.AperiodicSchedulers.NonPreemptiveLemmas
import FypSchedulingAlgorithms.ProcessSimpLemmas
import FypSchedulingAlgorithms.SchedStateSimpLemmas

/-!
# Total waiting time of a run

`totalWait` (in `TotalWait`) is a formula on a list of bursts.  This file ties it
to actual executions.

* `runWait run as T` is the waiting time of a *run*: at each of the first `T`
  steps, every job sitting in `ready` waits one tick.  Summed over jobs this is
  each job's time in the ready queue -- the textbook definition -- and it makes
  sense for any scheduler presented as a run function: non-preemptive,
  preemptive (`runSteps · stepSRTF`) or Round Robin
  (`fun as t => (runStepsRR q as t).sched`).
* `dispatchOrder select l` is the order in which a non-preemptive policy
  dispatches a batch `l`: ask `select`, remove its choice, repeat.  It is a
  permutation of `l` (`dispatchOrder_perm`).
* **The bridge** (`runWait_batch_eq_totalWait`): releasing a batch at time 0,
  the run of `stepNonPreemptive select` waits exactly
  `totalWait` of the bursts in dispatch order, once it has run long enough to
  finish everything.

The bridge is a special case of a statement about any state with the arrivals
switched off (`waitFrom_drain`): if a job with `r` ticks left is on the CPU and
fresh jobs `R` wait, the wait still to come is `r * R.length` plus `totalWait`
of `R` in dispatch order.

Combined with `totalWait_sorted_le` (shortest first is optimal) this gives a
run-level characterisation of the batch convoy effect
(`hasBatchConvoyEffect_iff_runWait`): a policy has it exactly when, on some batch,
its run waits strictly longer than SJF's.
-/

namespace ConvoyEffect

open scoped List
open NonPreemptive

/-! ## Waiting time of a run -/

/-- Total waiting time of a run over its first `T` steps: at each step every job
in `ready` waits one tick.  Summed over jobs this is each job's time in the ready
queue (the textbook definition), for any scheduler, preemptive or not. -/
def runWait (run : (ℕ → List AperiodicProcess) → ℕ → SchedState)
    (arrival_stream : ℕ → List AperiodicProcess) (T : ℕ) : ℕ :=
  ((List.range T).map fun t => (run arrival_stream t).ready.length).sum

/-- Waiting time of the `T` states `s, step s, step (step s), ...`: the wait
still to come from state `s` when nothing else arrives. -/
def waitFrom (step : SchedState → SchedState) (s : SchedState) (T : ℕ) : ℕ :=
  ((List.range T).map fun t => (step^[t] s).ready.length).sum

/-- Over a zero horizon nobody waits. -/
@[simp] theorem waitFrom_zero (step : SchedState → SchedState) (s : SchedState) :
    waitFrom step s 0 = 0 := rfl

/-- Peel off the current state. -/
theorem waitFrom_succ (step : SchedState → SchedState) (s : SchedState) (T : ℕ) :
    waitFrom step s (T + 1) = s.ready.length + waitFrom step (step s) T := by
  simp only [waitFrom, List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map,
    Function.iterate_zero_apply]
  congr 2

/-! ### Runs with no arrivals for a while -/

/-- When nothing arrives at time `t + 1`, run step `t + 1` is just one `step`. -/
theorem runSteps_succ_of_nil (step : SchedState → SchedState)
    (arrival_stream : ℕ → List AperiodicProcess) (t : ℕ) (h : arrival_stream (t + 1) = []) :
    runSteps arrival_stream step (t + 1) = step (runSteps arrival_stream step t) := by
  simp [runSteps, h]

/-- When nothing arrives in `(t, t + k]`, the run from time `t` on is `step`
iterated. -/
theorem runSteps_add_eq_iterate (step : SchedState → SchedState)
    (arrival_stream : ℕ → List AperiodicProcess) (t k : ℕ)
    (h : ∀ j, t < j → j ≤ t + k → arrival_stream j = []) :
    runSteps arrival_stream step (t + k) = step^[k] (runSteps arrival_stream step t) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [← Nat.add_assoc, runSteps_succ_of_nil _ _ _ (h _ (by omega) (by omega)),
      ih (fun j h1 h2 => h j h1 (by omega)), Function.iterate_succ_apply']

/-- **Splitting a run's waiting time.** When nothing arrives in `(t, t + T)`, the
wait over the first `t + T` steps is the wait up to `t` plus the wait still to
come from the state at `t`. -/
theorem runWait_add (step : SchedState → SchedState)
    (arrival_stream : ℕ → List AperiodicProcess) (t T : ℕ)
    (h : ∀ j, t < j → j < t + T → arrival_stream j = []) :
    runWait (runSteps · step) arrival_stream (t + T) =
      runWait (runSteps · step) arrival_stream t +
        waitFrom step (runSteps arrival_stream step t) T := by
  unfold runWait waitFrom
  rw [List.range_add, List.map_append, List.sum_append, List.map_map]
  congr 2
  apply List.map_congr_left
  intro k hk
  have hk' := List.mem_range.mp hk
  simp only [Function.comp_apply]
  rw [runSteps_add_eq_iterate step arrival_stream t k (fun j h1 h2 => h j h1 (by omega))]

/-- A longer horizon never waits less: `runWait` only adds terms as `T` grows. -/
theorem runWait_mono (run : (ℕ → List AperiodicProcess) → ℕ → SchedState)
    (arrival_stream : ℕ → List AperiodicProcess) {T T' : ℕ} (h : T ≤ T') :
    runWait run arrival_stream T ≤ runWait run arrival_stream T' := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  unfold runWait
  rw [List.range_add, List.map_append, List.sum_append]
  exact Nat.le_add_right _ _

/-- On a batch nothing arrives after time 0, so each run step is one `step`. -/
theorem runSteps_batch_succ (step : SchedState → SchedState) (l : List AperiodicProcess)
    (t : ℕ) : runSteps (batchStream l) step (t + 1) = step (runSteps (batchStream l) step t) :=
  runSteps_succ_of_nil step _ t rfl

/-- After time 0 a batch stream is empty. -/
theorem batchStream_succ (l : List AperiodicProcess) (j : ℕ) (hj : 0 < j) :
    batchStream l j = [] := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  rfl

/-- On a batch, the run is `step` iterated from the state after step 0. -/
theorem runSteps_batch_eq_iterate (step : SchedState → SchedState) (l : List AperiodicProcess)
    (t : ℕ) : runSteps (batchStream l) step t = step^[t] (runSteps (batchStream l) step 0) := by
  have := runSteps_add_eq_iterate step (batchStream l) 0 t
    (fun j h1 _ => batchStream_succ l j h1)
  rwa [Nat.zero_add] at this

/-- On a batch, the run's waiting time is the wait from the state after step 0. -/
theorem runWait_batch_eq_waitFrom (step : SchedState → SchedState) (l : List AperiodicProcess)
    (T : ℕ) :
    runWait (fun as => runSteps as step) (batchStream l) T =
      waitFrom step (runSteps (batchStream l) step 0) T := by
  have := runWait_add step (batchStream l) 0 T (fun j h1 _ => batchStream_succ l j h1)
  rw [Nat.zero_add] at this
  rw [this]
  exact Nat.zero_add _

/-! ## Dispatch order of a non-preemptive policy -/

/-- `n` rounds of: ask `select` for a job, remove it from the queue. -/
def dispatchOrderAux (select : List AperiodicProcess → Option AperiodicProcess) :
    ℕ → List AperiodicProcess → List AperiodicProcess
  | 0,     _     => []
  | n + 1, ready => match select ready with
    | none   => []
    | some p => p :: dispatchOrderAux select n (ready.erase p)

/-- The order in which a non-preemptive policy dispatches the jobs of `ready`
when nothing else arrives.  The fuel `ready.length` is enough: every round
removes one job. -/
def dispatchOrder (select : List AperiodicProcess → Option AperiodicProcess)
    (ready : List AperiodicProcess) : List AperiodicProcess :=
  dispatchOrderAux select ready.length ready

/-- Nothing to dispatch. -/
@[simp] theorem dispatchOrder_nil (select : List AperiodicProcess → Option AperiodicProcess) :
    dispatchOrder select [] = [] := rfl

/-- One round of `dispatchOrder`. -/
theorem dispatchOrder_of_select {select : List AperiodicProcess → Option AperiodicProcess}
    (h_mem : ∀ l p, select l = some p → p ∈ l) {l : List AperiodicProcess}
    {p : AperiodicProcess} (h : select l = some p) :
    dispatchOrder select l = p :: dispatchOrder select (l.erase p) := by
  have h_len := List.length_erase_of_mem (h_mem l p h)
  obtain ⟨n, hn⟩ : ∃ n, l.length = n + 1 :=
    ⟨l.length - 1, by have := List.length_pos_of_mem (h_mem l p h); omega⟩
  unfold dispatchOrder
  rw [hn, h_len, hn]
  simp [dispatchOrderAux, h]

/-- **The dispatch order is a permutation of the batch**: every job is
dispatched exactly once. -/
theorem dispatchOrder_perm {select : List AperiodicProcess → Option AperiodicProcess}
    (h_mem : ∀ l p, select l = some p → p ∈ l) (h_none : ∀ l, select l = none → l = [])
    (l : List AperiodicProcess) : dispatchOrder select l ~ l := by
  obtain ⟨n, hn⟩ : ∃ n, l.length = n := ⟨_, rfl⟩
  induction n generalizing l with
  | zero => rw [List.length_eq_zero_iff.mp hn]; exact List.Perm.nil
  | succ n ih =>
    cases h : select l with
    | none => rw [h_none l h]; exact List.Perm.nil
    | some p =>
      have hp := h_mem l p h
      rw [dispatchOrder_of_select h_mem h]
      refine ((ih (l.erase p) ?_).cons p).trans (List.perm_cons_erase hp).symm
      rw [List.length_erase_of_mem hp, hn]
      rfl

/-- If the policy picks a shortest job from every queue in some family `P` that
is closed under removing a job, it dispatches every queue of the family in
non-decreasing order of burst. -/
theorem dispatchOrder_sorted_on {select : List AperiodicProcess → Option AperiodicProcess}
    (h_mem : ∀ l p, select l = some p → p ∈ l) (h_none : ∀ l, select l = none → l = [])
    (P : List AperiodicProcess → Prop) (hP : ∀ l p, P l → P (l.erase p))
    (h_short : ∀ l, P l → ∀ p, select l = some p → ∀ q ∈ l, p.burst ≤ q.burst)
    (l : List AperiodicProcess) (hl : P l) :
    ((dispatchOrder select l).map (·.burst)).Pairwise (· ≤ ·) := by
  obtain ⟨n, hn⟩ : ∃ n, l.length = n := ⟨_, rfl⟩
  induction n generalizing l with
  | zero => rw [List.length_eq_zero_iff.mp hn]; simp
  | succ n ih =>
    cases h : select l with
    | none => rw [h_none l h]; simp
    | some p =>
      have hp := h_mem l p h
      rw [dispatchOrder_of_select h_mem h, List.map_cons, List.pairwise_cons]
      refine ⟨?_, ih (l.erase p) (hP l p hl) (by rw [List.length_erase_of_mem hp, hn]; rfl)⟩
      intro b hb
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hb
      have hq' := List.mem_of_mem_erase ((dispatchOrder_perm h_mem h_none _).subset hq)
      exact h_short l hl p h q hq'

/-- A policy that always picks a shortest job, from any queue, dispatches any
queue in non-decreasing order of burst.  (No batch assumption: this applies to
the queue a run has built up mid-way.) -/
theorem dispatchOrder_sorted_of_min {select : List AperiodicProcess → Option AperiodicProcess}
    (h_mem : ∀ l p, select l = some p → p ∈ l) (h_none : ∀ l, select l = none → l = [])
    (h_short : ∀ l p, select l = some p → ∀ q ∈ l, p.burst ≤ q.burst)
    (l : List AperiodicProcess) :
    ((dispatchOrder select l).map (·.burst)).Pairwise (· ≤ ·) :=
  dispatchOrder_sorted_on h_mem h_none (fun _ => True) (fun _ _ _ => trivial)
    (fun l _ p h => h_short l p h) l trivial

/-- If the policy always picks a shortest job of a batch, it dispatches the
batch in non-decreasing order of burst. -/
theorem dispatchOrder_sorted {select : List AperiodicProcess → Option AperiodicProcess}
    (h_mem : ∀ l p, select l = some p → p ∈ l) (h_none : ∀ l, select l = none → l = [])
    (h_short : RunsShortestProcessBatch select) (l : List AperiodicProcess) (h_batch : IsBatch l) :
    ((dispatchOrder select l).map (·.burst)).Pairwise (· ≤ ·) :=
  -- what is left of a batch is again a batch
  dispatchOrder_sorted_on h_mem h_none IsBatch
    (fun _ _ h_batch => ⟨fun q hq => h_batch.1 q (List.mem_of_mem_erase hq),
      h_batch.2.sublist ((List.erase_sublist).map _)⟩)
    (fun l h_batch p h => h_short l h_batch p (h_mem l p h) h) l h_batch

/-- Taking a job out of a batch takes its burst out of the total work. -/
theorem sum_map_erase (f : AperiodicProcess → ℕ) {l : List AperiodicProcess}
    {x : AperiodicProcess} (h : x ∈ l) :
    (l.map f).sum = f x + ((l.erase x).map f).sum := by
  induction l with
  | nil => simp at h
  | cons y ys ih =>
    by_cases hxy : y = x
    · subst hxy; simp
    · have hx : x ∈ ys := (List.mem_cons.mp h).resolve_left (Ne.symm hxy)
      simp only [List.erase_cons, beq_iff_eq, hxy, ↓reduceIte, List.map_cons, List.sum_cons,
        ih hx]
      omega

/-! ## The bridge -/

/-- An idle CPU with nothing waiting stays that way, and nobody waits. -/
theorem waitFrom_idle {select : List AperiodicProcess → Option AperiodicProcess}
    (h_mem : ∀ l p, select l = some p → p ∈ l) (s : SchedState)
    (h_run : s.running = none) (h_ready : s.ready = []) (T : ℕ) :
    waitFrom (stepNonPreemptive select) s T = 0 := by
  have h_sel : select [] = none := by
    cases h : select [] with
    | none => rfl
    | some p => exact absurd (h_mem [] p h) List.not_mem_nil
  induction T generalizing s with
  | zero => rfl
  | succ T ih =>
    obtain ⟨h1, h2⟩ := stepNonPreemptive_idle select s h_run (by rw [h_ready]; exact h_sel)
    rw [waitFrom_succ, ih _ h1 (by rw [h2, h_ready]), h_ready]
    rfl

/-- **Draining a state.** Suppose arrivals have stopped, a job with `r > 0`
ticks left holds the CPU, and the jobs `R` waiting in `ready` are untouched.
Then over any horizon long enough to finish everything, the run of
`stepNonPreemptive select` waits `r` ticks for each job of `R` while the current
job finishes, plus `totalWait` of `R` in the order the policy dispatches it. -/
theorem waitFrom_drain {select : List AperiodicProcess → Option AperiodicProcess}
    (h_mem : ∀ l p, select l = some p → p ∈ l) (h_none : ∀ l, select l = none → l = [])
    (s : SchedState) (p : AperiodicProcess) (h_run : s.running = some p)
    (h_pos : 0 < p.remaining) (h_fresh : ∀ q ∈ s.ready, q.remaining = q.burst)
    (T : ℕ) (hT : p.remaining + (s.ready.map (·.burst)).sum ≤ T) :
    waitFrom (stepNonPreemptive select) s T =
      p.remaining * s.ready.length + totalWait ((dispatchOrder select s.ready).map (·.burst)) := by
  -- each step uses up one tick of the work left, so induct on the horizon
  induction T generalizing s p with
  | zero => omega
  | succ T ih =>
    rw [waitFrom_succ]
    by_cases h_left : 1 < p.remaining
    · -- the current job ticks and keeps the CPU
      obtain ⟨h1, h2⟩ := stepNonPreemptive_tick select s h_run h_left
      rw [ih (stepNonPreemptive select s) _ h1 (by simp only; omega) (by rw [h2]; exact h_fresh)
        (by simp only [h2]; omega), h2]
      obtain ⟨r, hr⟩ : ∃ r, p.remaining = r + 1 := ⟨p.remaining - 1, by omega⟩
      simp only [hr, Nat.add_sub_cancel, Nat.succ_mul]
      omega
    · -- the current job finishes
      cases h_sel : select s.ready with
      | none =>
        -- nothing left to run
        obtain ⟨h1, h2⟩ := stepNonPreemptive_complete_idle select s h_run (by omega) h_sel
        have h_nil := h_none _ h_sel
        rw [waitFrom_idle h_mem _ h1 (by rw [h2, h_nil]), h_nil]
        simp
      | some q =>
        -- `q` takes over, untouched, and the rest of `ready` waits on
        obtain ⟨h1, h2⟩ := stepNonPreemptive_complete_dispatch select s h_run (by omega) h_sel
        have hq := h_mem _ _ h_sel
        have hq_fresh := h_fresh q hq
        have h_sum := sum_map_erase (·.burst) hq
        have h_len := List.length_erase_of_mem hq
        have h_len_pos := List.length_pos_of_mem hq
        rw [ih (stepNonPreemptive select s) q h1 (by rw [hq_fresh]; exact q.burst_exceed_zero)
          (by rw [h2]; exact fun r hr => h_fresh r (List.mem_of_mem_erase hr))
          (by rw [h2]; omega), h2, dispatchOrder_of_select h_mem h_sel, List.map_cons,
          totalWait_cons, List.length_map,
          (dispatchOrder_perm h_mem h_none (s.ready.erase q)).length_eq, hq_fresh]
        have : p.remaining = 1 := by omega
        rw [this]
        omega

/-- **Bridge: the run waits `totalWait` of its dispatch order.** Release a batch
of untouched jobs at time 0 and run `stepNonPreemptive select`; once the
horizon covers the total work, the run's waiting time is `totalWait` of the
bursts in the order the policy dispatches them. -/
theorem runWait_batch_eq_totalWait {select : List AperiodicProcess → Option AperiodicProcess}
    (h_mem : ∀ l p, select l = some p → p ∈ l) (h_none : ∀ l, select l = none → l = [])
    (l : List AperiodicProcess) (h_fresh : ∀ p ∈ l, p.remaining = p.burst) (T : ℕ)
    (hT : (l.map (·.burst)).sum ≤ T) :
    runWait (fun as => runSteps as (stepNonPreemptive select)) (batchStream l) T =
      totalWait ((dispatchOrder select l).map (·.burst)) := by
  rw [runWait_batch_eq_waitFrom]
  -- step 0 starts from an idle CPU with the whole batch waiting
  have h0 : runSteps (batchStream l) (stepNonPreemptive select) 0 =
      stepNonPreemptive select { SchedStateMethods.init with ready := l } := rfl
  cases h_sel : select l with
  | none =>
    have h_nil := h_none l h_sel
    obtain ⟨h1, h2⟩ := stepNonPreemptive_idle select { SchedStateMethods.init with ready := l }
      rfl h_sel
    rw [h0, waitFrom_idle h_mem _ h1 (by rw [h2]; exact h_nil), h_nil]
    rfl
  | some q =>
    obtain ⟨h1, h2⟩ := stepNonPreemptive_dispatch select { SchedStateMethods.init with ready := l }
      rfl h_sel
    replace h2 : _ = l.erase q := h2
    have hq := h_mem _ _ h_sel
    have hq_fresh := h_fresh q hq
    have h_sum := sum_map_erase (·.burst) hq
    rw [h0, waitFrom_drain h_mem h_none _ q h1 (by rw [hq_fresh]; exact q.burst_exceed_zero)
      (by rw [h2]; exact fun r hr => h_fresh r (List.mem_of_mem_erase hr))
      T (by rw [h2]; omega), h2, dispatchOrder_of_select h_mem h_sel, List.map_cons,
      totalWait_cons, List.length_map,
      (dispatchOrder_perm h_mem h_none (l.erase q)).length_eq, hq_fresh]

/-! ## Shortest first, at the level of runs -/

/-- SJF's run on a batch waits `totalWait` of its dispatch order, which lists the
bursts in non-decreasing order. -/
theorem runWait_sjf_batch (l : List AperiodicProcess) (h_batch : IsBatch l) (T : ℕ)
    (hT : (l.map (·.burst)).sum ≤ T) :
    runWait (runSteps · stepSJF) (batchStream l) T =
      totalWait ((dispatchOrder selectSJF l).map (·.burst)) :=
  runWait_batch_eq_totalWait selectSJF_mem selectSJF_none_imp_empty l
    (fun p hp => (h_batch.1 p hp).2) T hT

/-- Two policies dispatch a batch in orders that are permutations of each other. -/
theorem dispatchOrder_burst_perm
    {select select' : List AperiodicProcess → Option AperiodicProcess}
    (h_mem : ∀ l p, select l = some p → p ∈ l) (h_none : ∀ l, select l = none → l = [])
    (h_mem' : ∀ l p, select' l = some p → p ∈ l) (h_none' : ∀ l, select' l = none → l = [])
    (l : List AperiodicProcess) :
    (dispatchOrder select l).map (·.burst) ~ (dispatchOrder select' l).map (·.burst) :=
  ((dispatchOrder_perm h_mem h_none l).trans (dispatchOrder_perm h_mem' h_none' l).symm).map _

/-- **SJF is optimal on a batch.** Among non-preemptive policies that never idle
while a job is waiting (`h_none`), none waits less than SJF on a batch released
at time 0, once the horizon covers the total work. -/
theorem runWait_sjf_le {select : List AperiodicProcess → Option AperiodicProcess}
    (h_mem : ∀ l p, select l = some p → p ∈ l) (h_none : ∀ l, select l = none → l = [])
    (l : List AperiodicProcess) (h_batch : IsBatch l) (T : ℕ) (hT : (l.map (·.burst)).sum ≤ T) :
    runWait (runSteps · stepSJF) (batchStream l) T ≤
      runWait (runSteps · (stepNonPreemptive select)) (batchStream l) T := by
  rw [runWait_sjf_batch l h_batch T hT,
    runWait_batch_eq_totalWait h_mem h_none l (fun p hp => (h_batch.1 p hp).2) T hT]
  exact totalWait_sorted_le
    (dispatchOrder_sorted_of_min selectSJF_mem selectSJF_none_imp_empty selectSJF_min l)
    (dispatchOrder_burst_perm selectSJF_mem selectSJF_none_imp_empty h_mem h_none l)

/-- **The batch convoy effect, measured on runs.** A non-preemptive policy has the
batch convoy effect exactly when, on some batch released at time 0, its run
waits strictly longer than SJF's, over the time it takes to finish the batch.

(→) it passes over a shorter job `q` for `p`; swapping them in its dispatch
order strictly lowers `totalWait` (`totalWait_swap_far_lt`), and SJF's sorted
order is no worse than the swapped one (`totalWait_sorted_le`).
(←) a policy that always picks a shortest job dispatches every batch in sorted
order, and the sorted permutation of a list of bursts is unique, so its run
waits exactly as long as SJF's. -/
theorem hasBatchConvoyEffect_iff_runWait (select : List AperiodicProcess → Option AperiodicProcess)
    (h_mem : ∀ l p, select l = some p → p ∈ l) (h_none : ∀ l, select l = none → l = []) :
    HasBatchConvoyEffect select ↔ ∃ l, IsBatch l ∧
      runWait (runSteps · stepSJF) (batchStream l) (l.map (·.burst)).sum <
        runWait (runSteps · (stepNonPreemptive select)) (batchStream l) (l.map (·.burst)).sum := by
  have h_sel : ∀ l, IsBatch l →
      runWait (runSteps · (stepNonPreemptive select)) (batchStream l) (l.map (·.burst)).sum =
        totalWait ((dispatchOrder select l).map (·.burst)) := fun l h_batch =>
    runWait_batch_eq_totalWait h_mem h_none l (fun p hp => (h_batch.1 p hp).2) _ le_rfl
  have h_perm := dispatchOrder_burst_perm selectSJF_mem selectSJF_none_imp_empty h_mem h_none
  have h_sjf_sorted := fun l (_ : IsBatch l) =>
    dispatchOrder_sorted_of_min selectSJF_mem selectSJF_none_imp_empty selectSJF_min l
  constructor
  · intro h
    obtain ⟨l, h_batch, p, hp, h_p, q, hq, h_lt⟩ := (hasBatchConvoyEffect_iff select).mp h
    refine ⟨l, h_batch, ?_⟩
    rw [runWait_sjf_batch l h_batch _ le_rfl, h_sel l h_batch]
    -- `q` is dispatched somewhere after `p`
    have h_ne : q ≠ p := fun h_eq => by subst h_eq; omega
    have hq' : q.burst ∈ (dispatchOrder select (l.erase p)).map (·.burst) :=
      List.mem_map_of_mem ((dispatchOrder_perm h_mem h_none _).symm.subset
        ((List.mem_erase_of_ne h_ne).mpr hq))
    obtain ⟨mid, post, h_split⟩ := List.append_of_mem hq'
    have h_order : (dispatchOrder select l).map (·.burst) = p.burst :: (mid ++ q.burst :: post) := by
      rw [dispatchOrder_of_select h_mem h_p, List.map_cons, h_split]
    rw [h_order]
    calc totalWait ((dispatchOrder selectSJF l).map (·.burst))
        ≤ totalWait (q.burst :: (mid ++ p.burst :: post)) :=
          totalWait_sorted_le (h_sjf_sorted l h_batch)
            ((h_perm l).trans (h_order ▸ perm_swap_far p.burst q.burst mid post))
      _ < totalWait (p.burst :: (mid ++ q.burst :: post)) := totalWait_swap_far_lt mid post h_lt
  · rintro ⟨l, h_batch, h_lt⟩
    by_contra h_no
    have h_short : RunsShortestProcessBatch select := Classical.not_not.mp h_no
    rw [runWait_sjf_batch l h_batch _ le_rfl, h_sel l h_batch,
      List.Perm.eq_of_pairwise (fun _ _ _ _ => Nat.le_antisymm) (h_sjf_sorted l h_batch)
        (dispatchOrder_sorted h_mem h_none h_short l h_batch) (h_perm l)] at h_lt
    exact lt_irrefl _ h_lt

/-! ## Sanity check

A batch with bursts `[5, 1, 3, 2]` (total work 11).  FCFS dispatches it in list
order and waits `totalWait [5, 1, 3, 2] = 20`; SJF dispatches `[1, 2, 3, 5]` and
waits 10.  (SRTF also waits 10 on this batch, by `#eval`; `decide` cannot
evaluate its `ℚ` priorities.) -/

/-- The sample batch: bursts 5, 1, 3, 2, ids 0..3, all at time 0. -/
def sampleBatch : List AperiodicProcess :=
  [⟨0, 0, 5, 5, by omega⟩, ⟨1, 0, 1, 1, by omega⟩, ⟨2, 0, 3, 3, by omega⟩, ⟨3, 0, 2, 2, by omega⟩]

example : runWait (runSteps · stepFCFS) (batchStream sampleBatch) 11 = 20 := by decide
example : totalWait [5, 1, 3, 2] = 20 := rfl
example : runWait (runSteps · stepSJF) (batchStream sampleBatch) 11 = 10 := by decide
example : totalWait [1, 2, 3, 5] = 10 := rfl

end ConvoyEffect
