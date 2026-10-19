/-
Copyright (c) 2026 Choo Kye Yong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Choo Kye Yong
-/
import FypSchedulingAlgorithms.Step

/-!
# General facts about `runSteps`

Facts about `runSteps` (`Step`) that hold for every scheduler `step`: they only
unfold `runSteps`, so most are stated for any `SchedStateG process_type`.

* **Runs with no arrivals for a while.** When nothing arrives at time `t + 1`,
  run step `t + 1` is one `step` (`runSteps_succ_of_nil`); when nothing arrives
  in `(t, t + k]`, the run from `t` on is `step` iterated
  (`runSteps_add_eq_iterate`).
* **The instance known at time `t`.** `knownAt as t` keeps the arrivals of `as`
  up to time `t` and drops the later ones.  A run cannot see the future, so up
  to step `t` it is the same on `as` and on `knownAt as t` (`runSteps_knownAt`).
  The known instance of a well-formed stream is well formed (`knownAt_wf`).
* **The state a step starts from.** `stateBefore as step t` is the state step `t`
  of the run is applied to: the previous state with the arrivals of time `t`
  added.  Each run step is one `step` from it (`runSteps_eq_step_stateBefore`),
  and two runs that agree before `t` start step `t` from the same state
  (`stateBefore_congr`).
-/

/-! ## Runs with no arrivals for a while -/

/-- When nothing arrives at time `t + 1`, run step `t + 1` is just one `step`. -/
theorem runSteps_succ_of_nil {process_type : Type} [SchedStateMethods process_type]
    (step : SchedStateG process_type → SchedStateG process_type)
    (arrival_stream : ℕ → List process_type) (t : ℕ) (h : arrival_stream (t + 1) = []) :
    runSteps arrival_stream step (t + 1) = step (runSteps arrival_stream step t) := by
  simp [runSteps, h]

/-- When nothing arrives in `(t, t + k]`, the run from time `t` on is `step`
iterated. -/
theorem runSteps_add_eq_iterate {process_type : Type} [SchedStateMethods process_type]
    (step : SchedStateG process_type → SchedStateG process_type)
    (arrival_stream : ℕ → List process_type) (t k : ℕ)
    (h : ∀ j, t < j → j ≤ t + k → arrival_stream j = []) :
    runSteps arrival_stream step (t + k) = step^[k] (runSteps arrival_stream step t) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [← Nat.add_assoc, runSteps_succ_of_nil _ _ _ (h _ (by omega) (by omega)),
      ih (fun j h1 h2 => h j h1 (by omega)), Function.iterate_succ_apply']

/-! ## The instance known at time `t` -/

/-- **The instance known at time `t`**: the arrivals of `arrival_stream` up to
time `t`, and nothing afterwards. -/
def knownAt {process_type : Type} (arrival_stream : ℕ → List process_type) (t : ℕ) :
    ℕ → List process_type :=
  fun t' => if t' ≤ t then arrival_stream t' else []

/-- Nothing is known to arrive after time `t`. -/
theorem knownAt_of_lt {process_type : Type} (arrival_stream : ℕ → List process_type) {t j : ℕ}
    (h : t < j) : knownAt arrival_stream t j = [] := by
  simp [knownAt, show ¬ j ≤ t by omega]

/-- The known instance of a well-formed stream is well formed. -/
theorem knownAt_wf {arrival_stream : ℕ → List AperiodicProcess}
    (h_wf : WellFormedStream arrival_stream) (t : ℕ) :
    WellFormedStream (knownAt arrival_stream t) := by
  have h_mem : ∀ p j, p ∈ knownAt arrival_stream t j → p ∈ arrival_stream j := fun p j hp => by
    unfold knownAt at hp
    split at hp
    · exact hp
    · simp at hp
  exact ⟨fun p j hp => h_wf.consistent p j (h_mem p j hp),
    fun p j hp => h_wf.fresh p j (h_mem p j hp),
    fun p1 p2 t1 t2 h1 h2 h_id => h_wf.unique p1 p2 t1 t2 (h_mem _ _ h1) (h_mem _ _ h2) h_id⟩

/-- **A run cannot see the future**: up to time `t` it is the same on the
stream and on the instance known at `t`. -/
theorem runSteps_knownAt {process_type : Type} [SchedStateMethods process_type]
    (arrival_stream : ℕ → List process_type)
    (step : SchedStateG process_type → SchedStateG process_type) {t t' : ℕ} (h : t' ≤ t) :
    runSteps (knownAt arrival_stream t) step t' = runSteps arrival_stream step t' := by
  induction t' with
  | zero => simp [runSteps, knownAt]
  | succ k ih =>
    simp only [runSteps]
    rw [ih (by omega)]
    simp [knownAt, h]

/-! ## The state a step starts from -/

/-- The state step `t` of a run starts from: the state after step `t - 1` (or
the initial state) with the arrivals of time `t` added to `ready`.  This is
the state on which the scheduler makes its decision at time `t`. -/
def stateBefore {process_type : Type} [SchedStateMethods process_type]
    (arrival_stream : ℕ → List process_type)
    (step : SchedStateG process_type → SchedStateG process_type) :
    ℕ → SchedStateG process_type
  | 0 => { SchedStateMethods.init with ready := arrival_stream 0 }
  | t + 1 => { runSteps arrival_stream step t with
      ready := (runSteps arrival_stream step t).ready ++ arrival_stream (t + 1) }

/-- Each run step is one `step` from the state it starts from. -/
theorem runSteps_eq_step_stateBefore {process_type : Type} [SchedStateMethods process_type]
    (arrival_stream : ℕ → List process_type)
    (step : SchedStateG process_type → SchedStateG process_type) (t : ℕ) :
    runSteps arrival_stream step t = step (stateBefore arrival_stream step t) := by
  cases t <;> rfl

/-- Two runs that agree before time `t` start step `t` from the same state. -/
theorem stateBefore_congr {process_type : Type} [SchedStateMethods process_type]
    (arrival_stream : ℕ → List process_type)
    {step step' : SchedStateG process_type → SchedStateG process_type} {t : ℕ}
    (h : ∀ k < t, runSteps arrival_stream step k = runSteps arrival_stream step' k) :
    stateBefore arrival_stream step t = stateBefore arrival_stream step' t := by
  cases t with
  | zero => rfl
  | succ k => simp only [stateBefore, h k (by omega)]
