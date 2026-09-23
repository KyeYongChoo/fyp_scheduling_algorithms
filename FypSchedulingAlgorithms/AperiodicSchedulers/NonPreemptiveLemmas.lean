/-
Copyright (c) 2026 Choo Kye Yong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Choo Kye Yong
-/
import FypSchedulingAlgorithms.Process
import FypSchedulingAlgorithms.SchedState
import FypSchedulingAlgorithms.Step
import FypSchedulingAlgorithms.SchedStateSimpLemmas

/-!
# Scheduler-agnostic facts about `stepNonPreemptive`

The lemmas here hold for *every* non-preemptive scheduler, i.e. every scheduler
of the form `stepNonPreemptive select`, so they are stated for an arbitrary
`select` rather than for `selectFCFS`/`selectSJF` specifically.

The only thing the proofs need to know about `select` is that it idles only when
there is genuinely nothing to pick:

  `h_select_none_imp_empty : ∀ l, select l = none → l = []`

which is the `mp` direction of the usual `select_none_iff_empty` lemma.  Any
`select` that returns a candidate whenever one exists satisfies it — in
particular `selectFCFS` and `selectSJF`.  Schedulers that are *not* of this
shape (notably `stepRR`, which carries a quantum counter in `RRState` and so is
built independently of `stepNonPreemptive`) need their own copies; see
`RRStarvationFree`.
-/

namespace NonPreemptive

/-- If a non-preemptive scheduler has nothing running at time `t`, the ready
queue must be empty too: otherwise `select` would have picked something to run.

This is the scheduler-agnostic form of `FCFSStarvation.idle_implies_empty_ready`. -/
theorem idle_implies_empty_ready
  (select : List AperiodicProcess → Option AperiodicProcess)
  (h_select_none_imp_empty : ∀ l, select l = none → l = [])
  (arrival_stream : ℕ → List AperiodicProcess)
  (t : ℕ)
  (h_running : (runSteps arrival_stream (stepNonPreemptive select) t).running = none) :
  (runSteps arrival_stream (stepNonPreemptive select) t).ready = [] := by
  induction t with
  | zero =>
    simp only [runSteps, stepNonPreemptive] at h_running ⊢
    -- after unfolding, running = none means select returned none
    -- h_select_none_imp_empty then gives ready = []
    simp only [SchedStateG.init_aperiodic] at h_running ⊢
    split at h_running
    · rename_i h_select
      exact h_select_none_imp_empty _ h_select
    · simp at h_running
  | succ t ih =>
    simp only [runSteps, stepNonPreemptive] at h_running ⊢
    split at h_running
    · -- prev.running = none, so select was called on ready
      rename_i h_prev_none
      split at h_running
      · -- select returned none → ready = []
        simp only [List.append_eq_nil_iff] at h_running ⊢
        apply And.intro
        · exact ih h_running
        · rename_i step_concat_arrivals_eq_none
          have h_ready_empty := ih h_running
          rw [h_ready_empty, List.nil_append] at step_concat_arrivals_eq_none
          exact h_select_none_imp_empty _ step_concat_arrivals_eq_none
      · -- select returned some p → running = some p, contradicts h_running
        contradiction
    · -- prev.running = some p, process ticked
      split at h_running
      · -- remaining ≤ 0, process completed, next select called
        rename_i h_remaining_after_tick_zero
        split at h_running
        · simp only [h_remaining_after_tick_zero, ↓reduceIte]
          rename_i h_none_after_1_step
          exact h_select_none_imp_empty _ h_none_after_1_step
        · contradiction
      · -- remaining > 0, running = some p, contradicts h_running = none
        contradiction

/-- Contrapositive of `idle_implies_empty_ready`: a nonempty ready queue at
time `t` means some process must be running at time `t`.

This is the scheduler-agnostic form of
`FCFSStarvation.ready_nonempty_implies_running_nonempty`. -/
theorem ready_nonempty_implies_running_nonempty
  (select : List AperiodicProcess → Option AperiodicProcess)
  (h_select_none_imp_empty : ∀ l, select l = none → l = [])
  (arrival_stream : ℕ → List AperiodicProcess)
  (t : ℕ)
  (h_ready_nonempty : (runSteps arrival_stream (stepNonPreemptive select) t).ready ≠ []) :
  ∃ p_running : AperiodicProcess,
    (runSteps arrival_stream (stepNonPreemptive select) t).running = some p_running := by
  cases h : (runSteps arrival_stream (stepNonPreemptive select) t).running with
  | none =>
    exfalso
    have := idle_implies_empty_ready select h_select_none_imp_empty arrival_stream t h
    tauto
  | some p => exact ⟨p, rfl⟩

end NonPreemptive
