/-
Copyright (c) 2026 Choo Kye Yong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Choo Kye Yong
-/
import FypSchedulingAlgorithms.Process
import FypSchedulingAlgorithms.SchedState
import FypSchedulingAlgorithms.Step
import FypSchedulingAlgorithms.SchedStateSimpLemmas
import FypSchedulingAlgorithms.ProcessSimpLemmas

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

The one-step lemmas at the end are stated once for `stepNonPreemptiveOnline`,
whose policy may look at the whole state and may idle on purpose, and then
transferred to `stepNonPreemptive` through `stepNonPreemptive_eq_online`.
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

/-! ## One non-preemptive step -/

section Steps

variable (select : SchedState → Option AperiodicProcess) (s : SchedState)

/-- A running job with more than one tick left is ticked and keeps the CPU. -/
theorem stepNonPreemptiveOnline_tick {p : AperiodicProcess} (h_run : s.running = some p)
    (h_left : 1 < p.remaining) :
    (stepNonPreemptiveOnline select s).running = some { p with remaining := p.remaining - 1 } ∧
      (stepNonPreemptiveOnline select s).ready = s.ready := by
  simp [stepNonPreemptiveOnline, h_run, show ¬ p.remaining - 1 = 0 by omega]

/-- A running job on its last tick completes, and the choice of `select` is
dispatched, unticked. -/
theorem stepNonPreemptiveOnline_complete_dispatch {p q : AperiodicProcess}
    (h_run : s.running = some p) (h_done : p.remaining ≤ 1) (h_sel : select s = some q) :
    (stepNonPreemptiveOnline select s).running = some q ∧
      (stepNonPreemptiveOnline select s).ready = s.ready.erase q := by
  simp [stepNonPreemptiveOnline, h_run, h_sel, show p.remaining - 1 = 0 by omega]

/-- A running job on its last tick completes; with nothing chosen the CPU goes
idle. -/
theorem stepNonPreemptiveOnline_complete_idle {p : AperiodicProcess}
    (h_run : s.running = some p) (h_done : p.remaining ≤ 1) (h_sel : select s = none) :
    (stepNonPreemptiveOnline select s).running = none ∧
      (stepNonPreemptiveOnline select s).ready = s.ready := by
  simp [stepNonPreemptiveOnline, h_run, h_sel, show p.remaining - 1 = 0 by omega]

/-- An idle CPU takes the choice of `select`, unticked. -/
theorem stepNonPreemptiveOnline_dispatch {q : AperiodicProcess}
    (h_run : s.running = none) (h_sel : select s = some q) :
    (stepNonPreemptiveOnline select s).running = some q ∧
      (stepNonPreemptiveOnline select s).ready = s.ready.erase q := by
  simp [stepNonPreemptiveOnline, h_run, h_sel]

/-- An idle CPU with nothing chosen stays idle. -/
theorem stepNonPreemptiveOnline_idle (h_run : s.running = none) (h_sel : select s = none) :
    (stepNonPreemptiveOnline select s).running = none ∧
      (stepNonPreemptiveOnline select s).ready = s.ready := by
  simp [stepNonPreemptiveOnline, h_run, h_sel]

/-- Every step advances the clock by one. -/
theorem stepNonPreemptiveOnline_time : (stepNonPreemptiveOnline select s).time = s.time + 1 := by
  unfold stepNonPreemptiveOnline
  cases s.running <;> cases select s <;> dsimp only <;> (try split_ifs) <;> rfl

/-- A step never adds jobs to the ready queue: it only removes the one it
dispatches. -/
theorem stepNonPreemptiveOnline_ready_subset :
    ∀ q ∈ (stepNonPreemptiveOnline select s).ready, q ∈ s.ready := by
  unfold stepNonPreemptiveOnline
  cases s.running <;> cases select s <;> dsimp only <;> (try split_ifs) <;>
    first
    | exact fun q hq => hq
    | exact fun q hq => List.mem_of_mem_erase hq

/-- **What a dispatch looks like.** If after a step the CPU holds `p`, and `p`
was not the job on the CPU before the step, then `p` was the choice of `select`
and was taken out of the ready queue.  (A job that keeps the CPU keeps its id.) -/
theorem stepNonPreemptiveOnline_dispatch_cases {p : AperiodicProcess}
    (h_run : (stepNonPreemptiveOnline select s).running = some p)
    (h_new : s.running.map (·.id) ≠ some p.id) :
    select s = some p ∧ (stepNonPreemptiveOnline select s).ready = s.ready.erase p := by
  unfold stepNonPreemptiveOnline at h_run ⊢
  cases h : s.running with
  | none =>
    rw [h] at h_run
    cases hs : select s with
    | none => rw [hs] at h_run; simp at h_run
    | some q =>
      rw [hs] at h_run
      simp only [Option.some.injEq] at h_run
      subst h_run
      simp
  | some r =>
    rw [h] at h_run
    by_cases hd : Process.remaining (Process.tick r) ≤ 0
    · simp only [hd, ↓reduceIte] at h_run ⊢
      cases hs : select s with
      | none => rw [hs] at h_run; simp at h_run
      | some q =>
        rw [hs] at h_run
        simp only [Option.some.injEq] at h_run
        subst h_run
        simp
    · -- the running job keeps the CPU, so `p` is not new
      simp only [hd, ↓reduceIte, Option.some.injEq] at h_run
      subst h_run
      simp [h] at h_new

end Steps

/-! The same lemmas for `stepNonPreemptive`. -/

section StepsList

variable (sel : List AperiodicProcess → Option AperiodicProcess) (s : SchedState)

/-- A running job with more than one tick left is ticked and keeps the CPU. -/
theorem stepNonPreemptive_tick {p : AperiodicProcess} (h_run : s.running = some p)
    (h_left : 1 < p.remaining) :
    (stepNonPreemptive sel s).running = some { p with remaining := p.remaining - 1 } ∧
      (stepNonPreemptive sel s).ready = s.ready := by
  rw [stepNonPreemptive_eq_online]
  exact stepNonPreemptiveOnline_tick _ s h_run h_left

/-- A running job on its last tick completes, and the choice of `sel` is
dispatched, unticked. -/
theorem stepNonPreemptive_complete_dispatch {p q : AperiodicProcess}
    (h_run : s.running = some p) (h_done : p.remaining ≤ 1) (h_sel : sel s.ready = some q) :
    (stepNonPreemptive sel s).running = some q ∧
      (stepNonPreemptive sel s).ready = s.ready.erase q := by
  rw [stepNonPreemptive_eq_online]
  exact stepNonPreemptiveOnline_complete_dispatch _ s h_run h_done h_sel

/-- A running job on its last tick completes; with nothing chosen the CPU goes
idle. -/
theorem stepNonPreemptive_complete_idle {p : AperiodicProcess}
    (h_run : s.running = some p) (h_done : p.remaining ≤ 1) (h_sel : sel s.ready = none) :
    (stepNonPreemptive sel s).running = none ∧
      (stepNonPreemptive sel s).ready = s.ready := by
  rw [stepNonPreemptive_eq_online]
  exact stepNonPreemptiveOnline_complete_idle _ s h_run h_done h_sel

/-- An idle CPU takes the choice of `sel`, unticked. -/
theorem stepNonPreemptive_dispatch {q : AperiodicProcess}
    (h_run : s.running = none) (h_sel : sel s.ready = some q) :
    (stepNonPreemptive sel s).running = some q ∧
      (stepNonPreemptive sel s).ready = s.ready.erase q := by
  rw [stepNonPreemptive_eq_online]
  exact stepNonPreemptiveOnline_dispatch _ s h_run h_sel

/-- An idle CPU with nothing chosen stays idle. -/
theorem stepNonPreemptive_idle (h_run : s.running = none) (h_sel : sel s.ready = none) :
    (stepNonPreemptive sel s).running = none ∧
      (stepNonPreemptive sel s).ready = s.ready := by
  rw [stepNonPreemptive_eq_online]
  exact stepNonPreemptiveOnline_idle _ s h_run h_sel

end StepsList

end NonPreemptive
