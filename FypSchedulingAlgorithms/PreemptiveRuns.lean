/-
Copyright (c) 2026 Choo Kye Yong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Choo Kye Yong
-/
import FypSchedulingAlgorithms.AperiodicSchedulers.PreemptiveLemmas
import FypSchedulingAlgorithms.RunStepsLemmas

/-!
# Steps and runs of `stepPreemptive`, for every job type

`PreemptiveLemmas` is about one selection (`selectByPriority`).  This file is about
whole steps and runs of `stepPreemptive process_type f`, for any job type with a
`Process` instance and any priority function `f : process_type → ℤ`, so the aperiodic
(SRTF) and periodic (RMS, EDF) developments can share them.  It imports nothing from
the convoy-effect files.

* **Job conservation** (`ConservesJobs`, `stepPreemptive_conservesJobs`): a step keeps
  the jobs in the system (ready or on the CPU), with the running job ticked and dropped
  exactly when that tick finished it.  This is `ConvoyEffect.ConservesJobs` stated with
  `Process.tick` and `Process.remaining` instead of the `AperiodicProcess` record
  update; for `AperiodicProcess` the two agree by definition
  (`ConvoyEffect.conservesJobs_iff`).
* **Work conservation** (`stepPreemptive_ready_nil_of_idle`,
  `runSteps_ready_nil_of_idle`): the CPU is idle after a step only when nothing is
  ready.
* **Priority run invariant** (`stepPreemptive_running_max`,
  `runSteps_running_max`): after every step, the running job's priority is at least
  that of every ready job.  It needs **no hypothesis on `f`**: it holds after *every*
  step, whatever state the step started from, because the step's last act is to
  compare the (already ticked) running job with the best ready job, and nothing is
  ticked after that comparison.  So no induction is needed either.
* **Positivity** (`ConservesJobs.remaining_pos`, `runSteps_remaining_pos`): if every
  arriving job has work left, then so does every job in the system, for any step that
  conserves jobs.

The job type needs `[LawfulBEq α]` only where a dispatched job is erased from the
queue and the proof needs `List.erase` to remove that very job.
-/

namespace PreemptiveRuns

open scoped List
open Preemptive

variable {α : Type} [Process α]

/-! ## Job conservation -/

/-- A step **conserves jobs** if the jobs in the system after it (ready or on the CPU)
are those before it, with the running job ticked, and dropped exactly when that tick
finished it.  The step may reorder `ready` and swap the job on the CPU, but it adds and
loses nothing. -/
def ConservesJobs (step : SchedStateG α → SchedStateG α) : Prop :=
  ∀ s : SchedStateG α,
    (step s).ready ++ (step s).running.toList ~
      s.ready ++ (s.running.toList.map Process.tick).filter fun b => 0 < Process.remaining b

/-- Dispatching a member of the queue keeps the jobs in the system. -/
theorem erase_append_singleton_perm {β : Type} [BEq β] [LawfulBEq β] {l : List β} {p : β}
    (h : p ∈ l) : l.erase p ++ [p] ~ l :=
  (List.perm_append_singleton p _).trans (List.perm_cons_erase h).symm

/-- **Every preemptive scheduler conserves jobs**, whatever its priority function. -/
theorem stepPreemptive_conservesJobs [LawfulBEq α] (f : α → ℤ) :
    ConservesJobs (stepPreemptive α f) := by
  intro s
  unfold stepPreemptive
  rcases hr : s.running with _ | b
  · simp only [Option.toList_none, List.map_nil, List.filter_nil, List.append_nil]
    split
    · simp
    · rename_i p h_sel
      exact erase_append_singleton_perm (selectByPriority_spec f _ p h_sel).1
  · simp only [Option.toList_some, List.map_cons, List.map_nil]
    split_ifs with h_done
    · have h0 : ¬ (0 < Process.remaining (Process.tick b)) := by omega
      simp only [List.filter_cons, List.filter_nil, h0, decide_false, Bool.false_eq_true,
        ↓reduceIte, List.append_nil]
      split
      · simp
      · rename_i p h_sel
        exact erase_append_singleton_perm (selectByPriority_spec f _ p h_sel).1
    · have h0 : 0 < Process.remaining (Process.tick b) := by omega
      simp only [List.filter_cons, List.filter_nil, h0, decide_true, ↓reduceIte]
      split
      · simp
      · rename_i p h_sel
        split_ifs
        · simp only [Option.toList_some, List.append_assoc, List.singleton_append]
          refine ((List.Perm.swap p _ []).append_left (s.ready.erase p)).trans ?_
          rw [← List.singleton_append, ← List.append_assoc]
          exact (erase_append_singleton_perm (selectByPriority_spec f _ p h_sel).1).append_right _
        · simp

/-! ## Work conservation -/

/-- **A preemptive step leaves the CPU idle only when nothing is ready.** -/
theorem stepPreemptive_ready_nil_of_idle (f : α → ℤ) (s : SchedStateG α)
    (h : (stepPreemptive α f s).running = none) :
    (stepPreemptive α f s).ready = [] := by
  unfold stepPreemptive at *
  rcases hr : s.running with _ | b <;> simp only [hr] at h ⊢
  · cases h_sel : selectByPriority f s.ready <;> simp only [h_sel] at h ⊢
    · exact selectByPriority_eq_none f _ h_sel
    · simp at h
  · split_ifs at h ⊢ <;> cases h_sel : selectByPriority f s.ready <;> simp only [h_sel] at h ⊢
    · exact selectByPriority_eq_none f _ h_sel
    all_goals (try split_ifs at h ⊢) <;> simp at h

/-- **In a run of a preemptive scheduler the CPU is idle only when nothing is ready.** -/
theorem runSteps_ready_nil_of_idle [SchedStateMethods α] (f : α → ℤ)
    (arrival_stream : ℕ → List α) (t : ℕ)
    (h : (runSteps arrival_stream (stepPreemptive α f) t).running = none) :
    (runSteps arrival_stream (stepPreemptive α f) t).ready = [] := by
  rw [runSteps_eq_step_stateBefore] at *
  exact stepPreemptive_ready_nil_of_idle f _ h

/-! ## The priority run invariant -/

/-- **After every preemptive step, the running job has the highest priority**: its
`f`-value is at least that of every ready job.  No hypothesis on `f` and none on the
state the step starts from: the step ends by comparing the (already ticked) running job
with the best ready job, and the loser of that comparison is what stays in `ready`. -/
theorem stepPreemptive_running_max (f : α → ℤ) (s : SchedStateG α) (p : α)
    (hp : (stepPreemptive α f s).running = some p) :
    ∀ q ∈ (stepPreemptive α f s).ready, f q ≤ f p := by
  -- dispatching the best job `p` of `ready` leaves behind jobs no better than `p`
  have h_dispatch : ∀ p, selectByPriority f s.ready = some p →
      ∀ q ∈ s.ready.erase p, f q ≤ f p := fun p h_sel q hq =>
    (selectByPriority_spec f _ p h_sel).2 q (List.mem_of_mem_erase hq)
  unfold stepPreemptive at *
  rcases hr : s.running with _ | b <;> simp only [hr] at hp ⊢
  · split at hp
    · simp at hp
    · rename_i p' h_sel
      simp only [Option.some.injEq] at hp
      subst hp
      exact h_dispatch _ h_sel
  · split_ifs at hp ⊢ with h_done
    · split at hp
      · simp at hp
      · rename_i p' h_sel
        simp only [Option.some.injEq] at hp
        subst hp
        simpa [h_sel] using h_dispatch _ h_sel
    · split at hp
      · rename_i h_sel
        simp [selectByPriority_eq_none f _ h_sel]
      · rename_i q h_sel
        split_ifs at hp ⊢ with h_pre
        · -- `q` preempts: the ticked job rejoins `ready`, and it lost to `q`
          simp only [Option.some.injEq] at hp
          subst hp
          intro r hr
          rcases List.mem_append.mp hr with hr | hr
          · exact h_dispatch _ h_sel r hr
          · simp only [List.mem_singleton] at hr; subst hr; exact le_of_lt h_pre
        · -- the ticked job keeps the CPU: it is no worse than the best ready job `q`
          simp only [Option.some.injEq] at hp
          subst hp
          intro r hr
          exact le_trans ((selectByPriority_spec f _ q h_sel).2 r hr) (not_lt.mp h_pre)

/-- **Priority run invariant.** In every state of a run of `stepPreemptive α f`, the
running job's `f`-value is at least that of every ready job.  It holds for every
priority function `f`. -/
theorem runSteps_running_max [SchedStateMethods α] (f : α → ℤ)
    (arrival_stream : ℕ → List α) (t : ℕ) (p : α)
    (hp : (runSteps arrival_stream (stepPreemptive α f) t).running = some p) :
    ∀ q ∈ (runSteps arrival_stream (stepPreemptive α f) t).ready, f q ≤ f p := by
  rw [runSteps_eq_step_stateBefore] at *
  exact stepPreemptive_running_max f _ p hp

/-! ## Positivity -/

/-- **A job-conserving step keeps every job's work positive**: if every job in the
system before the step has work left, so does every job after it. -/
theorem ConservesJobs.remaining_pos {step : SchedStateG α → SchedStateG α}
    (h_step : ConservesJobs step) (s : SchedStateG α)
    (h : ∀ q ∈ s.ready ++ s.running.toList, 0 < Process.remaining q) :
    ∀ q ∈ (step s).ready ++ (step s).running.toList, 0 < Process.remaining q := by
  intro q hq
  rcases List.mem_append.mp ((h_step s).mem_iff.mp hq) with hq | hq
  · exact h q (List.mem_append_left _ hq)
  · exact of_decide_eq_true (List.mem_filter.mp hq).2

/-- **Positivity run invariant.** If every arriving job has work left (for instance,
fresh jobs with `remaining = burst > 0`), then in every state of a run of a
job-conserving step every ready or running job has work left.  The initial state must
have an idle CPU (`h_init`), as it does for both job types (`rfl`). -/
theorem runSteps_remaining_pos [SchedStateMethods α] {step : SchedStateG α → SchedStateG α}
    (h_step : ConservesJobs step)
    (h_init : (SchedStateMethods.init : SchedStateG α).running = none)
    {arrival_stream : ℕ → List α}
    (h_arr : ∀ t, ∀ q ∈ arrival_stream t, 0 < Process.remaining q) (t : ℕ) :
    ∀ q ∈ (runSteps arrival_stream step t).ready ++
        (runSteps arrival_stream step t).running.toList, 0 < Process.remaining q := by
  induction t with
  | zero =>
    apply h_step.remaining_pos
    intro q hq
    simp only [h_init, Option.toList_none, List.append_nil] at hq
    exact h_arr 0 q hq
  | succ t ih =>
    apply h_step.remaining_pos
    intro q hq
    simp only [List.mem_append] at hq ih
    rcases hq with (hq | hq) | hq
    · exact ih q (Or.inl hq)
    · exact h_arr _ q hq
    · exact ih q (Or.inr hq)

end PreemptiveRuns
