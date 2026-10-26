/-
Copyright (c) 2026 Choo Kye Yong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Choo Kye Yong
-/
import FypSchedulingAlgorithms.PeriodicSchedulers.PeriodicSchedules

/-!
# Runs repeat with the hyperperiod

If every period divides `H`, the releases repeat every `H` steps, shifted in time
(`releasesAt_add`).  A preemptive scheduler whose priority order is unchanged when every
release time is shifted by `H` (`EDF` and every fixed priority) then repeats its run too,
provided its first `H` steps end with nothing in the system: the run from step `H` on is
the run from step 0 with every release time shifted by `H` (`runSteps_shiftRel`).  So a
run that lists no missed deadline in its first `H` steps lists none ever
(`missedDeadlines_eq_nil_of_hyperperiod`).  This turns a finite check into an all-time
statement.

The comparison ignores `completed`, which keeps growing; the miss check does not look at
it.
-/

namespace Periodic

open PreemptiveRuns

/-- Job `p` released `H` steps later. -/
def shiftJob (H : ℕ) (p : PeriodicProcess) : PeriodicProcess :=
  { p with arrival := p.arrival + H }

@[simp] theorem shiftJob_arrival (H : ℕ) (p : PeriodicProcess) :
    (shiftJob H p).arrival = p.arrival + H := rfl

@[simp] theorem shiftJob_deadline (H : ℕ) (p : PeriodicProcess) :
    (shiftJob H p).deadline = p.deadline := rfl

theorem shiftJob_injective (H : ℕ) : Function.Injective (shiftJob H) := by
  rintro ⟨_, _, _, _, _, _, _⟩ ⟨_, _, _, _, _, _, _⟩ h
  simp only [shiftJob, PeriodicProcess.mk.injEq] at h
  obtain ⟨rfl, h_arr, rfl, rfl, rfl, rfl⟩ := h
  simp only [PeriodicProcess.mk.injEq, true_and, and_true]
  omega

/-- **Releases repeat with the hyperperiod.** -/
theorem releasesAt_add {tasks : List PeriodicProcess} {H : ℕ}
    (h_div : ∀ τ ∈ tasks, τ.period ∣ H) (t : ℕ) :
    PeriodicProcess.releasesAt tasks (t + H) =
      (PeriodicProcess.releasesAt tasks t).map (shiftJob H) := by
  unfold PeriodicProcess.releasesAt
  rw [List.map_map]
  congr 1
  refine List.filter_congr fun τ hτ => ?_
  obtain ⟨c, hc⟩ := h_div τ hτ
  rw [hc, Nat.add_mul_mod_self_left]

/-- Selection commutes with a map that keeps the priority order. -/
theorem selectByPriority_map {α : Type} (f : α → ℤ) (g : α → α)
    (h : ∀ p q, f (g p) < f (g q) ↔ f p < f q) (l : List α) :
    selectByPriority f (l.map g) = (selectByPriority f l).map g := by
  unfold selectByPriority
  suffices ∀ init : Option α, (l.map g).foldl (fun best p =>
      match best with
      | none   => some p
      | some b => if f b < f p then some p else some b) (init.map g) =
      (l.foldl (fun best p =>
      match best with
      | none   => some p
      | some b => if f b < f p then some p else some b) init).map g from this none
  induction l with
  | nil => intro init; rfl
  | cons x xs ih =>
    intro init
    rw [List.map_cons, List.foldl_cons, List.foldl_cons, ← ih]
    congr 1
    cases init with
    | none => rfl
    | some b =>
      simp only [Option.map_some, h]
      split <;> rfl

/-- Erasing a shifted job from the shifted list. -/
theorem erase_map_shiftJob (H : ℕ) (l : List PeriodicProcess) (p : PeriodicProcess) :
    (l.map (shiftJob H)).erase (shiftJob H p) = (l.erase p).map (shiftJob H) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    by_cases hx : x = p
    · subst hx
      simp
    · have hx' : shiftJob H x ≠ shiftJob H p := (shiftJob_injective H).ne hx
      simp [hx, hx', ih]

/-- State `s'` is state `s` shifted `H` steps later (up to `completed`). -/
def ShiftRel (H : ℕ) (s s' : PeriodicSchedState) : Prop :=
  s'.ready = s.ready.map (shiftJob H) ∧ s'.running = s.running.map (shiftJob H) ∧
    s'.time = s.time + H

/-- **A preemptive step keeps the shift**, for a priority whose order is unchanged by
shifting release times. -/
theorem stepPreemptive_shiftRel (f : PeriodicProcess → ℤ) {H : ℕ}
    (h_f : ∀ p q, f (shiftJob H p) < f (shiftJob H q) ↔ f p < f q)
    {s s' : PeriodicSchedState} (h : ShiftRel H s s') :
    ShiftRel H (stepPreemptive PeriodicProcess f s) (stepPreemptive PeriodicProcess f s') := by
  obtain ⟨hr, hrun, ht⟩ := h
  unfold stepPreemptive
  rw [hrun, hr, selectByPriority_map f _ h_f]
  rcases hs : s.running with _ | b
  · cases hsel : selectByPriority f s.ready with
    | none => simp [ShiftRel, ht]; omega
    | some p => simp [ShiftRel, ht, erase_map_shiftJob]; omega
  · have h_tick : Process.tick (shiftJob H b) = shiftJob H (Process.tick b) := rfl
    have h_rem : Process.remaining (shiftJob H (Process.tick b)) =
        Process.remaining (Process.tick b) := rfl
    simp only [Option.map_some, h_tick, h_rem]
    split_ifs with h_done
    · cases hsel : selectByPriority f s.ready with
      | none => simp [ShiftRel, ht]; omega
      | some p => simp [ShiftRel, ht, erase_map_shiftJob]; omega
    · cases hsel : selectByPriority f s.ready with
      | none => simp [ShiftRel, ht]; omega
      | some q =>
        simp only [Option.map_some, h_f]
        split_ifs
        · simp [ShiftRel, ht, erase_map_shiftJob]; omega
        · simp [ShiftRel, ht]; omega

/-- The miss check does not see a shift. -/
theorem missedDeadlines_eq_nil_iff_of_shiftRel {H : ℕ} {s s' : PeriodicSchedState}
    (h : ShiftRel H s s') :
    PeriodicProcess.missedDeadlines s' = [] ↔ PeriodicProcess.missedDeadlines s = [] := by
  obtain ⟨hr, hrun, ht⟩ := h
  unfold PeriodicProcess.missedDeadlines
  rw [hr, hrun, ht]
  simp only [List.filter_eq_nil_iff, List.mem_append, List.mem_map, Option.mem_toList,
    Option.map_eq_some_iff, decide_eq_true_eq]
  constructor
  · intro h' p hp
    rcases hp with hp | hp
    · have := h' _ (Or.inl ⟨p, hp, rfl⟩)
      simp only [shiftJob_arrival, shiftJob_deadline] at this
      omega
    · have := h' _ (Or.inr ⟨p, hp, rfl⟩)
      simp only [shiftJob_arrival, shiftJob_deadline] at this
      omega
  · rintro h' _ (⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩)
    · have := h' p (Or.inl hp)
      simp only [shiftJob_arrival, shiftJob_deadline]
      omega
    · have := h' p (Or.inr hp)
      simp only [shiftJob_arrival, shiftJob_deadline]
      omega

section Run

variable (f : PeriodicProcess → ℤ) {tasks : List PeriodicProcess} {n : ℕ}
  (h_f : ∀ p q, f (shiftJob (n + 1) p) < f (shiftJob (n + 1) q) ↔ f p < f q)
  (h_div : ∀ τ ∈ tasks, τ.period ∣ n + 1)
  (h_idle : (runSteps (PeriodicProcess.releasesAt tasks)
    (stepPreemptive PeriodicProcess f) n).running = none)
  (h_empty : (runSteps (PeriodicProcess.releasesAt tasks)
    (stepPreemptive PeriodicProcess f) n).ready = [])
include h_f h_div h_idle h_empty

/-- **The run repeats with the hyperperiod `H = n + 1`**: if the state after step `n` is
empty, the state after step `H + k` is the state after step `k` shifted by `H`. -/
theorem runSteps_shiftRel (k : ℕ) :
    ShiftRel (n + 1)
      (runSteps (PeriodicProcess.releasesAt tasks) (stepPreemptive PeriodicProcess f) k)
      (runSteps (PeriodicProcess.releasesAt tasks) (stepPreemptive PeriodicProcess f)
        (n + 1 + k)) := by
  induction k with
  | zero =>
    apply stepPreemptive_shiftRel f h_f
    refine ⟨?_, ?_, ?_⟩
    · simp only [h_empty, List.nil_append]
      rw [← releasesAt_add h_div 0, Nat.zero_add]
    · simp [h_idle]
    · simp [runSteps_stepPreemptive_time f rfl]
  | succ k ih =>
    have e1 : runSteps (PeriodicProcess.releasesAt tasks) (stepPreemptive PeriodicProcess f)
        (n + 1 + (k + 1)) = stepPreemptive PeriodicProcess f
          { runSteps (PeriodicProcess.releasesAt tasks) (stepPreemptive PeriodicProcess f)
              (n + 1 + k) with
            ready := (runSteps (PeriodicProcess.releasesAt tasks)
              (stepPreemptive PeriodicProcess f) (n + 1 + k)).ready ++
              PeriodicProcess.releasesAt tasks (n + 1 + k + 1) } := rfl
    have e2 : runSteps (PeriodicProcess.releasesAt tasks) (stepPreemptive PeriodicProcess f)
        (k + 1) = stepPreemptive PeriodicProcess f
          { runSteps (PeriodicProcess.releasesAt tasks) (stepPreemptive PeriodicProcess f) k with
            ready := (runSteps (PeriodicProcess.releasesAt tasks)
              (stepPreemptive PeriodicProcess f) k).ready ++
              PeriodicProcess.releasesAt tasks (k + 1) } := rfl
    rw [e1, e2]
    apply stepPreemptive_shiftRel f h_f
    obtain ⟨hr, hrun, ht⟩ := ih
    refine ⟨?_, hrun, ht⟩
    rw [hr, List.map_append, show n + 1 + k + 1 = k + 1 + (n + 1) by omega,
      releasesAt_add h_div]

/-- **A finite check over one hyperperiod is an all-time check.**  If the run of
`stepPreemptive f` lists no missed deadline in its first `H = n + 1` steps and ends them
with nothing in the system, it never lists a missed deadline. -/
theorem missedDeadlines_eq_nil_of_hyperperiod
    (h_ok : ∀ t < n + 1, PeriodicProcess.missedDeadlines
      (runSteps (PeriodicProcess.releasesAt tasks) (stepPreemptive PeriodicProcess f) t) = [])
    (t : ℕ) :
    PeriodicProcess.missedDeadlines
      (runSteps (PeriodicProcess.releasesAt tasks) (stepPreemptive PeriodicProcess f) t) = [] := by
  induction t using Nat.strong_induction_on with
  | _ t ih =>
  by_cases ht : t < n + 1
  · exact h_ok t ht
  obtain ⟨k, rfl⟩ : ∃ k, t = n + 1 + k := ⟨t - (n + 1), by omega⟩
  exact (missedDeadlines_eq_nil_iff_of_shiftRel
    (runSteps_shiftRel f h_f h_div h_idle h_empty k)).mpr (ih k (by omega))

end Run

/-- EDF's priority order is unchanged by shifting every release time. -/
theorem edf_shift_order (H : ℕ) (p q : PeriodicProcess) :
    (fun p : PeriodicProcess => -((p.arrival + p.deadline : ℕ) : ℤ)) (shiftJob H p) <
        (fun p : PeriodicProcess => -((p.arrival + p.deadline : ℕ) : ℤ)) (shiftJob H q) ↔
      (fun p : PeriodicProcess => -((p.arrival + p.deadline : ℕ) : ℤ)) p <
        (fun p : PeriodicProcess => -((p.arrival + p.deadline : ℕ) : ℤ)) q := by
  simp only [shiftJob]
  omega

end Periodic
