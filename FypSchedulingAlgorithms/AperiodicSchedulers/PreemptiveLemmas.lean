/-
Copyright (c) 2026 Choo Kye Yong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Choo Kye Yong
-/
import FypSchedulingAlgorithms.Step

/-!
# Scheduler-agnostic facts about `stepPreemptive`

The lemmas here hold for *every* preemptive scheduler, i.e. every scheduler of
the form `stepPreemptive process_type priority_func`: they are about
`selectByPriority`, which picks the candidate run at each step, and are stated
for an arbitrary priority function rather than for SRTF's `-remaining`
specifically.  This is the preemptive counterpart of `NonPreemptiveLemmas`.
-/

namespace Preemptive

/-- Invariant of the `foldl` inside `selectByPriority`: the result is either the
starting accumulator or one of the scanned jobs, and its priority is at least
that of the accumulator and of every scanned job. -/
theorem selectByPriority_foldl_spec {α : Type} (f : α → ℤ) (l : List α)
    (init : Option α) (p : α)
    (h : l.foldl (fun best q =>
        match best with
        | none   => some q
        | some b => if f b < f q then some q else some b) init = some p) :
    (init = some p ∨ p ∈ l) ∧ (∀ b, init = some b → f b ≤ f p) ∧ ∀ q ∈ l, f q ≤ f p := by
  induction l generalizing init with
  | nil =>
    simp only [List.foldl_nil] at h
    subst h
    exact ⟨Or.inl rfl, fun b hb => by cases hb; exact le_rfl, by simp⟩
  | cons x xs ih =>
    simp only [List.foldl_cons] at h
    obtain ⟨ih_mem, ih_acc, ih_rest⟩ := ih _ h
    cases init with
    | none =>
      have hx := ih_acc x rfl
      refine ⟨?_, by simp, ?_⟩
      · rcases ih_mem with h_eq | h_mem
        · cases h_eq; exact Or.inr (List.mem_cons_self ..)
        · exact Or.inr (List.mem_cons_of_mem _ h_mem)
      · intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · exact hx
        · exact ih_rest q hq
    | some b =>
      by_cases hlt : f b < f x
      · -- `x` is strictly better: it replaces `b`
        have hx := ih_acc x (by simp [hlt])
        refine ⟨?_, fun b' hb' => by cases hb'; exact le_trans (le_of_lt hlt) hx, ?_⟩
        · rcases ih_mem with h_eq | h_mem
          · simp only [hlt, ↓reduceIte, Option.some.injEq] at h_eq
            subst h_eq; exact Or.inr (List.mem_cons_self ..)
          · exact Or.inr (List.mem_cons_of_mem _ h_mem)
        · intro q hq
          rcases List.mem_cons.mp hq with rfl | hq
          · exact hx
          · exact ih_rest q hq
      · -- `b` is at least as good: it stays
        have hb := ih_acc b (by simp [hlt])
        refine ⟨?_, fun b' hb' => by cases hb'; exact hb, ?_⟩
        · rcases ih_mem with h_eq | h_mem
          · simp only [hlt, ↓reduceIte] at h_eq; exact Or.inl h_eq
          · exact Or.inr (List.mem_cons_of_mem _ h_mem)
        · intro q hq
          rcases List.mem_cons.mp hq with rfl | hq
          · exact le_trans (not_lt.mp hlt) hb
          · exact ih_rest q hq

/-- **Every preemptive scheduler runs a highest-priority candidate.** The job
`selectByPriority` returns is one of the candidates, and no candidate has
strictly higher priority. -/
theorem selectByPriority_spec {α : Type} (f : α → ℤ) (l : List α) (p : α)
    (h : selectByPriority f l = some p) : p ∈ l ∧ ∀ q ∈ l, f q ≤ f p := by
  obtain ⟨h_mem, -, h_max⟩ := selectByPriority_foldl_spec f l none p h
  exact ⟨h_mem.resolve_left (by simp), h_max⟩

/-- `selectByPriority` comes back empty-handed only when there are no
candidates: once it has seen one job it always holds some best-so-far. -/
theorem selectByPriority_eq_none {α : Type} (f : α → ℤ) (l : List α)
    (h : selectByPriority f l = none) : l = [] := by
  cases l with
  | nil => rfl
  | cons x xs =>
    exfalso
    have key : ∀ (ys : List α) (b : α), ys.foldl (fun best q =>
        match best with
        | none   => some q
        | some b => if f b < f q then some q else some b) (some b) ≠ none := by
      intro ys
      induction ys with
      | nil => simp
      | cons y ys ih =>
        intro b
        simp only [List.foldl_cons]
        split_ifs <;> exact ih _
    exact key xs x h

/-- **Ties go to the earlier candidate.** Selecting from `l ++ [b]` returns the
best job `q` of `l` unless `b` has strictly higher priority.  Not used by `stepPreemptive`,
which compares the running job with the winner of `ready` explicitly. -/
theorem selectByPriority_append_singleton {α : Type} (f : α → ℤ) (l : List α) (b : α) :
    selectByPriority f (l ++ [b]) =
      match selectByPriority f l with
      | none   => some b
      | some q => if f q < f b then some b else some q := by
  unfold selectByPriority
  rw [List.foldl_append]
  rfl

/-- One scan step from the front: `x` replaces `b` as best-so-far only if it has
strictly higher priority. -/
theorem selectByPriority_cons_cons {α : Type} (f : α → ℤ) (b x : α) (xs : List α) :
    selectByPriority f (b :: x :: xs) =
      if f b < f x then selectByPriority f (x :: xs) else selectByPriority f (b :: xs) := by
  unfold selectByPriority
  simp only [List.foldl_cons]
  split_ifs <;> rfl

/-- **The running job wins ties.** Selecting from `b :: l` (the running job `b`
scanned first, then the ready queue `l`) returns `b` unless the best job of `l`
has strictly higher priority.  This is how `stepPreemptive` decides whether to
preempt the running job `b`. -/
theorem selectByPriority_cons {α : Type} (f : α → ℤ) (l : List α) (b : α) :
    selectByPriority f (b :: l) =
      match selectByPriority f l with
      | none   => some b
      | some q => if f b < f q then some q else some b := by
  induction l generalizing b with
  | nil => rfl
  | cons x xs ih =>
    rw [selectByPriority_cons_cons, ih x, ih b]
    cases selectByPriority f xs with
    | none => rfl
    | some q =>
      simp only
      by_cases hbx : f b < f x <;> by_cases hxq : f x < f q <;> by_cases hbq : f b < f q <;>
        simp only [hbx, hxq, hbq, ↓reduceIte] <;>
        first
        | exact absurd (lt_trans hbx hxq) hbq
        | exact absurd (lt_of_lt_of_le hbq (not_lt.mp hxq)) hbx

end Preemptive
