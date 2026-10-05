/-
Copyright (c) 2026 Choo Kye Yong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Choo Kye Yong
-/
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Total waiting time of a batch, and the exchange lemmas

The *cost* side of the convoy effect, stated purely on lists of bursts.  For a
batch run back-to-back, swapping two jobs changes total waiting time by exactly
the difference of their bursts (times their distance apart), so a longer job
ahead of a shorter one is always strictly worse than the swapped order.

`ConvoySpec` uses `totalWait_swap_far_lt` to justify the definition of
`HasConvoyEffect`.
-/

namespace ConvoyEffect

/-- Total waiting time of a batch of jobs, all available at time 0, run
back-to-back in list order (given by their bursts).  Each job waits for the sum
of the bursts ahead of it, so each burst is paid once per job behind it. -/
def totalWait : List ℕ → ℕ
  | []      => 0
  | b :: bs => b * bs.length + totalWait bs

@[simp] theorem totalWait_nil : totalWait [] = 0 := rfl

@[simp] theorem totalWait_cons (b : ℕ) (bs : List ℕ) :
    totalWait (b :: bs) = b * bs.length + totalWait bs := rfl

/-- **Exchange lemma.** Swapping two adjacent jobs changes total waiting time by
exactly the difference of their bursts.  Stated additively to avoid truncated
subtraction on `ℕ`: running `b` before `a` saves `a` and costs `b`. -/
theorem totalWait_swap (pre post : List ℕ) (a b : ℕ) :
    totalWait (pre ++ b :: a :: post) + a = totalWait (pre ++ a :: b :: post) + b := by
  induction pre with
  | nil => simp only [List.nil_append, totalWait_cons, List.length_cons]; ring
  | cons x pre ih =>
    simp only [List.cons_append, totalWait_cons, List.length_append, List.length_cons]
    linarith

/-- Running a longer job `a` directly ahead of a strictly shorter job `b` is
strictly worse than the swapped order. -/
theorem totalWait_swap_lt (pre post : List ℕ) {a b : ℕ} (h : b < a) :
    totalWait (pre ++ b :: a :: post) < totalWait (pre ++ a :: b :: post) := by
  have := totalWait_swap pre post a b
  omega

/-- Inserting `x` before `post` adds one waiter behind each job of `mid`
(costing `mid.sum`) and makes `x` wait-for by each job of `post`. -/
theorem totalWait_append_cons (mid post : List ℕ) (x : ℕ) :
    totalWait (mid ++ x :: post) = totalWait (mid ++ post) + mid.sum + x * post.length := by
  induction mid with
  | nil => simp [Nat.add_comm]
  | cons y mid ih =>
    simp only [List.cons_append, totalWait_cons, List.length_append, List.length_cons,
      ih, List.sum_cons]
    ring

/-- **Exchange lemma, any distance apart.** Swapping the first job `a` with a
job `b` that runs `mid.length` jobs later changes total waiting time by
`(a - b) * (mid.length + 1)`.  Stated additively to avoid truncated subtraction. -/
theorem totalWait_swap_far (mid post : List ℕ) (a b : ℕ) :
    totalWait (b :: (mid ++ a :: post)) + a * (mid.length + 1) =
      totalWait (a :: (mid ++ b :: post)) + b * (mid.length + 1) := by
  simp only [totalWait_cons, List.length_append, List.length_cons, totalWait_append_cons]
  ring

/-- Running a longer job `a` first, ahead of a strictly shorter job `b` that
runs later, is strictly worse than swapping them -- whatever runs in between. -/
theorem totalWait_swap_far_lt (mid post : List ℕ) {a b : ℕ} (h : b < a) :
    totalWait (b :: (mid ++ a :: post)) < totalWait (a :: (mid ++ b :: post)) := by
  have h_eq := totalWait_swap_far mid post a b
  have h_mul : b * (mid.length + 1) < a * (mid.length + 1) :=
    Nat.mul_lt_mul_of_pos_right h (Nat.succ_pos _)
  omega

end ConvoyEffect
