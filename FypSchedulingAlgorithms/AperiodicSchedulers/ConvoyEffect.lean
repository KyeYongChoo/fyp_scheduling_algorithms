/-
Copyright (c) 2026 Choo Kye Yong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Choo Kye Yong
-/
import FypSchedulingAlgorithms.Process
import FypSchedulingAlgorithms.AperiodicSchedulers.AperiodicStep
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The convoy effect

The convoy effect is the textbook observation that a long job running ahead of
shorter ones that are already waiting inflates the total waiting time of the
whole batch: every job behind it pays for its full burst.

This file states it at two levels.

* **The cost** (`totalWait`, `totalWait_swap`): for a batch run back-to-back,
  swapping two adjacent jobs changes total waiting time by exactly the
  difference of their bursts.  So a longer job ahead of a shorter one is
  strictly worse than the swapped order -- the comparison is against the
  scheduler's *own* order with one inversion fixed, not against some external
  optimum.
* **The cause** (`NoInversion`, `HasConvoyEffect`): a selection policy has the
  convoy effect when it can dispatch a job while a strictly shorter one is
  waiting in the same ready queue.  This is checked per decision, so it makes
  sense for arbitrary (infinite) arrival streams, where total waiting time does
  not.

Under this definition FCFS has the convoy effect and SJF does not.  A short job
arriving *after* non-preemptive SJF has committed to a long one is not an
inversion -- the short job was not in `ready` when the choice was made -- and is
better described as the cost of non-preemption, which SRTF removes.
Starvation is an independent liveness property (`StarvationSpec`): SJF is
convoy-free yet starves.
-/

namespace ConvoyEffect

/-! ## The cost: total waiting time of a batch -/

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

/-! ## The cause: inversions at decision time -/

/-- A selection policy never dispatches a job while a strictly shorter job is
waiting in the same ready queue. -/
def NoInversion (select : List AperiodicProcess → Option AperiodicProcess) : Prop :=
  ∀ ready p, select ready = some p → ∀ q ∈ ready, p.burst ≤ q.burst

/-- A selection policy has the **convoy effect** when, for some ready queue, it
dispatches a job ahead of a strictly shorter one that is already waiting. -/
def HasConvoyEffect (select : List AperiodicProcess → Option AperiodicProcess) : Prop :=
  ¬ NoInversion select

/-- Unfolded form of `HasConvoyEffect`: an explicit ready queue and an explicit
shorter job that the policy passes over. -/
theorem hasConvoyEffect_iff (select : List AperiodicProcess → Option AperiodicProcess) :
    HasConvoyEffect select ↔
      ∃ ready p, select ready = some p ∧ ∃ q ∈ ready, q.burst < p.burst := by
  unfold HasConvoyEffect NoInversion
  push Not
  rfl

/-! ## FCFS has the convoy effect -/

/-- The convoy leader: a long job (burst 5) at the head of the queue. -/
def leader : AperiodicProcess := ⟨0, 0, 5, 5, by omega⟩

/-- A short job (burst 1) waiting behind it. -/
def shortJob : AperiodicProcess := ⟨1, 0, 1, 1, by omega⟩

/-- **FCFS has the convoy effect**: with `leader` ahead of `shortJob` in the
ready queue, FCFS dispatches the leader even though the short job is waiting. -/
theorem fcfs_hasConvoyEffect : HasConvoyEffect selectFCFS :=
  (hasConvoyEffect_iff _).mpr
    ⟨[leader, shortJob], leader, rfl, shortJob, by simp, by decide⟩

/-! ## SJF has no convoy effect -/

/-- Invariant of the `foldl` inside `selectSJF`: the result is no longer than
the accumulator it started from, nor than any job it scanned. -/
theorem selectSJF_foldl_min (l : List AperiodicProcess) (init : Option AperiodicProcess)
    (p : AperiodicProcess)
    (h : l.foldl (fun best q =>
        match best with
        | none   => some q
        | some b => if q.burst < b.burst then some q else some b) init = some p) :
    (∀ b, init = some b → p.burst ≤ b.burst) ∧ ∀ q ∈ l, p.burst ≤ q.burst := by
  induction l generalizing init with
  | nil =>
    simp only [List.foldl_nil] at h
    subst h
    exact ⟨fun b hb => by cases hb; exact le_rfl, by simp⟩
  | cons x xs ih =>
    simp only [List.foldl_cons] at h
    obtain ⟨ih_acc, ih_rest⟩ := ih _ h
    cases init with
    | none =>
      have hx := ih_acc x rfl
      exact ⟨by simp, by
        intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · exact hx
        · exact ih_rest q hq⟩
    | some b =>
      by_cases hlt : x.burst < b.burst
      · have hx := ih_acc x (by simp [hlt])
        refine ⟨fun b' hb' => by cases hb'; omega, ?_⟩
        intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · exact hx
        · exact ih_rest q hq
      · have hb := ih_acc b (by simp [hlt])
        refine ⟨fun b' hb' => by cases hb'; exact hb, ?_⟩
        intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · omega
        · exact ih_rest q hq

/-- **SJF never inverts**: the job it dispatches is no longer than any job in
the ready queue. -/
theorem sjf_noInversion : NoInversion selectSJF := fun ready p h =>
  (selectSJF_foldl_min ready none p h).2

/-- SJF does not have the convoy effect. -/
theorem sjf_not_hasConvoyEffect : ¬ HasConvoyEffect selectSJF :=
  not_not_intro sjf_noInversion

end ConvoyEffect
