/-
Copyright (c) 2026 Choo Kye Yong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Choo Kye Yong
-/
import FypSchedulingAlgorithms.AperiodicSchedulers.Schedule

/-!
# What response time is

*Response time* is the time from a job's arrival until it first gets the CPU.  It is a
property of a schedule (`Schedule`), so it means the same thing for every scheduler: a run
follows the schedule `scheduleOfRun run` (`runSchedule step` for a step function), and Round
Robin's run `runRR quantum` is a run like any other.

**The definition** (`IsFirstDispatchAt σ i t`): schedule `σ` puts job `i` on the CPU after
step `t`, and never before.  It is a predicate, not a function: a schedule that never runs
job `i` (a starving one) has no first dispatch, and nothing here asks for a proof that one
exists.  When there is one it is unique (`IsFirstDispatchAt.unique`).  Equivalently, job `i`
is on the CPU after step `t` and has had no ticks before it
(`isFirstDispatchAt_iff_ticksBefore_eq_zero`).

By the tick convention (`Step`) a job released at time `r` can be on the CPU after step `r`
at the earliest, and then gets its first tick in step `r + 1`.  So job `p` has **response
time** `r` (`HasResponseTime σ p r`) when `σ` first dispatches it after step
`p.arrival + r`; response time 0 means it is put on the CPU in the step that releases it.
On a batch (`AllArrivalsAtZero`) every arrival is 0, so a job's response time is the step
at which it is first dispatched (`hasResponseTime_iff_of_arrival_eq_zero`).

The per-scheduler results are in `RRResponseTime` and `FCFSResponseTime`.
-/

namespace ResponseTime

/-- `σ` first puts job `i` on the CPU after step `t`: it holds the CPU then, and never before. -/
def IsFirstDispatchAt (σ : Schedule) (i t : ℕ) : Prop :=
  σ t = some i ∧ ∀ t' < t, σ t' ≠ some i

/-- **A job is first dispatched at most once**: two first-dispatch steps of the same job in
the same schedule are equal. -/
theorem IsFirstDispatchAt.unique {σ : Schedule} {i t t' : ℕ} (h : IsFirstDispatchAt σ i t)
    (h' : IsFirstDispatchAt σ i t') : t = t' := by
  rcases Nat.lt_trichotomy t t' with h_lt | h_eq | h_gt
  · exact absurd h.1 (h'.2 t h_lt)
  · exact h_eq
  · exact absurd h'.1 (h.2 t' h_gt)

/-- A first dispatch is a step at which the job holds the CPU without having had any tick
before. -/
theorem isFirstDispatchAt_iff_ticksBefore_eq_zero (σ : Schedule) (i t : ℕ) :
    IsFirstDispatchAt σ i t ↔ σ t = some i ∧ ticksBefore σ i t = 0 := by
  refine and_congr_right fun _ => ⟨ticksBefore_eq_zero, fun h t' ht' h_eq => ?_⟩
  unfold ticksBefore at h
  rw [List.countP_eq_zero] at h
  exact h t' (List.mem_range.mpr ht') (by simpa using h_eq)

/-- Job `p` has **response time** `r` under `σ`: `σ` first puts it on the CPU after step
`p.arrival + r`, i.e. `r` steps after the step that releases it. -/
def HasResponseTime (σ : Schedule) (p : AperiodicProcess) (r : ℕ) : Prop :=
  IsFirstDispatchAt σ p.id (p.arrival + r)

/-- A job has at most one response time. -/
theorem HasResponseTime.unique {σ : Schedule} {p : AperiodicProcess} {r r' : ℕ}
    (h : HasResponseTime σ p r) (h' : HasResponseTime σ p r') : r = r' := by
  have := IsFirstDispatchAt.unique h h'
  omega

/-- For a job that arrives at time 0, as in a batch, the response time is the step at which
it is first dispatched. -/
theorem hasResponseTime_iff_of_arrival_eq_zero (σ : Schedule) {p : AperiodicProcess}
    (h_arrival : p.arrival = 0) (r : ℕ) :
    HasResponseTime σ p r ↔ IsFirstDispatchAt σ p.id r := by
  rw [HasResponseTime, h_arrival, Nat.zero_add]

end ResponseTime
