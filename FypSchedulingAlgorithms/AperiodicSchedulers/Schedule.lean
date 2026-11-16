/-
Copyright (c) 2026 Choo Kye Yong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Choo Kye Yong
-/
import FypSchedulingAlgorithms.Step
-- `Nat.le_induction`, for `ticksBefore_mono`
import Mathlib.Data.Nat.Init

/-!
# Schedules

A **schedule** `σ : ℕ → Option ℕ` describes a run without a step function: it names, for
each step `t`, the job (by id) that holds the CPU after step `t`, if any.  As in `runSteps`
(see the tick convention in `Step`), that job receives the tick of step `t + 1`, so job `i`
has had `ticksBefore σ i t` ticks before step `t`.

Every run follows a schedule: `scheduleOfRun run` reads off the id of the job on the CPU
after each step, and `runSchedule step arrival_stream` is the same for the run of a step
function.  This makes properties stated on schedules apply to every scheduler, Round Robin
(`runRR`) included.

This file only says what a schedule is.  Which schedules are possible (`IsAdmissible`), what
they cost (`schedWait`) and the bridge from runs to schedules are in
`ConvoyEffect/Optimality/Schedules`.
-/

/-! ## Schedules -/

/-- A **schedule** says, for each step `t`, which job (by id) holds the CPU after step `t`, if any.
That job receives the tick of step `t + 1`. -/
abbrev Schedule := ℕ → Option ℕ

/-- The ticks job `i` has received from schedule `σ` before step `t`:
one for each earlier step `t' < t` in which it held the CPU. -/
def ticksBefore (σ : Schedule) (i t : ℕ) : ℕ :=
  (List.range t).countP fun t' => σ t' = some i

/-- No ticks before step 0. -/
@[simp] theorem ticksBefore_zero (σ : Schedule) (i : ℕ) : ticksBefore σ i 0 = 0 := rfl

/-- Step `t` adds a tick to the job on the CPU after it. -/
theorem ticksBefore_succ (σ : Schedule) (i t : ℕ) :
    ticksBefore σ i (t + 1) = ticksBefore σ i t + if σ t = some i then 1 else 0 := by
  simp [ticksBefore, List.range_succ, List.countP_append]

/-- A job that never held the CPU before step `t` has had no ticks. -/
theorem ticksBefore_eq_zero {σ : Schedule} {i t : ℕ} (h : ∀ t' < t, σ t' ≠ some i) :
    ticksBefore σ i t = 0 := by
  unfold ticksBefore
  rw [List.countP_eq_zero]
  intro t' ht'
  simpa using h t' (List.mem_range.mp ht')

/-- Ticks only accumulate. -/
theorem ticksBefore_mono (σ : Schedule) (i : ℕ) {t t' : ℕ} (h : t ≤ t') :
    ticksBefore σ i t ≤ ticksBefore σ i t' := by
  induction t', h using Nat.le_induction with
  | base => exact Nat.le_refl _
  | succ n _ ih => rw [ticksBefore_succ]; omega

/-- Ticking `σ`'s job of step `t` is the only change from step `t` to `t + 1`. -/
theorem ticksBefore_succ_of_ne {σ : Schedule} {i t : ℕ} (h : σ t ≠ some i) :
    ticksBefore σ i (t + 1) = ticksBefore σ i t := by
  simp [ticksBefore_succ, h]

/-! ## Runs as schedules -/

/-- The schedule a run follows: the id of the job on the CPU after each step. -/
def scheduleOfRun (run : ℕ → SchedState) : Schedule :=
  fun t => (run t).running.map (·.id)

/-- The schedule a run of `step` follows: the id of the job on the CPU after each
step (`scheduleOfRun` of `runSteps`, `runSchedule_eq_scheduleOfRun`). -/
def runSchedule (step : SchedState → SchedState) (arrival_stream : ℕ → List AperiodicProcess) :
    Schedule :=
  scheduleOfRun (runSteps arrival_stream step)

/-- `runSchedule` is `scheduleOfRun` of `runSteps`, by definition. -/
theorem runSchedule_eq_scheduleOfRun (step : SchedState → SchedState)
    (arrival_stream : ℕ → List AperiodicProcess) :
    runSchedule step arrival_stream = scheduleOfRun (runSteps arrival_stream step) :=
  rfl
