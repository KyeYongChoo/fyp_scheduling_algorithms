/-
Copyright (c) 2026 Choo Kye Yong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Choo Kye Yong
-/
import FypSchedulingAlgorithms.Process
import FypSchedulingAlgorithms.SchedState
import FypSchedulingAlgorithms.Step

/-!
# What it means for a scheduler to be starvation-free

This file only states the property; the proofs live in the per-scheduler files
(`FCFSStarvationFree`, `RRStarvationFree`, `SJFStarvation`, ...).  Keeping the
statement in one place means "starvation-free" means the *same thing* for every
scheduler, so `StarvationFree` and `¬ StarvationFree` results are directly
comparable, and a scheduler can be plugged in as data rather than by copying a
theorem statement.

`StarvationFreeRun` is stated over a *run function* `run arrival_stream t`
(the state after `t` steps) rather than over a one-step function, because not
every scheduler in this development is a `SchedState → SchedState`:

* non-preemptive and preemptive schedulers are, and get the convenience
  wrapper `StarvationFree step` (= `StarvationFreeRun (runSteps · step)`);
* Round Robin carries a quantum counter, so it steps `RRState → RRState` and
  is described by `StarvationFreeRun (fun as t => (runStepsRR quantum as t).sched)`.

`WellFormedStream` (see `Step`) is a hypothesis rather than part of the
conclusion: an ill-formed stream can re-announce the same process forever, or
hand a process a `remaining` that disagrees with its `burst`, and no scheduler
could be expected to cope with that.  Processes are matched by `Process.id`
rather than by `=` because `remaining` changes as a process is ticked.
-/

/-- A scheduler, presented as the function `run arrival_stream t` giving the
state after `t` steps, is **starvation-free** when every process that ever
arrives in a well-formed stream eventually turns up in `completed`. -/
def StarvationFreeRun (run : (ℕ → List AperiodicProcess) → ℕ → SchedState) : Prop :=
  ∀ arrival_stream : ℕ → List AperiodicProcess,
    WellFormedStream arrival_stream →
    ∀ (arrival_time : ℕ) (process : AperiodicProcess),
      process ∈ arrival_stream arrival_time →
      ∃ completion_time, ∃ finished_process ∈
        (run arrival_stream completion_time).completed,
          Process.id finished_process = Process.id process

/-- A one-step scheduler is starvation-free when iterating it with `runSteps`
is.  This is the form used for every scheduler except Round Robin. -/
def StarvationFree (step : SchedState → SchedState) : Prop :=
  StarvationFreeRun (fun arrival_stream => runSteps arrival_stream step)

/-- Unfolded form of `¬ StarvationFree step`: some well-formed stream has an
arriving process that never shows up in `completed`, at any time.  Handy for
starvation *proofs*, which have to produce exactly this data. -/
theorem not_starvationFree_iff (step : SchedState → SchedState) :
    ¬ StarvationFree step ↔
      ∃ (arrival_stream : ℕ → List AperiodicProcess), WellFormedStream arrival_stream ∧
        ∃ (arrival_time : ℕ) (process : AperiodicProcess),
          process ∈ arrival_stream arrival_time ∧
          ∀ (t : ℕ), ∀ finished_process ∈ (runSteps arrival_stream step t).completed,
            Process.id finished_process ≠ Process.id process := by
  unfold StarvationFree StarvationFreeRun
  push Not
  rfl
