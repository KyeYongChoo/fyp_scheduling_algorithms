/-
Copyright (c) 2026 Choo Kye Yong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Choo Kye Yong
-/
import FypSchedulingAlgorithms.Process
import FypSchedulingAlgorithms.Step
import FypSchedulingAlgorithms.SchedState
import FypSchedulingAlgorithms.AperiodicSchedulers.AperiodicStep
import FypSchedulingAlgorithms.AperiodicSchedulers.StarvationSpec
import FypSchedulingAlgorithms.AperiodicSchedulers.StarvationWitnesses
import FypSchedulingAlgorithms.ProcessSimpLemmas
import FypSchedulingAlgorithms.SchedStateSimpLemmas

/-!
# SJF is not starvation-free

Shortest Job First starves long jobs: a steady trickle of short jobs keeps
jumping the queue ahead of a longer one, forever.

The witness is deliberately minimal, so that the state after `t` steps is an
exact closed form rather than a growing queue:

* `victim`  -- burst 2, arrives at time 0, and is never scheduled;
* `flood t` -- burst 1, one arriving at every time `t`, each with a fresh id.

Because a unit-burst job is dispatched and retired in the very next step, and a
replacement arrives in that same step, the ready queue is *always* exactly
`[victim]` (`starvation_stream_invariant`).  `selectSJF` compares bursts, so it
takes the `flood` job (burst 1) over `victim` (burst 2) every single time.

Note this does not depend on SJF being non-preemptive: the victim never gets
dispatched in the first place, so there is nothing to preempt.
-/

namespace SJFStarvation

open StarvationWitnesses

/-- **The heart of the argument.** After `t` steps the ready queue still holds
exactly the victim, the CPU is busy with the unit-burst job that arrived this
tick, and nothing with the victim's id has ever completed. -/
theorem starvation_stream_invariant (t : ℕ) :
    (runSteps starvation_stream stepSJF t).ready = [victim] ∧
    (runSteps starvation_stream stepSJF t).running = some (flood t) ∧
    ∀ p ∈ (runSteps starvation_stream stepSJF t).completed, p.id ≠ 0 := by
  induction t with
  | zero =>
    -- ready = [victim, flood 0]: SJF picks `flood 0` (burst 1 < 2), leaving [victim]
    refine ⟨?_, ?_, ?_⟩ <;>
      simp [runSteps, stepSJF, stepNonPreemptive, starvation_stream, selectSJF, victim, flood]
  | succ t ih =>
    obtain ⟨ih_ready, ih_running, ih_completed⟩ := ih
    -- Stage 1: expose the next step and feed in the IH.  `stepSJF` must stay folded
    -- here, or the rewrite targets `(runSteps .. stepSJF t).ready` disappear too.
    simp only [runSteps, starvation_stream, ih_ready, ih_running]
    -- Stage 2: now the state is concrete, so the step computes: `flood t` finishes its
    -- one tick and retires, and SJF picks `flood (t+1)` over `victim` again
    refine ⟨?_, ?_, ?_⟩ <;>
      simp only [stepSJF, stepNonPreemptive, selectSJF, victim, flood, List.cons_append,
        List.nil_append, List.foldl_cons, List.foldl_nil, AperiodicProcess.process_tick,
        AperiodicProcess.process_remaining]
    · simp
    · simp
    · intro p hp
      simp only [Nat.reduceSub, Nat.le_refl, ↓reduceIte, Nat.reduceLT, List.mem_append,
        List.mem_singleton] at hp
      rcases hp with hp | rfl
      · exact ih_completed p hp
      · simp

/-- **Main theorem.** SJF is *not* starvation-free: `starvation_stream` is
well formed, yet `victim` never appears in `completed` at any time. -/
theorem not_starvationFree : ¬ StarvationFree stepSJF := by
  intro h_starvation_free
  obtain ⟨completion_time, finished_process, h_mem, h_id⟩ :=
    h_starvation_free starvation_stream starvation_stream_wf 0 victim (by simp [starvation_stream])
  -- the invariant says nothing with id 0 has completed, but `victim.id = 0`
  exact (starvation_stream_invariant completion_time).2.2 finished_process h_mem
    (by simpa [victim] using h_id)

end SJFStarvation
