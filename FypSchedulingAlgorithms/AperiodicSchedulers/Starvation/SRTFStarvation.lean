/-
Copyright (c) 2026 Choo Kye Yong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Choo Kye Yong
-/
import FypSchedulingAlgorithms.AperiodicSchedulers.AperiodicStep
import FypSchedulingAlgorithms.AperiodicSchedulers.Starvation.StarvationSpec
import FypSchedulingAlgorithms.SchedStateSimpLemmas
import FypSchedulingAlgorithms.AperiodicSchedulers.Starvation.StarvationWitnesses
import Mathlib.Tactic.NormNum

/-!
# SRTF is not starvation-free

SRTF (`stepSRTF`, the preemptive form of SJF) starves long jobs on exactly the
same witness as SJF, `StarvationWitnesses.starvation_stream`, which is shared
between the two files along with its well-formedness proof.

The mechanism is the same as for SJF: the victim (remaining 2) sits in `ready`
forever.  Each step the unit job on the CPU uses its single tick and retires, and
the freshly arrived unit job (remaining 1) beats the victim to the CPU:

  `(runSteps starvation_stream stepSRTF t).ready = [victim]`  for every `t`

Preemption does not help the victim, because it never gets the CPU in the first
place; it only reaches the CPU when the queue has nothing shorter.
-/

namespace SRTFStarvation

open StarvationWitnesses

/-- **The heart of the argument.** After `t` steps the victim is the only job
waiting, untouched, the CPU holds the unit job `flood t` that arrived in this
step, and only `flood` jobs have ever completed. -/
theorem starvation_stream_invariant (t : ℕ) :
    (runSteps starvation_stream stepSRTF t).ready = [victim] ∧
    (runSteps starvation_stream stepSRTF t).running = some (flood t) ∧
    ∀ p ∈ (runSteps starvation_stream stepSRTF t).completed, p.id ≠ 0 := by
  induction t with
  | zero =>
    -- the CPU is idle and `ready = [victim, flood 0]`: priority -2 vs -1, so
    -- `flood 0` is dispatched (unticked) and the victim stays behind
    refine ⟨?_, ?_, ?_⟩ <;>
      norm_num [runSteps, stepSRTF, stepPreemptive, selectByPriority, starvation_stream,
        victim, flood]
  | succ t ih =>
    obtain ⟨ih_ready, ih_running, ih_completed⟩ := ih
    -- Stage 1: expose the next step and feed in the IH; `stepSRTF` must stay folded
    -- here, or the rewrite targets `(runSteps .. stepSRTF t).ready` disappear too.
    simp only [runSteps, starvation_stream, ih_ready, ih_running]
    -- Stage 2: `flood t` uses its single tick and retires; the arriving `flood (t+1)`
    -- outranks the victim (-1 > -2), so it is dispatched in its place
    refine ⟨?_, ?_, ?_⟩ <;>
      norm_num [stepSRTF, stepPreemptive, selectByPriority, victim, flood]
    intro p hp
    rcases hp with hp | rfl
    · exact ih_completed p hp
    · simp

/-- **Main theorem.** SRTF is *not* starvation-free: `starvation_stream` is well
formed, yet `victim` never appears in `completed` at any time: it waits in
`ready` at every single time step. -/
theorem not_starvationFree : ¬ StarvationFree stepSRTF := by
  intro h_starvation_free
  obtain ⟨completion_time, finished_process, h_mem, h_id⟩ :=
    h_starvation_free starvation_stream starvation_stream_wf 0 victim (by simp [starvation_stream])
  exact (starvation_stream_invariant completion_time).2.2 finished_process h_mem
    (by simpa [victim] using h_id)

end SRTFStarvation
