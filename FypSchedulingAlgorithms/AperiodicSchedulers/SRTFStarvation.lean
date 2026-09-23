/-
Copyright (c) 2026 Choo Kye Yong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Choo Kye Yong
-/
import FypSchedulingAlgorithms.AperiodicSchedulers.AperiodicStep
import FypSchedulingAlgorithms.AperiodicSchedulers.StarvationSpec
import FypSchedulingAlgorithms.SchedStateSimpLemmas
import FypSchedulingAlgorithms.AperiodicSchedulers.StarvationWitnesses
import Mathlib.Tactic.NormNum

/-!
# SRTF is not starvation-free

SRTF (`stepSRTF`, the preemptive form of SJF) starves long jobs on exactly the
same witness as SJF, `StarvationWitnesses.starvation_stream`, which is shared
between the two files along with its well-formedness proof.

The *mechanism* differs, though, and is if anything worse.  Under SJF the victim
simply sat in `ready` and was never dispatched.  Under SRTF it is dispatched at
the end of every single step -- `stepPreemptive` fills the idle CPU with the
only remaining candidate once the unit-burst job retires -- and then preempted
at the start of the next step, before it is ever ticked.  So the victim looks
permanently *running*, yet its `remaining` never budges from 2:

  `(runSteps starvation_stream stepSRTF t).running = some victim`  for every `t`

Being perpetually scheduled and making no progress is still starvation: it never
reaches `completed`.  It also means an "is the CPU busy?" liveness check would
see nothing wrong here, unlike in the SJF case.
-/

namespace SRTFStarvation

open StarvationWitnesses

/-- **The heart of the argument.** After `t` steps the CPU holds the victim with
its `remaining` untouched, the ready queue is empty (the victim was just
re-dispatched out of it), and only `flood` jobs have ever completed. -/
theorem starvation_stream_invariant (t : ℕ) :
    (runSteps starvation_stream stepSRTF t).ready = [] ∧
    (runSteps starvation_stream stepSRTF t).running = some victim ∧
    ∀ p ∈ (runSteps starvation_stream stepSRTF t).completed, p.id ≠ 0 := by
  induction t with
  | zero =>
    -- candidates = [victim, flood 0]: priority 1/2 vs 1/1, so `flood 0` runs,
    -- finishes its single tick, and the victim is dispatched in its place
    refine ⟨?_, ?_, ?_⟩ <;>
      norm_num [runSteps, stepSRTF, stepPreemptive, selectByPriority, starvation_stream,
        victim, flood]
  | succ t ih =>
    obtain ⟨ih_ready, ih_running, ih_completed⟩ := ih
    -- Stage 1: expose the next step and feed in the IH; `stepSRTF` must stay folded
    -- here, or the rewrite targets `(runSteps .. stepSRTF t).ready` disappear too.
    simp only [runSteps, starvation_stream, ih_ready, ih_running]
    -- Stage 2: the arriving `flood (t+1)` outranks the victim (1/1 > 1/2), so it
    -- preempts, retires one tick later, and the victim is re-dispatched untouched
    refine ⟨?_, ?_, ?_⟩ <;>
      norm_num [stepSRTF, stepPreemptive, selectByPriority, victim, flood]
    intro p hp
    rcases hp with hp | rfl
    -- `norm_num` normalised `1 / x` to `x⁻¹` inside the scheduler, so line the IH up
    -- with `hp` before using it (the two forms are equal, but not definitionally)
    · simp only [stepSRTF, one_div] at ih_completed
      exact ih_completed p hp
    · simp

/-- **Main theorem.** SRTF is *not* starvation-free: `starvation_stream` is well
formed, yet `victim` never appears in `completed` at any time -- despite being
the running process at every single time step. -/
theorem not_starvationFree : ¬ StarvationFree stepSRTF := by
  intro h_starvation_free
  obtain ⟨completion_time, finished_process, h_mem, h_id⟩ :=
    h_starvation_free starvation_stream starvation_stream_wf 0 victim (by simp [starvation_stream])
  exact (starvation_stream_invariant completion_time).2.2 finished_process h_mem
    (by simpa [victim] using h_id)

end SRTFStarvation
