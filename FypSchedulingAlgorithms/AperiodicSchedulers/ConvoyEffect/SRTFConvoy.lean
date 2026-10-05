/-
Copyright (c) 2026 Choo Kye Yong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Choo Kye Yong
-/
import FypSchedulingAlgorithms.AperiodicSchedulers.ConvoyEffect.ConvoySpec
import FypSchedulingAlgorithms.AperiodicSchedulers.ConvoyEffect.ConvoyWitnesses
import FypSchedulingAlgorithms.AperiodicSchedulers.AperiodicStep
import FypSchedulingAlgorithms.AperiodicSchedulers.PreemptiveLemmas
import FypSchedulingAlgorithms.ProcessSimpLemmas
import FypSchedulingAlgorithms.SchedStateSimpLemmas
import Mathlib.Algebra.Order.Field.Basic

/-! # SRTF: preemption removes the late-arrival convoy

SRTF is preemptive, so it is described by a priority function (`1 / remaining`)
passed to `stepPreemptive`, not by a `select` function.  The preemptive analogue
of `RunsShortestProcess` is that every step runs a candidate with the least
*remaining* time (`srtf_runs_shortest_remaining`), and it follows from a lemma
about `selectByPriority` that holds for every preemptive scheduler
(`Preemptive.selectByPriority_spec`, in `PreemptiveLemmas`).

The payoff is the late-arrival convoy (`lateConvoyArrivalStream`): a long job
starts at time 0 and a unit job arrives at time 1.  Non-preemptive SJF has
already committed to the long job, so the short job waits until step `L`
(`sjf_late_convoy_waiting`) -- the price of non-preemption, not an inversion.
SRTF preempts and finishes the short job at step 1 (`srtf_late_convoy_completes`).
-/

namespace ConvoyEffect

open Preemptive

/-- **SRTF runs the shortest remaining job.** Among candidates that all still
have work left, the one SRTF picks has the least remaining time. -/
theorem srtf_runs_shortest_remaining (candidates : List AperiodicProcess)
    (p : AperiodicProcess)
    (h : selectByPriority (fun p : AperiodicProcess => (1 : ℚ) / p.remaining) candidates = some p)
    (h_pos : ∀ q ∈ candidates, 0 < q.remaining) :
    ∀ q ∈ candidates, p.remaining ≤ q.remaining := by
  obtain ⟨hp_mem, h_max⟩ := selectByPriority_spec _ candidates p h
  intro q hq
  have hp : (0 : ℚ) < p.remaining := by exact_mod_cast h_pos p hp_mem
  have hq' : (0 : ℚ) < q.remaining := by exact_mod_cast h_pos q hq
  exact_mod_cast (one_div_le_one_div hq' hp).mp (h_max q hq)

/-- **One SRTF step.** If every job in the system still has work left, then
after one step that is still true, and the job on the CPU has no more work left
than any job waiting in `ready`. -/
theorem srtf_step_spec (s : SchedState)
    (h_pos : ∀ q ∈ s.ready ++ s.running.toList, 0 < q.remaining) :
    (∀ q ∈ (stepSRTF s).ready, 0 < q.remaining) ∧
      ∀ p, (stepSRTF s).running = some p →
        0 < p.remaining ∧ ∀ q ∈ (stepSRTF s).ready, p.remaining ≤ q.remaining := by
  unfold stepSRTF stepPreemptive
  dsimp only
  split
  · rename_i h_none
    have h_nil := selectByPriority_eq_none _ _ h_none
    simp_all
  · rename_i p h_sel
    have hp_mem := (selectByPriority_spec _ _ p h_sel).1
    have h_min := srtf_runs_shortest_remaining _ p h_sel h_pos
    have hp_pos := h_pos p hp_mem
    -- `N` below is the queue left once `p` is taken out (and a preempted job put back).
    -- Every job in it was a candidate, so it has work left, and at least as much as `p`.
    have h_N : ∀ N : List AperiodicProcess, (∀ q ∈ N, q ∈ s.ready ++ s.running.toList) →
        ∀ q ∈ N, 0 < q.remaining ∧ p.remaining ≤ q.remaining :=
      fun N hN q hq => ⟨h_pos q (hN q hq), h_min q (hN q hq)⟩
    rcases hr : s.running with _ | b
    -- Name `N` in each of the three cases: nothing was running; `p` was already
    -- running; or `p` preempted a different running job `b`.
    on_goal 1 =>
      simp only [hr] at h_N ⊢
      generalize hN : s.ready.erase p = N
      have hN' := h_N N (by
        rw [← hN]; intro q hq; exact List.mem_append_left _ (List.mem_of_mem_erase hq))
    on_goal 2 =>
      simp only [hr] at h_N ⊢
      by_cases hbp : b = p
    on_goal 2 =>
      simp only [hbp, beq_self_eq_true, ↓reduceIte]
      generalize hN : s.ready = N
      have hN' := h_N N (by rw [← hN]; intro q hq; exact List.mem_append_left _ hq)
    on_goal 3 =>
      simp only [beq_iff_eq, hbp, ↓reduceIte]
      generalize hN : s.ready.erase p ++ [b] = N
      have hN' := h_N N (by
        rw [← hN]; intro q hq
        rcases List.mem_append.mp hq with hq | hq
        · exact List.mem_append_left _ (List.mem_of_mem_erase hq)
        · simp only [List.mem_singleton] at hq; subst hq; simp)
    -- Now the same argument finishes all three cases.
    all_goals
      simp only [AperiodicProcess.process_tick, AperiodicProcess.process_remaining]
      split_ifs with h_done
      · split
        · -- `p` finished and nothing is left to run
          exact ⟨fun q hq => (hN' q hq).1, fun p' hp' => by simp at hp'⟩
        · -- `p` finished and `q'`, the shortest job in `N`, takes over
          rename_i q' h_q'
          have hq'_mem := (selectByPriority_spec _ _ q' h_q').1
          have h_min' := srtf_runs_shortest_remaining N q' h_q' (fun q hq => (hN' q hq).1)
          refine ⟨fun q hq => (hN' q (List.mem_of_mem_erase hq)).1, fun p' hp' => ?_⟩
          simp only [Option.some.injEq] at hp'
          subst hp'
          exact ⟨(hN' _ hq'_mem).1, fun q hq => h_min' q (List.mem_of_mem_erase hq)⟩
      · -- `p` still has work left, one tick less than before: still the shortest
        refine ⟨fun q hq => (hN' q hq).1, fun p' hp' => ?_⟩
        simp only [Option.some.injEq] at hp'
        subst hp'
        exact ⟨by simp only; omega, fun q hq => by have := (hN' q hq).2; simp only; omega⟩

/-- **SRTF invariant.** On a well-formed stream, at every step every job in the
system has work left, and the running job has no more work left than any job
waiting in `ready`. -/
theorem srtf_run_invariant (arrival_stream : ℕ → List AperiodicProcess)
    (h_wf : WellFormedStream arrival_stream) (t : ℕ) :
    (∀ q ∈ (runSteps arrival_stream stepSRTF t).ready, 0 < q.remaining) ∧
      ∀ p, (runSteps arrival_stream stepSRTF t).running = some p →
        0 < p.remaining ∧
          ∀ q ∈ (runSteps arrival_stream stepSRTF t).ready, p.remaining ≤ q.remaining := by
  -- a fresh arrival has work left: its `remaining` is its (positive) burst
  have h_arr : ∀ t, ∀ q ∈ arrival_stream t, 0 < q.remaining := fun t q hq => by
    rw [h_wf.fresh q t hq]; exact q.burst_exceed_zero
  induction t with
  | zero =>
    simp only [runSteps]
    apply srtf_step_spec
    intro q hq
    simp only [SchedStateG.init_aperiodic, Option.toList_none, List.append_nil] at hq
    exact h_arr 0 q hq
  | succ t ih =>
    obtain ⟨ih_ready, ih_running⟩ := ih
    simp only [runSteps]
    apply srtf_step_spec
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · rcases List.mem_append.mp hq with hq | hq
      · exact ih_ready q hq
      · exact h_arr _ q hq
    · exact (ih_running q (Option.mem_toList.mp hq)).1

/-- **SRTF always runs the shortest remaining job**, on every well-formed
stream and at every step. -/
theorem srtf_runsShortestRemaining :
    RunsShortestRemainingRun (fun arrival_stream => runSteps arrival_stream stepSRTF) :=
  fun arrival_stream h_wf t p hp => ((srtf_run_invariant arrival_stream h_wf t).2 p hp).2

/-- **SRTF has no online convoy effect.** -/
theorem srtf_not_hasOnlineConvoyEffect : ¬ HasOnlineConvoyEffect stepSRTF :=
  not_not_intro srtf_runsShortestRemaining

/-- **SRTF preempts the convoy.** On the late-arrival convoy (with `L ≥ 3`, so
the long job still has more than one tick left at time 1), the short job is
dispatched and finished at step 1 -- the step it arrives. -/
theorem srtf_late_convoy_completes (L : ℕ) (hL : 2 < L) :
    (runSteps (lateConvoyArrivalStream L (by omega)) stepSRTF 1).completed =
      [{ lateShortJob with remaining := 0 }] := by
  -- Stage 1: at step 0 only the long job has arrived; SRTF runs it for one tick
  have h0 :
      (runSteps (lateConvoyArrivalStream L (by omega)) stepSRTF 0).running =
          some { longJob L (by omega) with remaining := L - 1 } ∧
        (runSteps (lateConvoyArrivalStream L (by omega)) stepSRTF 0).ready = [] ∧
        (runSteps (lateConvoyArrivalStream L (by omega)) stepSRTF 0).completed = [] := by
    refine ⟨?_, ?_, ?_⟩ <;>
      simp [runSteps, stepSRTF, stepPreemptive, selectByPriority, lateConvoyArrivalStream,
        longJob, show ¬ L - 1 = 0 by omega]
  obtain ⟨h_running, h_ready, h_completed⟩ := h0
  -- peel off exactly one step; `simp only [runSteps]` would unroll step 0 as well
  have h_step : runSteps (lateConvoyArrivalStream L (by omega)) stepSRTF 1 =
      stepSRTF { runSteps (lateConvoyArrivalStream L (by omega)) stepSRTF 0 with
        ready := (runSteps (lateConvoyArrivalStream L (by omega)) stepSRTF 0).ready ++
          lateConvoyArrivalStream L (by omega) 1 } := rfl
  rw [h_step]
  simp only [lateConvoyArrivalStream, h_running, h_ready, h_completed, List.nil_append]
  -- Stage 2: the short job (priority 1/1) outranks the long one (1/(L-1)), so it
  -- preempts, uses its single tick, and completes in this same step
  have h_prio : ((L - 1 : ℕ) : ℚ)⁻¹ < 1 :=
    inv_lt_one_of_one_lt₀ (by exact_mod_cast (by omega : 1 < L - 1))
  simp [stepSRTF, stepPreemptive, selectByPriority, longJob, lateShortJob, h_prio]

end ConvoyEffect
