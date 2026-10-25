/-
Copyright (c) 2026 Choo Kye Yong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Choo Kye Yong
-/
import FypSchedulingAlgorithms.AperiodicSchedulers.ConvoyEffect.ConvoySpec
import FypSchedulingAlgorithms.AperiodicSchedulers.ConvoyEffect.ConvoyWitnesses
import FypSchedulingAlgorithms.AperiodicSchedulers.AperiodicStep
import FypSchedulingAlgorithms.AperiodicSchedulers.PreemptiveLemmas
import FypSchedulingAlgorithms.PreemptiveRuns
import FypSchedulingAlgorithms.ProcessSimpLemmas
import FypSchedulingAlgorithms.SchedStateSimpLemmas

/-! # SRTF: preemption removes the late-arrival convoy

SRTF is preemptive, so it is described by a priority function (`-remaining`)
passed to `stepPreemptive`, not by a `select` function.  Every step runs a
candidate with the least *remaining* time (`srtf_runs_shortest_remaining`), which
follows from a lemma about `selectByPriority` that holds for every preemptive
scheduler (`Preemptive.selectByPriority_spec`, in `PreemptiveLemmas`).  So SRTF
has neither the online convoy effect nor, in particular, the convoy effect
(`srtf_not_hasConvoyEffect`).

The payoff is the late-arrival convoy (`lateConvoyArrivalStream`): a long job
starts at time 0 and a unit job arrives at time 1.  Non-preemptive SJF has
already committed to the long job, so the short job waits until step `L`
(`sjf_late_convoy_waiting`) -- the price of non-preemption, not an inversion.
SRTF preempts: the short job is on the CPU at step 1, the step it arrives, and
finishes at step 2 (`srtf_late_convoy_completes`).
-/

namespace ConvoyEffect

open Preemptive

/-- **SRTF runs the shortest remaining job.** Among candidates that all still
have work left, the one SRTF picks has the least remaining time.

The positivity hypothesis `_h_pos` is no longer used: SRTF's priority is the
negated remaining time, which reverses the order on all of `ℕ`.  It was needed
when the priority was `1 / remaining`; it is kept so that the hypotheses and the
call sites stay as they were. -/
theorem srtf_runs_shortest_remaining (candidates : List AperiodicProcess)
    (p : AperiodicProcess)
    (h : selectByPriority (fun p : AperiodicProcess => -(p.remaining : ℤ)) candidates = some p)
    (_h_pos : ∀ q ∈ candidates, 0 < q.remaining) :
    ∀ q ∈ candidates, p.remaining ≤ q.remaining := by
  intro q hq
  have h_le : -(q.remaining : ℤ) ≤ -(p.remaining : ℤ) :=
    (selectByPriority_spec _ candidates p h).2 q hq
  omega

/-- **One SRTF step.** If every job in the system still has work left, then
after one step that is still true, and the job on the CPU has no more work left
than any job waiting in `ready`. -/
theorem srtf_step_spec (s : SchedState)
    (h_pos : ∀ q ∈ s.ready ++ s.running.toList, 0 < q.remaining) :
    (∀ q ∈ (stepSRTF s).ready, 0 < q.remaining) ∧
      ∀ p, (stepSRTF s).running = some p →
        0 < p.remaining ∧ ∀ q ∈ (stepSRTF s).ready, p.remaining ≤ q.remaining := by
  -- both halves are generic facts about `stepPreemptive` (`PreemptiveRuns`)
  have h_all := (PreemptiveRuns.stepPreemptive_conservesJobs _ :
    PreemptiveRuns.ConservesJobs stepSRTF).remaining_pos s h_pos
  refine ⟨fun q hq => h_all q (List.mem_append_left _ hq), fun p hp =>
    ⟨h_all p (List.mem_append_right _ (Option.mem_toList.mpr hp)), fun q hq => ?_⟩⟩
  have h_le : -(q.remaining : ℤ) ≤ -(p.remaining : ℤ) :=
    PreemptiveRuns.stepPreemptive_running_max _ s p hp q hq
  omega

/-- **SRTF invariant.** On a well-formed stream, at every step every job in the
system has work left, and the running job has no more work left than any job
waiting in `ready`. -/
theorem srtf_run_invariant (arrival_stream : ℕ → List AperiodicProcess)
    (h_wf : WellFormedStream arrival_stream) (t : ℕ) :
    (∀ q ∈ (runSteps arrival_stream stepSRTF t).ready, 0 < q.remaining) ∧
      ∀ p, (runSteps arrival_stream stepSRTF t).running = some p →
        0 < p.remaining ∧
          ∀ q ∈ (runSteps arrival_stream stepSRTF t).ready, p.remaining ≤ q.remaining := by
  -- both halves are generic run invariants of `stepPreemptive` (`PreemptiveRuns`);
  -- a fresh arrival has work left: its `remaining` is its (positive) burst
  have h_all := PreemptiveRuns.runSteps_remaining_pos
    (PreemptiveRuns.stepPreemptive_conservesJobs _ : PreemptiveRuns.ConservesJobs stepSRTF) rfl
    (fun t q hq => by
      rw [AperiodicProcess.process_remaining, h_wf.fresh q t hq]; exact q.burst_exceed_zero) t
  refine ⟨fun q hq => h_all q (List.mem_append_left _ hq), fun p hp =>
    ⟨h_all p (List.mem_append_right _ (Option.mem_toList.mpr hp)), fun q hq => ?_⟩⟩
  have h_le : -(q.remaining : ℤ) ≤ -(p.remaining : ℤ) :=
    PreemptiveRuns.runSteps_running_max _ arrival_stream t p hp q hq
  omega

/-- **SRTF always runs the shortest remaining job**, on every well-formed
stream and at every step. -/
theorem srtf_runsShortestRemaining :
    RunsShortestRemainingRun (fun arrival_stream => runSteps arrival_stream stepSRTF) :=
  fun arrival_stream h_wf t p hp => ((srtf_run_invariant arrival_stream h_wf t).2 p hp).2

/-- **SRTF has no online convoy effect.** -/
theorem srtf_not_hasOnlineConvoyEffect : ¬ HasOnlineConvoyEffect stepSRTF :=
  not_not_intro srtf_runsShortestRemaining

/-- **SRTF runs the shortest job at every dispatch** (it does so at every step). -/
theorem srtf_runsShortestAtDispatch :
    RunsShortestAtDispatchRun (fun arrival_stream => runSteps arrival_stream stepSRTF) :=
  runsShortestRemainingRun_imp_atDispatch srtf_runsShortestRemaining

/-- **SRTF has no convoy effect.** -/
theorem srtf_not_hasConvoyEffect : ¬ HasConvoyEffect stepSRTF :=
  not_not_intro srtf_runsShortestAtDispatch

/-- **SRTF preempts the convoy.** On the late-arrival convoy (with `L ≥ 3`, so
the long job still has more than one tick left at time 1), the short job is
dispatched at step 1 -- the step it arrives, preempting the long job -- and
completes at step 2, after its single tick -- so it never waits in `ready`
(compare `sjf_late_convoy_waiting`). -/
theorem srtf_late_convoy_completes (L : ℕ) (hL : 2 < L) :
    (runSteps (lateConvoyArrivalStream L (by omega)) stepSRTF 1).running = some lateShortJob ∧
      (runSteps (lateConvoyArrivalStream L (by omega)) stepSRTF 2).completed =
        [{ lateShortJob with remaining := 0 }] := by
  -- Stage 1: at step 0 only the long job has arrived; SRTF dispatches it (unticked)
  have h0 :
      (runSteps (lateConvoyArrivalStream L (by omega)) stepSRTF 0).running =
          some (longJob L (by omega)) ∧
        (runSteps (lateConvoyArrivalStream L (by omega)) stepSRTF 0).ready = [] ∧
        (runSteps (lateConvoyArrivalStream L (by omega)) stepSRTF 0).completed = [] := by
    refine ⟨?_, ?_, ?_⟩ <;>
      simp [runSteps, stepSRTF, stepPreemptive, selectByPriority, lateConvoyArrivalStream]
  obtain ⟨h_running0, h_ready0, h_completed0⟩ := h0
  -- Stage 2: the long job uses a tick (`L - 1` left); the short job (priority -1)
  -- outranks it (-(L-1)), so it preempts, unticked, and the long job rejoins `ready`
  have h_prio : 1 < L - 1 := by omega
  have h1 :
      (runSteps (lateConvoyArrivalStream L (by omega)) stepSRTF 1).running =
          some lateShortJob ∧
        (runSteps (lateConvoyArrivalStream L (by omega)) stepSRTF 1).ready =
          [{ longJob L (by omega) with remaining := L - 1 }] ∧
        (runSteps (lateConvoyArrivalStream L (by omega)) stepSRTF 1).completed = [] := by
    -- peel off exactly one step; `simp only [runSteps]` would unroll step 0 as well
    have h_step : runSteps (lateConvoyArrivalStream L (by omega)) stepSRTF 1 =
        stepSRTF { runSteps (lateConvoyArrivalStream L (by omega)) stepSRTF 0 with
          ready := (runSteps (lateConvoyArrivalStream L (by omega)) stepSRTF 0).ready ++
            lateConvoyArrivalStream L (by omega) 1 } := rfl
    rw [h_step]
    simp only [lateConvoyArrivalStream, h_running0, h_ready0, h_completed0, List.nil_append]
    refine ⟨?_, ?_, ?_⟩ <;>
      simp [stepSRTF, stepPreemptive, selectByPriority, longJob, lateShortJob, h_prio,
        show ¬ L - 1 = 0 by omega]
  obtain ⟨h_running1, h_ready1, h_completed1⟩ := h1
  refine ⟨h_running1, ?_⟩
  -- Stage 3: the short job uses its single tick and completes
  have h_step : runSteps (lateConvoyArrivalStream L (by omega)) stepSRTF 2 =
      stepSRTF { runSteps (lateConvoyArrivalStream L (by omega)) stepSRTF 1 with
        ready := (runSteps (lateConvoyArrivalStream L (by omega)) stepSRTF 1).ready ++
          lateConvoyArrivalStream L (by omega) 2 } := rfl
  rw [h_step]
  simp only [lateConvoyArrivalStream, h_running1, h_ready1, h_completed1, List.append_nil]
  simp [stepSRTF, stepPreemptive, selectByPriority, lateShortJob]

end ConvoyEffect
