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
SRTF preempts: the short job is on the CPU at step 1, the step it arrives, and
finishes at step 2 (`srtf_late_convoy_completes`).
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

/-- SRTF's priority `1 / remaining` reverses the order on (positive) remaining
times. -/
theorem one_div_remaining_lt_iff (a c : ℕ) (ha : 0 < a) (hc : 0 < c) :
    (1 : ℚ) / a < 1 / c ↔ c < a := by
  rw [one_div_lt_one_div (by exact_mod_cast ha) (by exact_mod_cast hc)]
  exact Nat.cast_lt

/-- **One SRTF step.** If every job in the system still has work left, then
after one step that is still true, and the job on the CPU has no more work left
than any job waiting in `ready`. -/
theorem srtf_step_spec (s : SchedState)
    (h_pos : ∀ q ∈ s.ready ++ s.running.toList, 0 < q.remaining) :
    (∀ q ∈ (stepSRTF s).ready, 0 < q.remaining) ∧
      ∀ p, (stepSRTF s).running = some p →
        0 < p.remaining ∧ ∀ q ∈ (stepSRTF s).ready, p.remaining ≤ q.remaining := by
  have h_ready : ∀ q ∈ s.ready, 0 < q.remaining :=
    fun q hq => h_pos q (List.mem_append_left _ hq)
  -- Dispatching the shortest job `q` of `ready`: it has work left, and what stays
  -- behind in `ready` still has work left, and at least as much as `q`.
  have h_dispatch : ∀ q, selectByPriority (fun p : AperiodicProcess => (1 : ℚ) / p.remaining)
      s.ready = some q →
      0 < q.remaining ∧ ∀ r ∈ s.ready.erase q, 0 < r.remaining ∧ q.remaining ≤ r.remaining := by
    intro q hq
    have h_min := srtf_runs_shortest_remaining _ q hq h_ready
    exact ⟨h_ready q (selectByPriority_spec _ _ q hq).1, fun r hr =>
      ⟨h_ready r (List.mem_of_mem_erase hr), h_min r (List.mem_of_mem_erase hr)⟩⟩
  unfold stepSRTF stepPreemptive
  rcases hr : s.running with _ | b
  · -- idle CPU: dispatch the shortest job of `ready`, if any
    simp only
    split
    · exact ⟨h_ready, by simp⟩
    · rename_i q h_sel
      obtain ⟨hq_pos, h_rest⟩ := h_dispatch q h_sel
      refine ⟨fun r hr => (h_rest r hr).1, fun p hp => ?_⟩
      simp only [Option.some.injEq] at hp
      subst hp
      exact ⟨hq_pos, fun r hr => (h_rest r hr).2⟩
  · have hb_pos : 0 < b.remaining := h_pos b (by simp [hr])
    simp only [AperiodicProcess.process_tick, AperiodicProcess.process_remaining]
    split_ifs with h_done
    · -- `b` finished: dispatch, exactly as from an idle CPU
      split
      · exact ⟨h_ready, by simp⟩
      · rename_i q h_sel
        obtain ⟨hq_pos, h_rest⟩ := h_dispatch q h_sel
        refine ⟨fun r hr => (h_rest r hr).1, fun p hp => ?_⟩
        simp only [Option.some.injEq] at hp
        subst hp
        exact ⟨hq_pos, fun r hr => (h_rest r hr).2⟩
    · -- `b` still has work left after its tick
      have hb'_pos : 0 < b.remaining - 1 := by omega
      split
      · -- nothing is waiting: `b` keeps the CPU
        rename_i h_sel
        rw [selectByPriority_eq_none _ _ h_sel]
        simpa using hb'_pos
      · rename_i q h_sel
        obtain ⟨hq_pos, h_rest⟩ := h_dispatch q h_sel
        have h_min := srtf_runs_shortest_remaining _ q h_sel h_ready
        split_ifs with h_pre
        · -- `q` is strictly shorter than `b`: it preempts, `b` rejoins `ready`
          rw [one_div_remaining_lt_iff _ _ hb'_pos hq_pos] at h_pre
          refine ⟨fun r hr => ?_, fun p hp => ?_⟩
          · rcases List.mem_append.mp hr with hr | hr
            · exact (h_rest r hr).1
            · simp only [List.mem_singleton] at hr; subst hr; exact hb'_pos
          · simp only [Option.some.injEq] at hp
            subst hp
            refine ⟨hq_pos, fun r hr => ?_⟩
            rcases List.mem_append.mp hr with hr | hr
            · exact (h_rest r hr).2
            · simp only [List.mem_singleton] at hr; subst hr; simp only; omega
        · -- `b` is no longer than the shortest waiting job `q`: it keeps the CPU
          rw [one_div_remaining_lt_iff _ _ hb'_pos hq_pos] at h_pre
          refine ⟨h_ready, fun p hp => ?_⟩
          simp only [Option.some.injEq] at hp
          subst hp
          exact ⟨hb'_pos, fun r hr => by have := h_min r hr; simp only; omega⟩

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
dispatched at step 1 -- the step it arrives, preempting the long job -- and
completes at step 2, after its single tick.  It never waits in `ready`. -/
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
  -- Stage 2: the long job uses a tick (`L - 1` left); the short job (priority 1/1)
  -- outranks it (1/(L-1)), so it preempts, unticked, and the long job rejoins `ready`
  have h_prio : ((L - 1 : ℕ) : ℚ)⁻¹ < 1 :=
    inv_lt_one_of_one_lt₀ (by exact_mod_cast (by omega : 1 < L - 1))
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
