/-
Copyright (c) 2026 Choo Kye Yong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Choo Kye Yong
-/
import FypSchedulingAlgorithms.AperiodicSchedulers.ConvoyEffect.ConvoySpec
import FypSchedulingAlgorithms.AperiodicSchedulers.ConvoyEffect.ConvoyWitnesses
import FypSchedulingAlgorithms.AperiodicSchedulers.AperiodicStep
import FypSchedulingAlgorithms.ProcessSimpLemmas
import FypSchedulingAlgorithms.SchedStateSimpLemmas

/-!
# FCFS has the convoy effect

FCFS dispatches the head of the queue regardless of burst, so it passes over a
waiting shorter job: it has the convoy effect (`fcfs_hasConvoyEffect`), already
on a batch (`fcfs_hasBatchConvoyEffect`).  On the concrete convoy the short
job waits the long job's full burst: it is dispatched only at step `L`
(`fcfs_convoy_dispatch`), which `RRConvoy` compares against Round Robin.
-/

namespace ConvoyEffect

/-- **FCFS has the batch convoy effect**: with `leader` ahead of `shortJob` in
the ready queue, FCFS dispatches the leader even though the short job is
waiting. -/
theorem fcfs_hasBatchConvoyEffect : HasBatchConvoyEffect selectFCFS :=
  (hasBatchConvoyEffect_iff _).mpr
    ⟨[leader, shortJob], by simp [IsBatch, leader, shortJob], leader, by simp, rfl,
      shortJob, by simp, by decide⟩

/-- While `t < L`, FCFS is still running the long job, with `L - t` ticks left
(dispatch takes a step without ticking), and the short job is waiting. -/
theorem fcfs_convoy_invariant (L : ℕ) (hL : 0 < L) (t : ℕ) (ht : t < L) :
    (runSteps (convoyArrivalStream L hL) stepFCFS t).running =
        some { longJob L hL with remaining := L - t } ∧
      (runSteps (convoyArrivalStream L hL) stepFCFS t).ready = [shortJob] := by
  induction t with
  | zero =>
    simp [runSteps, stepFCFS, stepNonPreemptive, selectFCFS, convoyArrivalStream,
      SchedStateMethods.init, longJob]
  | succ t ih =>
    obtain ⟨ih_running, ih_ready⟩ := ih (by omega)
    -- `stepFCFS` must stay folded here, or the IH rewrite targets disappear
    simp only [runSteps, convoyArrivalStream, ih_ready, ih_running, List.append_nil]
    simp only [stepFCFS, stepNonPreemptive, longJob,
      AperiodicProcess.process_tick, AperiodicProcess.process_remaining]
    have h1 : ¬ L - t - 1 ≤ 0 := by omega
    simp [h1]
    omega

/-- **FCFS lets the convoy run its full length**: the short job is dispatched
only at step `L`, once the long job has finished. -/
theorem fcfs_convoy_dispatch (L : ℕ) (hL : 0 < L) :
    (runSteps (convoyArrivalStream L hL) stepFCFS L).running = some shortJob := by
  obtain ⟨m, rfl⟩ : ∃ m, L = m + 1 := ⟨L - 1, by omega⟩
  obtain ⟨h_running, h_ready⟩ := fcfs_convoy_invariant (m + 1) hL m (by omega)
  simp only [runSteps, convoyArrivalStream, h_ready, h_running, List.append_nil]
  simp [stepFCFS, stepNonPreemptive, longJob, selectFCFS]

/-- **FCFS has the convoy effect**: on the convoy with `L = 2`, at step 0 FCFS
dispatches the long job (2 ticks) while the short job (1 tick) waits. -/
theorem fcfs_hasConvoyEffect : HasConvoyEffect stepFCFS := by
  rw [HasConvoyEffect, hasConvoyEffectRun_iff]
  obtain ⟨h_running, h_ready⟩ := fcfs_convoy_invariant 2 (by omega) 0 (by omega)
  exact ⟨_, convoyArrivalStream_wf 2 (by omega), 0, _, dispatchesAt_zero h_running, shortJob,
    by simp [h_ready], by simp [shortJob]⟩

/-- **FCFS has the online convoy effect** (a consequence of the convoy effect). -/
theorem fcfs_hasOnlineConvoyEffect : HasOnlineConvoyEffect stepFCFS :=
  hasConvoyEffectRun_imp_online fcfs_hasConvoyEffect

end ConvoyEffect
