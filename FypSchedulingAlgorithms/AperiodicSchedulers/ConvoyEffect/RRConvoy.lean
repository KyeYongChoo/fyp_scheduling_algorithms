/-
Copyright (c) 2026 Choo Kye Yong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Choo Kye Yong
-/
import FypSchedulingAlgorithms.AperiodicSchedulers.ConvoyEffect.ConvoySpec
import FypSchedulingAlgorithms.AperiodicSchedulers.ConvoyEffect.ConvoyWitnesses
import FypSchedulingAlgorithms.AperiodicSchedulers.ConvoyEffect.FCFSConvoy
import FypSchedulingAlgorithms.AperiodicSchedulers.AperiodicStep
import FypSchedulingAlgorithms.ProcessSimpLemmas
import FypSchedulingAlgorithms.SchedStateSimpLemmas

/-! # Round Robin: the quantum caps the convoy

Round Robin always dispatches the head of the queue, regardless of burst, so in
the yes/no sense above it inverts just as FCFS does.  What the quantum changes
is the *cost* of the convoy: a long job can hold the CPU for at most `quantum`
ticks before the job behind it gets a turn.

On the two-job convoy (`longJob L` ahead of `shortJob`, both arriving at time 0)
the short job is first dispatched at step `min quantum L` under RR
(`rr_convoy_dispatch`), against step `L` under FCFS (`fcfs_convoy_dispatch`).
So the delay grows with the quantum, and once `quantum ≥ L` RR is exactly as
bad as FCFS.

This does **not** mean a smaller quantum lowers total waiting time in general:
`rr_smaller_quantum_not_better` gives two equal jobs for which quantum 1
finishes them later than quantum 2, because they interleave.
-/

namespace ConvoyEffect

/-- While `t < min quantum L`, RR is still running the long job (with `L - t`
ticks left, having used `t` of its quantum) and the short job is waiting. -/
theorem rr_convoy_invariant (quantum L : ℕ) (hL : 0 < L) (t : ℕ)
    (ht : t < min quantum L) :
    (runStepsRR quantum (convoyArrivalStream L hL) t).sched.running =
        some { longJob L hL with remaining := L - t } ∧
      (runStepsRR quantum (convoyArrivalStream L hL) t).sched.ready = [shortJob] ∧
      (runStepsRR quantum (convoyArrivalStream L hL) t).ticksUsed = t := by
  induction t with
  | zero =>
    simp [runStepsRR, stepRR, convoyArrivalStream, SchedStateMethods.init, longJob]
  | succ t ih =>
    obtain ⟨ih_running, ih_ready, ih_ticks⟩ := ih (by omega)
    have h_lt := lt_min_iff.mp ht
    simp only [runStepsRR, convoyArrivalStream, ih_ready, List.append_nil]
    simp only [stepRR, ih_running, ih_ticks, longJob]
    have h1 : ¬ L - t ≤ 1 := by omega
    have h2 : ¬ t ≥ quantum - 1 := by omega
    simp [h1, h2]
    omega

/-- **RR caps the convoy at one quantum.** With a positive quantum, the short
job is dispatched at step `min quantum L`: after a full quantum if the long job
is preempted, or as soon as the long job finishes if it fits in one quantum. -/
theorem rr_convoy_dispatch (quantum L : ℕ) (hq : 0 < quantum) (hL : 0 < L) :
    (runStepsRR quantum (convoyArrivalStream L hL) (min quantum L)).sched.running = some shortJob := by
  obtain ⟨m, hm⟩ : ∃ m, min quantum L = m + 1 := ⟨min quantum L - 1, by omega⟩
  obtain ⟨h_running, h_ready, h_ticks⟩ :=
    rr_convoy_invariant quantum L hL m (by omega)
  have h_le := (le_min_iff.mp (le_of_eq hm.symm))
  rw [hm]
  simp only [runStepsRR, convoyArrivalStream, h_ready, List.append_nil]
  simp only [stepRR, h_running, h_ticks, longJob]
  by_cases hfin : L - m ≤ 1
  · simp [hfin]
  · have : m ≥ quantum - 1 := by omega
    simp [hfin, this]

/-- Before step `min quantum L`, the short job has not been dispatched: it is
still waiting in the ready queue. -/
theorem rr_convoy_waiting (quantum L : ℕ) (hL : 0 < L) (t : ℕ) (ht : t < min quantum L) :
    shortJob ∈ (runStepsRR quantum (convoyArrivalStream L hL) t).sched.ready := by
  simp [(rr_convoy_invariant quantum L hL t ht).2.1]

/-- Once the quantum is at least the long job's burst, RR dispatches the short
job at exactly the same step as FCFS: RR degenerates to FCFS on the convoy. -/
theorem rr_convoy_eq_fcfs (quantum L : ℕ) (hL : 0 < L) (hq : L ≤ quantum) :
    (runStepsRR quantum (convoyArrivalStream L hL) L).sched.running =
      (runSteps (convoyArrivalStream L hL) stepFCFS L).running := by
  have h := rr_convoy_dispatch quantum L (by omega) hL
  rw [min_eq_right hq] at h
  rw [h, fcfs_convoy_dispatch]

/-- **RR has the online convoy effect, for every quantum**: it dispatches the
head of the queue, so on the convoy with `L = 2` the short job (1 tick) waits
behind the long job (2 ticks) at step 0. -/
theorem rr_hasOnlineConvoyEffect (quantum : ℕ) :
    HasOnlineConvoyEffectRun (fun arrival_stream t => (runStepsRR quantum arrival_stream t).sched) := by
  rw [hasOnlineConvoyEffectRun_iff]
  refine ⟨_, convoyArrivalStream_wf 2 (by omega), 0, longJob 2 (by omega), ?_, shortJob, ?_,
    by simp [shortJob, longJob]⟩ <;>
    simp [runStepsRR, stepRR, convoyArrivalStream]

/-! ### A smaller quantum is not better in general -/

/-- **Smaller quantum, later completion.** On `equalPair`, quantum 2 has job 0
finished by step 2, while quantum 1 interleaves the two jobs and job 0 has not
finished by step 2 (it finishes at step 3; job 1 finishes at step 4 under
both).  So total turnaround is 6 with quantum 2 and 7 with quantum 1. -/
theorem rr_smaller_quantum_not_better :
    (runStepsRR 2 equalPair 2).sched.completed.map (·.id) = [0] ∧
    (runStepsRR 1 equalPair 2).sched.completed.map (·.id) = [] ∧
    (runStepsRR 1 equalPair 3).sched.completed.map (·.id) = [0] ∧
    (runStepsRR 1 equalPair 4).sched.completed.map (·.id) = [0, 1] ∧
    (runStepsRR 2 equalPair 4).sched.completed.map (·.id) = [0, 1] := by
  decide

end ConvoyEffect
