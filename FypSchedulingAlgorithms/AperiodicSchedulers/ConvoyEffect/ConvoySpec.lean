/-
Copyright (c) 2026 Choo Kye Yong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Choo Kye Yong
-/
import FypSchedulingAlgorithms.Process
import FypSchedulingAlgorithms.Step
import FypSchedulingAlgorithms.AperiodicSchedulers.ConvoyEffect.TotalWait
import FypSchedulingAlgorithms.ProcessSimpLemmas
import FypSchedulingAlgorithms.SchedStateSimpLemmas
import Mathlib.Data.List.Nodup

/-!
# The convoy effect

The convoy effect is the textbook observation that a long job put on the CPU
ahead of shorter ones that are already waiting inflates the total waiting time:
every job behind it pays for its full burst.

**The definition** (`HasConvoyEffectRun`, `HasConvoyEffect`) watches real runs
on well-formed arrival streams, with no restriction on when jobs arrive.  A
scheduler has the convoy effect when, at some *dispatch moment* -- a step at
which a job is put on the CPU that was not on it the step before
(`DispatchesAt`) -- a job with strictly less work left is waiting in `ready`.
Like `StarvationFreeRun`, it is stated over a run function, so it applies to
non-preemptive, preemptive and Round Robin schedulers alike.

* FCFS and RR have it (`fcfs_hasConvoyEffect`, `rr_hasConvoyEffect`).
* SJF and SRTF do not (`sjf_not_hasConvoyEffect`, `srtf_not_hasConvoyEffect`).
  In particular a short job arriving *after* non-preemptive SJF has committed to
  a long one is not a convoy: it was not in `ready` when the choice was made
  (`sjf_late_convoy_runsShortestAtDispatch`).  It is the cost of non-preemption,
  which SRTF removes, and `OnlineImpossibility` shows that no online
  non-preemptive policy can avoid it on every stream.

Two related notions:

* The **batch convoy effect** (`HasBatchConvoyEffect`) judges a selection
  policy's decision on a single *batch* (jobs all present at time 0).  It is the
  special case of the definition at step 0 of a batch run
  (`hasBatchConvoyEffect_imp_hasConvoyEffect`), and it is the form in which the
  cost is visible: for a batch, swapping the two jobs strictly lowers total
  waiting time (`hasBatchConvoyEffect_iff_swap_improves`), and in `RunWait` a
  policy has the batch convoy effect exactly when its run waits strictly longer
  than SJF's on some batch (`hasBatchConvoyEffect_iff_runWait`).
* The **online convoy effect** (`HasOnlineConvoyEffect`) is weaker: a shorter
  job waits behind the running one at *any* step, not just at a dispatch.  The
  convoy effect implies it (`hasConvoyEffectRun_imp_online`), but not
  conversely: SJF has the online convoy effect without the convoy effect
  (`online_convoy_not_imp_convoy`).

`remaining` rather than `burst` is the right measure in the run-based notions,
because a preempted job re-enters the queue with part of its burst done.
Starvation is an independent liveness property (`StarvationSpec`): SJF is
convoy-free yet starves.
-/

/-!
## Layout

This file only states the properties and connects them; the per-scheduler
results live in `FCFSConvoy`, `SJFConvoy`, `SRTFConvoy` and `RRConvoy`, sharing
the arrival streams in `ConvoyWitnesses`.  The cost side is in `TotalWait`, and
`RunWait` ties it to actual runs: there `runWait` measures a run's waiting time,
a batch run of a non-preemptive policy waits exactly `totalWait` of its dispatch
order, and `hasBatchConvoyEffect_iff_runWait` restates `HasBatchConvoyEffect` as
"on some batch, the run waits strictly longer than SJF's".  `OnlineImpossibility`
shows that no online non-preemptive policy waits least on every stream.
-/

namespace ConvoyEffect

/-! ## The convoy effect at dispatch moments -/

/-- In run `run` on stream `arrival_stream`, job `p` is **dispatched at step
`t`**: it holds the CPU after step `t`, and (if `t > 0`) the job on the CPU
after step `t - 1` had a different id.  This covers a dispatch into an idle CPU,
after a completion, and by preemption; a job that simply keeps the CPU is not
dispatched again. -/
def DispatchesAt (run : (ℕ → List AperiodicProcess) → ℕ → SchedState)
    (arrival_stream : ℕ → List AperiodicProcess) (t : ℕ) (p : AperiodicProcess) : Prop :=
  (run arrival_stream t).running = some p ∧
    ∀ t', t = t' + 1 → (run arrival_stream t').running.map (·.id) ≠ some p.id

/-- A scheduler, presented as `run arrival_stream t`, **runs the shortest job at
every dispatch**: on every well-formed stream, whenever it puts a job on the
CPU, no job waiting in `ready` has strictly less work left. -/
def RunsShortestAtDispatchRun (run : (ℕ → List AperiodicProcess) → ℕ → SchedState) : Prop :=
  ∀ arrival_stream : ℕ → List AperiodicProcess,
    WellFormedStream arrival_stream →
    ∀ (t : ℕ) (p : AperiodicProcess), DispatchesAt run arrival_stream t p →
      ∀ q ∈ (run arrival_stream t).ready, p.remaining ≤ q.remaining

/-- A scheduler has the **convoy effect** when, on some well-formed stream, it
puts a job on the CPU while a job with strictly less work left is waiting. -/
def HasConvoyEffectRun (run : (ℕ → List AperiodicProcess) → ℕ → SchedState) : Prop :=
  ¬ RunsShortestAtDispatchRun run

/-- The convoy effect for a one-step scheduler iterated with `runSteps`; every
scheduler except Round Robin has this form. -/
def HasConvoyEffect (step : SchedState → SchedState) : Prop :=
  HasConvoyEffectRun (fun arrival_stream => runSteps arrival_stream step)

/-- Unfolded form of `HasConvoyEffectRun`: an explicit stream, dispatch moment,
dispatched job, and shorter waiting job. -/
theorem hasConvoyEffectRun_iff (run : (ℕ → List AperiodicProcess) → ℕ → SchedState) :
    HasConvoyEffectRun run ↔
      ∃ arrival_stream, WellFormedStream arrival_stream ∧
        ∃ (t : ℕ) (p : AperiodicProcess), DispatchesAt run arrival_stream t p ∧
          ∃ q ∈ (run arrival_stream t).ready, q.remaining < p.remaining := by
  unfold HasConvoyEffectRun RunsShortestAtDispatchRun
  push Not
  rfl

/-- Whatever holds the CPU after step 0 was dispatched at step 0. -/
theorem dispatchesAt_zero {run : (ℕ → List AperiodicProcess) → ℕ → SchedState}
    {arrival_stream : ℕ → List AperiodicProcess} {p : AperiodicProcess}
    (h : (run arrival_stream 0).running = some p) : DispatchesAt run arrival_stream 0 p :=
  ⟨h, fun t' ht' => by omega⟩

/-! ## The batch convoy effect -/

/-- A **batch**: jobs that all arrive at time 0, untouched (`remaining = burst`),
with distinct ids.  These are the ready queues a scheduler can actually face at
the start of a well-formed run (`batchStream_wf`). -/
def IsBatch (ready : List AperiodicProcess) : Prop :=
  (∀ p ∈ ready, p.arrival = 0 ∧ p.remaining = p.burst) ∧ (ready.map (·.id)).Nodup

/-- A selection policy never dispatches a job from a batch while a strictly
shorter job of the batch is waiting.  (Only jobs *from* the batch count: a
`select` returning some job outside the queue is not judged here.) -/
def RunsShortestProcessBatch (select : List AperiodicProcess → Option AperiodicProcess) :
    Prop :=
  ∀ ready, IsBatch ready → ∀ p ∈ ready, select ready = some p → ∀ q ∈ ready, p.burst ≤ q.burst

/-- A selection policy has the **batch convoy effect** when, for some batch, it
dispatches a job ahead of a strictly shorter one that is already waiting. -/
def HasBatchConvoyEffect (select : List AperiodicProcess → Option AperiodicProcess) : Prop :=
  ¬ RunsShortestProcessBatch select

/-- Unfolded form of `HasBatchConvoyEffect`: an explicit batch and an explicit
shorter job that the policy passes over. -/
theorem hasBatchConvoyEffect_iff (select : List AperiodicProcess → Option AperiodicProcess) :
    HasBatchConvoyEffect select ↔
      ∃ ready, IsBatch ready ∧ ∃ p ∈ ready, select ready = some p ∧
        ∃ q ∈ ready, q.burst < p.burst := by
  unfold HasBatchConvoyEffect RunsShortestProcessBatch
  push Not
  rfl

/-! ### Why "not running the shortest process" is the right definition

`HasBatchConvoyEffect` is a property of single decisions, while `totalWait`
measures a whole batch.  They are linked by a non-adjacent version of the
exchange lemma: if the policy dispatches `p` while a strictly shorter `q` is
waiting, then *whatever* order the remaining jobs run in afterwards -- `q` sits
somewhere in it, as `mid ++ q :: post` -- swapping `p` and `q` strictly lowers
total waiting time.  Conversely, if every such swap helps, `q` really was
shorter.

So `hasBatchConvoyEffect_iff_swap_improves` says: a policy has the batch convoy
effect exactly when one of its dispatch decisions is provably wasteful,
independently of everything the scheduler does later.
-/

/-- **Batch convoy effect = a provably wasteful dispatch.** A policy has the
batch convoy effect iff, for some batch, it dispatches `p` while some other
waiting job `q` exists such that swapping `p` and `q` strictly lowers total
waiting time in *every* continuation `mid ++ q :: post`. -/
theorem hasBatchConvoyEffect_iff_swap_improves
    (select : List AperiodicProcess → Option AperiodicProcess) :
    HasBatchConvoyEffect select ↔
      ∃ ready, IsBatch ready ∧ ∃ p ∈ ready, select ready = some p ∧
        ∃ q ∈ ready.erase p, ∀ mid post : List ℕ,
        totalWait (q.burst :: (mid ++ p.burst :: post)) <
          totalWait (p.burst :: (mid ++ q.burst :: post)) := by
  rw [hasBatchConvoyEffect_iff]
  constructor
  · rintro ⟨ready, h_batch, p, hp, h_sel, q, hq, h_lt⟩
    have h_ne : q ≠ p := fun h_eq => by subst h_eq; omega
    exact ⟨ready, h_batch, p, hp, h_sel, q, List.mem_erase_of_ne h_ne |>.mpr hq,
      fun mid post => totalWait_swap_far_lt mid post h_lt⟩
  · rintro ⟨ready, h_batch, p, hp, h_sel, q, hq, h_swap⟩
    -- the two-job continuation already pins down `q.burst < p.burst`
    have h_lt := h_swap [] []
    simp only [List.nil_append, totalWait_cons, List.length_cons, List.length_nil,
      totalWait_nil] at h_lt
    exact ⟨ready, h_batch, p, hp, h_sel, q, List.mem_of_mem_erase hq, by omega⟩

/-! ## The online convoy effect

The online convoy effect watches every step, not just dispatches: at some step
of some well-formed arrival stream, a job is waiting in `ready` with strictly
less work left than the job holding the CPU.

* FCFS and RR have it on `convoyArrivalStream`, where both jobs are present
  from the start.
* Non-preemptive SJF has it on `lateConvoyArrivalStream`, where the short job
  arrives after the long one has been dispatched -- even though SJF has no
  convoy effect.
* SRTF never has it: preemption always hands the CPU to the job with least
  remaining work.
-/

/-- A scheduler, presented as `run arrival_stream t`, always **runs the job with
the least remaining work**: whenever a job is on the CPU, no waiting job has
strictly less work left. -/
def RunsShortestRemainingRun (run : (ℕ → List AperiodicProcess) → ℕ → SchedState) : Prop :=
  ∀ arrival_stream : ℕ → List AperiodicProcess,
    WellFormedStream arrival_stream →
    ∀ (t : ℕ) (p : AperiodicProcess), (run arrival_stream t).running = some p →
      ∀ q ∈ (run arrival_stream t).ready, p.remaining ≤ q.remaining

/-- A scheduler has the **online convoy effect** when, on some well-formed
arrival stream, a job with strictly less work left waits behind the running
job. -/
def HasOnlineConvoyEffectRun (run : (ℕ → List AperiodicProcess) → ℕ → SchedState) : Prop :=
  ¬ RunsShortestRemainingRun run

/-- The online convoy effect for a one-step scheduler iterated with `runSteps`;
every scheduler except Round Robin has this form. -/
def HasOnlineConvoyEffect (step : SchedState → SchedState) : Prop :=
  HasOnlineConvoyEffectRun (fun arrival_stream => runSteps arrival_stream step)

/-- Unfolded form of `HasOnlineConvoyEffectRun`: an explicit stream, step,
running job, and shorter waiting job. -/
theorem hasOnlineConvoyEffectRun_iff (run : (ℕ → List AperiodicProcess) → ℕ → SchedState) :
    HasOnlineConvoyEffectRun run ↔
      ∃ arrival_stream, WellFormedStream arrival_stream ∧
        ∃ (t : ℕ) (p : AperiodicProcess), (run arrival_stream t).running = some p ∧
          ∃ q ∈ (run arrival_stream t).ready, q.remaining < p.remaining := by
  unfold HasOnlineConvoyEffectRun RunsShortestRemainingRun
  push Not
  rfl

/-! ## How the three notions relate -/

/-- Running the shortest job at every step in particular runs it at every
dispatch. -/
theorem runsShortestRemainingRun_imp_atDispatch
    {run : (ℕ → List AperiodicProcess) → ℕ → SchedState} (h : RunsShortestRemainingRun run) :
    RunsShortestAtDispatchRun run :=
  fun arrival_stream h_wf t p h_disp => h arrival_stream h_wf t p h_disp.1

/-- **The convoy effect implies the online convoy effect.** -/
theorem hasConvoyEffectRun_imp_online {run : (ℕ → List AperiodicProcess) → ℕ → SchedState}
    (h : HasConvoyEffectRun run) : HasOnlineConvoyEffectRun run :=
  fun h_short => h (runsShortestRemainingRun_imp_atDispatch h_short)

/-- The arrival stream that releases `ready` at time 0 and nothing afterwards. -/
def batchStream (ready : List AperiodicProcess) : ℕ → List AperiodicProcess
  | 0 => ready
  | _ => []

theorem mem_batchStream {ready : List AperiodicProcess} {p : AperiodicProcess} {t : ℕ}
    (h : p ∈ batchStream ready t) : t = 0 ∧ p ∈ ready := by
  rcases t with _ | t <;> simp_all [batchStream]

/-- Releasing a batch at time 0 is a well-formed arrival stream. -/
theorem batchStream_wf {ready : List AperiodicProcess} (h_batch : IsBatch ready) :
    WellFormedStream (batchStream ready) where
  consistent p t h := by
    obtain ⟨rfl, hp⟩ := mem_batchStream h
    exact (h_batch.1 p hp).1
  fresh p t h := (h_batch.1 p (mem_batchStream h).2).2
  unique p1 p2 t1 t2 h1 h2 h_id := by
    obtain ⟨rfl, hp1⟩ := mem_batchStream h1
    obtain ⟨rfl, hp2⟩ := mem_batchStream h2
    exact ⟨rfl, List.inj_on_of_nodup_map h_batch.2 hp1 hp2 h_id⟩

/-- **The batch convoy effect is the convoy effect at step 0.** If a
non-preemptive policy passes over a shorter job in some batch, then releasing
that batch at time 0 makes it do so in a real run: at step 0 it dispatches the
chosen job while the shorter one waits. -/
theorem hasBatchConvoyEffect_imp_hasConvoyEffect
    (select : List AperiodicProcess → Option AperiodicProcess)
    (h : HasBatchConvoyEffect select) : HasConvoyEffect (stepNonPreemptive select) := by
  obtain ⟨ready, h_batch, p, hp, h_sel, q, hq, h_lt⟩ := (hasBatchConvoyEffect_iff select).mp h
  have h_ne : q ≠ p := fun h_eq => by subst h_eq; omega
  rw [HasConvoyEffect, hasConvoyEffectRun_iff]
  refine ⟨batchStream ready, batchStream_wf h_batch, 0, p, dispatchesAt_zero ?_, q, ?_, ?_⟩
  · simp [runSteps, stepNonPreemptive, batchStream, h_sel]
  · simpa [runSteps, stepNonPreemptive, batchStream, h_sel] using
      (List.mem_erase_of_ne h_ne).mpr hq
  · -- in a batch nothing has run yet, so `remaining` is the burst
    rw [(h_batch.1 q hq).2, (h_batch.1 p hp).2]
    exact h_lt

/-- **The batch convoy effect implies the online convoy effect.** -/
theorem hasBatchConvoyEffect_imp_online (select : List AperiodicProcess → Option AperiodicProcess)
    (h : HasBatchConvoyEffect select) : HasOnlineConvoyEffect (stepNonPreemptive select) :=
  hasConvoyEffectRun_imp_online (hasBatchConvoyEffect_imp_hasConvoyEffect select h)

end ConvoyEffect
