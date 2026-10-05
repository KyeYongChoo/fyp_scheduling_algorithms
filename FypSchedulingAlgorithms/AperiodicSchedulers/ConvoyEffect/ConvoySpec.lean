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

The convoy effect is the textbook observation that a long job running ahead of
shorter ones that are already waiting inflates the total waiting time of the
whole batch: every job behind it pays for its full burst.

This folder states it at two levels.

* **The cost** (`totalWait`, `totalWait_swap`): for a batch run back-to-back,
  swapping two adjacent jobs changes total waiting time by exactly the
  difference of their bursts.  So a longer job ahead of a shorter one is
  strictly worse than the swapped order -- the comparison is against the
  scheduler's *own* order with one inversion fixed, not against some external
  optimum.
* **The cause** (`RunsShortestProcess`, `HasConvoyEffect`): a selection policy has the
  convoy effect when, faced with a batch of jobs, it can dispatch one while a
  strictly shorter one is waiting in the same ready queue.

A third, weaker notion watches whole runs instead of single decisions: the
**online convoy effect** (`HasOnlineConvoyEffect`), where at some step a job
with less work left waits behind the running one.  It applies to preemptive
schedulers and Round Robin too.  The batch convoy effect implies it
(`hasConvoyEffect_imp_online`), but not conversely: SJF has the online convoy
effect without the batch one (`online_convoy_not_imp_convoy`).

Under this definition FCFS has the convoy effect and SJF does not.  A short job
arriving *after* non-preemptive SJF has committed to a long one is not an
inversion -- the short job was not in `ready` when the choice was made -- and is
better described as the cost of non-preemption, which SRTF removes.
Starvation is an independent liveness property (`StarvationSpec`): SJF is
convoy-free yet starves.
-/

/-!
## Layout

This file only states the property and connects it to `totalWait`
(`hasConvoyEffect_iff_swap_improves`); the per-scheduler results live in
`FCFSConvoy`, `SJFConvoy`, `SRTFConvoy` and `RRConvoy`, sharing the arrival
streams in `ConvoyWitnesses`.  The cost side is in `TotalWait`.
-/

namespace ConvoyEffect

/-- A **batch**: jobs that all arrive at time 0, untouched (`remaining = burst`),
with distinct ids.  These are the ready queues a scheduler can actually face at
the start of a well-formed run (`batchStream_wf`); restricting to them stops a
policy from being blamed for its behaviour on queues no run produces. -/
def IsBatch (ready : List AperiodicProcess) : Prop :=
  (∀ p ∈ ready, p.arrival = 0 ∧ p.remaining = p.burst) ∧ (ready.map (·.id)).Nodup

/-- A selection policy never dispatches a job from a batch while a strictly
shorter job of the batch is waiting.  (Only jobs *from* the batch count: a
`select` returning some job outside the queue is not judged here.) -/
def RunsShortestProcess (select : List AperiodicProcess → Option AperiodicProcess) : Prop :=
  ∀ ready, IsBatch ready → ∀ p ∈ ready, select ready = some p → ∀ q ∈ ready, p.burst ≤ q.burst

/-- A selection policy has the **convoy effect** when, for some batch, it
dispatches a job ahead of a strictly shorter one that is already waiting. -/
def HasConvoyEffect (select : List AperiodicProcess → Option AperiodicProcess) : Prop :=
  ¬ RunsShortestProcess select

/-- Unfolded form of `HasConvoyEffect`: an explicit batch and an explicit
shorter job that the policy passes over. -/
theorem hasConvoyEffect_iff (select : List AperiodicProcess → Option AperiodicProcess) :
    HasConvoyEffect select ↔
      ∃ ready, IsBatch ready ∧ ∃ p ∈ ready, select ready = some p ∧
        ∃ q ∈ ready, q.burst < p.burst := by
  unfold HasConvoyEffect RunsShortestProcess
  push Not
  rfl

/-! ## Why "not running the shortest process" is the right definition

`HasConvoyEffect` is a property of single decisions, while `totalWait` measures
a whole batch.  They are linked by a non-adjacent version of the exchange
lemma: if the policy dispatches `p` while a strictly shorter `q` is waiting,
then *whatever* order the remaining jobs run in afterwards -- `q` sits somewhere
in it, as `mid ++ q :: post` -- swapping `p` and `q` strictly lowers total
waiting time.  Conversely, if every such swap helps, `q` really was shorter.

So `hasConvoyEffect_iff_swap_improves` says: a policy has the convoy effect
exactly when one of its dispatch decisions is provably wasteful, independently
of everything the scheduler does later.
-/

/-- **Convoy effect = a provably wasteful dispatch.** A policy has the convoy
effect iff, for some ready queue, it dispatches `p` while some other waiting job
`q` exists such that swapping `p` and `q` strictly lowers total waiting time in
*every* continuation `mid ++ q :: post`. -/
theorem hasConvoyEffect_iff_swap_improves
    (select : List AperiodicProcess → Option AperiodicProcess) :
    HasConvoyEffect select ↔
      ∃ ready, IsBatch ready ∧ ∃ p ∈ ready, select ready = some p ∧
        ∃ q ∈ ready.erase p, ∀ mid post : List ℕ,
        totalWait (q.burst :: (mid ++ p.burst :: post)) <
          totalWait (p.burst :: (mid ++ q.burst :: post)) := by
  rw [hasConvoyEffect_iff]
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

`HasConvoyEffect` judges a single dispatch decision on a fixed ready queue, so
it only applies to non-preemptive schedulers built from a `select` function,
and it cannot see jobs that arrive *after* a decision was made.

The online convoy effect instead watches a whole run: at some step of some
well-formed arrival stream, a job is waiting in `ready` with strictly less work
left than the job holding the CPU.  It applies to every scheduler -- like
`StarvationFreeRun`, it is stated over a run function, so Round Robin (which
steps an `RRState`) fits too.

* FCFS and RR have it on `convoyArrivalStream`, where both jobs are present
  from the start.
* Non-preemptive SJF has it on `lateConvoyArrivalStream`, where the short job
  arrives after the long one has been dispatched -- even though SJF has no
  (batch) convoy effect.
* SRTF never has it: preemption always hands the CPU to the job with least
  remaining work.

`remaining` rather than `burst` is the right measure here, because a preempted
job re-enters the queue with part of its burst already done.
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

/-! ## The batch convoy effect implies the online one -/

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

/-- **The batch convoy effect implies the online convoy effect.** If a
non-preemptive policy passes over a shorter job in some batch, then releasing
that batch at time 0 makes it do so in a real run: after step 0 the chosen job
holds the CPU while the shorter one waits. -/
theorem hasConvoyEffect_imp_online (select : List AperiodicProcess → Option AperiodicProcess)
    (h : HasConvoyEffect select) : HasOnlineConvoyEffect (stepNonPreemptive select) := by
  obtain ⟨ready, h_batch, p, hp, h_sel, q, hq, h_lt⟩ := (hasConvoyEffect_iff select).mp h
  have h_ne : q ≠ p := fun h_eq => by subst h_eq; omega
  rw [HasOnlineConvoyEffect, hasOnlineConvoyEffectRun_iff]
  refine ⟨batchStream ready, batchStream_wf h_batch, 0, p, ?_, q, ?_, ?_⟩
  · simp [runSteps, stepNonPreemptive, batchStream, h_sel]
  · simpa [runSteps, stepNonPreemptive, batchStream, h_sel] using
      (List.mem_erase_of_ne h_ne).mpr hq
  · -- in a batch nothing has run yet, so `remaining` is the burst
    rw [(h_batch.1 q hq).2, (h_batch.1 p hp).2]
    exact h_lt

end ConvoyEffect
