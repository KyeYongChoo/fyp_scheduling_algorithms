/-
Copyright (c) 2026 Choo Kye Yong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Choo Kye Yong
-/
import FypSchedulingAlgorithms.AperiodicSchedulers.ConvoyEffect.ConvoySpec
import FypSchedulingAlgorithms.AperiodicSchedulers.ConvoyEffect.ConvoyWitnesses
import FypSchedulingAlgorithms.AperiodicSchedulers.AperiodicStep
import FypSchedulingAlgorithms.AperiodicSchedulers.NonPreemptiveLemmas
import FypSchedulingAlgorithms.ProcessSimpLemmas
import FypSchedulingAlgorithms.SchedStateSimpLemmas

/-!
# SJF has no convoy effect -- but still pays for non-preemption

SJF always dispatches a job of least burst in the ready queue (`selectSJF_min`),
and in a non-preemptive run the waiting jobs are untouched, so their burst is
their remaining work.  So at every dispatch, on every well-formed stream, SJF
runs a shortest job: it has no convoy effect (`sjf_not_hasConvoyEffect`), and in
particular no batch convoy effect (`sjf_not_hasBatchConvoyEffect`).  The
argument works for any non-preemptive policy that always picks a shortest job,
even one that sees the whole state
(`nonPreemptiveOnline_runsShortestAtDispatch`).

It is still non-preemptive, though: on the late-arrival convoy a short job that
arrives after the long one has been dispatched waits until step `L`
(`sjf_late_convoy_waiting`).  That is not a convoy -- the short job was not in
`ready` when the choice was made (`sjf_late_convoy_runsShortestAtDispatch`) --
but it is the online convoy effect (`sjf_hasOnlineConvoyEffect`), and
`SRTFConvoy` shows preemption removes it.
-/

namespace ConvoyEffect

open NonPreemptive

/-- Invariant of the `foldl` inside `selectSJF`: the result is no longer than
the accumulator it started from, nor than any job it scanned. -/
theorem selectSJF_foldl_min (l : List AperiodicProcess) (init : Option AperiodicProcess)
    (p : AperiodicProcess)
    (h : l.foldl (fun best q =>
        match best with
        | none   => some q
        | some b => if q.burst < b.burst then some q else some b) init = some p) :
    (∀ b, init = some b → p.burst ≤ b.burst) ∧ ∀ q ∈ l, p.burst ≤ q.burst := by
  induction l generalizing init with
  | nil =>
    simp only [List.foldl_nil] at h
    subst h
    exact ⟨fun b hb => by cases hb; exact le_rfl, by simp⟩
  | cons x xs ih =>
    simp only [List.foldl_cons] at h
    obtain ⟨ih_acc, ih_rest⟩ := ih _ h
    cases init with
    | none =>
      have hx := ih_acc x rfl
      exact ⟨by simp, by
        intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · exact hx
        · exact ih_rest q hq⟩
    | some b =>
      by_cases hlt : x.burst < b.burst
      · have hx := ih_acc x (by simp [hlt])
        refine ⟨fun b' hb' => by cases hb'; omega, ?_⟩
        intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · exact hx
        · exact ih_rest q hq
      · have hb := ih_acc b (by simp [hlt])
        refine ⟨fun b' hb' => by cases hb'; exact hb, ?_⟩
        intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · omega
        · exact ih_rest q hq

/-- Invariant of the `foldl` inside `selectSJF`: the result is either the
accumulator it started from or one of the scanned jobs. -/
theorem selectSJF_foldl_mem (l : List AperiodicProcess) (init : Option AperiodicProcess)
    (p : AperiodicProcess)
    (h : l.foldl (fun best q =>
        match best with
        | none   => some q
        | some b => if q.burst < b.burst then some q else some b) init = some p) :
    init = some p ∨ p ∈ l := by
  induction l generalizing init with
  | nil => exact Or.inl h
  | cons x xs ih =>
    simp only [List.foldl_cons] at h
    rcases ih _ h with h_eq | h_mem
    · cases init with
      | none =>
        simp only [Option.some.injEq] at h_eq
        exact Or.inr (h_eq ▸ List.mem_cons_self ..)
      | some b =>
        by_cases hlt : x.burst < b.burst
        · simp only [hlt, ↓reduceIte, Option.some.injEq] at h_eq
          exact Or.inr (h_eq ▸ List.mem_cons_self ..)
        · simp only [hlt, ↓reduceIte] at h_eq
          exact Or.inl h_eq
    · exact Or.inr (List.mem_cons_of_mem _ h_mem)

/-- SJF only ever picks a job from the queue it is given. -/
theorem selectSJF_mem (l : List AperiodicProcess) (p : AperiodicProcess)
    (h : selectSJF l = some p) : p ∈ l :=
  (selectSJF_foldl_mem l none p h).resolve_left (by simp)

/-- SJF idles only when the queue is empty. -/
theorem selectSJF_none_imp_empty (l : List AperiodicProcess) (h : selectSJF l = none) :
    l = [] := by
  cases l with
  | nil => rfl
  | cons x xs =>
    exfalso
    -- once the fold holds some job it keeps holding one
    have key : ∀ (ys : List AperiodicProcess) (b : AperiodicProcess), ys.foldl (fun best q =>
        match best with
        | none   => some q
        | some b => if q.burst < b.burst then some q else some b) (some b) ≠ none := by
      intro ys
      induction ys with
      | nil => simp
      | cons y ys ih =>
        intro b
        simp only [List.foldl_cons]
        split_ifs <;> exact ih _
    exact key xs x h

/-- SJF picks a job of least burst from *any* queue, batch or not. -/
theorem selectSJF_min (l : List AperiodicProcess) (p : AperiodicProcess)
    (h : selectSJF l = some p) : ∀ q ∈ l, p.burst ≤ q.burst :=
  (selectSJF_foldl_min l none p h).2

/-- **SJF never inverts on a batch**: the job it dispatches is no longer than
any job in the ready queue. -/
theorem sjf_noInversion : RunsShortestProcessBatch selectSJF := fun ready _ p _ h =>
  selectSJF_min ready p h

/-- SJF does not have the batch convoy effect. -/
theorem sjf_not_hasBatchConvoyEffect : ¬ HasBatchConvoyEffect selectSJF :=
  not_not_intro sjf_noInversion

/-- **Shortest-first non-preemptive policies run the shortest job at every
dispatch.** If an online non-preemptive policy only picks waiting jobs, and
always one of least burst, then on every well-formed stream (arrivals at any
time) no waiting job has less work left than the job it dispatches.  Reason: a
dispatched job was the policy's choice from the queue (a job that keeps the CPU
keeps its id), and in a non-preemptive run waiting jobs are untouched. -/
theorem nonPreemptiveOnline_runsShortestAtDispatch
    (select : SchedState → Option AperiodicProcess)
    (h_mem : ∀ s p, select s = some p → p ∈ s.ready)
    (h_short : ∀ s p, select s = some p → ∀ q ∈ s.ready, p.burst ≤ q.burst) :
    RunsShortestAtDispatchRun (fun as => runSteps as (stepNonPreemptiveOnline select)) := by
  intro as h_wf t p h_disp q hq
  obtain ⟨h_run, h_new⟩ := h_disp
  -- the state step `t` starts from: the previous state with this step's arrivals
  obtain ⟨s, h_eq, h_s_new, h_s_fresh⟩ : ∃ s : SchedState,
      runSteps as (stepNonPreemptiveOnline select) t = stepNonPreemptiveOnline select s ∧
      s.running.map (·.id) ≠ some p.id ∧ ∀ r ∈ s.ready, r.remaining = r.burst := by
    cases t with
    | zero =>
      refine ⟨{ SchedStateMethods.init with ready := as 0 }, rfl, by simp, ?_⟩
      intro r hr
      exact h_wf.fresh r 0 (by simpa using hr)
    | succ t =>
      refine ⟨{ runSteps as (stepNonPreemptiveOnline select) t with
        ready := (runSteps as (stepNonPreemptiveOnline select) t).ready ++ as (t + 1) }, rfl,
        h_new t rfl, ?_⟩
      intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · exact nonPreemptiveOnline_ready_fresh select as h_wf t r hr
      · exact h_wf.fresh r _ hr
  simp only at h_run hq
  rw [h_eq] at h_run hq
  obtain ⟨h_sel, h_ready⟩ := stepNonPreemptiveOnline_dispatch_cases select s h_run h_s_new
  rw [h_ready] at hq
  have hp := h_mem s p h_sel
  have hq' := List.mem_of_mem_erase hq
  rw [h_s_fresh p hp, h_s_fresh q hq']
  exact h_short s p h_sel q hq'

/-- **SJF runs the shortest job at every dispatch**, on every well-formed
stream. -/
theorem sjf_runsShortestAtDispatch :
    RunsShortestAtDispatchRun (fun as => runSteps as stepSJF) :=
  nonPreemptiveOnline_runsShortestAtDispatch (fun s => selectSJF s.ready)
    (fun _ p h => selectSJF_mem _ p h) (fun _ p h => selectSJF_min _ p h)

/-- **SJF does not have the convoy effect.** -/
theorem sjf_not_hasConvoyEffect : ¬ HasConvoyEffect stepSJF :=
  not_not_intro sjf_runsShortestAtDispatch

/-- While `t < L`, non-preemptive SJF is still running the long job, and from
time 1 the short job is waiting behind it. -/
theorem sjf_late_convoy_invariant (L : ℕ) (hL : 0 < L) (t : ℕ) (ht : t < L) :
    (runSteps (lateConvoyArrivalStream L hL) stepSJF t).running =
        some { longJob L hL with remaining := L - t } ∧
      (runSteps (lateConvoyArrivalStream L hL) stepSJF t).ready =
        if t = 0 then [] else [lateShortJob] := by
  induction t with
  | zero =>
    simp [runSteps, stepSJF, stepNonPreemptive, selectSJF, lateConvoyArrivalStream,
      SchedStateMethods.init, longJob]
  | succ t ih =>
    obtain ⟨ih_running, ih_ready⟩ := ih (by omega)
    -- `stepSJF` must stay folded here, or the IH rewrite targets disappear
    simp only [runSteps, ih_ready, ih_running]
    -- the long job still has ticks left after this step, so SJF keeps running it
    rcases t with _ | t
    · simp [stepSJF, stepNonPreemptive, lateConvoyArrivalStream, longJob,
        show ¬ L - 1 = 0 by omega]
    · simp [stepSJF, stepNonPreemptive, lateConvoyArrivalStream, longJob,
        show ¬ L - (t + 1) - 1 = 0 by omega]
      omega

/-- **Non-preemptive SJF cannot escape the late-arrival convoy**: from the
moment it arrives until step `L`, the short job waits in the ready queue. -/
theorem sjf_late_convoy_waiting (L : ℕ) (hL : 0 < L) (t : ℕ) (h1 : 1 ≤ t) (ht : t < L) :
    lateShortJob ∈ (runSteps (lateConvoyArrivalStream L hL) stepSJF t).ready := by
  rw [(sjf_late_convoy_invariant L hL t ht).2, if_neg (by omega)]
  exact List.mem_singleton_self _

/-- **The late-arrival convoy is not a convoy for SJF**: at every step at which
SJF dispatches a job on `lateConvoyArrivalStream`, no shorter job is waiting.
(The short job arrives only after the long one has been dispatched.) -/
theorem sjf_late_convoy_runsShortestAtDispatch (L : ℕ) (hL : 0 < L) (t : ℕ)
    (p : AperiodicProcess)
    (h : DispatchesAt (fun as => runSteps as stepSJF) (lateConvoyArrivalStream L hL) t p) :
    ∀ q ∈ (runSteps (lateConvoyArrivalStream L hL) stepSJF t).ready,
      p.remaining ≤ q.remaining :=
  sjf_runsShortestAtDispatch _ (lateConvoyArrivalStream_wf L hL) t p h

/-- **Non-preemptive SJF has the online convoy effect**, although it has no
convoy effect: on the late-arrival convoy with `L = 3`, at step 1 the short job
(1 tick) waits behind the long job (2 ticks left). -/
theorem sjf_hasOnlineConvoyEffect : HasOnlineConvoyEffect stepSJF := by
  rw [HasOnlineConvoyEffect, hasOnlineConvoyEffectRun_iff]
  obtain ⟨h_running, h_ready⟩ := sjf_late_convoy_invariant 3 (by omega) 1 (by omega)
  exact ⟨_, lateConvoyArrivalStream_wf 3 (by omega), 1, _, h_running, lateShortJob,
    by simp [h_ready], by simp [lateShortJob]⟩

/-- **The online convoy effect does not imply the convoy effect.** SJF is the
counterexample: it never dispatches a job while a shorter one is waiting, yet a
short job that arrives after SJF has committed to a long one still waits. -/
theorem online_convoy_not_imp_convoy :
    ¬ ∀ step, HasOnlineConvoyEffect step → HasConvoyEffect step :=
  fun h => sjf_not_hasConvoyEffect (h stepSJF sjf_hasOnlineConvoyEffect)

/-- Nor does it imply the batch convoy effect (same counterexample). -/
theorem online_convoy_not_imp_batch_convoy :
    ¬ ∀ select, HasOnlineConvoyEffect (stepNonPreemptive select) → HasBatchConvoyEffect select :=
  fun h => sjf_not_hasBatchConvoyEffect (h selectSJF sjf_hasOnlineConvoyEffect)

end ConvoyEffect
