/-
Copyright (c) 2026 Choo Kye Yong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Choo Kye Yong
-/
import FypSchedulingAlgorithms.AperiodicSchedulers.ConvoyEffect.PreemptiveOptimality
import FypSchedulingAlgorithms.ListLemmas

/-!
# SRTF waits least among all admissible schedules

`PreemptiveOptimality` states the classic result of Schrage (1968) as
`SRTFMinimisesWait`; this file proves it (`srtfMinimisesWait`).  On every
well-formed stream without repeats, at every horizon `T`, SRTF's run waits no
longer than any admissible schedule (`Schedules`): preemptive or not, idling or
not, online or clairvoyant.  So, unlike the non-preemptive case
(`no_optimal_online_nonPreemptive`), there is an online scheduler that is
optimal on every stream, and it is SRTF; in particular it waits no longer than
any online non-preemptive policy (`srtf_le_onlineRun`) or any other
job-conserving step function (`srtf_le_runWait_of_conservesJobs`).

**Scope.**  The result holds inside the discrete model of `Schedules`: the
shared tick convention of `Step`, no context-switch cost, and streams without
repeats (`NoRepeats`).  "Optimal" means against every admissible schedule.  The
corollaries do not cover Round Robin, which has no bridge for its `RRState`.
Optimality is weak (`≤`): strictly less waiting is only claimed on the witness
streams of `PreemptiveOptimality` (`srtf_beats_online_nonPreemptive`).

**Stronger, pointwise.**  After every step SRTF has no more unfinished jobs
than any admissible schedule (`srtf_unfinished_le`), and so no more waiting
jobs (`srtf_ready_le_waiting`): every schedule leaves all its unfinished jobs
but at most one waiting, SRTF exactly all but one.  Summing over the steps gives
the wait at every horizon, with no need to count busy steps.

**How.**  Compare the remaining works of the released jobs (`remWork`) through
`smallSum x k`, the sum of the `k` smallest entries of `x`.  After every step and
for every `k`, SRTF's is no larger (`srtf_majorises`), by induction on the step:

* a tick of any schedule lowers `smallSum` by at most 1 (`smallSum_cons_le`);
* SRTF's tick, on a job of least remaining work (`srtf_tick_min`, from
  `srtf_run_invariant`), lowers it by exactly 1 unless the `k` smallest are all
  0 already (`smallSum_cons_sub_one`); when SRTF idles everything released is
  finished (`srtf_remWork_of_none`);
* releases add the same fresh jobs to both sides, which keeps the comparison
  (`smallSum_cons_mono`, `smallSum_append_mono`).

A schedule with `z` finished jobs has `smallSum _ z = 0`, so SRTF has at least
`z` finished jobs too (`length_filter_pos_le`).  `smallSum` is `≤`-minimal over
orderings (`smallSum_le`), by `sum_take_sorted_le`.  `smallSum` and its lemmas
are in `ListLemmas`.
-/

namespace ConvoyEffect

open scoped List

/-! ## Remaining work under a schedule -/

/-- The remaining work of each released job after step `t` of `σ`: its burst
less the ticks it has had (0 once it is finished). -/
def remWork (arrival_stream : ℕ → List AperiodicProcess) (σ : Schedule) (t : ℕ) : List ℕ :=
  (arrivedBy arrival_stream t).map fun p => p.burst - ticksBefore σ p.id t

/-- The remaining work of the jobs released by time `t` once step `t + 1` has
ticked `σ`'s job of step `t`, before the releases of time `t + 1`. -/
def remWorkAfter (arrival_stream : ℕ → List AperiodicProcess) (σ : Schedule) (t : ℕ) :
    List ℕ :=
  (arrivedBy arrival_stream t).map fun p => p.burst - ticksBefore σ p.id (t + 1)

/-- The unfinished jobs are the positive entries of the remaining work. -/
theorem length_unfinished_eq (arrival_stream : ℕ → List AperiodicProcess) (σ : Schedule)
    (t : ℕ) : (unfinished arrival_stream σ t).length =
      ((remWork arrival_stream σ t).filter fun a => 0 < a).length := by
  unfold unfinished remWork
  rw [List.filter_map, List.length_map]
  congr 1
  refine List.filter_congr fun p _ => ?_
  simp only [Function.comp_apply, decide_eq_decide]
  omega

section Admissible

variable {arrival_stream : ℕ → List AperiodicProcess} (h_wf : WellFormedStream arrival_stream)
  (h_rep : NoRepeats arrival_stream)
include h_wf

/-- An admissible schedule has not run a job before its release. -/
theorem ticksBefore_of_mem {σ : Schedule} (h_adm : IsAdmissible arrival_stream σ) {t : ℕ}
    {p : AperiodicProcess} (hp : p ∈ arrival_stream t) : ticksBefore σ p.id t = 0 := by
  refine ticksBefore_eq_zero fun t' ht' h_eq => ?_
  obtain ⟨q, hq, h_id, -⟩ := h_adm t' _ h_eq
  obtain ⟨t'', ht'', hq⟩ := mem_arrivedBy.mp hq
  have := (h_wf.unique q p t'' t hq hp h_id).1
  omega

/-- One step of remaining work: the tick, then the releases, fresh. -/
theorem remWork_succ {σ : Schedule} (h_adm : IsAdmissible arrival_stream σ) (t : ℕ) :
    remWork arrival_stream σ (t + 1) =
      remWorkAfter arrival_stream σ t ++ (arrival_stream (t + 1)).map (·.burst) := by
  unfold remWork remWorkAfter
  rw [arrivedBy_succ, List.map_append]
  congr 1
  exact List.map_congr_left fun p hp => by simp [ticksBefore_of_mem h_wf h_adm hp]

omit h_wf in
/-- An idle step changes no remaining work. -/
theorem remWorkAfter_of_none {σ : Schedule} {t : ℕ} (h : σ t = none) :
    remWorkAfter arrival_stream σ t = remWork arrival_stream σ t :=
  List.map_congr_left fun p _ => by rw [ticksBefore_succ_of_ne (by simp [h])]

include h_rep in
/-- **A tick of an admissible schedule** lowers the remaining work `v > 0` of the
job it runs by one and leaves the others, `X`, alone. -/
theorem remWork_tick {σ : Schedule} (h_adm : IsAdmissible arrival_stream σ) {t i : ℕ}
    (h : σ t = some i) :
    ∃ p0 ∈ arrivedBy arrival_stream t, p0.id = i ∧ ∃ X : List ℕ,
      remWork arrival_stream σ t ~ (p0.burst - ticksBefore σ i t) :: X ∧
      remWorkAfter arrival_stream σ t ~ (p0.burst - ticksBefore σ i t - 1) :: X ∧
      0 < p0.burst - ticksBefore σ i t ∧
      ∀ u ∈ X, ∃ q ∈ arrivedBy arrival_stream t, q.id ≠ i ∧ u = q.burst - ticksBefore σ q.id t := by
  obtain ⟨p0, hp0, rfl, h_lt⟩ := h_adm t i h
  have h_nd := arrivedBy_nodup h_wf h_rep t
  have h_perm := List.perm_cons_erase hp0
  have h_ne : ∀ q ∈ (arrivedBy arrival_stream t).erase p0, q.id ≠ p0.id := fun q hq h_id =>
    ((h_nd.mem_erase_iff).mp hq).1 (arrivedBy_id_inj h_wf (List.mem_of_mem_erase hq) hp0 h_id)
  refine ⟨p0, hp0, rfl, ((arrivedBy arrival_stream t).erase p0).map
    fun q => q.burst - ticksBefore σ q.id t, ?_, ?_, by omega, ?_⟩
  · simpa [remWork] using h_perm.map fun q => q.burst - ticksBefore σ q.id t
  · refine (h_perm.map _).trans ?_
    rw [List.map_cons]
    have h_tick : ticksBefore σ p0.id (t + 1) = ticksBefore σ p0.id t + 1 := by
      simp [ticksBefore_succ, h]
    rw [h_tick, show p0.burst - (ticksBefore σ p0.id t + 1) =
      p0.burst - ticksBefore σ p0.id t - 1 by omega]
    refine List.Perm.cons _ (List.Perm.of_eq (List.map_congr_left fun q hq => ?_))
    rw [ticksBefore_succ_of_ne (by rw [h]; simpa using (h_ne q hq).symm)]
  · intro u hu
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hu
    exact ⟨q, List.mem_of_mem_erase hq, h_ne q hq, rfl⟩

end Admissible

/-! ## SRTF's ticks -/

section SRTF

variable {arrival_stream : ℕ → List AperiodicProcess} (h_wf : WellFormedStream arrival_stream)
  (h_rep : NoRepeats arrival_stream)
include h_wf h_rep

/-- When SRTF idles, every released job is finished. -/
theorem srtf_remWork_of_none {t : ℕ} (h : runSchedule stepSRTF arrival_stream t = none) :
    ∀ u ∈ remWork arrival_stream (runSchedule stepSRTF arrival_stream) t, u = 0 := by
  have h_run : (runSteps arrival_stream stepSRTF t).running = none := by
    simpa [runSchedule] using h
  have h_sys := inSystem_perm stepSRTF_conservesJobs h_wf h_rep t
  rw [inSystem, srtf_ready_nil_of_idle arrival_stream t h_run, h_run] at h_sys
  have h_nil := List.eq_nil_of_length_eq_zero (by simpa using h_sys.length_eq.symm)
  intro u hu
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hu
  have : p ∉ unfinished arrival_stream (runSchedule stepSRTF arrival_stream) t := by
    rw [h_nil]; exact List.not_mem_nil
  simp only [unfinished, List.mem_filter, hp, true_and, decide_eq_true_eq] at this
  omega

/-- **SRTF ticks a job of least remaining work**: in the schedule's terms, no
other unfinished job has less work left than the one SRTF runs. -/
theorem srtf_tick_min {t i : ℕ} (h : runSchedule stepSRTF arrival_stream t = some i)
    {p0 : AperiodicProcess} (hp0 : p0 ∈ arrivedBy arrival_stream t) (h_id : p0.id = i)
    {q : AperiodicProcess} (hq : q ∈ arrivedBy arrival_stream t) (hq_id : q.id ≠ i)
    (hq_pos : 0 < q.burst - ticksBefore (runSchedule stepSRTF arrival_stream) q.id t) :
    p0.burst - ticksBefore (runSchedule stepSRTF arrival_stream) i t ≤
      q.burst - ticksBefore (runSchedule stepSRTF arrival_stream) q.id t := by
  set σ := runSchedule stepSRTF arrival_stream
  obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp h
  have h_inv := inSystem_perm stepSRTF_conservesJobs h_wf h_rep t
  obtain ⟨q', hq', hb'⟩ := List.mem_map.mp
    (h_inv.subset (show b ∈ inSystem _ by simp [inSystem, hb]))
  have h_eq : q' = p0 :=
    arrivedBy_id_inj h_wf (List.mem_of_mem_filter hq') hp0 (by rw [h_id, ← hb']; rfl)
  subst h_eq
  have hq_unf : q ∈ unfinished arrival_stream σ t :=
    List.mem_filter.mpr ⟨hq, by simp only [decide_eq_true_eq]; omega⟩
  have hq_sys : jobAt σ t q ∈ inSystem (runSteps arrival_stream stepSRTF t) :=
    h_inv.symm.subset (List.mem_map_of_mem hq_unf)
  have hq_ready : jobAt σ t q ∈ (runSteps arrival_stream stepSRTF t).ready := by
    simp only [inSystem, hb, Option.toList_some, List.mem_append, List.mem_singleton] at hq_sys
    refine hq_sys.resolve_right fun h_eq => hq_id ?_
    rw [← h_eq]
    rfl
  have := ((srtf_run_invariant arrival_stream h_wf t).2 b hb).2 _ hq_ready
  rw [← hb'] at this
  rw [← h_id]
  exact this

end SRTF

/-! ## SRTF majorises every admissible schedule -/

/-- **The majorisation invariant.** After every step, for every `k`, the `k`
smallest remaining works of SRTF's schedule sum to no more than those of any
admissible schedule. -/
theorem srtf_majorises {arrival_stream : ℕ → List AperiodicProcess}
    (h_wf : WellFormedStream arrival_stream) (h_rep : NoRepeats arrival_stream)
    {σ : Schedule} (h_adm : IsAdmissible arrival_stream σ) (t k : ℕ) :
    smallSum (remWork arrival_stream (runSchedule stepSRTF arrival_stream) t) k ≤
      smallSum (remWork arrival_stream σ t) k := by
  set σs := runSchedule stepSRTF arrival_stream
  have h_adms : IsAdmissible arrival_stream σs :=
    runSchedule_isAdmissible stepSRTF_conservesJobs h_wf h_rep
  induction t generalizing k with
  | zero => simp [remWork]
  | succ t ih =>
    rw [remWork_succ h_wf h_adms, remWork_succ h_wf h_adm]
    refine smallSum_append_mono (by simp [remWorkAfter]) (fun j => ?_) _ k
    cases hs : σs t with
    | none =>
      rw [remWorkAfter_of_none hs, smallSum_eq_zero (srtf_remWork_of_none h_wf h_rep hs) j]
      exact Nat.zero_le _
    | some i =>
      obtain ⟨p0, hp0, h_id, X, h_rem, h_after, h_pos, hX⟩ := remWork_tick h_wf h_rep h_adms hs
      have h_min : ∀ u ∈ X, 0 < u → p0.burst - ticksBefore σs i t ≤ u := by
        intro u hu hu_pos
        obtain ⟨q, hq, hq_id, rfl⟩ := hX u hu
        exact srtf_tick_min h_wf h_rep hs hp0 h_id hq hq_id hu_pos
      have h_srtf := smallSum_cons_sub_one h_pos h_min j
      rw [← smallSum_perm h_after, ← smallSum_perm h_rem] at h_srtf
      have ih_j := ih j
      cases hσ : σ t with
      | none =>
        rw [remWorkAfter_of_none hσ]
        omega
      | some i' =>
        obtain ⟨p1, -, -, Y, h_rem', h_after', -, -⟩ := remWork_tick h_wf h_rep h_adm hσ
        have h_tick := smallSum_cons_le (p1.burst - ticksBefore σ i' t) Y j
        rw [← smallSum_perm h_after', ← smallSum_perm h_rem'] at h_tick
        omega

/-- **SRTF has the fewest unfinished jobs** after every step, among all
admissible schedules (`N(t)` is pointwise minimal). -/
theorem srtf_unfinished_le {arrival_stream : ℕ → List AperiodicProcess}
    (h_wf : WellFormedStream arrival_stream) (h_rep : NoRepeats arrival_stream)
    {σ : Schedule} (h_adm : IsAdmissible arrival_stream σ) (t : ℕ) :
    (unfinished arrival_stream (runSchedule stepSRTF arrival_stream) t).length ≤
      (unfinished arrival_stream σ t).length := by
  rw [length_unfinished_eq, length_unfinished_eq]
  exact length_filter_pos_le (by simp [remWork]) (srtf_majorises h_wf h_rep h_adm t)

/-- **SRTF has the fewest waiting jobs** after every step, among all admissible
schedules. -/
theorem srtf_ready_le_waiting {arrival_stream : ℕ → List AperiodicProcess}
    (h_wf : WellFormedStream arrival_stream) (h_rep : NoRepeats arrival_stream)
    {σ : Schedule} (h_adm : IsAdmissible arrival_stream σ) (t : ℕ) :
    (runSteps arrival_stream stepSRTF t).ready.length ≤ (waiting arrival_stream σ t).length := by
  rw [srtf_ready_length h_wf h_rep t]
  have := srtf_unfinished_le h_wf h_rep h_adm t
  have := length_unfinished_sub_one_le h_wf h_rep h_adm t
  omega

/-- **SRTF waits least among all admissible schedules** (Schrage 1968), on every
well-formed stream without repeats, at every horizon. -/
theorem srtfMinimisesWait : SRTFMinimisesWait := by
  intro arrival_stream h_wf h_rep σ h_adm T
  unfold runWait schedWait
  exact sum_map_le_sum_map _ fun t _ => srtf_ready_le_waiting h_wf h_rep h_adm t

/-- **SRTF waits no longer than any online non-preemptive policy**, on every
well-formed stream without repeats, at every horizon. -/
theorem srtf_le_onlineRun {select : SchedState → Option AperiodicProcess}
    (h_mem : IsOnlinePolicy select) {arrival_stream : ℕ → List AperiodicProcess}
    (h_wf : WellFormedStream arrival_stream) (h_rep : NoRepeats arrival_stream) (T : ℕ) :
    runWait (runSteps · stepSRTF) arrival_stream T ≤ runWait (onlineRun select) arrival_stream T :=
  srtf_le_onlineRun_of srtfMinimisesWait h_mem h_wf h_rep T

/-- **SRTF waits no longer than any job-conserving scheduler** (every preemptive
priority scheduler, every online non-preemptive policy), on every well-formed
stream without repeats, at every horizon. -/
theorem srtf_le_runWait_of_conservesJobs {step : SchedState → SchedState}
    (h_step : ConservesJobs step) {arrival_stream : ℕ → List AperiodicProcess}
    (h_wf : WellFormedStream arrival_stream) (h_rep : NoRepeats arrival_stream) (T : ℕ) :
    runWait (runSteps · stepSRTF) arrival_stream T ≤
      runWait (runSteps · step) arrival_stream T := by
  rw [runWait_eq_schedWait h_step h_wf h_rep]
  exact srtfMinimisesWait arrival_stream h_wf h_rep _
    (runSchedule_isAdmissible h_step h_wf h_rep) T

end ConvoyEffect
