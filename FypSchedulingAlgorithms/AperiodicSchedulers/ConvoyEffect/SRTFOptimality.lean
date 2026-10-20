/-
Copyright (c) 2026 Choo Kye Yong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Choo Kye Yong
-/
import FypSchedulingAlgorithms.AperiodicSchedulers.ConvoyEffect.PreemptiveOptimality

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
orderings (`smallSum_le`), by `sum_take_sorted_le` from `OnlineOptimality`.
-/

namespace ConvoyEffect

open scoped List

/-! ## The sum of the `k` smallest entries -/

/-- The sum of the `k` smallest entries of `x` (all of them if `k ≥ x.length`). -/
def smallSum (x : List ℕ) (k : ℕ) : ℕ :=
  ((x.mergeSort fun a b => decide (a ≤ b)).take k).sum

/-- `mergeSort` sorts. -/
theorem mergeSort_pairwise_le (x : List ℕ) :
    (x.mergeSort fun a b => decide (a ≤ b)).Pairwise (· ≤ ·) :=
  (List.pairwise_mergeSort (fun a b c hab hbc => by simp at *; omega)
    (fun a b => by simp; omega) x).imp (by simp)

/-- **The `k` smallest entries sum to the least `k`-prefix sum** over all
orderings of the list. -/
theorem smallSum_le {x c : List ℕ} (h : x ~ c) (k : ℕ) : smallSum x k ≤ (c.take k).sum :=
  sum_take_sorted_le (mergeSort_pairwise_le x) ((List.mergeSort_perm _ _).trans h) k

/-- `smallSum` only depends on the entries, not their order. -/
theorem smallSum_perm {x y : List ℕ} (h : x ~ y) (k : ℕ) : smallSum x k = smallSum y k :=
  Nat.le_antisymm (smallSum_le (h.trans (List.mergeSort_perm y _).symm) k)
    (smallSum_le (h.symm.trans (List.mergeSort_perm x _).symm) k)

/-- A list of zeros has nothing to sum. -/
theorem smallSum_eq_zero {x : List ℕ} (h : ∀ u ∈ x, u = 0) (k : ℕ) : smallSum x k = 0 := by
  have := smallSum_le (List.Perm.refl x) k
  have h0 : (x.take k).sum = 0 :=
    List.sum_eq_zero_iff_forall_eq_nat.mpr fun u hu => h u (List.mem_of_mem_take hu)
  omega

/-- Changing one entry of a list, as seen from the rest of a permutation. -/
theorem perm_middle_replace {A R X : List ℕ} {v : ℕ} (h : A ++ v :: R ~ v :: X) (w : ℕ) :
    A ++ w :: R ~ w :: X :=
  List.perm_middle.trans ((List.perm_middle.symm.trans h).cons_inv.cons w)

/-- Lowering one entry by 1 lowers each prefix sum by at most 1. -/
theorem sum_take_sub_one_le (A R : List ℕ) (v k : ℕ) :
    ((A ++ v :: R).take k).sum ≤ ((A ++ (v - 1) :: R).take k).sum + 1 := by
  induction A generalizing k with
  | nil =>
    cases k with
    | zero => simp
    | succ k => simp only [List.nil_append, List.take_succ_cons, List.sum_cons]; omega
  | cons a A ih =>
    cases k with
    | zero => simp
    | succ k =>
      simp only [List.cons_append, List.take_succ_cons, List.sum_cons]
      have := ih k
      omega

/-- Lowering a positive entry inside the prefix lowers the prefix sum by exactly 1. -/
theorem sum_take_sub_one_eq (A R : List ℕ) {v k : ℕ} (hv : 0 < v) (hk : A.length < k) :
    ((A ++ (v - 1) :: R).take k).sum + 1 = ((A ++ v :: R).take k).sum := by
  induction A generalizing k with
  | nil =>
    obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by simp at hk; omega⟩
    simp only [List.nil_append, List.take_succ_cons, List.sum_cons]
    omega
  | cons a A ih =>
    obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by simp at hk; omega⟩
    simp only [List.cons_append, List.take_succ_cons, List.sum_cons]
    have := ih (k := k) (by simp at hk; omega)
    omega

/-- **A tick lowers the `k` smallest by at most 1**, whichever entry it lowers. -/
theorem smallSum_cons_le (v : ℕ) (X : List ℕ) (k : ℕ) :
    smallSum (v :: X) k ≤ smallSum ((v - 1) :: X) k + 1 := by
  set c := ((v - 1) :: X).mergeSort fun a b => decide (a ≤ b)
  have hc : c ~ (v - 1) :: X := List.mergeSort_perm _ _
  obtain ⟨A, B, hAB⟩ := List.append_of_mem (hc.symm.subset (List.mem_cons_self ..))
  rw [hAB] at hc
  calc smallSum (v :: X) k ≤ ((A ++ v :: B).take k).sum :=
        smallSum_le (perm_middle_replace hc v).symm k
    _ ≤ ((A ++ (v - 1) :: B).take k).sum + 1 := sum_take_sub_one_le A B v k
    _ = smallSum ((v - 1) :: X) k + 1 := by rw [← hAB]; rfl

/-- **SRTF's tick lowers the `k` smallest by exactly 1**, unless they are all 0
already: it lowers a least positive entry. -/
theorem smallSum_cons_sub_one {v : ℕ} {X : List ℕ} (hv : 0 < v)
    (h_min : ∀ u ∈ X, 0 < u → v ≤ u) (k : ℕ) :
    smallSum ((v - 1) :: X) k + 1 ≤ smallSum (v :: X) k ∨ smallSum ((v - 1) :: X) k = 0 := by
  set c := (v :: X).mergeSort fun a b => decide (a ≤ b) with hc_def
  have hc : c ~ v :: X := List.mergeSort_perm _ _
  have h_sorted : c.Pairwise (· ≤ ·) := mergeSort_pairwise_le _
  have h_split := List.take_append_drop k c
  by_cases hP : v ∈ c.take k
  · -- `v` is among the `k` smallest: lower it there
    left
    obtain ⟨A, B, hAB⟩ := List.append_of_mem hP
    have hc' : c = A ++ v :: (B ++ c.drop k) := by
      calc c = c.take k ++ c.drop k := h_split.symm
        _ = _ := by rw [hAB]; simp
    have hlen : A.length < k := by
      have := List.length_take_le k c
      rw [hAB] at this
      simp at this
      omega
    rw [hc'] at hc
    have h1 := smallSum_le (perm_middle_replace hc (v - 1)).symm k
    have h2 := sum_take_sub_one_eq A (B ++ c.drop k) hv hlen
    have h3 : smallSum (v :: X) k = ((A ++ v :: (B ++ c.drop k)).take k).sum := by
      rw [← hc']
      rfl
    omega
  · -- the `k` smallest are all 0, and `v` lies beyond them
    right
    have hv_c : v ∈ c := hc.symm.subset (List.mem_cons_self ..)
    have hv_drop : v ∈ c.drop k := by
      rw [← h_split] at hv_c
      exact (List.mem_append.mp hv_c).resolve_left hP
    have h_le : ∀ a ∈ c.take k, ∀ b ∈ c.drop k, a ≤ b := by
      have := h_sorted
      rw [← h_split] at this
      exact (List.pairwise_append.mp this).2.2
    have h_zero : ∀ u ∈ c.take k, u = 0 := by
      intro u hu
      have hu_ne : u ≠ v := fun h => hP (h ▸ hu)
      have hu_X : u ∈ X := by
        have := hc.subset (List.mem_of_mem_take hu)
        exact (List.mem_cons.mp this).resolve_left hu_ne
      have := h_le u hu v hv_drop
      by_contra h0
      have := h_min u hu_X (by omega)
      omega
    obtain ⟨A, B, hAB⟩ := List.append_of_mem hv_drop
    have hc' : c = (c.take k ++ A) ++ v :: B := by
      rw [List.append_assoc, ← hAB, h_split]
    have h_len : (c.take k).length = k := by
      have : c.drop k ≠ [] := by rw [hAB]; simp
      rw [List.length_take]
      have := List.drop_eq_nil_iff.not.mp this
      omega
    rw [hc'] at hc
    have h1 := smallSum_le (perm_middle_replace hc (v - 1)).symm k
    rw [List.append_assoc, List.take_append_of_le_length (by omega),
      List.take_of_length_le (by omega),
      List.sum_eq_zero_iff_forall_eq_nat.mpr h_zero] at h1
    omega

/-- **Releases preserve the majorisation**: adding the same entry to two lists
of the same length keeps "the `k` smallest sum to no more" for every `k`. -/
theorem smallSum_cons_mono {x y : List ℕ} (hlen : y.length = x.length)
    (h : ∀ j, smallSum y j ≤ smallSum x j) (b k : ℕ) :
    smallSum (b :: y) k ≤ smallSum (b :: x) k := by
  set c := (b :: x).mergeSort fun a b => decide (a ≤ b)
  have hc : c ~ b :: x := List.mergeSort_perm _ _
  obtain ⟨A, B, hAB⟩ := List.append_of_mem (hc.symm.subset (List.mem_cons_self ..))
  rw [hAB] at hc
  have hx : A ++ B ~ x := (List.perm_middle.symm.trans hc).cons_inv
  have hA : A.length ≤ x.length := by rw [← hx.length_eq]; simp
  have h_eq : smallSum (b :: x) k = ((A ++ b :: B).take k).sum := by rw [← hAB]; rfl
  set s := y.mergeSort fun a b => decide (a ≤ b)
  have hs : s ~ y := List.mergeSort_perm _ _
  rw [h_eq]
  by_cases hk : k ≤ A.length
  · -- the new entry is not among the `k` smallest of `b :: x`
    have h1 := smallSum_le ((hs.append_right [b]).trans (List.perm_append_singleton b y)).symm k
    rw [List.take_append_of_le_length (by rw [hs.length_eq]; omega)] at h1
    have h2 := smallSum_le hx.symm k
    rw [List.take_append_of_le_length hk] at h2
    rw [List.take_append_of_le_length hk]
    have := h k
    change smallSum (b :: y) k ≤ smallSum y k at h1
    omega
  · -- it is: the rest are the `k - 1` smallest of `x`, at best
    obtain ⟨m, rfl⟩ : ∃ m, k = A.length + 1 + m := ⟨k - A.length - 1, by omega⟩
    have h1 := smallSum_le (List.Perm.cons b hs).symm (A.length + 1 + m)
    rw [show A.length + 1 + m = (m + A.length) + 1 by omega, List.take_succ_cons,
      List.sum_cons] at h1
    have h2 := smallSum_le hx.symm (A.length + m)
    have h3 := h (A.length + m)
    rw [List.take_append, List.take_of_length_le (by omega), show A.length + m - A.length = m by
      omega] at h2
    rw [List.take_append, List.take_of_length_le (by omega),
      show A.length + 1 + m - A.length = m + 1 by omega, List.take_succ_cons, List.sum_append,
      List.sum_cons]
    rw [List.sum_append] at h2
    change smallSum (b :: y) (m + A.length + 1) ≤ b + smallSum y (m + A.length) at h1
    rw [show m + A.length + 1 = A.length + 1 + m by omega, Nat.add_comm m A.length] at h1
    omega

/-- Releases of a whole list preserve the majorisation. -/
theorem smallSum_append_mono {x y : List ℕ} (hlen : y.length = x.length)
    (h : ∀ j, smallSum y j ≤ smallSum x j) (L : List ℕ) (k : ℕ) :
    smallSum (y ++ L) k ≤ smallSum (x ++ L) k := by
  induction L generalizing x y with
  | nil => simpa using h k
  | cons b L ih =>
    have h' : ∀ j, smallSum (y ++ [b]) j ≤ smallSum (x ++ [b]) j := fun j => by
      rw [smallSum_perm (List.perm_append_singleton b y),
        smallSum_perm (List.perm_append_singleton b x)]
      exact smallSum_cons_mono hlen h b j
    have := ih (x := x ++ [b]) (y := y ++ [b]) (by simp [hlen]) h'
    simpa using this

/-- **Counting finished jobs.** If, for every `k`, the `k` smallest entries of
`y` sum to no more than those of `x` (two lists of the same length), then `y`
has no more positive entries than `x`: the `z` zeros of `x` force `z` zeros on
`y`. -/
theorem length_filter_pos_le {x y : List ℕ} (hlen : y.length = x.length)
    (h : ∀ k, smallSum y k ≤ smallSum x k) :
    (y.filter fun a => 0 < a).length ≤ (x.filter fun a => 0 < a).length := by
  set p : ℕ → Bool := fun a => decide (0 < a)
  have hx := (List.filter_append_perm p x).length_eq
  have hy := (List.filter_append_perm p y).length_eq
  simp only [List.length_append] at hx hy
  set z := (x.filter fun a => !p a).length
  -- the zeros of `x` come first in some ordering, so its `z` smallest sum to 0
  have hx0 : smallSum x z = 0 := by
    have := smallSum_le ((List.perm_append_comm.trans (List.filter_append_perm p x))).symm z
    rw [List.take_append_of_le_length le_rfl, List.take_of_length_le le_rfl,
      List.sum_eq_zero_iff_forall_eq_nat.mpr fun u hu => by
        simpa [p] using (List.mem_filter.mp hu).2] at this
    omega
  -- so the `z` smallest entries of `y` are zeros
  set s := y.mergeSort fun a b => decide (a ≤ b)
  have hs : s ~ y := List.mergeSort_perm _ _
  have hy0 : (s.take z).sum = 0 := by have := h z; change (s.take z).sum ≤ _ at this; omega
  have h_all : ∀ u ∈ s.take z, u = 0 := List.sum_eq_zero_iff_forall_eq_nat.mp hy0
  have h_take_len : (s.take z).length = z := by
    rw [List.length_take, hs.length_eq]
    omega
  have h_sub : (s.take z).filter (fun a => !p a) <+ s.filter (fun a => !p a) :=
    (List.take_sublist z s).filter _
  rw [List.filter_eq_self.mpr fun u hu => by simp [p, h_all u hu]] at h_sub
  have := h_sub.length_le
  rw [h_take_len, (hs.filter _).length_eq] at this
  change (y.filter p).length ≤ (x.filter p).length
  omega

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
