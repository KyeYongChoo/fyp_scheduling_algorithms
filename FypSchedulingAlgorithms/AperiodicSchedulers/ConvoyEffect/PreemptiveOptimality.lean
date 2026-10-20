/-
Copyright (c) 2026 Choo Kye Yong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Choo Kye Yong
-/
import FypSchedulingAlgorithms.AperiodicSchedulers.ConvoyEffect.Schedules
import FypSchedulingAlgorithms.AperiodicSchedulers.ConvoyEffect.OnlineOptimality
import FypSchedulingAlgorithms.AperiodicSchedulers.ConvoyEffect.SRTFConvoy

/-!
# Preemption removes the impossibility

`OnlineImpossibility` shows that no online non-preemptive policy waits least on
every stream: at time 0 a policy facing the 4-tick job of `streamA`/`streamB`
must either idle (and lose on `streamA`, where nothing else comes) or dispatch it
(and lose on `streamB`, where a unit job arrives at time 1 and waits behind it).
A preemptive scheduler need not choose: SRTF dispatches the long job and, when
the unit job arrives, preempts it.

**What is proved** (against the admissible schedules of `Schedules`, which
include every preemptive or non-preemptive, online or clairvoyant way of running
the jobs, with the cost `schedWait`, equal to `runWait` on runs):

* SRTF waits 0 on `streamA` at every horizon (`srtf_runWait_streamA`) and 1 on
  `streamB` at every horizon `T ≥ 2` (`srtf_runWait_streamB`);
* no admissible schedule waits less on either stream, at any horizon
  (`srtf_le_schedWait_streamA`, `srtf_le_schedWait_streamB`): on `streamB` both
  jobs are unfinished after step 1, whatever the schedule, so one of them waits
  (`one_le_schedWait_streamB`);
* so SRTF strictly beats *every* online non-preemptive policy on `streamA` or on
  `streamB`, at every horizon `T ≥ 4` (`srtf_beats_online_nonPreemptive`), and
  those policies' runs are themselves admissible schedules
  (`onlineRun_isAdmissible`, `runWait_onlineRun_eq_schedWait`).

The concrete values come from the bridge rather than from unfolding the run:
SRTF never idles while a job waits (`srtf_ready_nil_of_idle`), so it leaves all
its unfinished jobs but one waiting (`srtf_ready_length`), and counting the
unfinished jobs of the schedule is enough.

**The general theorem** (`SRTFMinimisesWait`, Schrage 1968): on every
well-formed stream without repeats, at every horizon, SRTF waits no longer than
any admissible schedule.  It is stated here as a proposition and proved in
`SRTFOptimality` (`srtfMinimisesWait`); `srtf_le_onlineRun_of` derives from it
that SRTF waits no longer than any online non-preemptive policy on every
stream, the contrast with `no_optimal_online_nonPreemptive`.
-/

namespace ConvoyEffect

open Preemptive

/-! ## SRTF never idles while a job waits -/

/-- A preemptive step leaves the CPU idle only when nothing is waiting. -/
theorem stepPreemptive_ready_nil_of_idle (f : AperiodicProcess → ℚ) (s : SchedState)
    (h : (stepPreemptive AperiodicProcess f s).running = none) :
    (stepPreemptive AperiodicProcess f s).ready = [] := by
  unfold stepPreemptive at *
  rcases hr : s.running with _ | b <;> simp only [hr] at h ⊢
  · cases h_sel : selectByPriority f s.ready <;> simp only [h_sel] at h ⊢
    · exact selectByPriority_eq_none f _ h_sel
    · simp at h
  · simp only [AperiodicProcess.process_tick, AperiodicProcess.process_remaining] at h ⊢
    split_ifs at h ⊢ <;> cases h_sel : selectByPriority f s.ready <;> simp only [h_sel] at h ⊢
    · exact selectByPriority_eq_none f _ h_sel
    all_goals (try split_ifs at h ⊢) <;> simp at h

/-- SRTF conserves jobs, so its runs are admissible schedules. -/
theorem stepSRTF_conservesJobs : ConservesJobs stepSRTF := stepPreemptive_conservesJobs _

/-- In an SRTF run the CPU is idle only when nothing is waiting. -/
theorem srtf_ready_nil_of_idle (arrival_stream : ℕ → List AperiodicProcess) (t : ℕ)
    (h : (runSteps arrival_stream stepSRTF t).running = none) :
    (runSteps arrival_stream stepSRTF t).ready = [] := by
  rw [runSteps_eq_step_stateBefore] at *
  exact stepPreemptive_ready_nil_of_idle _ _ h

/-- **SRTF leaves waiting all its unfinished jobs but one**: the one it runs. -/
theorem srtf_ready_length {arrival_stream : ℕ → List AperiodicProcess}
    (h_wf : WellFormedStream arrival_stream) (h_rep : NoRepeats arrival_stream) (t : ℕ) :
    (runSteps arrival_stream stepSRTF t).ready.length =
      (unfinished arrival_stream (runSchedule stepSRTF arrival_stream) t).length - 1 := by
  have := (inSystem_perm stepSRTF_conservesJobs h_wf h_rep t).length_eq
  simp only [inSystem, List.length_append, List.length_map] at this
  cases h : (runSteps arrival_stream stepSRTF t).running
  · rw [srtf_ready_nil_of_idle arrival_stream t h] at this ⊢
    simp only [List.length_nil, h, Option.toList_none, Nat.add_zero] at this ⊢
    omega
  · simp_all
    omega

/-! ## The witness streams again -/

/-- Stream A lists no job twice. -/
theorem streamA_noRepeats : NoRepeats streamA := by
  intro t
  cases t <;> simp [streamA, batchStream]

/-- Stream B lists no job twice. -/
theorem streamB_noRepeats : NoRepeats streamB := by
  intro t
  rcases t with _ | _ | t <;> simp [streamB, lateConvoyArrivalStream]

/-- The long job is all that stream A ever releases. -/
theorem arrivedBy_streamA (t : ℕ) : arrivedBy streamA t = [longJob4] := by
  induction t with
  | zero => rfl
  | succ t ih => rw [arrivedBy_succ, ih, streamA_nil _ (by omega), List.append_nil]

/-- From time 1 on, stream B has released both of its jobs. -/
theorem arrivedBy_streamB (t : ℕ) : arrivedBy streamB (t + 1) = [longJob4, lateShortJob] := by
  induction t with
  | zero => rfl
  | succ t ih => rw [arrivedBy_succ, ih, streamB_nil _ (by omega), List.append_nil]

/-- **Both jobs of stream B are unfinished after step 1**, whatever the schedule:
the unit job cannot have run, since it was not released at time 0, and the long
job has had at most one of its four ticks. -/
theorem unfinished_streamB_one {σ : Schedule} (h_adm : IsAdmissible streamB σ) :
    (unfinished streamB σ 1).length = 2 := by
  have h0 : σ 0 ≠ some 1 := fun h => by
    obtain ⟨p, hp, h_id, -⟩ := h_adm 0 1 h
    simp only [arrivedBy_zero, streamB, lateConvoyArrivalStream, List.mem_singleton] at hp
    subst hp
    simp [longJob] at h_id
  have h_long : ticksBefore σ 0 1 < 4 := by
    rw [ticksBefore_succ]
    split <;> simp
  have h_unit : ticksBefore σ 1 1 < 1 := by
    rw [ticksBefore_succ]
    simp [h0]
  unfold unfinished
  rw [arrivedBy_streamB 0]
  simp [longJob, lateShortJob, h_long, h_unit]

/-- Once the unit job of stream B has had its tick, at most the long job is
unfinished. -/
theorem unfinished_streamB_le_one {σ : Schedule} {t : ℕ} (h : 1 ≤ ticksBefore σ 1 (t + 1)) :
    (unfinished streamB σ (t + 1)).length ≤ 1 := by
  unfold unfinished
  rw [arrivedBy_streamB t]
  simp only [List.filter_cons, List.filter_nil]
  have : ¬ ticksBefore σ lateShortJob.id (t + 1) < lateShortJob.burst := by
    simp [lateShortJob]
    omega
  simp only [this, decide_false, Bool.false_eq_true, ↓reduceIte]
  split <;> simp

/-! ## SRTF on the witness streams -/

/-- **SRTF waits 0 on stream A**, at every horizon: it runs the long job at once. -/
theorem srtf_runWait_streamA (T : ℕ) : runWait (runSteps · stepSRTF) streamA T = 0 := by
  unfold runWait
  refine List.sum_eq_zero_iff_forall_eq_nat.mpr fun x hx => ?_
  obtain ⟨t, -, rfl⟩ := List.mem_map.mp hx
  dsimp only
  rw [srtf_ready_length streamA_wf streamA_noRepeats t]
  have : (unfinished streamA (runSchedule stepSRTF streamA) t).length ≤ 1 :=
    (List.length_filter_le _ _).trans (by simp [arrivedBy_streamA])
  omega

/-- On stream B, SRTF puts the unit job on the CPU after step 1, preempting the
long job. -/
theorem srtf_streamB_schedule_one : runSchedule stepSRTF streamB 1 = some 1 := by
  simp [runSchedule, streamB, (srtf_late_convoy_completes 4 (by omega)).1, lateShortJob]

/-- After step 0 of stream B, SRTF has the long job on the CPU and nobody
waits. -/
theorem srtf_streamB_ready_zero : (runSteps streamB stepSRTF 0).ready.length = 0 := by
  rw [srtf_ready_length streamB_wf streamB_noRepeats]
  have : (unfinished streamB (runSchedule stepSRTF streamB) 0).length ≤ 1 :=
    (List.length_filter_le _ _).trans (by simp [streamB, lateConvoyArrivalStream])
  omega

/-- **SRTF waits 1 on stream B**, at every horizon `T ≥ 2`: the long job waits
for the one step the unit job runs. -/
theorem srtf_runWait_streamB {T : ℕ} (hT : 2 ≤ T) :
    runWait (runSteps · stepSRTF) streamB T = 1 := by
  have h_len := srtf_ready_length streamB_wf streamB_noRepeats
  set σ := runSchedule stepSRTF streamB
  have h0 := srtf_streamB_ready_zero
  have h1 : (runSteps streamB stepSRTF 1).ready.length = 1 := by
    rw [h_len, unfinished_streamB_one
      (runSchedule_isAdmissible stepSRTF_conservesJobs streamB_wf streamB_noRepeats)]
  have h_late : ∀ j, (runSteps streamB stepSRTF (2 + j)).ready.length = 0 := by
    intro j
    rw [show 2 + j = j + 1 + 1 by omega, h_len]
    have h_tick : 1 ≤ ticksBefore σ 1 (j + 1 + 1) := by
      refine le_trans ?_ (ticksBefore_mono σ 1 (show 2 ≤ j + 1 + 1 by omega))
      rw [ticksBefore_succ]
      simp [σ, srtf_streamB_schedule_one]
    have := unfinished_streamB_le_one h_tick
    omega
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hT
  have h_rest : ((List.range k).map fun j => (runSteps streamB stepSRTF (2 + j)).ready.length).sum
      = 0 :=
    List.sum_eq_zero_iff_forall_eq_nat.mpr fun x hx => by
      obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx
      exact h_late j
  change ((List.range (2 + k)).map fun t => (runSteps streamB stepSRTF t).ready.length).sum = 1
  simp only [List.range_add, List.map_append, List.sum_append, List.map_map, Function.comp_def,
    h_rest]
  simp [List.range_succ, h0, h1]

/-- **No schedule waits less than 1 on stream B** over a horizon `T ≥ 2`: after
step 1 both jobs are unfinished, so one of them waits. -/
theorem one_le_schedWait_streamB {σ : Schedule} (h_adm : IsAdmissible streamB σ) {T : ℕ}
    (hT : 2 ≤ T) : 1 ≤ schedWait streamB σ T := by
  refine le_trans ?_ (schedWait_mono streamB σ hT)
  have := length_unfinished_sub_one_le streamB_wf streamB_noRepeats h_adm 1
  rw [unfinished_streamB_one h_adm] at this
  simp [schedWait, List.range_succ]
  omega

/-! ## Preemption removes the dilemma -/

/-- **SRTF waits least on stream A**: no admissible schedule waits less, at any
horizon. -/
theorem srtf_le_schedWait_streamA (σ : Schedule) (T : ℕ) :
    runWait (runSteps · stepSRTF) streamA T ≤ schedWait streamA σ T := by
  rw [srtf_runWait_streamA]
  exact Nat.zero_le _

/-- **SRTF waits least on stream B**: no admissible schedule waits less, at any
horizon. -/
theorem srtf_le_schedWait_streamB {σ : Schedule} (h_adm : IsAdmissible streamB σ) (T : ℕ) :
    runWait (runSteps · stepSRTF) streamB T ≤ schedWait streamB σ T := by
  rcases Nat.lt_or_ge T 2 with hT | hT
  · have : runWait (runSteps · stepSRTF) streamB T = 0 := by
      rcases T with _ | _ | T
      · rfl
      · simpa [runWait] using srtf_streamB_ready_zero
      · omega
    omega
  · rw [srtf_runWait_streamB hT]
    exact one_le_schedWait_streamB h_adm hT

/-- An online non-preemptive run is an admissible schedule. -/
theorem onlineRun_isAdmissible {select : SchedState → Option AperiodicProcess}
    (h_mem : IsOnlinePolicy select) {arrival_stream : ℕ → List AperiodicProcess}
    (h_wf : WellFormedStream arrival_stream) (h_rep : NoRepeats arrival_stream) :
    IsAdmissible arrival_stream (runSchedule (stepNonPreemptiveOnline select) arrival_stream) :=
  runSchedule_isAdmissible (stepNonPreemptiveOnline_conservesJobs h_mem) h_wf h_rep

/-- An online non-preemptive run waits what its schedule waits. -/
theorem runWait_onlineRun_eq_schedWait {select : SchedState → Option AperiodicProcess}
    (h_mem : IsOnlinePolicy select) {arrival_stream : ℕ → List AperiodicProcess}
    (h_wf : WellFormedStream arrival_stream) (h_rep : NoRepeats arrival_stream) (T : ℕ) :
    runWait (onlineRun select) arrival_stream T =
      schedWait arrival_stream (runSchedule (stepNonPreemptiveOnline select) arrival_stream) T :=
  runWait_eq_schedWait (stepNonPreemptiveOnline_conservesJobs h_mem) h_wf h_rep T

/-- **SRTF beats every online non-preemptive policy on stream A or on stream B**,
at every horizon `T ≥ 4`.  A policy that idles at time 0 waits at least 1 on
stream A, where SRTF waits 0; a policy that dispatches the long job waits at
least 3 on stream B, where SRTF waits 1.  (Compare `online_nonPreemptive_beaten`:
there the winner had to be chosen per policy and per stream; here one
scheduler, SRTF, wins against all of them.) -/
theorem srtf_beats_online_nonPreemptive (select : SchedState → Option AperiodicProcess)
    (h_mem : IsOnlinePolicy select) {T : ℕ} (hT : 4 ≤ T) :
    runWait (runSteps · stepSRTF) streamA T < runWait (onlineRun select) streamA T ∨
      runWait (runSteps · stepSRTF) streamB T < runWait (onlineRun select) streamB T := by
  cases h : select witnessStart with
  | none =>
    have := idle_costs_on_streamA select h (T := T) (by omega)
    rw [srtf_runWait_streamA]
    omega
  | some p =>
    have := dispatch_costs_on_streamB select h_mem p h hT
    rw [srtf_runWait_streamB (by omega)]
    omega

/-! ## The general theorem -/

/-- **SRTF waits least among all admissible schedules** (Schrage 1968): on every
well-formed stream without repeats, at every horizon `T`, SRTF's run waits no
longer than any admissible schedule, preemptive or not, online or clairvoyant.
SRTF itself is online: its step sees only the current state.

Proved in `SRTFOptimality` (`srtfMinimisesWait`), along these lines, in the
model of `Schedules`:

1. *Pointwise reduction.*  Every admissible schedule leaves all its unfinished
   jobs but at most one waiting (`length_unfinished_sub_one_le`), and SRTF
   leaves exactly all but one (`srtf_ready_length`).  So it is enough that
   SRTF has, after every step, no more unfinished jobs than any admissible
   schedule (`N(t)` minimal pointwise); summing over the steps gives every
   horizon, with no need to count busy ticks.
2. *Majorisation.*  Compare the lists of remaining works (burst less ticks) of
   the released jobs: for every `k`, the sum of the `k` smallest is no larger
   for SRTF.  Releases add the same works to both sides (the `k` smallest of a
   list with one more entry are the `k` smallest, or the `k - 1` smallest plus
   the new entry); a schedule's tick lowers that sum by at most 1; SRTF's tick
   on a job of least positive remaining work lowers it by exactly 1 unless the
   `k` smallest are all 0 already.  Induction on the step.
3. *Counting.*  If a schedule has `z` finished jobs, its `z` smallest remaining
   works sum to 0, so SRTF's do too, and SRTF has at least `z` finished jobs.
   (Both lists have the same length: the released jobs.)

The ingredients on SRTF's side are `inSystem_perm` (its run is its schedule)
and `srtf_run_invariant` (the running job has the least remaining work, and
every job in the system has work left). -/
def SRTFMinimisesWait : Prop :=
  ∀ arrival_stream : ℕ → List AperiodicProcess, WellFormedStream arrival_stream →
    NoRepeats arrival_stream → ∀ σ : Schedule, IsAdmissible arrival_stream σ → ∀ T : ℕ,
      runWait (runSteps · stepSRTF) arrival_stream T ≤ schedWait arrival_stream σ T

/-- **Given the general theorem, SRTF waits no longer than any online
non-preemptive policy** on every well-formed stream without repeats, at every
horizon: so among online schedulers there is an optimal one once preemption is
allowed, in contrast with `no_optimal_online_nonPreemptive`. -/
theorem srtf_le_onlineRun_of (h : SRTFMinimisesWait)
    {select : SchedState → Option AperiodicProcess}
    (h_mem : IsOnlinePolicy select) {arrival_stream : ℕ → List AperiodicProcess}
    (h_wf : WellFormedStream arrival_stream) (h_rep : NoRepeats arrival_stream) (T : ℕ) :
    runWait (runSteps · stepSRTF) arrival_stream T ≤
      runWait (onlineRun select) arrival_stream T := by
  rw [runWait_onlineRun_eq_schedWait h_mem h_wf h_rep]
  exact h arrival_stream h_wf h_rep _ (onlineRun_isAdmissible h_mem h_wf h_rep) T

end ConvoyEffect
