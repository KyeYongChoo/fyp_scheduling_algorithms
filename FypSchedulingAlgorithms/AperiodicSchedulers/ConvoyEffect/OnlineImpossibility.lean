/-
Copyright (c) 2026 Choo Kye Yong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Choo Kye Yong
-/
import FypSchedulingAlgorithms.AperiodicSchedulers.ConvoyEffect.RunWait
import FypSchedulingAlgorithms.AperiodicSchedulers.ConvoyEffect.ConvoyWitnesses
import FypSchedulingAlgorithms.AperiodicSchedulers.NonPreemptiveLemmas

/-!
# No online non-preemptive scheduler waits least on every stream

SJF waits least on a batch (`runWait_sjf_le`), but a batch shows the whole
instance at time 0.  Online, a non-preemptive scheduler has to commit before it
knows what is coming, and no policy can commit correctly on every stream.

**The class.**  An *online non-preemptive policy* is any
`select : SchedState → Option AperiodicProcess` that only ever picks a waiting
job (`IsOnlinePolicy`), run with `stepNonPreemptiveOnline`.  Its choice may
depend on everything known so far -- the time, the ready queue, the running and
completed jobs -- and it may idle on purpose, returning `none` while jobs wait.
Every `stepNonPreemptive sel` (FCFS, SJF, ...) is such a policy
(`stepNonPreemptive_eq_online`).  The cost is `runWait`, the total time jobs
spend in `ready`, over the horizon `horizon = 10`.

**The witnesses.**  `streamA` releases a single 4-tick job at time 0;
`streamB` releases the same job and, at time 1, a unit job
(`lateConvoyArrivalStream 4`).  Step 0 sees the same state on both streams, so
a policy must make the same decision on both:

* dispatch the long job: on `streamB` the unit job then waits 3 ticks, but
  "idle at time 0, then SJF" (`idleThenSJF`) waits only 2;
* idle: on `streamA` the long job waits 1 tick, but FCFS waits 0.

So every policy of the class is strictly beaten on `streamA` or on `streamB` by
another policy of the class (`online_nonPreemptive_beaten`), and none is
optimal on every well-formed stream (`no_optimal_online_nonPreemptive`).  In
particular SJF is not (`sjf_not_optimal_online`).  Preemption removes the
dilemma: SRTF dispatches the long job and preempts it when the unit job
arrives, waiting 1 tick on `streamB` (by `#eval`) and 0 on `streamA`.
-/

namespace ConvoyEffect

open NonPreemptive

/-! ## The class of online non-preemptive policies -/

/-- An **online non-preemptive policy** only ever dispatches a job that is
waiting.  (It may return `none` while jobs wait: deliberate idling.) -/
def IsOnlinePolicy (select : SchedState → Option AperiodicProcess) : Prop :=
  ∀ s p, select s = some p → p ∈ s.ready

/-- The run of an online non-preemptive policy. -/
def onlineRun (select : SchedState → Option AperiodicProcess) :
    (ℕ → List AperiodicProcess) → ℕ → SchedState :=
  fun arrival_stream => runSteps arrival_stream (stepNonPreemptiveOnline select)

/-- Every ready-queue policy `sel` is an online policy, with the same run as
`stepNonPreemptive sel`. -/
theorem onlineRun_ready (sel : List AperiodicProcess → Option AperiodicProcess) :
    onlineRun (fun s => sel s.ready) = fun as => runSteps as (stepNonPreemptive sel) := by
  rw [stepNonPreemptive_eq_online]
  rfl

/-- FCFS, as an online policy. -/
def fcfsOnline : SchedState → Option AperiodicProcess := fun s => selectFCFS s.ready

/-- Idle at time 0, then behave like SJF. -/
def idleThenSJF : SchedState → Option AperiodicProcess :=
  fun s => if s.time = 0 then none else selectSJF s.ready

theorem fcfsOnline_isOnlinePolicy : IsOnlinePolicy fcfsOnline := by
  intro s p h
  unfold fcfsOnline selectFCFS at h
  split at h
  · simp at h
  · rename_i q qs h_ready
    simp only [Option.some.injEq] at h
    subst h
    rw [h_ready]
    exact List.mem_cons_self ..

theorem idleThenSJF_isOnlinePolicy : IsOnlinePolicy idleThenSJF := by
  intro s p h
  unfold idleThenSJF at h
  split at h
  · simp at h
  · exact selectSJF_mem _ p h

/-! ## The witness streams -/

/-- The long job of the witnesses: 4 ticks, id 0, at time 0. -/
abbrev longJob4 : AperiodicProcess := longJob 4 (by omega)

/-- Stream A: just the long job, at time 0. -/
def streamA : ℕ → List AperiodicProcess := batchStream [longJob4]

/-- Stream B: the long job at time 0 and a unit job at time 1. -/
def streamB : ℕ → List AperiodicProcess := lateConvoyArrivalStream 4 (by omega)

theorem streamA_wf : WellFormedStream streamA :=
  batchStream_wf ⟨by simp [longJob], by simp⟩

theorem streamB_wf : WellFormedStream streamB := lateConvoyArrivalStream_wf 4 (by omega)

/-- The horizon: long enough for the competitors to finish both streams. -/
def horizon : ℕ := 10

/-- **Step 0 cannot tell the streams apart.** -/
theorem streamA_zero_eq_streamB_zero : streamA 0 = streamB 0 := rfl

/-! ## The competitors' costs -/

theorem runWait_fcfsOnline_streamA : runWait (onlineRun fcfsOnline) streamA horizon = 0 := by
  decide

theorem runWait_idleThenSJF_streamB : runWait (onlineRun idleThenSJF) streamB horizon = 2 := by
  decide

theorem runWait_sjf_streamB : runWait (runSteps · stepSJF) streamB horizon = 3 := by
  decide

theorem runWait_fcfs_streamB : runWait (runSteps · stepFCFS) streamB horizon = 3 := by
  decide

/-! ## Any policy, on its first steps -/

/-- The wait over the horizon counts the ready queue at each of the steps
`0, …, 9`. -/
theorem runWait_horizon (run : (ℕ → List AperiodicProcess) → ℕ → SchedState)
    (as : ℕ → List AperiodicProcess) :
    runWait run as horizon = (run as 0).ready.length + (run as 1).ready.length +
      (run as 2).ready.length + (run as 3).ready.length + (run as 4).ready.length +
      (run as 5).ready.length + (run as 6).ready.length + (run as 7).ready.length +
      (run as 8).ready.length + (run as 9).ready.length := by
  simp [runWait, horizon, List.range_succ]
  omega

/-- The state step 0 starts from, on both streams. -/
abbrev startState : SchedState := { SchedStateMethods.init with ready := [longJob4] }

/-- **Idling at time 0 costs a tick on stream A**: the long job waits. -/
theorem idle_costs_on_streamA (select : SchedState → Option AperiodicProcess)
    (h_idle : select startState = none) :
    1 ≤ runWait (onlineRun select) streamA horizon := by
  have h0 : (onlineRun select streamA 0).ready = [longJob4] :=
    (stepNonPreemptiveOnline_idle select startState rfl h_idle).2
  rw [runWait_horizon, h0, List.length_singleton]
  omega

/-- **Dispatching at time 0 costs three ticks on stream B**: the long job holds
the CPU for steps 1, 2 and 3, and the unit job, arriving at time 1, waits
through all three. -/
theorem dispatch_costs_on_streamB (select : SchedState → Option AperiodicProcess)
    (h_mem : IsOnlinePolicy select) (p : AperiodicProcess)
    (h_disp : select startState = some p) :
    3 ≤ runWait (onlineRun select) streamB horizon := by
  have hp : p = longJob4 := by simpa using h_mem _ _ h_disp
  subst hp
  have h_step : ∀ t, onlineRun select streamB (t + 1) =
      stepNonPreemptiveOnline select { onlineRun select streamB t with
        ready := (onlineRun select streamB t).ready ++ streamB (t + 1) } := fun _ => rfl
  -- step 0: the long job is dispatched, untouched
  have h0 := stepNonPreemptiveOnline_dispatch select startState rfl h_disp
  have h0r : (onlineRun select streamB 0).running = some longJob4 := h0.1
  have h0q : (onlineRun select streamB 0).ready = [] := h0.2.trans (by simp)
  -- steps 1-3: the long job ticks, the unit job (arrived at time 1) waits
  have h1 := stepNonPreemptiveOnline_tick select
    { onlineRun select streamB 0 with ready := (onlineRun select streamB 0).ready ++ streamB 1 }
    h0r (by simp [longJob])
  rw [← h_step 0] at h1
  obtain ⟨h1r, h1q⟩ := h1
  simp only [h0q, List.nil_append] at h1q
  have h2 := stepNonPreemptiveOnline_tick select
    { onlineRun select streamB 1 with ready := (onlineRun select streamB 1).ready ++ streamB 2 }
    h1r (by simp [longJob])
  rw [← h_step 1] at h2
  obtain ⟨h2r, h2q⟩ := h2
  simp only [h1q] at h2q
  have h3 := stepNonPreemptiveOnline_tick select
    { onlineRun select streamB 2 with ready := (onlineRun select streamB 2).ready ++ streamB 3 }
    h2r (by simp [longJob])
  rw [← h_step 2] at h3
  obtain ⟨_, h3q⟩ := h3
  simp only [h2q] at h3q
  rw [runWait_horizon, h1q, h2q, h3q]
  simp only [streamB, lateConvoyArrivalStream, List.append_nil, List.length_singleton]
  omega

/-! ## No policy is optimal -/

/-- **Every online non-preemptive policy is strictly beaten on stream A or on
stream B by another online non-preemptive policy.** Step 0 sees the same state
on both streams.  If the policy dispatches the long job there, "idle at time 0,
then SJF" waits less on stream B (2 against at least 3); if it idles, FCFS waits
less on stream A (0 against at least 1). -/
theorem online_nonPreemptive_beaten (select : SchedState → Option AperiodicProcess)
    (h_mem : IsOnlinePolicy select) :
    ∃ select', IsOnlinePolicy select' ∧
      (runWait (onlineRun select') streamA horizon < runWait (onlineRun select) streamA horizon ∨
        runWait (onlineRun select') streamB horizon <
          runWait (onlineRun select) streamB horizon) := by
  cases h : select startState with
  | none =>
    refine ⟨fcfsOnline, fcfsOnline_isOnlinePolicy, Or.inl ?_⟩
    have := idle_costs_on_streamA select h
    rw [runWait_fcfsOnline_streamA]
    omega
  | some p =>
    refine ⟨idleThenSJF, idleThenSJF_isOnlinePolicy, Or.inr ?_⟩
    have := dispatch_costs_on_streamB select h_mem p h
    rw [runWait_idleThenSJF_streamB]
    omega

/-- **No online non-preemptive policy is optimal**: none waits no longer than
every other online non-preemptive policy on every well-formed stream. -/
theorem no_optimal_online_nonPreemptive :
    ¬ ∃ select, IsOnlinePolicy select ∧ ∀ select', IsOnlinePolicy select' →
      ∀ as, WellFormedStream as →
        runWait (onlineRun select) as horizon ≤ runWait (onlineRun select') as horizon := by
  rintro ⟨select, h_mem, h_opt⟩
  obtain ⟨select', h_mem', h_lt | h_lt⟩ := online_nonPreemptive_beaten select h_mem
  · exact absurd (h_opt select' h_mem' streamA streamA_wf) (not_le.mpr h_lt)
  · exact absurd (h_opt select' h_mem' streamB streamB_wf) (not_le.mpr h_lt)

/-- **SJF is not an optimal online non-preemptive scheduler**: on stream B,
idling once and then running SJF waits 2 ticks, while SJF itself waits 3.
(SJF is optimal on batches, `runWait_sjf_le`: it is the late arrival that it
cannot anticipate.) -/
theorem sjf_not_optimal_online :
    IsOnlinePolicy idleThenSJF ∧ WellFormedStream streamB ∧
      runWait (onlineRun idleThenSJF) streamB horizon <
        runWait (runSteps · stepSJF) streamB horizon := by
  refine ⟨idleThenSJF_isOnlinePolicy, streamB_wf, ?_⟩
  rw [runWait_idleThenSJF_streamB, runWait_sjf_streamB]
  omega

end ConvoyEffect
