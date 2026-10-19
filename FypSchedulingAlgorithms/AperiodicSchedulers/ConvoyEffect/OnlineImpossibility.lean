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
job (`IsOnlinePolicy`), run with `stepNonPreemptiveOnline`.  "Online" means it
cannot see future arrivals; it does see everything about the jobs that have
already arrived, bursts included (the usual assumption behind SJF).  Its choice
may depend on everything known so far -- the time, the ready queue, the running
and completed jobs -- and it may idle on purpose, returning `none` while jobs
wait.  A policy is a function of the current state rather than of the run's
history; that loses nothing here, since the state carries the strictly
increasing `time`, and the argument only uses each policy's decision at time 0,
where state and history coincide.  Every `stepNonPreemptive sel` (FCFS, SJF,
...) is such a policy (`stepNonPreemptive_eq_online`).  The cost is `runWait`,
the total time jobs spend in `ready` over the first `T` steps, for any horizon
`T ≥ 4`.

**The witnesses.**  `streamA` releases a single 4-tick job at time 0;
`streamB` releases the same job and, at time 1, a unit job
(`lateConvoyArrivalStream 4`).  Step 0 sees the same state on both streams, so
a policy must make the same decision on both:

* dispatch the long job: on `streamB` the unit job then waits 3 ticks, but
  "idle at time 0, then SJF" (`idleThenSJF`) waits only 2;
* idle: on `streamA` the long job waits 1 tick, but FCFS waits 0.

So every policy of the class is strictly beaten on `streamA` or on `streamB` by
another policy of the class, chosen before the horizon and winning at every
horizon `T ≥ 4` (`online_nonPreemptive_beaten`), and at no such horizon is any
policy optimal on every well-formed stream (`no_optimal_online_nonPreemptive`).
In particular SJF is not (`sjf_not_optimal_online`).  The competitors finish
both streams by step 4, after which nothing more arrives, so their waits are
fixed from then on (`runWait_online_eq_of_drained`), while the beaten policy's
wait can only grow (`runWait_mono`).  Four is the least horizon at which these
two streams separate the policies: over three steps, dispatching the long job
costs only 2 on `streamB`, no more than `idleThenSJF`.

The competitor that beats a policy which dispatches at time 0 idles at time 0.
The theorem is about the class that includes deliberate idling; a statement
about work-conserving policies alone (never idle while a job waits) would be a
different claim, not made here.

What SJF lacks is only the future: given only the past, it is optimal
(`OnlineOptimality`).  On the instance known at any time `t`, its run waits no
longer than any policy of the class that agrees with it before `t`.

Preemption removes the dilemma: SRTF dispatches the long job and preempts it
when the unit job arrives, waiting 1 tick on `streamB` and 0 on `streamA`, the
least any schedule can wait on either stream, so it beats every policy of the
class on one of them (`PreemptiveOptimality`).
-/

namespace ConvoyEffect

open NonPreemptive

/-! ## The class of online non-preemptive policies -/

/-- An **online non-preemptive policy** only ever dispatches a job that is
waiting.  (It may return `none` while jobs wait: deliberate idling.)  It sees
the current state only: the jobs that have arrived, with their bursts, but no
future arrivals.  Since the state includes the strictly increasing `time`, this
is no restriction on any one stream compared with seeing the whole history so
far (across streams, two histories can reach the same state). -/
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

/-- FCFS only dispatches the head of the ready queue. -/
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

/-- `idleThenSJF` dispatches nothing at time 0 and a waiting job after that. -/
theorem idleThenSJF_isOnlinePolicy : IsOnlinePolicy idleThenSJF := by
  intro s p h
  unfold idleThenSJF at h
  split at h
  · simp at h
  · exact selectSJF_mem _ p h

/-! ## Waiting stops once the queue drains -/

/-- With nothing arriving, an empty ready queue stays empty, so nobody waits:
a non-preemptive step never adds to `ready`. -/
theorem waitFrom_online_nil (select : SchedState → Option AperiodicProcess) (s : SchedState)
    (h_ready : s.ready = []) (T : ℕ) :
    waitFrom (stepNonPreemptiveOnline select) s T = 0 := by
  induction T generalizing s with
  | zero => rfl
  | succ T ih =>
    have h1 : (stepNonPreemptiveOnline select s).ready = [] :=
      List.eq_nil_iff_forall_not_mem.mpr fun q hq => by
        simpa [h_ready] using stepNonPreemptiveOnline_ready_subset select s q hq
    rw [waitFrom_succ, ih _ h1, h_ready]
    rfl

/-- **A drained run waits no more.** If nothing arrives after time `t` and the
ready queue is empty after step `t`, the wait over any horizon `T ≥ t` is the
wait over the first `t` steps. -/
theorem runWait_online_eq_of_drained (select : SchedState → Option AperiodicProcess)
    (as : ℕ → List AperiodicProcess) (t : ℕ) (h_arr : ∀ j, t < j → as j = [])
    (h_ready : (onlineRun select as t).ready = []) {T : ℕ} (hT : t ≤ T) :
    runWait (onlineRun select) as T = runWait (onlineRun select) as t := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hT
  have h_ready' : (runSteps as (stepNonPreemptiveOnline select) t).ready = [] := h_ready
  have h := runWait_add (stepNonPreemptiveOnline select) as t k (fun j h1 _ => h_arr j h1)
  rw [waitFrom_online_nil select _ h_ready', Nat.add_zero] at h
  exact h

/-! ## The witness streams -/

/-- The long job of the witnesses: 4 ticks, id 0, at time 0. -/
abbrev longJob4 : AperiodicProcess := longJob 4 (by omega)

/-- Stream A: just the long job, at time 0. -/
def streamA : ℕ → List AperiodicProcess := batchStream [longJob4]

/-- Stream B: the long job at time 0 and a unit job at time 1. -/
def streamB : ℕ → List AperiodicProcess := lateConvoyArrivalStream 4 (by omega)

/-- Stream A is well formed. -/
theorem streamA_wf : WellFormedStream streamA :=
  batchStream_wf ⟨by simp [longJob], by simp⟩

/-- Stream B is well formed. -/
theorem streamB_wf : WellFormedStream streamB := lateConvoyArrivalStream_wf 4 (by omega)

/-- Nothing arrives on stream A after time 0. -/
theorem streamA_nil (j : ℕ) (hj : 0 < j) : streamA j = [] := batchStream_succ _ j hj

/-- Nothing arrives on stream B after time 1. -/
theorem streamB_nil (j : ℕ) (hj : 1 < j) : streamB j = [] := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
  rfl

/-- **Step 0 cannot tell the streams apart.** -/
theorem streamA_zero_eq_streamB_zero : streamA 0 = streamB 0 := rfl

/-- The state step 0 starts from, on both streams. -/
abbrev witnessStart : SchedState := { SchedStateMethods.init with ready := [longJob4] }

/-! ## The competitors' costs -/

/-- FCFS on stream A over 4 steps: the long job is dispatched at once and never waits. -/
theorem runWait_fcfsOnline_streamA_four : runWait (onlineRun fcfsOnline) streamA 4 = 0 := by
  decide

/-- `idleThenSJF` on stream B over 4 steps: the long job waits at steps 0 and 1. -/
theorem runWait_idleThenSJF_streamB_four :
    runWait (onlineRun idleThenSJF) streamB 4 = 2 := by
  decide

/-- SJF on stream B over 4 steps: the unit job waits at steps 1, 2 and 3. -/
theorem runWait_sjf_streamB_four : runWait (runSteps · stepSJF) streamB 4 = 3 := by
  decide

/-- FCFS on stream B over 4 steps: the same 3 ticks as SJF. -/
theorem runWait_fcfs_streamB_four : runWait (runSteps · stepFCFS) streamB 4 = 3 := by
  decide

/-- **FCFS waits 0 on stream A at every horizon**: after step 4 its queue is
empty and nothing more arrives. -/
theorem runWait_fcfsOnline_streamA (T : ℕ) (hT : 4 ≤ T) :
    runWait (onlineRun fcfsOnline) streamA T = 0 := by
  rw [runWait_online_eq_of_drained fcfsOnline streamA 4 (fun j hj => streamA_nil j (by omega))
    (by decide) hT]
  exact runWait_fcfsOnline_streamA_four

/-- **`idleThenSJF` waits 2 on stream B at every horizon `T ≥ 4`**: after step 4
its queue is empty and nothing more arrives. -/
theorem runWait_idleThenSJF_streamB (T : ℕ) (hT : 4 ≤ T) :
    runWait (onlineRun idleThenSJF) streamB T = 2 := by
  rw [runWait_online_eq_of_drained idleThenSJF streamB 4 (fun j hj => streamB_nil j (by omega))
    (by decide) hT]
  exact runWait_idleThenSJF_streamB_four

/-! ## Any policy, on its first steps -/

/-- The wait over 4 steps counts the ready queue at each of the steps `0, …, 3`. -/
theorem runWait_four (run : (ℕ → List AperiodicProcess) → ℕ → SchedState)
    (as : ℕ → List AperiodicProcess) :
    runWait run as 4 = (run as 0).ready.length + (run as 1).ready.length +
      (run as 2).ready.length + (run as 3).ready.length := by
  simp [runWait, List.range_succ]
  omega

/-- **Idling at time 0 costs a tick on stream A** at every horizon `T ≥ 1`: the
long job waits. -/
theorem idle_costs_on_streamA (select : SchedState → Option AperiodicProcess)
    (h_idle : select witnessStart = none) {T : ℕ} (hT : 1 ≤ T) :
    1 ≤ runWait (onlineRun select) streamA T := by
  have h0 : (onlineRun select streamA 0).ready = [longJob4] :=
    (stepNonPreemptiveOnline_idle select witnessStart rfl h_idle).2
  have h1 : runWait (onlineRun select) streamA 1 = 1 := by
    simp [runWait, h0]
  exact h1 ▸ runWait_mono _ _ hT

/-- **Dispatching at time 0 costs three ticks on stream B** at every horizon
`T ≥ 4`: the long job holds the CPU for steps 1, 2 and 3, and the unit job,
arriving at time 1, waits through all three. -/
theorem dispatch_costs_on_streamB (select : SchedState → Option AperiodicProcess)
    (h_mem : IsOnlinePolicy select) (p : AperiodicProcess)
    (h_disp : select witnessStart = some p) {T : ℕ} (hT : 4 ≤ T) :
    3 ≤ runWait (onlineRun select) streamB T := by
  refine le_trans ?_ (runWait_mono _ _ hT)
  have hp : p = longJob4 := by simpa using h_mem _ _ h_disp
  subst hp
  have h_step : ∀ t, onlineRun select streamB (t + 1) =
      stepNonPreemptiveOnline select { onlineRun select streamB t with
        ready := (onlineRun select streamB t).ready ++ streamB (t + 1) } := fun _ => rfl
  -- step 0: the long job is dispatched, untouched
  have h0 := stepNonPreemptiveOnline_dispatch select witnessStart rfl h_disp
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
  rw [runWait_four, h1q, h2q, h3q]
  simp only [streamB, lateConvoyArrivalStream, List.append_nil, List.length_singleton]
  omega

/-! ## No policy is optimal -/

/-- **Every online non-preemptive policy is strictly beaten on stream A or on
stream B by another online non-preemptive policy**, the same competitor at
every horizon `T ≥ 4`.  Step 0 sees the same state on both streams.  If the
policy dispatches the long job there, "idle at time 0, then SJF" waits less on
stream B (2 against at least 3); if it idles, FCFS waits less on stream A (0
against at least 1). -/
theorem online_nonPreemptive_beaten (select : SchedState → Option AperiodicProcess)
    (h_mem : IsOnlinePolicy select) :
    ∃ select', IsOnlinePolicy select' ∧
      ((∀ T, 4 ≤ T →
          runWait (onlineRun select') streamA T < runWait (onlineRun select) streamA T) ∨
        (∀ T, 4 ≤ T →
          runWait (onlineRun select') streamB T < runWait (onlineRun select) streamB T)) := by
  cases h : select witnessStart with
  | none =>
    refine ⟨fcfsOnline, fcfsOnline_isOnlinePolicy, Or.inl fun T hT => ?_⟩
    have := idle_costs_on_streamA select h (T := T) (by omega)
    rw [runWait_fcfsOnline_streamA T hT]
    omega
  | some p =>
    refine ⟨idleThenSJF, idleThenSJF_isOnlinePolicy, Or.inr fun T hT => ?_⟩
    have := dispatch_costs_on_streamB select h_mem p h hT
    rw [runWait_idleThenSJF_streamB T hT]
    omega

/-- **No online non-preemptive policy is optimal**: at every horizon `T ≥ 4`,
none waits no longer than every other online non-preemptive policy on every
well-formed stream. -/
theorem no_optimal_online_nonPreemptive :
    ∀ T, 4 ≤ T → ¬ ∃ select, IsOnlinePolicy select ∧ ∀ select', IsOnlinePolicy select' →
      ∀ as, WellFormedStream as →
        runWait (onlineRun select) as T ≤ runWait (onlineRun select') as T := by
  rintro T hT ⟨select, h_mem, h_opt⟩
  obtain ⟨select', h_mem', h_lt | h_lt⟩ := online_nonPreemptive_beaten select h_mem
  · exact absurd (h_opt select' h_mem' streamA streamA_wf) (not_le.mpr (h_lt T hT))
  · exact absurd (h_opt select' h_mem' streamB streamB_wf) (not_le.mpr (h_lt T hT))

/-- **SJF is not an optimal online non-preemptive scheduler**: on stream B, at
every horizon `T ≥ 4`, idling once and then running SJF waits 2 ticks, while
SJF itself waits at least 3.  (SJF is optimal on batches, `runWait_sjf_le`: it
is the late arrival that it cannot anticipate.) -/
theorem sjf_not_optimal_online :
    IsOnlinePolicy idleThenSJF ∧ WellFormedStream streamB ∧
      ∀ T, 4 ≤ T → runWait (onlineRun idleThenSJF) streamB T <
        runWait (runSteps · stepSJF) streamB T := by
  refine ⟨idleThenSJF_isOnlinePolicy, streamB_wf, fun T hT => ?_⟩
  have := runWait_mono (runSteps · stepSJF) streamB hT
  rw [runWait_sjf_streamB_four] at this
  rw [runWait_idleThenSJF_streamB T hT]
  omega

end ConvoyEffect
