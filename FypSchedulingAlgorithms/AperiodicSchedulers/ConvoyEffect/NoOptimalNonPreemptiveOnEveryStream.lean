/-
Copyright (c) 2026 Choo Kye Yong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Choo Kye Yong
-/
import FypSchedulingAlgorithms.AperiodicSchedulers.ConvoyEffect.RunWait
import FypSchedulingAlgorithms.AperiodicSchedulers.ConvoyEffect.ConvoyWitnesses
import FypSchedulingAlgorithms.AperiodicSchedulers.NonPreemptiveLemmas

/-!
# No non-preemptive scheduler waits least on every stream

SJF waits least on a batch (`runWait_sjf_le`), but a batch shows the whole
instance at time 0.  Without seeing future arrivals, a non-preemptive scheduler has
to commit before it knows what is coming, and no policy can commit correctly on
every stream.

**The class.**  A *non-preemptive state-select policy* is any
`select : SchedState → Option AperiodicProcess` that only ever picks a waiting
job (`DrawsFromReadyQueue`), run with `stepNonPreemptiveStateSelect`.  It
cannot see future arrivals; it does see everything about the jobs that have
already arrived, bursts included (the usual assumption behind SJF).  Its choice
may depend on everything known so far -- the time, the ready queue, the running
and completed jobs -- and it may idle on purpose, returning `none` while jobs
wait.  A policy is a function of the current state rather than of the run's
history; that loses nothing here, since the state carries the strictly
increasing `time`, and the argument only uses each policy's decision at time 0,
where state and history coincide.  Every `stepNonPreemptive sel` (FCFS, SJF,
...) is such a policy (`stepNonPreemptive_eq_stateSelect`).  The cost is `runWait`,
the total time jobs spend in `ready` over the first `T` steps.

**The witnesses.**  `streamA` releases a single 4-tick job at time 0;
`streamB` releases the same job and, at time 1, a unit job
(`lateConvoyArrivalStream 4`).  Step 0 sees the same state on both streams, so
a policy must make the same decision on both:

* dispatch the long job: on `streamB` the unit job then waits 3 ticks, but
  "idle at time 0, then SJF" (`idleThenSJF`) waits only 2;
* idle: on `streamA` the long job waits 1 tick, but FCFS waits 0.

So every policy of the class is strictly beaten on `streamA` or on `streamB` by
another policy of the class, chosen before the horizon and winning at every
horizon `T ≥ 4` (`nonPreemptive_beaten_on_streamA_or_streamB`), and at no such horizon is any
policy optimal on every well-formed stream (`no_optimal_nonPreemptive_on_every_stream`).
In particular SJF is not (`sjf_beaten_by_idleThenSJF_on_streamB`).  The competitors finish
both streams by step 4, after which nothing more arrives, so their waits are
fixed from then on (`runWait_stateSelect_eq_of_drained`), while the beaten policy's
wait can only grow (`runWait_mono`).  Four is the least horizon at which these
two streams separate the policies: over three steps, dispatching the long job
costs only 2 on `streamB`, no more than `idleThenSJF`.  It is the least horizon for
every stream too: at every `T ≤ 3`, SJF is optimal (`sjf_isOptimalOverSteps_of_le_three`
in `ShortHorizon`), so an optimal policy exists exactly when `T ≤ 3`
(`exists_optimal_iff`).

The competitor that beats a policy which dispatches at time 0 idles at time 0.
The theorem is about the class that includes deliberate idling; a statement
about work-conserving policies alone (never idle while a job waits) would be a
different claim, not made here.

What SJF lacks is only the future: given only the past, it is optimal
(`SJFOptimalityGivenSamePast`).  On the instance known at any time `t`, its run waits no
longer than any policy of the class that agrees with it before `t`.

Preemption removes the dilemma: SRTF dispatches the long job and preempts it
when the unit job arrives, waiting 1 tick on `streamB` and 0 on `streamA`, the
least any schedule can wait on either stream, so it beats every policy of the
class on one of them (`PreemptiveOptimality`).
-/

namespace ConvoyEffect

open NonPreemptive

/-! ## The class of non-preemptive state-select policies -/

/-- `select` **draws from the ready queue**: every job it picks is waiting in `ready`.
That stops it from picking a job that is running or completed, or one it made up.  It
may still return `none` while jobs wait, i.e. idle on purpose.

A `select` with this property, run by `stepNonPreemptiveStateSelect`, is a
**non-preemptive state-select policy**, the class this file is about.  It sees the
whole current state (time, ready queue, running and completed jobs), not just the
ready queue.  That it cannot see future arrivals comes from the type, not from this
condition: `select` is given only the current state, which holds no future arrivals. -/
def DrawsFromReadyQueue (select : SchedState → Option AperiodicProcess) : Prop :=
  ∀ s p, select s = some p → p ∈ s.ready

/-- The run of a non-preemptive state-select policy. -/
def runStateSelect (select : SchedState → Option AperiodicProcess) :
    (ℕ → List AperiodicProcess) → ℕ → SchedState :=
  fun arrival_stream => runSteps arrival_stream (stepNonPreemptiveStateSelect select)

/-- Every ready-queue policy `sel` is a state-select policy, with the same run as
`stepNonPreemptive sel`. -/
theorem runStateSelect_ready (sel : List AperiodicProcess → Option AperiodicProcess) :
    runStateSelect (fun s => sel s.ready) =
      fun arrival_stream => runSteps arrival_stream (stepNonPreemptive sel) := by
  rw [stepNonPreemptive_eq_stateSelect]
  rfl

/-- FCFS, as a state-select policy. -/
def fcfsStateSelect : SchedState → Option AperiodicProcess := fun s => selectFCFS s.ready

/-- Idle at time 0, then behave like SJF. -/
def idleThenSJF : SchedState → Option AperiodicProcess :=
  fun s => if s.time = 0 then none else selectSJF s.ready

/-- FCFS only dispatches the head of the ready queue. -/
theorem fcfsStateSelect_drawsFromReadyQueue : DrawsFromReadyQueue fcfsStateSelect := by
  intro s p h
  unfold fcfsStateSelect selectFCFS at h
  split at h
  · simp at h
  · rename_i q qs h_ready
    simp only [Option.some.injEq] at h
    subst h
    rw [h_ready]
    exact List.mem_cons_self ..

/-- `idleThenSJF` dispatches nothing at time 0 and a waiting job after that. -/
theorem idleThenSJF_drawsFromReadyQueue : DrawsFromReadyQueue idleThenSJF := by
  intro s p h
  unfold idleThenSJF at h
  split at h
  · simp at h
  · exact selectSJF_mem _ p h

/-! ## Waiting stops once the queue drains -/

/-- With nothing arriving, an empty ready queue stays empty, so nobody waits:
a non-preemptive step never adds to `ready`. -/
theorem waitFrom_stateSelect_nil (select : SchedState → Option AperiodicProcess) (s : SchedState)
    (h_ready : s.ready = []) (T : ℕ) :
    waitFrom (stepNonPreemptiveStateSelect select) s T = 0 := by
  induction T generalizing s with
  | zero => rfl
  | succ T ih =>
    have h1 : (stepNonPreemptiveStateSelect select s).ready = [] :=
      List.eq_nil_iff_forall_not_mem.mpr fun q hq => by
        simpa [h_ready] using stepNonPreemptiveStateSelect_ready_subset select s q hq
    rw [waitFrom_succ, ih _ h1, h_ready]
    rfl

/-- **A drained run waits no more.** If nothing arrives after time `t` and the
ready queue is empty after step `t`, the wait over any horizon `T ≥ t` is the
wait over the first `t` steps. -/
theorem runWait_stateSelect_eq_of_drained (select : SchedState → Option AperiodicProcess)
    (arrival_stream : ℕ → List AperiodicProcess) (t : ℕ)
    (h_arr : ∀ j, t < j → arrival_stream j = [])
    (h_ready : (runStateSelect select arrival_stream t).ready = []) {T : ℕ} (hT : t ≤ T) :
    runWait (runStateSelect select) arrival_stream T =
      runWait (runStateSelect select) arrival_stream t := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hT
  have h_ready' :
      (runSteps arrival_stream (stepNonPreemptiveStateSelect select) t).ready = [] := h_ready
  have h := runWait_add (stepNonPreemptiveStateSelect select) arrival_stream t k
    (fun j h1 _ => h_arr j h1)
  rw [waitFrom_stateSelect_nil select _ h_ready', Nat.add_zero] at h
  exact h

/-! ## The witness streams -/

/-- The long job of the witnesses: 4 ticks, id 0, at time 0. -/
abbrev longJob4 : AperiodicProcess := longJob 4 (by omega)

/-- Stream A: just the long job, at time 0. -/
def streamA : ℕ → List AperiodicProcess := allArrivalsAtZeroStream [longJob4]

/-- Stream B: the long job at time 0 and a unit job at time 1. -/
def streamB : ℕ → List AperiodicProcess := lateConvoyArrivalStream 4 (by omega)

/-- Stream A is well formed. -/
theorem streamA_wf : WellFormedStream streamA :=
  allArrivalsAtZeroStream_wf ⟨by simp [longJob], by simp⟩

/-- Stream B is well formed. -/
theorem streamB_wf : WellFormedStream streamB := lateConvoyArrivalStream_wf 4 (by omega)

/-- Nothing arrives on stream A after time 0. -/
theorem streamA_nil (j : ℕ) (hj : 0 < j) : streamA j = [] := allArrivalsAtZeroStream_succ _ j hj

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
theorem runWait_fcfsStateSelect_streamA_four :
    runWait (runStateSelect fcfsStateSelect) streamA 4 = 0 := by
  decide

/-- `idleThenSJF` on stream B over 4 steps: the long job waits at steps 0 and 1. -/
theorem runWait_idleThenSJF_streamB_four :
    runWait (runStateSelect idleThenSJF) streamB 4 = 2 := by
  decide

/-- SJF on stream B over 4 steps: the unit job waits at steps 1, 2 and 3. -/
theorem runWait_sjf_streamB_four : runWait (runSteps · stepSJF) streamB 4 = 3 := by
  decide

/-- FCFS on stream B over 4 steps: the same 3 ticks as SJF. -/
theorem runWait_fcfs_streamB_four : runWait (runSteps · stepFCFS) streamB 4 = 3 := by
  decide

/-- **FCFS waits 0 on stream A at every horizon**: after step 4 its queue is
empty and nothing more arrives. -/
theorem runWait_fcfsStateSelect_streamA (T : ℕ) (hT : 4 ≤ T) :
    runWait (runStateSelect fcfsStateSelect) streamA T = 0 := by
  rw [runWait_stateSelect_eq_of_drained fcfsStateSelect streamA 4
    (fun j hj => streamA_nil j (by omega)) (by decide) hT]
  exact runWait_fcfsStateSelect_streamA_four

/-- **`idleThenSJF` waits 2 on stream B at every horizon `T ≥ 4`**: after step 4
its queue is empty and nothing more arrives. -/
theorem runWait_idleThenSJF_streamB (T : ℕ) (hT : 4 ≤ T) :
    runWait (runStateSelect idleThenSJF) streamB T = 2 := by
  rw [runWait_stateSelect_eq_of_drained idleThenSJF streamB 4 (fun j hj => streamB_nil j (by omega))
    (by decide) hT]
  exact runWait_idleThenSJF_streamB_four

/-! ## Any policy, on its first steps -/

/-- The wait over 4 steps counts the ready queue at each of the steps `0, …, 3`. -/
theorem runWait_four (run : (ℕ → List AperiodicProcess) → ℕ → SchedState)
    (arrival_stream : ℕ → List AperiodicProcess) :
    runWait run arrival_stream 4 =
      (run arrival_stream 0).ready.length + (run arrival_stream 1).ready.length +
        (run arrival_stream 2).ready.length + (run arrival_stream 3).ready.length := by
  simp [runWait, List.range_succ]
  omega

/-- **Idling at time 0 costs a tick on stream A** at every horizon `T ≥ 1`: the
long job waits. -/
theorem idle_costs_on_streamA (select : SchedState → Option AperiodicProcess)
    (h_idle : select witnessStart = none) {T : ℕ} (hT : 1 ≤ T) :
    1 ≤ runWait (runStateSelect select) streamA T := by
  have h0 : (runStateSelect select streamA 0).ready = [longJob4] :=
    (stepNonPreemptiveStateSelect_idle select witnessStart rfl h_idle).2
  have h1 : runWait (runStateSelect select) streamA 1 = 1 := by
    simp [runWait, h0]
  exact h1 ▸ runWait_mono _ _ hT

/-- **Dispatching at time 0 costs three ticks on stream B** at every horizon
`T ≥ 4`: the long job holds the CPU for steps 1, 2 and 3, and the unit job,
arriving at time 1, waits through all three. -/
theorem dispatch_costs_on_streamB (select : SchedState → Option AperiodicProcess)
    (h_mem : DrawsFromReadyQueue select) (p : AperiodicProcess)
    (h_disp : select witnessStart = some p) {T : ℕ} (hT : 4 ≤ T) :
    3 ≤ runWait (runStateSelect select) streamB T := by
  refine le_trans ?_ (runWait_mono _ _ hT)
  have hp : p = longJob4 := by simpa using h_mem _ _ h_disp
  subst hp
  have h_step : ∀ t, runStateSelect select streamB (t + 1) =
      stepNonPreemptiveStateSelect select { runStateSelect select streamB t with
        ready := (runStateSelect select streamB t).ready ++ streamB (t + 1) } := fun _ => rfl
  -- step 0: the long job is dispatched, untouched
  have h0 := stepNonPreemptiveStateSelect_dispatch select witnessStart rfl h_disp
  have h0r : (runStateSelect select streamB 0).running = some longJob4 := h0.1
  have h0q : (runStateSelect select streamB 0).ready = [] := h0.2.trans (by simp)
  -- steps 1-3: the long job ticks, the unit job (arrived at time 1) waits
  have h1 := stepNonPreemptiveStateSelect_tick select
    { runStateSelect select streamB 0 with
      ready := (runStateSelect select streamB 0).ready ++ streamB 1 }
    h0r (by simp [longJob])
  rw [← h_step 0] at h1
  obtain ⟨h1r, h1q⟩ := h1
  simp only [h0q, List.nil_append] at h1q
  have h2 := stepNonPreemptiveStateSelect_tick select
    { runStateSelect select streamB 1 with
      ready := (runStateSelect select streamB 1).ready ++ streamB 2 }
    h1r (by simp [longJob])
  rw [← h_step 1] at h2
  obtain ⟨h2r, h2q⟩ := h2
  simp only [h1q] at h2q
  have h3 := stepNonPreemptiveStateSelect_tick select
    { runStateSelect select streamB 2 with
      ready := (runStateSelect select streamB 2).ready ++ streamB 3 }
    h2r (by simp [longJob])
  rw [← h_step 2] at h3
  obtain ⟨_, h3q⟩ := h3
  simp only [h2q] at h3q
  rw [runWait_four, h1q, h2q, h3q]
  simp only [streamB, lateConvoyArrivalStream, List.append_nil, List.length_singleton]
  omega

/-! ## Optimal and beaten, over the first `T` steps

The first, intuitive definition of optimality: wait least **on every stream**,
counting the waiting over the first `T` steps.  Its negation has its own name,
`IsBeatenOverSteps`, so that "not optimal" can be stated as "beaten"
(`not_isOptimalOverSteps_iff`).  This file shows that no non-preemptive policy is
optimal in this sense once `T ≥ 4`; `SJFOptimalityGivenSamePast` proves SJF optimal in a
second sense, given the same past.
-/

/-- `select` is **optimal over the first `T` steps**: on every well-formed stream, it
waits no longer over the first `T` steps than any other non-preemptive state-select
policy. -/
def IsOptimalOverSteps (T : ℕ) (select : SchedState → Option AperiodicProcess) : Prop :=
  ∀ select', DrawsFromReadyQueue select' →
    ∀ arrival_stream, WellFormedStream arrival_stream →
      runWait (runStateSelect select) arrival_stream T ≤
        runWait (runStateSelect select') arrival_stream T

/-- `select` is **beaten over the first `T` steps**: on some well-formed stream, some
other non-preemptive state-select policy waits strictly less over the first `T`
steps. -/
def IsBeatenOverSteps (T : ℕ) (select : SchedState → Option AperiodicProcess) : Prop :=
  ∃ select', DrawsFromReadyQueue select' ∧
    ∃ arrival_stream, WellFormedStream arrival_stream ∧
      runWait (runStateSelect select') arrival_stream T <
        runWait (runStateSelect select) arrival_stream T

/-- **Not optimal is beaten.** -/
theorem not_isOptimalOverSteps_iff (T : ℕ) (select : SchedState → Option AperiodicProcess) :
    ¬ IsOptimalOverSteps T select ↔ IsBeatenOverSteps T select := by
  simp only [IsOptimalOverSteps, IsBeatenOverSteps, not_forall, not_le, exists_prop]

/-! ## No policy is optimal -/

/-- **Every non-preemptive state-select policy is strictly beaten on stream A or on
stream B by another non-preemptive state-select policy**, the same competitor at
every horizon `T ≥ 4`.  Step 0 sees the same state on both streams.  If the
policy dispatches the long job there, "idle at time 0, then SJF" waits less on
stream B (2 against at least 3); if it idles, FCFS waits less on stream A (0
against at least 1). -/
theorem nonPreemptive_beaten_on_streamA_or_streamB (select : SchedState → Option AperiodicProcess)
    (h_mem : DrawsFromReadyQueue select) :
    ∃ select', DrawsFromReadyQueue select' ∧
      ((∀ T, 4 ≤ T →
          runWait (runStateSelect select') streamA T < runWait (runStateSelect select) streamA T) ∨
        (∀ T, 4 ≤ T →
          runWait (runStateSelect select') streamB T <
            runWait (runStateSelect select) streamB T)) := by
  cases h : select witnessStart with
  | none =>
    refine ⟨fcfsStateSelect, fcfsStateSelect_drawsFromReadyQueue, Or.inl fun T hT => ?_⟩
    have := idle_costs_on_streamA select h (T := T) (by omega)
    rw [runWait_fcfsStateSelect_streamA T hT]
    omega
  | some p =>
    refine ⟨idleThenSJF, idleThenSJF_drawsFromReadyQueue, Or.inr fun T hT => ?_⟩
    have := dispatch_costs_on_streamB select h_mem p h hT
    rw [runWait_idleThenSJF_streamB T hT]
    omega

/-- **Every non-preemptive state-select policy is beaten** over the first `T` steps,
for every `T ≥ 4`. -/
theorem every_nonPreemptive_isBeatenOverSteps :
    ∀ T, 4 ≤ T → ∀ select, DrawsFromReadyQueue select → IsBeatenOverSteps T select := by
  intro T hT select h_mem
  obtain ⟨select', h_mem', h_lt | h_lt⟩ := nonPreemptive_beaten_on_streamA_or_streamB select h_mem
  · exact ⟨select', h_mem', streamA, streamA_wf, h_lt T hT⟩
  · exact ⟨select', h_mem', streamB, streamB_wf, h_lt T hT⟩

/-- **No non-preemptive state-select policy is optimal on every stream**: none is
optimal over the first `T` steps, for any `T ≥ 4`. -/
theorem no_optimal_nonPreemptive_on_every_stream :
    ∀ T, 4 ≤ T → ¬ ∃ select, DrawsFromReadyQueue select ∧ IsOptimalOverSteps T select := by
  rintro T hT ⟨select, h_mem, h_opt⟩
  exact (not_isOptimalOverSteps_iff T select).mpr
    (every_nonPreemptive_isBeatenOverSteps T hT select h_mem) h_opt

/-- **SJF is not an optimal non-preemptive state-select scheduler**: on stream B, at
every horizon `T ≥ 4`, idling once and then running SJF waits 2 ticks, while
SJF itself waits at least 3.  (SJF is optimal on batches, `runWait_sjf_le`: it
is the late arrival that it cannot anticipate.) -/
theorem sjf_beaten_by_idleThenSJF_on_streamB :
    DrawsFromReadyQueue idleThenSJF ∧ WellFormedStream streamB ∧
      ∀ T, 4 ≤ T → runWait (runStateSelect idleThenSJF) streamB T <
        runWait (runSteps · stepSJF) streamB T := by
  refine ⟨idleThenSJF_drawsFromReadyQueue, streamB_wf, fun T hT => ?_⟩
  have := runWait_mono (runSteps · stepSJF) streamB hT
  rw [runWait_sjf_streamB_four] at this
  rw [runWait_idleThenSJF_streamB T hT]
  omega

end ConvoyEffect
