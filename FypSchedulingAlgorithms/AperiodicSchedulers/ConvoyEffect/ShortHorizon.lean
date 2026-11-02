/-
Copyright (c) 2026 Choo Kye Yong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Choo Kye Yong
-/
import FypSchedulingAlgorithms.AperiodicSchedulers.ConvoyEffect.NoOptimalNonPreemptiveOnEveryStream

/-!
# SJF is optimal over the first three steps

`no_optimal_nonPreemptive_on_every_stream` says that from horizon `T = 4` on, no
non-preemptive state-select policy waits least on every well-formed stream.  This file
shows that `4` is sharp: at every horizon `T ≤ 3`, SJF does
(`sjf_isOptimalOverSteps_of_le_three`), so an optimal policy exists exactly when `T ≤ 3`
(`exists_optimal_iff`).

**Why three steps are not enough to regret.**  A dispatched job never returns to
`ready`, so the wait over the first `T` steps is fixed by how many jobs each step
dispatches: dispatch as many as possible, as early as possible.  The only reason to idle
is to keep the CPU free for a short job arriving later.  A unit job arriving at time 1
is dispatched at step 1 and frees the CPU at step 2; that pays back the tick lost by
idling only from step 3 on, which is outside a horizon of 3.

**The proof.**  It compares SJF with any competitor step by step, through two numbers
per state: the length of `ready`, and the ticks the running job has left
(`runningRemaining`; the next step decides exactly when this is at most 1).
`stepNonPreemptiveStateSelect_cases` lists what one step can do: tick a running job,
idle, or dispatch a waiting job.  SJF never idles while a job waits, and it dispatches a
job of least burst.  Cases on steps 0 and 1 of both runs leave linear arithmetic, which
`omega` closes, except for one point.  If both runs dispatch at steps 0 and 1, SJF's job
at step 1 must be no longer than the competitor's, although their queues differ by the
job each dispatched at step 0 (`exists_burst_le_of_mem_erase_append`).  At step 2 only
the queue lengths matter.
-/

namespace ConvoyEffect

open NonPreemptive

/-- The ticks the running job has left, or 0 when the CPU is idle.  The next step makes a
decision (the CPU is idle or its job finishes) exactly when this is at most 1. -/
def runningRemaining (s : SchedState) : ℕ :=
  match s.running with
  | none => 0
  | some p => p.remaining

/-- **What one non-preemptive step can do.**  If the running job has two or more ticks
left, it is ticked and the queue is unchanged.  Otherwise the step decides: it idles,
leaving the queue unchanged and the CPU empty, or it dispatches a waiting job `q`,
which leaves the queue and goes on the CPU unticked. -/
theorem stepNonPreemptiveStateSelect_cases {select : SchedState → Option AperiodicProcess}
    (h_mem : DrawsFromReadyQueue select) {s s' : SchedState}
    (h_step : s' = stepNonPreemptiveStateSelect select s) :
    (2 ≤ runningRemaining s ∧ s'.ready = s.ready ∧
        runningRemaining s' = runningRemaining s - 1) ∨
      (runningRemaining s ≤ 1 ∧ select s = none ∧ s'.ready = s.ready ∧
        runningRemaining s' = 0) ∨
      (runningRemaining s ≤ 1 ∧ ∃ q, select s = some q ∧ q ∈ s.ready ∧
        s'.ready = s.ready.erase q ∧ runningRemaining s' = q.remaining) := by
  subst h_step
  by_cases h2 : 2 ≤ runningRemaining s
  · left
    cases h_run : s.running with
    | none => simp [runningRemaining, h_run] at h2
    | some p =>
      have hp : 1 < p.remaining := by
        simp only [runningRemaining, h_run] at h2
        omega
      obtain ⟨h1, h2'⟩ := stepNonPreemptiveStateSelect_tick select s h_run hp
      refine ⟨h2, h2', ?_⟩
      simp [runningRemaining, h1, h_run]
  · right
    have h_dec : ∀ p, s.running = some p → p.remaining ≤ 1 := by
      intro p hp
      simp only [runningRemaining, hp] at h2
      omega
    obtain ⟨h_some, h_none⟩ := stepNonPreemptiveStateSelect_decide select s h_dec
    cases h_sel : select s with
    | none =>
      obtain ⟨h1, h2'⟩ := h_none h_sel
      exact Or.inl ⟨by omega, rfl, h2', by simp [runningRemaining, h1]⟩
    | some q =>
      obtain ⟨h1, h2'⟩ := h_some q h_sel
      exact Or.inr ⟨by omega, q, rfl, h_mem s q h_sel, h2', by simp [runningRemaining, h1]⟩

/-- **Queue length after any step.**  arrival_stream step dispatches at most one job, so the queue
shrinks by at most one; while the running job has two or more ticks left it does not
change. -/
theorem length_ready_stepNonPreemptiveStateSelect
    {select : SchedState → Option AperiodicProcess} (h_mem : DrawsFromReadyQueue select)
    {s s' : SchedState} (h_step : s' = stepNonPreemptiveStateSelect select s) :
    s.ready.length - 1 ≤ s'.ready.length ∧
      (2 ≤ runningRemaining s → s'.ready.length = s.ready.length) := by
  rcases stepNonPreemptiveStateSelect_cases h_mem h_step with
    ⟨h, hr, -⟩ | ⟨h, -, hr, -⟩ | ⟨h, q, -, hq, hr, -⟩
  · simp [hr]
  · simp only [hr]
    omega
  · rw [hr, List.length_erase_of_mem hq]
    omega

/-- SJF as a state-select policy. -/
abbrev sjfStateSelect : SchedState → Option AperiodicProcess := fun s => selectSJF s.ready

/-- SJF dispatches a waiting job whenever the CPU is free. -/
theorem sjfStateSelect_drawsFromReadyQueue : DrawsFromReadyQueue sjfStateSelect :=
  fun s p h => selectSJF_mem s.ready p h

/-- **Queue length after an SJF step.**  SJF never idles while a job waits, so when the
step decides, the queue shrinks by one (or stays empty). -/
theorem length_ready_stepSJFStateSelect {s s' : SchedState}
    (h_step : s' = stepNonPreemptiveStateSelect sjfStateSelect s) :
    (runningRemaining s ≤ 1 → s'.ready.length = s.ready.length - 1) ∧
      (2 ≤ runningRemaining s → s'.ready.length = s.ready.length) := by
  rcases stepNonPreemptiveStateSelect_cases sjfStateSelect_drawsFromReadyQueue h_step with
    ⟨h, hr, -⟩ | ⟨h, h_sel, hr, -⟩ | ⟨h, q, -, hq, hr, -⟩
  · exact ⟨fun h' => by omega, fun _ => by rw [hr]⟩
  · have h_nil : s.ready = [] := selectSJF_none_imp_empty _ h_sel
    exact ⟨fun _ => by simp [hr, h_nil], fun h' => by omega⟩
  · exact ⟨fun _ => by rw [hr, List.length_erase_of_mem hq], fun h' => by omega⟩

/-- If a unit job `p` of `l` was dispatched and then `r` was taken from what was left
and the next arrivals `m`, then dispatching any other job `q` of `l` first still leaves
a job no longer than `r`: either `r` itself, or `p`. -/
theorem exists_burst_le_of_mem_erase_append {l m : List AperiodicProcess}
    {p q r : AperiodicProcess} (hp : p ∈ l) (hp1 : p.burst ≤ 1) (hr : r ∈ l.erase p ++ m) :
    ∃ x ∈ l.erase q ++ m, x.burst ≤ r.burst := by
  rcases List.mem_append.mp hr with hr | hr
  · by_cases hpq : p = q
    · subst hpq
      exact ⟨r, List.mem_append_left _ hr, le_rfl⟩
    · exact ⟨p, List.mem_append_left _ (List.mem_erase_of_ne hpq |>.mpr hp),
        le_trans hp1 r.burst_exceed_zero⟩
  · exact ⟨r, List.mem_append_right _ hr, le_rfl⟩

/-- **SJF's queue is no longer, summed over each of the first three steps.**  Against any
non-preemptive state-select policy, on any well-formed stream, the ready-queue lengths
of SJF after step 0, after steps 0–1 and after steps 0–2 add up to no more than the
competitor's. -/
theorem sjf_ready_length_sums_le_over_first_three_steps
    (select : SchedState → Option AperiodicProcess) (h_mem : DrawsFromReadyQueue select)
    (arrival_stream : ℕ → List AperiodicProcess) (h_wf : WellFormedStream arrival_stream) :
    let ℓ := fun t => (runStateSelect sjfStateSelect arrival_stream t).ready.length
    let ℓ' := fun t => (runStateSelect select arrival_stream t).ready.length
    ℓ 0 ≤ ℓ' 0 ∧ ℓ 0 + ℓ 1 ≤ ℓ' 0 + ℓ' 1 ∧ ℓ 0 + ℓ 1 + ℓ 2 ≤ ℓ' 0 + ℓ' 1 + ℓ' 2 := by
  intro ℓ ℓ'
  dsimp only [ℓ, ℓ']
  have h_sjf := sjfStateSelect_drawsFromReadyQueue
  set S := runStateSelect sjfStateSelect arrival_stream with hS_def
  set S' := runStateSelect select arrival_stream with hS'_def
  set B := stateBefore arrival_stream (stepNonPreemptiveStateSelect sjfStateSelect) with hB_def
  set B' := stateBefore arrival_stream (stepNonPreemptiveStateSelect select) with hB'_def
  have hS : ∀ t, S t = stepNonPreemptiveStateSelect sjfStateSelect (B t) :=
    runSteps_eq_step_stateBefore arrival_stream _
  have hS' : ∀ t, S' t = stepNonPreemptiveStateSelect select (B' t) :=
    runSteps_eq_step_stateBefore arrival_stream _
  have hf : ∀ t, ∀ q ∈ (B t).ready, q.remaining = q.burst :=
    stateBefore_ready_fresh sjfStateSelect arrival_stream h_wf
  have hf' : ∀ t, ∀ q ∈ (B' t).ready, q.remaining = q.burst :=
    stateBefore_ready_fresh select arrival_stream h_wf
  have hB0r : (B 0).ready = arrival_stream 0 := rfl
  have hB0r' : (B' 0).ready = arrival_stream 0 := rfl
  have hB0l : (B' 0).ready.length = (B 0).ready.length := rfl
  have hB0ρ : runningRemaining (B 0) = 0 := rfl
  have hB0ρ' : runningRemaining (B' 0) = 0 := rfl
  have hB1r : (B 1).ready = (S 0).ready ++ arrival_stream 1 := rfl
  have hB1r' : (B' 1).ready = (S' 0).ready ++ arrival_stream 1 := rfl
  have hB1ρ : runningRemaining (B 1) = runningRemaining (S 0) := rfl
  have hB1ρ' : runningRemaining (B' 1) = runningRemaining (S' 0) := rfl
  have hB1l : (B 1).ready.length = (S 0).ready.length + (arrival_stream 1).length := by
    rw [hB1r, List.length_append]
  have hB1l' : (B' 1).ready.length = (S' 0).ready.length + (arrival_stream 1).length := by
    rw [hB1r', List.length_append]
  have hB2l : (B 2).ready.length = (S 1).ready.length + (arrival_stream 2).length := by
    rw [← List.length_append]; rfl
  have hB2l' : (B' 2).ready.length = (S' 1).ready.length + (arrival_stream 2).length := by
    rw [← List.length_append]; rfl
  have hB2ρ : runningRemaining (B 2) = runningRemaining (S 1) := rfl
  have hB2ρ' : runningRemaining (B' 2) = runningRemaining (S' 1) := rfl
  -- step 2: only the queue lengths matter
  obtain ⟨g2a, g2b⟩ := length_ready_stepNonPreemptiveStateSelect h_mem (hS' 2)
  obtain ⟨s2a, s2b⟩ := length_ready_stepSJFStateSelect (hS 2)
  rw [hB2l'] at g2a g2b
  rw [hB2ρ'] at g2b
  rw [hB2l] at s2a s2b
  rw [hB2ρ] at s2a s2b
  -- step 1, for any policy
  obtain ⟨g1a, g1b⟩ := length_ready_stepNonPreemptiveStateSelect h_mem (hS' 1)
  obtain ⟨s1a, s1b⟩ := length_ready_stepSJFStateSelect (hS 1)
  rw [hB1l'] at g1a g1b
  rw [hB1ρ'] at g1b
  rw [hB1l] at s1a s1b
  rw [hB1ρ] at s1a s1b
  -- step 0
  rcases stepNonPreemptiveStateSelect_cases h_sjf (hS 0) with
    ⟨h, -⟩ | ⟨-, hsel0, hr0, hρ0⟩ | ⟨-, q0, hsel0, hq0, hr0, hρ0⟩
  · omega
  · -- nothing arrives at time 0, so the competitor idles too
    have hA0 : arrival_stream 0 = [] := selectSJF_none_imp_empty _ hsel0
    rcases stepNonPreemptiveStateSelect_cases h_mem (hS' 0) with
      ⟨h, -⟩ | ⟨-, -, hr0', hρ0'⟩ | ⟨-, p0, -, hp0, -, -⟩
    · omega
    · have e0 : (S 0).ready.length = 0 := by simp [hr0, hB0r, hA0]
      have e0' : (S' 0).ready.length = 0 := by simp [hr0', hB0r', hA0]
      have hB1 : (B' 1).ready = (B 1).ready := by rw [hB1r, hB1r', hr0, hr0', hB0r, hB0r']
      rw [hρ0] at s1a s1b
      rw [hρ0'] at g1b
      rcases stepNonPreemptiveStateSelect_cases h_sjf (hS 1) with
          ⟨h1, -⟩ | ⟨-, -, hr1, hρ1⟩ | ⟨-, q1, hsel1, hq1, hr1, hρ1⟩ <;>
        rcases stepNonPreemptiveStateSelect_cases h_mem (hS' 1) with
          ⟨h1', -⟩ | ⟨-, -, hr1', hρ1'⟩ | ⟨-, p1, -, hp1, hr1', hρ1'⟩
      all_goals (try rw [hB1ρ, hρ0] at h1)
      all_goals (try rw [hB1ρ', hρ0'] at h1')
      all_goals (try rw [hf 1 q1 hq1] at hρ1)
      all_goals (try rw [hf' 1 p1 hp1] at hρ1')
      all_goals (try have e1' := congrArg List.length hr1')
      all_goals (try rw [List.length_erase_of_mem hp1] at e1')
      all_goals (try have p1pos := List.length_pos_of_mem hp1)
      all_goals (try have q1pos := List.length_pos_of_mem hq1)
      all_goals (try have hle : q1.burst ≤ p1.burst :=
        selectSJF_min _ q1 hsel1 p1 (by rw [← hB1]; exact hp1))
      all_goals (try rw [hρ1] at s2a s2b)
      all_goals (try rw [hρ1'] at g2b)
      all_goals omega
    · simp [hB0r', hA0] at hp0
  · -- SJF dispatches a shortest job `q0` at time 0
    rw [hf 0 q0 hq0] at hρ0
    rw [hρ0] at s1a s1b
    have e0 := congrArg List.length hr0
    rw [List.length_erase_of_mem hq0] at e0
    have q0pos := List.length_pos_of_mem hq0
    have q0burst := q0.burst_exceed_zero
    have hmin0 : ∀ x ∈ (B 0).ready, q0.burst ≤ x.burst := selectSJF_min _ q0 hsel0
    rcases stepNonPreemptiveStateSelect_cases h_mem (hS' 0) with
      ⟨h, -⟩ | ⟨-, -, hr0', hρ0'⟩ | ⟨-, p0, -, hp0, hr0', hρ0'⟩
    · omega
    · -- the competitor idles at time 0
      have e0' := congrArg List.length hr0'
      rw [hρ0'] at g1b
      rcases stepNonPreemptiveStateSelect_cases h_sjf (hS 1) with
          ⟨h1, -, hρ1⟩ | ⟨h1, -, hr1, hρ1⟩ | ⟨h1, q1, hsel1, hq1, hr1, hρ1⟩
      all_goals (try rw [hB1ρ, hρ0] at h1)
      all_goals (try rw [hB1ρ, hρ0] at hρ1)
      all_goals (try rw [hf 1 q1 hq1] at hρ1)
      all_goals (try rw [hρ1] at s2a s2b)
      all_goals (try have q1pos := List.length_pos_of_mem hq1)
      all_goals omega
    · -- the competitor dispatches `p0` at time 0, no shorter than `q0`
      have hle0 : q0.burst ≤ p0.burst := hmin0 p0 hp0
      rw [hf' 0 p0 hp0] at hρ0'
      rw [hρ0'] at g1b
      have e0' := congrArg List.length hr0'
      rw [List.length_erase_of_mem hp0] at e0'
      -- if `p0` is a unit job, SJF's queue at time 1 has a job as short as any the
      -- competitor's has
      have hR1 : p0.burst ≤ 1 → ∀ q1 p1, sjfStateSelect (B 1) = some q1 →
          p1 ∈ (B' 1).ready → q1.burst ≤ p1.burst := by
        intro hp01 q1 p1 hsel1 hp1
        rw [hB1r', hr0', hB0r'] at hp1
        obtain ⟨x, hx, hxp⟩ :=
          exists_burst_le_of_mem_erase_append (q := q0) (hB0r ▸ hp0) hp01 hp1
        rw [← hB0r, ← hr0, ← hB1r] at hx
        exact le_trans (selectSJF_min _ q1 hsel1 x hx) hxp
      rcases stepNonPreemptiveStateSelect_cases h_sjf (hS 1) with
          ⟨h1, -, hρ1⟩ | ⟨h1, -, hr1, hρ1⟩ | ⟨h1, q1, hsel1, hq1, hr1, hρ1⟩ <;>
        rcases stepNonPreemptiveStateSelect_cases h_mem (hS' 1) with
          ⟨h1', -, hρ1'⟩ | ⟨h1', -, hr1', hρ1'⟩ | ⟨h1', p1, -, hp1, hr1', hρ1'⟩
      all_goals (try rw [hB1ρ, hρ0] at h1)
      all_goals (try rw [hB1ρ, hρ0] at hρ1)
      all_goals (try rw [hB1ρ', hρ0'] at h1')
      all_goals (try rw [hB1ρ', hρ0'] at hρ1')
      all_goals (try rw [hf 1 q1 hq1] at hρ1)
      all_goals (try rw [hf' 1 p1 hp1] at hρ1')
      all_goals (try have e1' := congrArg List.length hr1')
      all_goals (try rw [List.length_erase_of_mem hp1] at e1')
      all_goals (try have p1pos := List.length_pos_of_mem hp1)
      all_goals (try have q1pos := List.length_pos_of_mem hq1)
      all_goals (try have hle1 : q1.burst ≤ p1.burst := hR1 h1' q1 p1 hsel1 hp1)
      all_goals (try rw [hρ1] at s2a s2b)
      all_goals (try rw [hρ1'] at g2b)
      all_goals omega


/-! ## SJF is optimal over the first three steps -/

/-- **SJF is optimal over the first `T` steps for every `T ≤ 3`**: on every well-formed
stream it waits no longer than any non-preemptive state-select policy.  The bound is
sharp: from `T = 4` no policy is optimal (`no_optimal_nonPreemptive_on_every_stream`). -/
theorem sjf_isOptimalOverSteps_of_le_three {T : ℕ} (hT : T ≤ 3) :
    IsOptimalOverSteps T (fun s => selectSJF s.ready) := by
  intro select h_mem arrival_stream h_wf
  have h := sjf_ready_length_sums_le_over_first_three_steps select h_mem arrival_stream h_wf
  dsimp only at h
  obtain ⟨h1, h2, h3⟩ := h
  change runWait (runStateSelect sjfStateSelect) arrival_stream T ≤
    runWait (runStateSelect select) arrival_stream T
  rcases (by omega : T = 0 ∨ T = 1 ∨ T = 2 ∨ T = 3) with rfl | rfl | rfl | rfl <;>
    simp only [runWait, List.range_succ, List.range_zero, List.nil_append, List.map_append,
      List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil] <;>
    omega

/-- **An optimal non-preemptive state-select policy exists exactly at the horizons
`T ≤ 3`.**  For `T ≤ 3` SJF is one (`sjf_isOptimalOverSteps_of_le_three`); for `T ≥ 4`
there is none (`no_optimal_nonPreemptive_on_every_stream`). -/
theorem exists_optimal_iff (T : ℕ) :
    (∃ select, DrawsFromReadyQueue select ∧ IsOptimalOverSteps T select) ↔ T ≤ 3 := by
  constructor
  · intro h
    by_contra hT
    exact no_optimal_nonPreemptive_on_every_stream T (by omega) h
  · intro hT
    exact ⟨_, sjfStateSelect_drawsFromReadyQueue, sjf_isOptimalOverSteps_of_le_three hT⟩

end ConvoyEffect
