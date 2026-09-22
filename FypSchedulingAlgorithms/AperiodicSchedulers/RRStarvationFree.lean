/-
Copyright (c) 2026 Choo Kye Yong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Choo Kye Yong
-/

import FypSchedulingAlgorithms.Process
import FypSchedulingAlgorithms.Step
import FypSchedulingAlgorithms.SchedState
import FypSchedulingAlgorithms.AperiodicSchedulers.AperiodicStep
import FypSchedulingAlgorithms.ProcessSimpLemmas
import Mathlib.Tactic.Linarith
import FypSchedulingAlgorithms.ListLemmas

/-!
# Starvation-freedom for Round Robin

Starvation: a process sits in the ready queue but never runs because it keeps
losing out to newer arrivals or a scheduler's prioritisation.

Processes arrive via an infinite `arrival_stream : ℕ → List AperiodicProcess`
(only finitely many arrive at each tick). `WellFormedStream` (`Step.lean`)
pins each process's `arrival` field to the time it actually shows up and
requires it to be `remaining = burst`-fresh on arrival.

The main result is `StarvationFree`: under `stepRR` with any `quantum`, every
process that ever arrives eventually shows up in `completed` (matched by `id`,
since `remaining` changes as a process runs).

Unlike a non-preemptive scheduler, a Round Robin process need not run straight
to completion once dispatched — quantum expiry can send it back to the queue.
So the argument alternates two phases, with `remaining` as the overall measure:

* *Getting to the front.* `waiting_is_ready_or_running` locates a just-arrived
  process as a canonical `pre ++ target :: suf` split of the ready queue (via
  `mem_split_canonical`), or shows it is already running.
  `target_index_decreases_one_step` shows one step either dispatches `target`,
  strictly shrinks `pre`, or leaves `pre` alone while the running process ticks
  down; `target_progresses` and `ready_eventually_runs` iterate that to reach
  the front. Quantum expiry never costs `target` ground, because the preempted
  process is appended to the *back* of the queue.
* *Making progress once running.* `running_step_cases` enumerates what one step
  does to the running process — finish it, preempt it to the back one tick
  lighter, or tick it down in place. `running_puts_at_back_or_completes` iterates
  that: within finitely many steps the process either completes or is back in
  the queue with strictly smaller `remaining`.

`StarvationFree` then inducts on `remaining`: each turn strictly decreases it,
so a process can be sent back to the queue only finitely often.

Supporting facts: `idle_implies_empty_ready` and its contrapositive
`ready_nonempty_implies_running_nonempty` relate an idle CPU to an empty queue,
and the state invariants `remaining_pos_of_ready_or_running` (nothing queued or
running has run out of time), `system_arrival_bound` (nothing from the future is
scheduled) and `system_provenance` (the scheduler invents no processes).

Generic list helpers used throughout (`mem_split_canonical`, `erase_head_split`,
`dispatch_preserves`, `expire_swap_preserves`) live in `ListLemmas.lean`, and are
stated for an arbitrary element type and predicate so both this file and
`FCFSStarvationFree.lean` can draw on them.
-/

namespace RRStarvation

/-- If the scheduler has nothing running at time `t`, the ready queue must be
empty too (otherwise stepRR would have dispatched the queue's head). -/
theorem idle_implies_empty_ready
  (arrival_stream : ℕ → List AperiodicProcess)
  (t quantum: ℕ)
  (h_running : (runStepsRR quantum arrival_stream t).sched.running = none) :
  (runStepsRR quantum arrival_stream t).sched.ready = [] := by
  induction t with
  | zero =>
    simp only [runStepsRR, stepRR] at h_running ⊢
    have h_init_running : (SchedStateMethods.init : SchedStateG AperiodicProcess).running = none := by
      rfl
    -- after unfolding, running = none forces the ready-queue match to have
    -- taken its `[]` branch, which is exactly the goal
    simp only [h_init_running] at h_running ⊢
    split at h_running
    · rename_i h_select
      assumption
    · simp at h_running
  | succ t ih =>
    simp only [runStepsRR, stepRR] at h_running ⊢
    split at h_running
    · -- prev.running = none, so stepRR dispatched off the ready queue
      rename_i h_prev_none
      split at h_running
      · -- ready was empty → nothing dispatched, and it stays empty
        simp only [List.append_eq_nil_iff] at h_running ⊢
        apply And.intro
        · exact ih h_running
        · rename_i step_concat_arrivals_eq_none
          have h_ready_empty := ih h_running
          rwa [h_ready_empty, List.nil_append] at step_concat_arrivals_eq_none
      · -- ready was p :: ps → running = some p, contradicts h_running
        contradiction
    · -- prev.running = some p, process ticked
      split at h_running
      · -- remaining ≤ 0, p completed, so the next process (if any) was dispatched
        rename_i h_remaining_after_tick_zero
        split at h_running
        · simp only [h_remaining_after_tick_zero, ↓reduceIte]
          rename_i h_none_after_1_step
          exact h_none_after_1_step
        · contradiction
      · -- remaining > 0, running = some p, contradicts h_running = none
        -- clear h_running
        rename_i p p_running p_remaining_mt_1
        simp [p_remaining_mt_1]
        split at h_running
        · split at h_running
          · simp at h_running
          · simp at h_running
        · simp at h_running

/-- Contrapositive of `idle_implies_empty_ready`: a nonempty ready queue at
time `t` means some process must be running at time `t`. -/
theorem ready_nonempty_implies_running_nonempty
  (arrival_stream : ℕ → List AperiodicProcess)
  (t quantum: ℕ)
  (h_ready_nonempty : (runStepsRR quantum arrival_stream t).sched.ready ≠ []):
  ∃ p_running : AperiodicProcess, (runStepsRR quantum arrival_stream t).sched.running = some p_running :=
  by
  cases h : (runStepsRR quantum arrival_stream t).sched.running with
  | none =>
    exfalso
    have := idle_implies_empty_ready arrival_stream t quantum h
    tauto
  | some p => exact ⟨p, rfl⟩

/-- Under a well-formed arrival stream, every process currently sitting in
the ready queue or running at time `t` still has positive `remaining` time
left (it arrived with `remaining = burst > 0`, and a tick only ever reduces the
*running* process's `remaining`, moving it to `completed` once it hits zero). -/
lemma remaining_pos_of_ready_or_running
  (arrival_stream : ℕ → List AperiodicProcess)
  (h_wf : WellFormedStream arrival_stream)
  (t quantum : ℕ) :
  (∀ p ∈ (runStepsRR quantum arrival_stream t).sched.ready, Process.remaining p > 0) ∧
  (∀ p, (runStepsRR quantum arrival_stream t).sched.running = some p → Process.remaining p > 0) := by
  have fresh_pos : ∀ (p : AperiodicProcess) (t_arrival : ℕ), p ∈ arrival_stream t_arrival → Process.remaining p > 0 := by
    intro p t_arrival hp
    simp only [AperiodicProcess.process_remaining, gt_iff_lt]
    rw [h_wf.fresh p t_arrival hp]
    exact Process.burst_exceed_zero p
  induction t with
  | zero =>
    have h_init_running : (SchedStateMethods.init : SchedStateG AperiodicProcess).running = none := rfl
    simp only [runStepsRR, stepRR, h_init_running]
    split
    · exact ⟨fun q hq => fresh_pos q 0 hq, by intro q hq; simp at hq⟩
    · rename_i arrival_stream_head arrival_stream_tail h_select
      refine ⟨?_, ?_⟩
      · intro q hq
        simp at hq
        exact fresh_pos q 0 (by grind)
      · intro q hq; simp only [Option.some.injEq] at hq; subst hq
        exact fresh_pos arrival_stream_head 0 (by grind)
  | succ t ih =>
    obtain ⟨ih_ready, ih_running⟩ := ih
    simp only [runStepsRR, stepRR]
    have ready_src : ∀ q ∈ (runStepsRR quantum arrival_stream t).sched.ready ++ arrival_stream (t + 1),
        Process.remaining q > 0 := by
      intro q hq
      rcases List.mem_append.mp hq with h | h
      · exact ih_ready q h
      · exact fresh_pos q (t + 1) h
    split  -- stepRR case: was anything running last tick?
    · -- running = none: dispatch straight off the (possibly just-grown) ready queue
      split  -- match on the combined ready queue
      · -- ready = []: still idle, nothing to check
        exact ⟨ready_src, by intro q hq; simp at hq; tauto⟩
      · -- ready = p :: ps: p gets dispatched to `running`, ps becomes the new ready queue
        rename_i p ps h_match   -- h_match : combined = p :: ps
        obtain ⟨h_ready, h_running⟩ := dispatch_preserves p ps (by rw [← h_match]; exact ready_src)
        exact ⟨h_ready, fun q hq => by simp only [Option.some.injEq] at hq; subst hq; exact h_running⟩
    · -- running = some p: p was already running; case on whether it finishes this tick
      rename_i p h_prev_running
      split  -- stepRR case: does p.remaining ≤ 1, i.e. does p complete this tick?
      · -- p completes: it moves to `completed`, and the next process (if any) is dispatched
        split  -- match on the combined ready queue
        · -- ready = []: p completes, CPU goes idle (running := none)
          exact ⟨ready_src, by intro q hq; simp at hq⟩
        · -- ready = p :: ps: p completes, next process p is dispatched, ps is the new ready queue
          rename_i p ps h_match   -- h_match : combined = p :: ps
          obtain ⟨h_ready, h_running⟩ := dispatch_preserves p ps (by rw [← h_match]; exact ready_src)
          exact ⟨h_ready, fun q hq => by simp only [Option.some.injEq] at hq; subst hq; exact h_running⟩
      · -- p.remaining > 1: p keeps running this tick (not preempted); only quantum bookkeeping
        -- below differs, depending on whether p's quantum has expired.
        rename_i h_not_done
        have h_tick_pos : Process.remaining { p with remaining := p.remaining - 1 } > 0 := by
          simp only [AperiodicProcess.process_remaining]
          omega
        constructor
        · -- ready-queue goal
          intro q hq
          split at hq  -- stepRR case: has p's quantum expired (ticksUsed ≥ quantum - 1)?
          · -- quantum expired: p goes back to the ready queue (with remaining - 1) if there's a next process
            split at hq  -- match on the combined ready queue
            · -- ready = []: no one to swap in, p just keeps running with remaining - 1
              simp at hq
              exact ready_src q (by grind)
            · -- ready = nx :: ps: nx is dispatched, p (remaining - 1) is appended to the back of ps
              rename_i nx ps h_match   -- h_match : combined = nx :: ps
              exact (expire_swap_preserves { p with remaining := p.remaining - 1 } nx ps
                (by rw [← h_match]; exact ready_src) h_tick_pos).1 q hq
          · -- quantum not expired: p just ticks down in place, ready queue is unchanged
            simp only [List.mem_append] at hq
            cases hq
            · exact ready_src q (by grind)
            · exact ready_src q (by grind)
        · -- running-process goal (mirror image of the ready-queue goal above)
          intro q hq
          split at hq  -- quantum expired?
          · split at hq  -- match on the combined ready queue
            · -- ready = []: p keeps running with remaining - 1 > 0 (since h_not_done)
              simp only [Option.some.injEq] at hq
              rw [← hq]
              exact h_tick_pos
            · -- ready = nx :: ps: nx is now running, already known positive via ready_src
              exact ready_src q (by grind)
          · -- quantum not expired: p keeps running with remaining - 1 > 0 (since h_not_done)
            simp only [Option.some.injEq] at hq
            rw [← hq]
            exact h_tick_pos

/-- Under a well-formed arrival stream, every process in the ready queue or
running at time `t` arrived at or before `t` (nothing from the future is
ever scheduled). -/
theorem system_arrival_bound
  (arrival_stream : ℕ → List AperiodicProcess)
  (h_wf : WellFormedStream arrival_stream)
  (t quantum: ℕ) :
  (∀ p ∈ (runStepsRR quantum arrival_stream t).sched.ready, Process.arrival p ≤ t) ∧
  (∀ p, (runStepsRR quantum arrival_stream t).sched.running = some p → Process.arrival p ≤ t) := by
  induction t with
  | zero =>
    have h_init_running : (SchedStateMethods.init : SchedStateG AperiodicProcess).running = none := rfl
    simp only [runStepsRR, stepRR, h_init_running]
    -- at time 0 the ready queue is exactly the first arrival batch, all of which arrived at 0
    have arrivals_at_zero : ∀ q ∈ arrival_stream 0, Process.arrival q ≤ 0 :=
      fun q hq => le_of_eq (h_wf.consistent q 0 hq)
    split  -- match on the initial ready queue (= arrival_stream 0)
    · -- ready = []: nothing to dispatch, CPU stays idle
      exact ⟨arrivals_at_zero, by intro q hq; simp at hq⟩
    · -- ready = p :: ps: p is dispatched to `running`, ps becomes the new ready queue
      rename_i p ps h_match   -- h_match : arrival_stream 0 = p :: ps
      obtain ⟨h_ready, h_running⟩ :=
        dispatch_preserves p ps (by rw [← h_match]; exact arrivals_at_zero)
      exact ⟨h_ready, fun q hq => by simp only [Option.some.injEq] at hq; subst hq; exact h_running⟩
  | succ t ih =>
    obtain ⟨ih_ready, ih_running⟩ := ih
    simp only [runStepsRR, stepRR]
    -- everything that could be in next tick's ready queue is either already queued (bound by
    -- `t`, so certainly by `t + 1`) or has just arrived at `t + 1`
    have ready_src : ∀ q ∈ (runStepsRR quantum arrival_stream t).sched.ready ++ arrival_stream (t + 1),
        Process.arrival q ≤ t + 1 := by
      intro q hq
      rcases List.mem_append.mp hq with h | h
      · exact le_trans (ih_ready q h) (by omega)
      · exact le_of_eq (h_wf.consistent q (t + 1) h)
    split  -- stepRR case: was anything running last tick?
    · -- running = none: dispatch straight off the (possibly just-grown) ready queue
      split  -- match on the combined ready queue
      · -- ready = []: still idle, nothing to check
        exact ⟨ready_src, by intro q hq; simp at hq; tauto⟩
      · -- ready = p :: ps: p gets dispatched to `running`, ps becomes the new ready queue
        rename_i p ps h_match   -- h_match : combined = p :: ps
        obtain ⟨h_ready, h_running⟩ := dispatch_preserves p ps (by rw [← h_match]; exact ready_src)
        exact ⟨h_ready, fun q hq => by simp only [Option.some.injEq] at hq; subst hq; exact h_running⟩
    · -- running = some p: p was already running; case on whether it finishes this tick
      rename_i p h_prev_running
      split  -- stepRR case: does p.remaining ≤ 1, i.e. does p complete this tick?
      · -- p completes: it moves to `completed`, and the next process (if any) is dispatched
        split  -- match on the combined ready queue
        · -- ready = []: p completes, CPU goes idle (running := none)
          exact ⟨ready_src, by intro q hq; simp at hq⟩
        · -- ready = nx :: ps: p completes, nx is dispatched, ps is the new ready queue
          rename_i nx ps h_match   -- h_match : combined = nx :: ps
          obtain ⟨h_ready, h_running⟩ := dispatch_preserves nx ps (by rw [← h_match]; exact ready_src)
          exact ⟨h_ready, fun q hq => by simp only [Option.some.injEq] at hq; subst hq; exact h_running⟩
      · -- p.remaining > 1: p keeps running this tick; only quantum bookkeeping differs below.
        -- Ticking never touches `arrival`, so p's own bound just weakens from `≤ t` to `≤ t + 1`.
        have h_tick_arrival : Process.arrival { p with remaining := p.remaining - 1 } ≤ t + 1 := by
          have h_p := ih_running p h_prev_running
          simp only [AperiodicProcess.process_arrival] at h_p ⊢
          omega
        split  -- stepRR case: has p's quantum expired (ticksUsed ≥ quantum - 1)?
        · -- expired: if there's a next process, swap it in and send p (ticked down) to the back
          split  -- match on the combined ready queue
          · -- ready = []: no one to swap in, p just keeps running as its ticked self
            exact ⟨ready_src, fun q hq => by
              simp only [Option.some.injEq] at hq; subst hq; exact h_tick_arrival⟩
          · -- ready = nx :: ps: nx is dispatched, p (ticked down) is appended to the back of ps
            rename_i nx ps h_match   -- h_match : combined = nx :: ps
            obtain ⟨h_ready, h_running⟩ :=
              expire_swap_preserves { p with remaining := p.remaining - 1 } nx ps
                (by rw [← h_match]; exact ready_src) h_tick_arrival
            exact ⟨h_ready, fun q hq => by
              simp only [Option.some.injEq] at hq; subst hq; exact h_running⟩
        · -- not expired: p just ticks down in place, ready queue is unchanged
          exact ⟨ready_src, fun q hq => by
            simp only [Option.some.injEq] at hq; subst hq; exact h_tick_arrival⟩

/-- Every process in the ready queue, running, or completed at time `t`
traces back (by `id`) to some process that actually arrived at some time
`s ≤ t`; the scheduler never manufactures processes out of thin air. -/
theorem system_provenance
  (arrival_stream : ℕ → List AperiodicProcess) (t quantum: ℕ) :
  (∀ p ∈ (runStepsRR quantum arrival_stream t).sched.ready,
     ∃ s ≤ t, ∃ q₀ ∈ arrival_stream s, Process.id q₀ = Process.id p) ∧
  (∀ p, (runStepsRR quantum arrival_stream t).sched.running = some p →
     ∃ s ≤ t, ∃ q₀ ∈ arrival_stream s, Process.id q₀ = Process.id p) ∧
  (∀ p ∈ (runStepsRR quantum arrival_stream t).sched.completed,
     ∃ s ≤ t, ∃ q₀ ∈ arrival_stream s, Process.id q₀ = Process.id p) := by
  induction t with
  | zero =>
    have h_init_running : (SchedStateMethods.init : SchedStateG AperiodicProcess).running = none := rfl
    have h_init_completed : (SchedStateMethods.init : SchedStateG AperiodicProcess).completed = [] := rfl
    simp only [runStepsRR, stepRR, h_init_running]
    -- at time 0 every queued process is its own witness: it arrived in the first batch
    have arrivals_at_zero : ∀ q ∈ arrival_stream 0,
        ∃ s ≤ 0, ∃ q₀ ∈ arrival_stream s, Process.id q₀ = Process.id q :=
      fun q hq => ⟨0, le_refl _, q, hq, rfl⟩
    split  -- match on the initial ready queue (= arrival_stream 0)
    · -- ready = []: nothing to dispatch, CPU idle, nothing completed
      exact ⟨arrivals_at_zero,
             by intro q hq; simp at hq,
             by intro q hq; simp [h_init_completed] at hq⟩
    · -- ready = p :: ps: p is dispatched to `running`, ps becomes the new ready queue
      rename_i p ps h_match   -- h_match : arrival_stream 0 = p :: ps
      obtain ⟨h_ready, h_running⟩ :=
        dispatch_preserves p ps (by rw [← h_match]; exact arrivals_at_zero)
      exact ⟨h_ready,
             fun q hq => by simp only [Option.some.injEq] at hq; subst hq; exact h_running,
             by intro q hq; simp [h_init_completed] at hq⟩
  | succ t ih =>
    obtain ⟨ih_ready, ih_running, ih_completed⟩ := ih
    simp only [runStepsRR, stepRR]
    -- a witness `s ≤ t` from the IH is still a witness once the clock moves to `t + 1`
    have weaken : ∀ (q: AperiodicProcess), (∃ s ≤ t, ∃ q₀ ∈ arrival_stream s, Process.id q₀ = Process.id q) →
        ∃ s ≤ t + 1, ∃ q₀ ∈ arrival_stream s, Process.id q₀ = Process.id q := by
      rintro q ⟨s, hs, q₀, hq₀, hid⟩
      exact ⟨s, by omega, q₀, hq₀, hid⟩
    -- anything that can end up queued next tick was either queued already or just arrived
    have ready_src : ∀ q ∈ (runStepsRR quantum arrival_stream t).sched.ready ++ arrival_stream (t + 1),
        ∃ s ≤ t + 1, ∃ q₀ ∈ arrival_stream s, Process.id q₀ = Process.id q := by
      intro q hq
      rcases List.mem_append.mp hq with h | h
      · exact weaken q (ih_ready q h)
      · exact ⟨t + 1, le_refl _, q, h, rfl⟩
    have completed_src : ∀ q ∈ (runStepsRR quantum arrival_stream t).sched.completed,
        ∃ s ≤ t + 1, ∃ q₀ ∈ arrival_stream s, Process.id q₀ = Process.id q :=
      fun q hq => weaken q (ih_completed q hq)
    split  -- stepRR case: was anything running last tick?
    · -- running = none: dispatch straight off the (possibly just-grown) ready queue
      split  -- match on the combined ready queue
      · -- ready = []: still idle, nothing dispatched or completed
        exact ⟨ready_src, by intro q hq; simp at hq; tauto, completed_src⟩
      · -- ready = p :: ps: p gets dispatched to `running`, ps becomes the new ready queue
        rename_i p ps h_match   -- h_match : combined = p :: ps
        obtain ⟨h_ready, h_running⟩ := dispatch_preserves p ps (by rw [← h_match]; exact ready_src)
        exact ⟨h_ready,
               fun q hq => by simp only [Option.some.injEq] at hq; subst hq; exact h_running,
               completed_src⟩
    · -- running = some p: p was already running; case on whether it finishes this tick
      rename_i p h_prev_running
      -- stepRR only ever rewrites p's `remaining`, and provenance is tracked by `id`, so
      -- p's own witness carries over to both the completed copy and the ticked-down copy
      have h_done_prov : ∃ s ≤ t + 1, ∃ q₀ ∈ arrival_stream s,
          Process.id q₀ = Process.id { p with remaining := 0 } := by
        simpa using weaken p (ih_running p h_prev_running)
      have h_tick_prov : ∃ s ≤ t + 1, ∃ q₀ ∈ arrival_stream s,
          Process.id q₀ = Process.id { p with remaining := p.remaining - 1 } := by
        simpa using weaken p (ih_running p h_prev_running)
      have completed_done : ∀ q ∈ (runStepsRR quantum arrival_stream t).sched.completed ++
            [{ p with remaining := 0 }],
          ∃ s ≤ t + 1, ∃ q₀ ∈ arrival_stream s, Process.id q₀ = Process.id q := by
        intro q hq
        rcases List.mem_append.mp hq with h | h
        · exact completed_src q h
        · simp only [List.mem_singleton] at h
          subst h
          exact h_done_prov
      split  -- stepRR case: does p.remaining ≤ 1, i.e. does p complete this tick?
      · -- p completes: it joins `completed`, and the next process (if any) is dispatched
        split  -- match on the combined ready queue
        · -- ready = []: p completes, CPU goes idle (running := none)
          exact ⟨ready_src, by intro q hq; simp at hq, completed_done⟩
        · -- ready = nx :: ps: p completes, nx is dispatched, ps is the new ready queue
          rename_i nx ps h_match   -- h_match : combined = nx :: ps
          obtain ⟨h_ready, h_running⟩ := dispatch_preserves nx ps (by rw [← h_match]; exact ready_src)
          exact ⟨h_ready,
                 fun q hq => by simp only [Option.some.injEq] at hq; subst hq; exact h_running,
                 completed_done⟩
      · -- p.remaining > 1: p keeps running, nothing completes; only quantum bookkeeping differs
        split  -- stepRR case: has p's quantum expired (ticksUsed ≥ quantum - 1)?
        · -- expired: if there's a next process, swap it in and send p (ticked down) to the back
          split  -- match on the combined ready queue
          · -- ready = []: no one to swap in, p just keeps running as its ticked self
            exact ⟨ready_src,
                   fun q hq => by simp only [Option.some.injEq] at hq; subst hq; exact h_tick_prov,
                   completed_src⟩
          · -- ready = nx :: ps: nx is dispatched, p (ticked down) is appended to the back of ps
            rename_i nx ps h_match   -- h_match : combined = nx :: ps
            obtain ⟨h_ready, h_running⟩ :=
              expire_swap_preserves { p with remaining := p.remaining - 1 } nx ps
                (by rw [← h_match]; exact ready_src) h_tick_prov
            exact ⟨h_ready,
                   fun q hq => by simp only [Option.some.injEq] at hq; subst hq; exact h_running,
                   completed_src⟩
        · -- not expired: p just ticks down in place, ready queue is unchanged
          exact ⟨ready_src,
                 fun q hq => by simp only [Option.some.injEq] at hq; subst hq; exact h_tick_prov,
                 completed_src⟩

/-- One Round Robin step, from a state where `target` sits at position `pre.length`
in the ready queue (`ready = pre ++ target :: suf`, `target ∉ pre`), leads to
exactly one of: `target` is now running; `target`'s prefix strictly shrank (the
process at the front of the queue was dispatched); or the prefix length is
unchanged because the running process merely ticked (and continues running as its
ticked self next step).

Quantum expiry never costs `target` any ground: the preempted process is appended
to the *back* of the queue, which only ever lengthens `suf`. -/
theorem target_index_decreases_one_step
  (arrival_stream : ℕ → List AperiodicProcess)
  (target : AperiodicProcess) (t quantum: ℕ) (pre suf : List AperiodicProcess)
  (h_split : (runStepsRR quantum arrival_stream t).sched.ready = pre ++ target :: suf)
  (h_target_not_in_pre : target ∉ pre) :
  (runStepsRR quantum arrival_stream (t + 1)).sched.running = some target
  ∨ (∃ pre' suf', (runStepsRR quantum arrival_stream (t + 1)).sched.ready = pre' ++ target :: suf'
                 ∧ target ∉ pre'
                 ∧ pre'.length < pre.length)
  ∨ (∃ pre' suf', (runStepsRR quantum arrival_stream (t + 1)).sched.ready = pre' ++ target :: suf'
                 ∧ target ∉ pre'
                 ∧ pre'.length = pre.length
                 ∧ ∀ p, (runStepsRR quantum arrival_stream t).sched.running = some p →
                     (runStepsRR quantum arrival_stream (t + 1)).sched.running = some (Process.tick p))
  := by
  -- `target` sits in the ready queue, so the queue is nonempty and something is running
  obtain ⟨p, h_prev_running⟩ :=
    ready_nonempty_implies_running_nonempty arrival_stream t quantum (by rw [h_split]; simp)
  -- knowing both `running` and `ready` collapses stepRR's outer match (and, once `pre` is
  -- destructed below, the ready-queue match too); only the two tests are left to case on
  simp only [runStepsRR, stepRR, h_prev_running, h_split]
  cases pre with
  | nil =>
    -- target is at the front of the queue: it is dispatched unless p simply keeps running
    simp only [List.nil_append, List.cons_append]
    split  -- stepRR case: does p complete this tick?
    · -- p completes and target, being at the front, is dispatched in its place
      exact Or.inl rfl
    · split  -- stepRR case: has p's quantum expired?
      · -- p is preempted and target, being at the front, is swapped in
        exact Or.inl rfl
      · -- p keeps running; target stays put at the front
        refine Or.inr (Or.inr ⟨[], suf ++ arrival_stream (t + 1), by simp, by simp, rfl, ?_⟩)
        intro p' h_p'
        obtain rfl : p' = p := (Option.some.inj h_p').symm
        rfl
  | cons hd tl =>
    -- target is behind `hd`; every branch either dispatches `hd` (so target moves up) or
    -- leaves the queue untouched
    simp only [List.cons_append]
    split  -- stepRR case: does p complete this tick?
    · -- p completes, hd is dispatched: target's prefix loses hd
      exact Or.inr (Or.inl ⟨tl, suf ++ arrival_stream (t + 1), by simp,
        List.not_mem_of_not_mem_cons h_target_not_in_pre, by simp⟩)
    · split  -- stepRR case: has p's quantum expired?
      · -- hd is dispatched and p goes to the back of the queue: target's prefix still loses hd
        exact Or.inr (Or.inl ⟨tl,
          suf ++ arrival_stream (t + 1) ++ [{ p with remaining := p.remaining - 1 }], by simp,
          List.not_mem_of_not_mem_cons h_target_not_in_pre, by simp⟩)
      · -- p keeps running; the queue is unchanged, so target holds its position
        refine Or.inr (Or.inr ⟨hd :: tl, suf ++ arrival_stream (t + 1), by simp,
          h_target_not_in_pre, rfl, ?_⟩)
        intro p' h_p'
        obtain rfl : p' = p := (Option.some.inj h_p').symm
        rfl

/-- Repeatedly applying `target_index_decreases_one_step`, bounded by the
running process's `remaining` time via `remaining_pos_of_ready_or_running`: a
process at a fixed position in the ready queue either starts running or
strictly closes the distance to the front within some finite `k > 0` steps
(it can't get stuck waiting behind the same prefix forever). -/
theorem target_progresses
  (arrival_stream : ℕ → List AperiodicProcess)
  (h_wf : WellFormedStream arrival_stream)
  (target : AperiodicProcess) (t quantum: ℕ) (pre suf : List AperiodicProcess)
  (h_split : (runStepsRR quantum arrival_stream t).sched.ready = pre ++ target :: suf)
  (h_target_not_in_pre : target ∉ pre):
  ∃ k > 0, (runStepsRR quantum arrival_stream (t + k)).sched.running = some target
  ∨ (∃ pre' suf', (runStepsRR quantum arrival_stream (t + k)).sched.ready = pre' ++ target :: suf'
    ∧ target ∉ pre'
    ∧ pre'.length < pre.length) := by

    -- Induct on a bound `n` for the running process's `remaining`: every step that leaves
    -- target's prefix unchanged ticks the running process down, so the bound must run out.
    suffices H : ∀ (n t₀ : ℕ) (pre₀ suf₀ : List AperiodicProcess) (q : AperiodicProcess),
      (runStepsRR quantum arrival_stream t₀).sched.running = some q →
      (runStepsRR quantum arrival_stream t₀).sched.ready = pre₀ ++ target :: suf₀ →
      Process.remaining q ≤ n →
      target ∉ pre₀ →
      ∃ k > 0, (runStepsRR quantum arrival_stream (t₀ + k)).sched.running = some target
      ∨ (∃ pre' suf', (runStepsRR quantum arrival_stream (t₀ + k)).sched.ready = pre' ++ target :: suf'
        ∧ target ∉ pre'
        ∧ pre'.length < pre₀.length)
      from by
      obtain ⟨q, q_running⟩ :=
        ready_nonempty_implies_running_nonempty arrival_stream t quantum (by rw [h_split]; simp)
      exact H (Process.remaining q) t pre suf q q_running h_split (by omega) h_target_not_in_pre
    intro n
    induction n with
    | zero =>
      -- vacuous: whatever is running still has positive `remaining`
      intro t' pre' suf' q h_running h_ready h_remaining h_notin
      have := (remaining_pos_of_ready_or_running arrival_stream h_wf t' quantum).2 q h_running
      omega

    | succ n ih =>
      intro t' pre' suf' q h_running h_ready h_remaining h_notin
      rcases target_index_decreases_one_step arrival_stream target t' quantum pre' suf' h_ready h_notin with
        h_run | h_shrink | h_same
      · exact ⟨1, by omega, Or.inl h_run⟩
      · exact ⟨1, by omega, Or.inr h_shrink⟩
      · -- prefix unchanged: q ticked but didn't finish, so recurse with smaller remaining
        obtain ⟨pre2, suf2, h_ready2, h_notin2, h_len_eq, h_tick⟩ := h_same
        have h_running2 := h_tick q h_running
        have h_remaining2 : Process.remaining (Process.tick q) ≤ n := by
          have := Process.tick_decrements q
          omega
        obtain ⟨k, h_k_pos, h_concl⟩ :=
          ih (t' + 1) pre2 suf2 (Process.tick q) h_running2 h_ready2 h_remaining2 h_notin2
        refine ⟨k + 1, by omega, ?_⟩
        rw [show t' + (k + 1) = t' + 1 + k by omega]
        rcases h_concl with h | ⟨pre3, suf3, h_ready3, h_notin3, h_lt⟩
        · exact Or.inl h
        · exact Or.inr ⟨pre3, suf3, h_ready3, h_notin3, by omega⟩

/-- A process `p` that arrives at time `t` is, at time `t`, either sitting
somewhere in the ready queue in canonical split form (`ready = pre ++ p ::
suf`, `p ∉ pre`, ready for `target_progresses` to consume) or already
running. -/
theorem waiting_is_ready_or_running
  (arrival_stream : ℕ → List AperiodicProcess) (t quantum: ℕ) (p : AperiodicProcess)
  (h_arrived : p ∈ arrival_stream t)
  (h_wf : WellFormedStream arrival_stream) :
  (∃ pre suf, (runStepsRR quantum arrival_stream t).sched.ready = pre ++ p :: suf ∧ p ∉ pre)
  ∨ (runStepsRR quantum arrival_stream t).sched.running = some p := by
  obtain ⟨pre, suf, arrival_t_composition, h_p_not_pre⟩ := mem_split_canonical h_arrived
  cases t with
  | zero =>
    -- at time 0 the queue is the first arrival batch, already split as `pre ++ p :: suf`
    have h_init_running : (SchedStateMethods.init : SchedStateG AperiodicProcess).running = none := rfl
    simp only [runStepsRR, stepRR, h_init_running, arrival_t_composition]
    cases pre with
    | nil =>
      -- p is at the front, so it is the one dispatched
      simp only [List.nil_append]
      exact Or.inr (by simp)
    | cons hd tl =>
      -- hd is dispatched and p keeps its place behind the rest of `tl`
      simp only [List.cons_append]
      exact Or.inl ⟨tl, suf, rfl, List.not_mem_of_not_mem_cons h_p_not_pre⟩
  | succ n =>
    -- p has only just arrived, so it cannot already be sitting in last tick's queue
    have h_p_not_prev_ready : p ∉ (runStepsRR quantum arrival_stream n).sched.ready := by
      intro h_mem
      have h_le := (system_arrival_bound arrival_stream h_wf n quantum).1 p h_mem
      have h_eq := h_wf.consistent p (n + 1) h_arrived
      simp at h_le; omega
    have h_p_not_comb : p ∉ (runStepsRR quantum arrival_stream n).sched.ready ++ pre := by
      simp [h_p_not_prev_ready, h_p_not_pre]
    -- so the queue stepRR sees splits canonically at p, with everything ahead of it
    -- gathered into `prev.ready ++ pre`
    have h_comb : (runStepsRR quantum arrival_stream n).sched.ready ++ arrival_stream (n + 1)
        = ((runStepsRR quantum arrival_stream n).sched.ready ++ pre) ++ p :: suf := by
      rw [arrival_t_composition, List.append_assoc]
    simp only [runStepsRR, stepRR, h_comb]
    -- p is either at the very front of that queue, or behind some `hd`
    rcases h_ahead : (runStepsRR quantum arrival_stream n).sched.ready ++ pre with _ | ⟨hd, tl⟩
    · -- nothing ahead of p: every branch that dispatches picks p itself
      simp only [List.nil_append]
      split  -- stepRR case: was anything running last tick?
      · exact Or.inr rfl
      · split  -- stepRR case: does the running process complete this tick?
        · exact Or.inr rfl
        · split  -- stepRR case: has its quantum expired?
          · exact Or.inr rfl
          · -- it just ticks down, so p stays at the front of an unchanged queue
            exact Or.inl ⟨[], suf, rfl, by simp⟩
    · -- p sits behind `hd`; whichever branch runs, p keeps a canonical split
      rw [h_ahead] at h_p_not_comb
      have h_p_not_tl : p ∉ tl := List.not_mem_of_not_mem_cons h_p_not_comb
      simp only [List.cons_append]
      split  -- stepRR case: was anything running last tick?
      · -- hd is dispatched, p moves up one place
        exact Or.inl ⟨tl, suf, rfl, h_p_not_tl⟩
      · rename_i q h_prev_running
        split  -- stepRR case: does q complete this tick?
        · -- q completes and hd is dispatched in its place
          exact Or.inl ⟨tl, suf, rfl, h_p_not_tl⟩
        · split  -- stepRR case: has q's quantum expired?
          · -- hd is dispatched and q is appended behind p, lengthening `suf`
            exact Or.inl ⟨tl, suf ++ [{ q with remaining := q.remaining - 1 }], by simp, h_p_not_tl⟩
          · -- q keeps running and the queue is untouched
            exact Or.inl ⟨hd :: tl, suf, by simp, h_p_not_comb⟩

/-- The three things one Round Robin step can do to the process it is running:
finish it (it joins `completed`), preempt it on quantum expiry (it goes to the
back of the ready queue, one tick lighter), or simply tick it down and carry on
running it. Everything is matched by `id`, since ticking changes `remaining`. -/
lemma running_step_cases
  (arrival_stream : ℕ → List AperiodicProcess) (t quantum : ℕ) (p : AperiodicProcess)
  (h_running : (runStepsRR quantum arrival_stream t).sched.running = some p) :
  (∃ p_completed ∈ (runStepsRR quantum arrival_stream (t + 1)).sched.completed,
      Process.id p_completed = Process.id p)
  ∨ (∃ p' ∈ (runStepsRR quantum arrival_stream (t + 1)).sched.ready,
      Process.id p' = Process.id p ∧ Process.remaining p' = Process.remaining p - 1)
  ∨ (runStepsRR quantum arrival_stream (t + 1)).sched.running = some (Process.tick p) := by
  simp only [runStepsRR, stepRR, h_running]
  split  -- stepRR case: does p complete this tick?
  · -- p completes, so it is appended to `completed` whether or not anyone succeeds it
    split  -- match on the combined ready queue
    · exact Or.inl ⟨{ p with remaining := 0 }, by simp, by simp⟩
    · exact Or.inl ⟨{ p with remaining := 0 }, by simp, by simp⟩
  · split  -- stepRR case: has p's quantum expired?
    · split  -- match on the combined ready queue
      · -- nobody to swap in, so p keeps running despite the expiry
        exact Or.inr (Or.inr rfl)
      · -- p is preempted and appended to the back of the queue
        exact Or.inr (Or.inl ⟨{ p with remaining := p.remaining - 1 }, by simp, by simp, by simp⟩)
    · -- quantum still has room: p just ticks down in place
      exact Or.inr (Or.inr rfl)

/-- A running process, within some bounded number `k ≥ 1` of further steps, either
finishes (appearing in `completed`, matched by `id`) or is put back in the ready
queue with strictly smaller `remaining`. Round Robin can preempt it before it is
done, so unlike a non-preemptive scheduler it need not run straight to completion
— but every step it does get strictly decreases `remaining`, which bounds this. -/
theorem running_puts_at_back_or_completes
  (arrival_stream : ℕ → List AperiodicProcess) (t quantum : ℕ) (p : AperiodicProcess)
  (h_running : (runStepsRR quantum arrival_stream t).sched.running = some p)
  (h_wf : WellFormedStream arrival_stream) :
  ∃ k ≥ 1,
    (∃ p_completed ∈ (runStepsRR quantum arrival_stream (t + k)).sched.completed,
        Process.id p_completed = Process.id p)
    ∨ (∃ p' ∈ (runStepsRR quantum arrival_stream (t + k)).sched.ready,
        Process.id p' = Process.id p ∧ Process.remaining p' < Process.remaining p) := by
  suffices H : ∀ (n t₀ : ℕ) (p₀ : AperiodicProcess),
      (runStepsRR quantum arrival_stream t₀).sched.running = some p₀ →
      Process.remaining p₀ ≤ n →
      ∃ k ≥ 1,
        (∃ p_completed ∈ (runStepsRR quantum arrival_stream (t₀ + k)).sched.completed,
            Process.id p_completed = Process.id p₀)
        ∨ (∃ p' ∈ (runStepsRR quantum arrival_stream (t₀ + k)).sched.ready,
            Process.id p' = Process.id p₀ ∧ Process.remaining p' < Process.remaining p₀) by
    exact H (Process.remaining p) t p h_running le_rfl
  intro n
  induction n with
  | zero =>
    -- vacuous: whatever is running still has positive `remaining`
    intro t₀ p₀ h_run h_rem
    have := (remaining_pos_of_ready_or_running arrival_stream h_wf t₀ quantum).2 p₀ h_run
    omega
  | succ n ih =>
    intro t₀ p₀ h_run h_rem
    rcases running_step_cases arrival_stream t₀ quantum p₀ h_run with h_done | h_back | h_still
    · exact ⟨1, le_rfl, Or.inl h_done⟩
    · obtain ⟨p', h_mem, h_id, h_rem'⟩ := h_back
      have h_pos := (remaining_pos_of_ready_or_running arrival_stream h_wf t₀ quantum).2 p₀ h_run
      exact ⟨1, le_rfl, Or.inr ⟨p', h_mem, h_id, by omega⟩⟩
    · -- p₀ is still running, one tick lighter, so the bound has shrunk: recurse
      have h_tick := Process.tick_decrements p₀
      obtain ⟨k, h_k, h_concl⟩ := ih (t₀ + 1) (Process.tick p₀) h_still (by omega)
      refine ⟨1 + k, by omega, ?_⟩
      rw [show t₀ + (1 + k) = t₀ + 1 + k by omega]
      rcases h_concl with ⟨q, hq, hid⟩ | ⟨q, hq, hid, hlt⟩
      · exact Or.inl ⟨q, hq, by simp [hid]⟩
      · exact Or.inr ⟨q, hq, by simp [hid], by omega⟩


/-- Chaining `target_progresses` by strong induction on the prefix length: a
process sitting anywhere in the ready queue eventually gets to run. -/
theorem ready_eventually_runs
  (arrival_stream : ℕ → List AperiodicProcess) (target : AperiodicProcess)
  (h_wf : WellFormedStream arrival_stream) (t quantum: ℕ) (pre suf : List AperiodicProcess)
  (h_split : (runStepsRR quantum arrival_stream t).sched.ready = pre ++ target :: suf)
  (h_notin : target ∉ pre) :
  ∃ k, (runStepsRR quantum arrival_stream (t + k)).sched.running = some target := by
  induction hn : pre.length using Nat.strong_induction_on generalizing t pre suf with
  | _ n ih =>
    obtain ⟨k, h_k_pos, h_concl⟩ :=
      target_progresses arrival_stream h_wf target t quantum pre suf h_split h_notin
    rcases h_concl with h_run | ⟨pre', suf', h_ready', h_notin', h_lt⟩
    · exact ⟨k, h_run⟩
    · obtain ⟨k', h_k'⟩ := ih pre'.length (by omega) (t + k) pre' suf' h_ready' h_notin' rfl
      exact ⟨k + k', by rw [show t + (k + k') = t + k + k' by omega]; exact h_k'⟩

/-- **Main theorem.** Round Robin is starvation-free: under a well-formed arrival
stream, every process that ever arrives is eventually found in `completed`
(matched by `id`). Combines `waiting_is_ready_or_running`,
`ready_eventually_runs`, and `running_puts_at_back_or_completes`.

Unlike a non-preemptive scheduler, a process here need not run straight to
completion once dispatched: quantum expiry can send it back to the queue. The
induction below is therefore on its `remaining` time, which strictly drops every
time it gets a turn, so it can be sent back only finitely often. -/
theorem StarvationFree
  (arrival_stream : Nat → List AperiodicProcess)
  (quantum : ℕ)
  (h_wf : WellFormedStream arrival_stream) :
  ∀ arrival_time process, process ∈ arrival_stream arrival_time →
  ∃ completion_time, ∃ finished_process ∈ (runStepsRR quantum arrival_stream completion_time).sched.completed,
    Process.id finished_process = Process.id process -- cannot directly compare a process via == since the `remaining` field changes
  := by
  intro arrival_time process h_arrived
  -- It suffices to show that a process which is queued or running at some time, with
  -- `remaining` bounded by `n`, eventually completes.
  suffices H : ∀ (n t : ℕ) (q : AperiodicProcess),
      Process.remaining q ≤ n →
      ((∃ pre suf, (runStepsRR quantum arrival_stream t).sched.ready = pre ++ q :: suf ∧ q ∉ pre)
        ∨ (runStepsRR quantum arrival_stream t).sched.running = some q) →
      ∃ ct, ∃ fp ∈ (runStepsRR quantum arrival_stream ct).sched.completed,
        Process.id fp = Process.id q by
    exact H (Process.remaining process) arrival_time process le_rfl
      (waiting_is_ready_or_running arrival_stream arrival_time quantum process h_arrived h_wf)
  intro n
  induction n with
  | zero =>
    -- vacuous: anything queued or running still has positive `remaining`
    intro t q h_rem h_where
    exfalso
    rcases h_where with ⟨pre, suf, h_split, _⟩ | h_run
    · have := (remaining_pos_of_ready_or_running arrival_stream h_wf t quantum).1 q
        (by rw [h_split]; simp)
      omega
    · have := (remaining_pos_of_ready_or_running arrival_stream h_wf t quantum).2 q h_run
      omega
  | succ n ih =>
    intro t q h_rem h_where
    -- whether q is queued or already running, it gets a turn at some point
    obtain ⟨t_run, h_run⟩ : ∃ t_run, (runStepsRR quantum arrival_stream t_run).sched.running = some q := by
      rcases h_where with ⟨pre, suf, h_split, h_notin⟩ | h_run
      · obtain ⟨k, h_k⟩ :=
          ready_eventually_runs arrival_stream q h_wf t quantum pre suf h_split h_notin
        exact ⟨t + k, h_k⟩
      · exact ⟨t, h_run⟩
    -- that turn either finishes q, or returns it to the queue strictly shorter
    obtain ⟨k, h_k, h_concl⟩ :=
      running_puts_at_back_or_completes arrival_stream t_run quantum q h_run h_wf
    rcases h_concl with ⟨fp, h_mem, h_id⟩ | ⟨q', h_mem, h_id, h_lt⟩
    · exact ⟨t_run + k, fp, h_mem, h_id⟩
    · -- back in the queue: re-split canonically and recurse on the smaller `remaining`
      obtain ⟨pre', suf', h_split', h_notin'⟩ := mem_split_canonical h_mem
      obtain ⟨ct, fp, h_fp_mem, h_fp_id⟩ :=
        ih (t_run + k) q' (by omega) (Or.inl ⟨pre', suf', h_split', h_notin'⟩)
      exact ⟨ct, fp, h_fp_mem, by rw [h_fp_id, h_id]⟩

end RRStarvation
