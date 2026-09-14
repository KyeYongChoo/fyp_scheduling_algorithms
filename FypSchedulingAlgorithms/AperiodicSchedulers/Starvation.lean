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
-- Starvation: When a process is put into the ready queue but never gets to run because it keeps being deprioritized compared to newer arriving processes.

theorem non_preemptive_processes_are_ready_running_completed_or_unarrived
  (select : List AperiodicProcess → Option AperiodicProcess)
  (arrival_stream : Nat → List AperiodicProcess)
  (process : AperiodicProcess)
  (h_process_in_arrival_time : ∃ arrival_time, process ∈ arrival_stream arrival_time):
  -- for all processes, for all time, processes are either
  ∀ current_time,
    -- ready
    process ∈ (runSteps arrival_stream (stepNonPreemptive select) current_time).ready ∨
    -- running
    (∃ p ∈ (runSteps arrival_stream (stepNonPreemptive select) current_time).running,
      p.id = process.id) ∨
    -- id equality for completed since tick changes remaining
    (∃ p ∈ (runSteps arrival_stream (stepNonPreemptive select) current_time).completed,
      p.id = process.id) ∨
    -- unarrived
    (∃ arrival_time, arrival_time > current_time ∧ process ∈ arrival_stream arrival_time)
  := by
    intro current_time
    induction current_time with
    | zero =>
      obtain ⟨arrival_time, h_arrival⟩ := h_process_in_arrival_time
      by_cases h_process_arrives_at_t_zero : process ∈ arrival_stream 0
      · -- process arrived at time 0, so it's in ready or running after scheduler step
        simp only [runSteps, stepNonPreemptive]
        -- after scheduler runs on init + arrivals at 0
        -- process is either picked to run or stays in ready
        have h_init_running : (SchedStateMethods.init : SchedStateG AperiodicProcess).running = none := by rfl
        simp only [h_init_running]

        split
        · -- select returned none, process stays in ready
          left
          -- goal: process ∈ arrival_stream 0
          -- which is exactly h_process_arrives_at_t_zero
          exact h_process_arrives_at_t_zero

        · -- select returned some p
          rename_i p h_select
          by_cases h_selected_process_eq_target_process : process = p
          · -- process was selected, it's running
            right; left
            simp [h_selected_process_eq_target_process]
          · -- different process selected, process stays in ready
            left
            induction h_arrival_stream_zero_contains : arrival_stream 0 with
            | nil =>
              rw [h_arrival_stream_zero_contains] at h_process_arrives_at_t_zero
              exact absurd h_process_arrives_at_t_zero List.not_mem_nil
            | cons hd tl ih =>
              unfold List.erase
              split
              · rename_i h_p_is_head
                rw [h_arrival_stream_zero_contains] at h_process_arrives_at_t_zero
                simp only [List.mem_cons] at h_process_arrives_at_t_zero
                rcases h_process_arrives_at_t_zero with rfl | h_tl
                · simp only [beq_iff_eq] at h_p_is_head
                  exact absurd h_p_is_head h_selected_process_eq_target_process
                · exact h_tl
              · rw [h_arrival_stream_zero_contains] at h_process_arrives_at_t_zero
                simp only [List.mem_cons] at h_process_arrives_at_t_zero
                rcases h_process_arrives_at_t_zero with rfl | h_tl
                · -- process = hd, so process ∈ hd :: removeFirst p tl
                  left
                · -- process ∈ tl, so process ∈ removeFirst p tl by ih
                  right
                  exact (List.mem_erase_of_ne h_selected_process_eq_target_process).mpr h_tl

      · -- process didn't arrive at time 0, it arrives later
        right; right; right
        refine ⟨arrival_time, ?_, h_arrival⟩
        by_contra h_le
        push Not at h_le
        have h_zero_eq : arrival_time = 0 := Nat.le_zero.mp h_le
        rw [h_zero_eq] at h_arrival
        exact absurd h_arrival h_process_arrives_at_t_zero
    | succ current_time_minus_one ih =>
      simp only [runSteps]
      rcases ih with h_ready | h_running | h_completed | h_unarrived
      · -- was in ready: after one step, either still ready, now running, or completed
        simp only [stepNonPreemptive]
        split
        · -- prev.running = none, select was called on ready
          split
          · -- select returned none, stays in ready
            left; simp [List.mem_append, h_ready]
          · -- select returned some p
            rename_i p h_select
            by_cases h_eq : process = p
            · -- process was selected, now running
              right; left; simp [h_eq]
            · -- different process selected, stays in ready
              left
              simp [List.mem_append, List.mem_erase_of_ne, h_ready, h_eq]
        · -- prev.running = some q, non-preemptive so ready list unchanged
          rename_i q h_q
          split
          · -- q completes, select is called on ready
            rename_i h_select
            split
            · -- select returned none, process stays in ready
              left
              simp [List.mem_append, h_ready]
            · -- select returned some r
              rename_i r h_r
              by_cases h_eq : process = r
              · -- process was selected, now running
                right; left
                simp [h_eq]
              · -- different process selected, stays in ready minus r
                left
                apply (List.mem_erase_of_ne h_eq).mpr
                simp [List.mem_append, h_ready]
          · -- q still running, ready completely unchanged
            left
            simp [List.mem_append, h_ready]

      · -- was running
        obtain ⟨p, h_p_running, h_p_id⟩ := h_running
        have h_running' : (runSteps arrival_stream (stepNonPreemptive select) current_time_minus_one).running = some p := h_p_running
        have h_tick_p := Process.tick_decrements p
        by_cases h_remaining : p.remaining ≤ 1
        · -- p completes this tick
          have h_done : Process.remaining (Process.tick p) = 0 := by
            rw [h_tick_p]
            have : Process.remaining p = p.remaining := rfl
            omega
          simp only [stepNonPreemptive, h_running', h_done, Nat.le_refl, ↓reduceIte]
          · right; right; left
            split
            · exact ⟨Process.tick p, by simp [List.mem_append], by
                exact (Process.id_invariant_wrt_tick p).trans h_p_id⟩
            · exact ⟨Process.tick p, by simp [List.mem_append], by
                exact (Process.id_invariant_wrt_tick p).trans h_p_id⟩
        · -- p still running
          push Not at h_remaining
          have h_not_done : ¬Process.remaining (Process.tick p) ≤ 0 := by
            rw [h_tick_p]
            have : Process.remaining p = p.remaining := rfl
            omega
          simp only [stepNonPreemptive, h_running', h_not_done, ↓reduceIte]
          right; left
          exact ⟨Process.tick p, rfl, (Process.id_invariant_wrt_tick p).trans h_p_id⟩

      · -- was completed: completed list only grows, so still completed
        right; right; left
        simp only [stepNonPreemptive]
        set prev := runSteps arrival_stream (stepNonPreemptive select) current_time_minus_one
        split
        · -- prev.running = none
          split
          · -- select = none, completed unchanged
            simp [h_completed]
          · -- select = some p, completed unchanged
            simp [h_completed]
        · -- prev.running = some p
          split
          · -- remaining ≤ 0, completed grows
            split
            · simp [List.mem_append, h_completed]
            · simp [List.mem_append, h_completed]
          · -- remaining > 0, completed unchanged
            simp [h_completed]
      · -- was unarrived
        obtain ⟨arrival_time, h_gt, h_mem⟩ := h_unarrived
        by_cases h_now : arrival_time = current_time_minus_one + 1
        · -- arrives this tick, so now in ready or running
          subst h_now
          simp only [stepNonPreemptive]
          set prev := runSteps arrival_stream (stepNonPreemptive select) current_time_minus_one
          split
          · -- prev.running = none
            split
            · -- select = none, process in ready (arrivals added)
              left
              simp [List.mem_append, h_mem]
            · -- select = some p
              rename_i p h_select
              by_cases h_eq : process = p
              · -- process selected, now running
                right; left; simp [h_eq]
              · -- different process selected, in ready
                left
                simp [List.mem_append, List.mem_erase_of_ne, h_mem, h_eq]
          · -- prev.running = some p, arrivals added to ready
            split
            · -- remaining ≤ 0, process completed
              split
              · -- select = none, process in ready
                left
                simp [List.mem_append, h_mem]
              · -- select = some q
                rename_i q h_select
                by_cases h_eq : process = q
                · right; left; simp [h_eq]
                · left
                  simp [List.mem_append, List.mem_erase_of_ne, h_mem, h_eq]
            · -- remaining > 0, process in ready
              left
              simp [List.mem_append, h_mem]
        · -- still unarrived
          right; right; right
          exact ⟨arrival_time, by omega, h_mem⟩

theorem foldl_ge_init
  {α}
  (f : ℕ → α → ℕ)
  (h_mono : ∀ acc x, acc ≤ f acc x)
  (l : List α) (init : ℕ) :
  init ≤ l.foldl f init := by
  induction l generalizing init with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl]
    exact le_trans (h_mono init hd) (ih (f init hd))

theorem foldl_prefix_le
  {α}
  (f : ℕ → α → ℕ)
  (h_mono : ∀ acc x, acc ≤ f acc x)
  (l : List α) (n : ℕ) (init : ℕ) :
  (l.take n).foldl f init ≤ l.foldl f init := by
  induction l generalizing n init with
  | nil => simp
  | cons hd tl ih =>
    cases n with
    | zero =>
      simp only [List.foldl]
      exact le_trans (h_mono init hd) (foldl_ge_init f h_mono tl (f init hd))
    | succ n =>
      simp only [List.take, List.foldl]
      apply ih

theorem selectFCFS_none_iff_empty
  (l : List AperiodicProcess) :
  selectFCFS l = none ↔ l = [] :=  by
  cases l with
  | nil => simp [selectFCFS]
  | cons h t => simp [selectFCFS]

theorem idle_implies_empty_ready
  (arrival_stream : ℕ → List AperiodicProcess)
  (t : ℕ)
  (h_running : (runSteps arrival_stream stepFCFS t).running = none) :
  (runSteps arrival_stream stepFCFS t).ready = [] := by
  induction t with
  | zero =>
    simp only [runSteps, stepFCFS, stepNonPreemptive] at h_running ⊢
    have h_init_running : (SchedStateMethods.init : SchedStateG AperiodicProcess).running = none := by
      rfl
    -- after unfolding, running = none means selectFCFS returned none
    -- selectFCFS_none_iff_empty then gives ready = []
    simp only [h_init_running] at h_running ⊢
    split at h_running
    · rename_i h_select
      rwa [selectFCFS_none_iff_empty] at h_select
    · simp at h_running
  | succ t ih =>
    simp only [runSteps, stepFCFS, stepNonPreemptive] at h_running ⊢
    split at h_running
    · -- prev.running = none, so select was called on ready
      rename_i h_prev_none
      split at h_running
      · -- select returned none → ready = []
        simp only [List.append_eq_nil_iff] at h_running ⊢
        apply And.intro
        · exact ih h_running
        · rename_i step_concat_arrivals_eq_none
          have h_ready_empty := ih h_running
          simp only [stepFCFS] at h_ready_empty
          rw [h_ready_empty, List.nil_append] at step_concat_arrivals_eq_none
          rwa [selectFCFS_none_iff_empty] at step_concat_arrivals_eq_none
      · -- select returned some p → running = some p, contradicts h_running
        contradiction
    · -- prev.running = some p, process ticked
      split at h_running
      · -- remaining ≤ 0, process completed, next select called
        rename_i h_remaining_after_tick_zero
        split at h_running
        · simp only [h_remaining_after_tick_zero, ↓reduceIte]
          rename_i h_none_after_1_step
          rw [selectFCFS_none_iff_empty] at h_none_after_1_step
          exact h_none_after_1_step
        · contradiction
      · -- remaining > 0, running = some p, contradicts h_running = none
        contradiction

theorem selectFCFS_mem {l q}: selectFCFS l = some q → q ∈ l := by
  unfold selectFCFS
  grind

theorem system_arrival_bound
  (arrival_stream : ℕ → List AperiodicProcess)
  (h_arrival_consistent : ∀ (p : AperiodicProcess) (t : ℕ), p ∈ arrival_stream t → p.arrival = t)
  (t : ℕ) :
  (∀ q ∈ (runSteps arrival_stream stepFCFS t).ready, Process.arrival q ≤ t) ∧
  (∀ q, (runSteps arrival_stream stepFCFS t).running = some q → Process.arrival q ≤ t) := by
  induction t with
  | zero =>
    have h_init_running : (SchedStateMethods.init : SchedStateG AperiodicProcess).running = none := rfl
    simp only [runSteps, stepFCFS, stepNonPreemptive, h_init_running]
    split
    · refine ⟨?_, ?_⟩
      · intro q hq; exact le_of_eq (h_arrival_consistent q 0 hq)
      · intro q hq; simp at hq
    · rename_i q₀ h_select
      refine ⟨?_, ?_⟩
      · intro q hq
        exact le_of_eq (h_arrival_consistent q 0 (List.mem_of_mem_erase hq))
      · intro q hq; simp only [Option.some.injEq] at hq; subst hq
        exact le_of_eq (h_arrival_consistent q₀ 0 (selectFCFS_mem h_select))
  | succ t ih =>
    obtain ⟨ih_ready, ih_running⟩ := ih
    simp only [runSteps, stepFCFS, stepNonPreemptive]
    have ready_src : ∀ q ∈ (runSteps arrival_stream stepFCFS t).ready ++ arrival_stream (t + 1),
        Process.arrival q ≤ t + 1 := by
      intro q hq
      rcases List.mem_append.mp hq with h | h
      · exact le_trans (ih_ready q h) (by omega)
      · exact le_of_eq (h_arrival_consistent q (t + 1) h)
    split
    · split
      · exact ⟨ready_src, by intro q hq; simp at hq; tauto⟩
      · rename_i q₀ h_select
        refine ⟨?_, ?_⟩
        · intro q hq; exact ready_src q (List.mem_of_mem_erase hq)
        · intro q hq; simp only [Option.some.injEq] at hq; subst hq
          exact ready_src q₀ (selectFCFS_mem h_select)
    · rename_i p h_prev_running
      split
      · split
        · exact ⟨ready_src, by intro q hq; simp at hq⟩
        · rename_i q₀ h_select
          refine ⟨?_, ?_⟩
          · intro q hq; exact ready_src q (List.mem_of_mem_erase hq)
          · intro q hq; simp only [Option.some.injEq] at hq; subst hq
            exact ready_src q₀ (selectFCFS_mem h_select)
      · refine ⟨ready_src, ?_⟩
        intro q hq; simp only [Option.some.injEq] at hq; subst hq
        rw [Process.arrival_invariant_wrt_tick]
        exact le_trans (ih_running p h_prev_running) (by omega)

theorem system_provenance
  (arrival_stream : ℕ → List AperiodicProcess) (t : ℕ) :
  (∀ q ∈ (runSteps arrival_stream stepFCFS t).ready,
     ∃ s ≤ t, ∃ q₀ ∈ arrival_stream s, Process.id q₀ = Process.id q) ∧
  (∀ q, (runSteps arrival_stream stepFCFS t).running = some q →
     ∃ s ≤ t, ∃ q₀ ∈ arrival_stream s, Process.id q₀ = Process.id q) ∧
  (∀ q ∈ (runSteps arrival_stream stepFCFS t).completed,
     ∃ s ≤ t, ∃ q₀ ∈ arrival_stream s, Process.id q₀ = Process.id q) := by
  induction t with
  | zero =>
    have h_init_running : (SchedStateMethods.init : SchedStateG AperiodicProcess).running = none := rfl
    have h_init_completed : (SchedStateMethods.init : SchedStateG AperiodicProcess).completed = [] := rfl
    simp only [runSteps, stepFCFS, stepNonPreemptive, h_init_running]
    split
    · rename_i h_select
      refine ⟨?_, ?_, ?_⟩
      · intro q hq; exact ⟨0, le_refl _, q, hq, rfl⟩
      · intro q hq; simp at hq
      · intro q hq; simp [h_init_completed] at hq
    · rename_i q₀ h_select
      refine ⟨?_, ?_, ?_⟩
      · intro q hq
        exact ⟨0, le_refl _, q, List.mem_of_mem_erase hq, rfl⟩
      · intro q hq
        simp only [Option.some.injEq] at hq
        rw [hq] at h_select
        exact ⟨0, le_refl _, q, selectFCFS_mem h_select, rfl⟩ -- here
      · intro q hq; simp [h_init_completed] at hq
  | succ t ih =>
    obtain ⟨ih_ready, ih_running, ih_completed⟩ := ih
    simp only [runSteps, stepFCFS, stepNonPreemptive]
    -- every `s ≤ t` from ih weakens to `s ≤ t + 1`
    have weaken : ∀ (q: AperiodicProcess), (∃ s ≤ t, ∃ q₀ ∈ arrival_stream s, Process.id q₀ = Process.id q) →
        ∃ s ≤ t + 1, ∃ q₀ ∈ arrival_stream s, Process.id q₀ = Process.id q := by
      rintro q ⟨s, hs, q₀, hq₀, hid⟩
      exact ⟨s, by omega, q₀, hq₀, hid⟩
    -- new ready is always a sub-multiset of `prev.ready ++ arrivals`
    have ready_src : ∀ q ∈ (runSteps arrival_stream stepFCFS t).ready ++ arrival_stream (t + 1),
        ∃ s ≤ t + 1, ∃ q₀ ∈ arrival_stream s, Process.id q₀ = Process.id q := by
      intro q hq
      rcases List.mem_append.mp hq with h | h
      · exact weaken q (ih_ready q h)
      · exact ⟨t + 1, le_refl _, q, h, rfl⟩
    split
    · -- prev.running = none
      split
      · exact ⟨ready_src, by intro q hq; simp at hq; tauto, fun q hq => weaken q (ih_completed q hq)⟩
      · rename_i q₀ h_select
        refine ⟨?_, ?_, fun q hq => weaken q (ih_completed q hq)⟩
        · intro q hq; exact ready_src q (List.mem_of_mem_erase hq)
        · intro q hq; simp only [Option.some.injEq] at hq; subst hq
          exact ready_src q₀ (selectFCFS_mem h_select)
    · -- prev.running = some p
      rename_i p h_prev_running
      split
      · -- p finished
        split
        · refine ⟨ready_src, by intro q hq; simp at hq, ?_⟩
          intro q hq
          rcases List.mem_append.mp hq with h | h
          · exact weaken q (ih_completed q h)
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at h; subst h
            rw [Process.id_invariant_wrt_tick]
            exact weaken p (ih_running p h_prev_running)
        · rename_i q₀ h_select
          refine ⟨?_, ?_, ?_⟩
          · intro q hq; exact ready_src q (List.mem_of_mem_erase hq)
          · intro q hq; simp only [Option.some.injEq] at hq; subst hq
            exact ready_src q₀ (selectFCFS_mem h_select)
          · intro q hq
            rcases List.mem_append.mp hq with h | h
            · exact weaken q (ih_completed q h)
            · simp only [List.mem_cons, List.not_mem_nil, or_false] at h; subst h
              rw [Process.id_invariant_wrt_tick]
              exact weaken p (ih_running p h_prev_running)
      · -- p continues
        refine ⟨ready_src, ?_, fun q hq => weaken q (ih_completed q hq)⟩
        intro q hq; simp only [Option.some.injEq] at hq; subst hq
        rw [Process.id_invariant_wrt_tick]
        exact weaken p (ih_running p h_prev_running)

theorem ready_ordered
  (arrival_stream : ℕ → List AperiodicProcess)
  (h_arrival_consistent : ∀ (p : AperiodicProcess) (t : ℕ), p ∈ arrival_stream t → p.arrival = t)
  (t : ℕ) :
  List.Pairwise (fun a b => Process.arrival a ≤ Process.arrival b)
    (runSteps arrival_stream stepFCFS t).ready
    := by
  have stream_sorted : ∀ t, List.Pairwise (fun a b => Process.arrival a ≤ Process.arrival b) (arrival_stream t) := by
    intro t
    rw [h_arrival_consistent a t ha, h_arrival_consistent b t hb]
  induction t with
  | zero =>
    simp only [runSteps, stepFCFS, stepNonPreemptive]
    have h_init : (SchedStateMethods.init : SchedStateG AperiodicProcess).running = none := rfl
    simp only [h_init]
    split
    · simpa using stream_sorted 0
    · exact (stream_sorted 0).sublist (List.erase_sublist)
  | succ t ih =>
    simp only [runSteps, stepFCFS, stepNonPreemptive]
    have h_append : List.Pairwise (fun a b => Process.arrival a ≤ Process.arrival b)
        ((runSteps arrival_stream stepFCFS t).ready ++ arrival_stream (t + 1)) := by
      apply List.Pairwise.append ih (stream_sorted (t+1))
      intro a ha b hb
      obtain ⟨-, s, hs, a₀, ha₀, hid⟩ := by   -- provenance on `a`
      sorry  -- arrival a ≤ t < t + 1 = arrival b
    split
    · split
      · exact h_append
      · exact h_append.sublist (List.erase_sublist _ _)
    · split
      · split
        · exact h_append
        · exact h_append.sublist (List.erase_sublist _ _)
      · exact h_append


theorem FCFSStarvationFree
  (arrival_stream : Nat → List AperiodicProcess)
  (h_arrival_unique : ∀ p1 p2 t1 t2, p1 ∈ arrival_stream t1 → p2 ∈ arrival_stream t2 → p1 = p2 → t1 = t2):
  ∀ arrival_time process, process ∈ arrival_stream arrival_time →
  ∃ completion_time, ∃ finished_process ∈ (runSteps arrival_stream stepFCFS completion_time).completed,
    Process.id finished_process = Process.id process -- cannot directly compare a process via == since the `remaining` field changes
  := by
  sorry


-- Proof that Starvation occurs in Shortest Job First, Shortest Remaining Time First schedulers

-- Proof that in the First Come First Serve, Round Robin scheduler every process will run
