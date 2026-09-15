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

theorem selectFCFS_mem {l q}: selectFCFS l = some q → q ∈ l := by
  unfold selectFCFS
  grind

theorem selectFCFS_head {q l}: selectFCFS l = some q ↔ ∃ rest, l = q :: rest := by
  cases l with
  | nil => simp [selectFCFS]
  | cons hd tl =>
    simp only [selectFCFS, Option.some.injEq]
    constructor
    · rintro rfl; exact ⟨tl, rfl⟩
    · rintro ⟨rest, h⟩
      exact (List.cons.injEq .. ▸ h).1

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

-- contrapositive of idle_implies_empty_ready, still very useufl
theorem ready_nonempty_implies_running_nonempty
  (arrival_stream : ℕ → List AperiodicProcess)
  (t : ℕ)
  (h_ready_nonempty : (runSteps arrival_stream stepFCFS t).ready ≠ []):
  ∃ p_running : AperiodicProcess, (runSteps arrival_stream stepFCFS t).running = some p_running :=
  by
  cases h : (runSteps arrival_stream stepFCFS t).running with
  | none =>
    exfalso
    have := idle_implies_empty_ready arrival_stream t h
    tauto
  | some p => exact ⟨p, rfl⟩

lemma ready_running_remaining_pos
  (arrival_stream : ℕ → List AperiodicProcess)
  (h_arrival_fresh : ∀ (p : AperiodicProcess) (t : ℕ), p ∈ arrival_stream t → p.remaining = p.burst)
  (t : ℕ) :
  (∀ q ∈ (runSteps arrival_stream stepFCFS t).ready, Process.remaining q > 0) ∧
  (∀ q, (runSteps arrival_stream stepFCFS t).running = some q → Process.remaining q > 0) := by
  have fresh_pos : ∀ (p : AperiodicProcess) (s : ℕ), p ∈ arrival_stream s → Process.remaining p > 0 := by
    intro p s hp
    simp only [AperiodicProcess.process_remaining, gt_iff_lt]
    rw [h_arrival_fresh p s hp]
    exact Process.burst_exceed_zero p
  induction t with
  | zero =>
    have h_init_running : (SchedStateMethods.init : SchedStateG AperiodicProcess).running = none := rfl
    simp only [runSteps, stepFCFS, stepNonPreemptive, h_init_running]
    split
    · exact ⟨fun q hq => fresh_pos q 0 hq, by intro q hq; simp at hq⟩
    · rename_i q₀ h_select
      refine ⟨?_, ?_⟩
      · intro q hq; exact fresh_pos q 0 (List.mem_of_mem_erase hq)
      · intro q hq; simp only [Option.some.injEq] at hq; subst hq
        exact fresh_pos q₀ 0 (selectFCFS_mem h_select)
  | succ t ih =>
    obtain ⟨ih_ready, ih_running⟩ := ih
    simp only [runSteps, stepFCFS, stepNonPreemptive]
    have ready_src : ∀ q ∈ (runSteps arrival_stream stepFCFS t).ready ++ arrival_stream (t + 1),
        Process.remaining q > 0 := by
      intro q hq
      rcases List.mem_append.mp hq with h | h
      · exact ih_ready q h
      · exact fresh_pos q (t + 1) h
    split
    · split
      · exact ⟨ready_src, by intro q hq; simp at hq; tauto⟩
      · rename_i q₀ h_select
        exact ⟨fun q hq => ready_src q (List.mem_of_mem_erase hq),
               by intro q hq; simp only [Option.some.injEq] at hq; subst hq
                  exact ready_src q₀ (selectFCFS_mem h_select)⟩
    · rename_i p h_prev_running
      split
      · split
        · exact ⟨ready_src, by intro q hq; simp at hq⟩
        · rename_i q₀ h_select
          exact ⟨fun q hq => ready_src q (List.mem_of_mem_erase hq),
                 by intro q hq; simp only [Option.some.injEq] at hq; subst hq
                    exact ready_src q₀ (selectFCFS_mem h_select)⟩
      · rename_i h_not_done
        refine ⟨ready_src, ?_⟩
        intro q hq; simp only [Option.some.injEq] at hq; subst hq
        omega

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
  have uniform_pairwise : ∀ (l : List AperiodicProcess) (c : ℕ),
    (∀ p ∈ l, Process.arrival p = c) →
    List.Pairwise (fun a b => Process.arrival a ≤ Process.arrival b) l := by
    intro l c h
    induction l with
    | nil => exact List.Pairwise.nil
    | cons hd tl ih =>
      refine List.Pairwise.cons ?_ (ih fun p hp => h p (List.mem_cons_of_mem _ hp))
      intro b hb
      rw [h hd (List.mem_cons_self), h b (List.mem_cons_of_mem _ hb)]

  have stream_sorted t := uniform_pairwise _ t (fun p hp => h_arrival_consistent p t hp)

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
      rw [List.pairwise_append]
      refine ⟨ih, stream_sorted (t + 1), ?_⟩
      intro a ha b hb
      have h_a : Process.arrival a ≤ t := (system_arrival_bound arrival_stream h_arrival_consistent t).1 a ha
      have h_b : Process.arrival b = t + 1 := h_arrival_consistent b (t + 1) hb
      omega
    split
    · split
      · exact h_append
      · exact h_append.sublist (List.erase_sublist)
    · split
      · split
        · exact h_append
        · exact h_append.sublist (List.erase_sublist)
      · exact h_append

theorem target_index_decreases_one_step
  (arrival_stream : ℕ → List AperiodicProcess)
  (target : AperiodicProcess) (t : ℕ) (pre suf : List AperiodicProcess)
  (h_split : (runSteps arrival_stream stepFCFS t).ready = pre ++ target :: suf)
  (h_target_not_in_pre : target ∉ pre) :
  (runSteps arrival_stream stepFCFS (t + 1)).running = some target
  ∨ (∃ pre' suf', (runSteps arrival_stream stepFCFS (t + 1)).ready = pre' ++ target :: suf'
                 ∧ target ∉ pre'
                 ∧ pre'.length < pre.length)
  ∨ (∃ pre' suf', (runSteps arrival_stream stepFCFS (t + 1)).ready = pre' ++ target :: suf'
                 ∧ target ∉ pre'
                 ∧ pre'.length = pre.length
                 ∧ ∀ q, (runSteps arrival_stream stepFCFS t).running = some q →
                     (runSteps arrival_stream stepFCFS (t + 1)).running = some (Process.tick q))
  -- ∨ ∃ suf', (runSteps arrival_stream stepFCFS (t + 1)).ready = target :: suf'
  := by
  simp only [runSteps, stepFCFS, stepNonPreemptive]
  split
  · -- running = none
    rename_i h_prev_none
    have idle_pre : (runSteps arrival_stream stepFCFS t).ready = [] := idle_implies_empty_ready arrival_stream t h_prev_none
    rw [idle_pre] at h_split
    simp at h_split
  · -- running = some q
    rename_i q h_prev_none
    split
    · -- something just completed
      rename_i remaining_after_tick_le_0
      unfold stepFCFS at h_split
      rw [h_split]
      split
      · -- SelectFCFS chose nothing
        rename_i selectFCFS_chose_nothing
        rw [selectFCFS_none_iff_empty] at selectFCFS_chose_nothing
        simp at selectFCFS_chose_nothing
      · -- SelectFCFS chose something
        rename_i selectFCFS_chose_something
        unfold selectFCFS at selectFCFS_chose_something

        -- unfold choose something over match statements
        split at selectFCFS_chose_something
        · simp at selectFCFS_chose_something
        · rename_i pre_target_suf_sum_to_something
          apply Option.some.inj at selectFCFS_chose_something
          subst selectFCFS_chose_something
          induction pre with
          | nil =>
            left
            simp only [List.nil_append, List.cons_append, List.cons.injEq] at pre_target_suf_sum_to_something
            obtain ⟨target_is_running, _⟩ := pre_target_suf_sum_to_something
            rw [←target_is_running]

          | cons head_pre tail_pre ih =>
            clear ih -- oh SNAP i didnt know i could do rcases on inductive types will do that next time
            right
            left
            use tail_pre, (suf ++ arrival_stream (t + 1))
            refine ⟨?_, ?_, ?_⟩
            · simp only [List.cons_append, List.cons.injEq] at pre_target_suf_sum_to_something
              obtain ⟨head_pre_is_running, _⟩ := pre_target_suf_sum_to_something
              subst head_pre_is_running
              simp
            · exact List.not_mem_of_not_mem_cons h_target_not_in_pre
            · simp
    · -- nothing completed, continue execution
      rename_i h_not_done
      right
      right
      use pre, (suf ++ arrival_stream (t + 1))
      refine ⟨?_, ?_, rfl, ?_⟩
      · unfold stepFCFS at h_split
        rw [h_split]
        simp
      · assumption
      · intro q' h_q'_running
        -- `q` was renamed from the outer split; h_prev_none : ...running = some q
        have : q' = q := by
          rw [h_prev_none] at h_q'_running
          exact (Option.some.inj h_q'_running).symm
        subst this
        rfl

theorem target_progresses
  (arrival_stream : ℕ → List AperiodicProcess)
  (h_arrival_fresh : ∀ (p : AperiodicProcess) (t : ℕ), p ∈ arrival_stream t → p.remaining = p.burst)
  (target : AperiodicProcess) (t : ℕ) (pre suf : List AperiodicProcess)
  (h_split : (runSteps arrival_stream stepFCFS t).ready = pre ++ target :: suf)
  (h_target_not_in_pre : target ∉ pre):
  ∃ k > 0, (runSteps arrival_stream stepFCFS (t + k)).running = some target
  ∨ (∃ pre' suf', (runSteps arrival_stream stepFCFS (t + k)).ready = pre' ++ target :: suf'
    ∧ target ∉ pre'
    ∧ pre'.length < pre.length) := by

    suffices H : ∀ (n t : ℕ) (pre suf : List AperiodicProcess) (q : AperiodicProcess),
      (runSteps arrival_stream stepFCFS t).running = some q →
      (runSteps arrival_stream stepFCFS t).ready = pre ++ target :: suf →
      Process.remaining q ≤ n →
      target ∉ pre →
      ∃ k > 0, (runSteps arrival_stream stepFCFS (t + k)).running = some target
      ∨ (∃ pre' suf', (runSteps arrival_stream stepFCFS (t + k)).ready = pre' ++ target :: suf'
        ∧ target ∉ pre'
        ∧ pre'.length < pre.length)
      from by
      have h_ready_nonempty : (runSteps arrival_stream stepFCFS t).ready ≠ [] := by
        rw [h_split]
        simp
      obtain ⟨q, q_running⟩ := ready_nonempty_implies_running_nonempty arrival_stream t (by rw [h_split]; simp)
      exact H (Process.remaining q) t pre suf q q_running h_split (by omega) h_target_not_in_pre
    intro n
    induction n with
    | zero =>
      intro t' pre' suf' q h_running h_ready h_remaining h_notin
      have := (ready_running_remaining_pos arrival_stream h_arrival_fresh t').2 q h_running
      omega

    | succ n ih =>
      intro t' pre' suf' q h_running h_ready h_remaining h_notin
      rcases target_index_decreases_one_step arrival_stream target t' pre' suf' h_ready h_notin with
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

theorem mem_split_canonical {α} {l : List α} {p : α} (h : p ∈ l) :
    ∃ pre suf, l = pre ++ p :: suf ∧ p ∉ pre := by
  induction l with
  | nil => simp at h
  | cons hd tl ih =>
    by_cases h_eq : hd = p
    · exact ⟨[], tl, by grind, by simp⟩
    · have h_tl : p ∈ tl := by
        rcases List.mem_cons.mp h with rfl | h'
        · exact absurd rfl h_eq
        · exact h'
      obtain ⟨pre, suf, h_split, h_notin⟩ := ih h_tl
      exact ⟨hd :: pre, suf, by rw [h_split]; rfl, by simp [h_notin, Ne.symm h_eq]⟩

lemma erase_head_split {α : Type*} [DecidableEq α] {l pre suf : List α} {p : α}
    (h_split : l = pre ++ p :: suf) (h_notin : p ∉ pre) (h_ne : l ≠ []) :
    (pre = [] ∧ l.head h_ne = p)
    ∨ (∃ pre', l.erase (l.head h_ne) = pre' ++ p :: suf ∧ p ∉ pre' ∧ pre'.length < pre.length) := by
  cases pre with
  | nil => left; exact ⟨rfl, by simp [h_split]⟩
  | cons hd tl =>
    right
    refine ⟨tl, ?_, List.not_mem_of_not_mem_cons h_notin, by simp⟩
    subst h_split
    simp

theorem arrived_is_ready_or_running
  (arrival_stream : ℕ → List AperiodicProcess) (t : ℕ) (p : AperiodicProcess)
  (h_arrived : p ∈ arrival_stream t)
  (h_arrival_consistent : ∀ (p : AperiodicProcess) (t : ℕ), p ∈ arrival_stream t → p.arrival = t):
  (∃ pre suf, (runSteps arrival_stream stepFCFS t).ready = pre ++ p :: suf ∧ p ∉ pre)
  ∨ (runSteps arrival_stream stepFCFS t).running = some p
  := by
    obtain ⟨pre, suf, arrival_t_composition, h_p_not_pre⟩ := mem_split_canonical h_arrived
    cases t with
    | zero =>
      cases pre with
      | nil =>
        right
        simp only [runSteps, stepFCFS, stepNonPreemptive]
        simp only [SchedStateMethods.init]
        rw [arrival_t_composition]
        simp only [selectFCFS]
        simp
      | cons pre_hd pre_tl =>
        left
        use pre_tl, suf
        simp only [runSteps, stepFCFS, stepNonPreemptive]
        simp only [SchedStateMethods.init]
        rw [arrival_t_composition]
        simp only [selectFCFS]
        grind
    | succ n =>
      have h_p_not_prev_ready : p ∉ (runSteps arrival_stream (stepNonPreemptive selectFCFS) n).ready := by
        intro h_mem
        have h_le := (system_arrival_bound arrival_stream h_arrival_consistent n).1 p h_mem
        have h_eq := h_arrival_consistent p (n + 1) h_arrived
        simp at h_le
        omega
      simp only [runSteps, stepFCFS, stepNonPreemptive]
      split
      · rename_i h_running_none
        have h_ready_empty := idle_implies_empty_ready arrival_stream n h_running_none
        simp only [stepFCFS] at h_ready_empty
        rw [h_ready_empty]
        simp only [List.nil_append, exists_and_right]

        cases pre with
        | nil =>
          simp at arrival_t_composition
          have selectFCFS_decision_p : selectFCFS (arrival_stream (n + 1)) = p
            := by
            rw [selectFCFS_head]
            use suf
          rw [selectFCFS_decision_p]
          simp
        | cons pre_hd pre_tl =>
          simp only [List.cons_append] at arrival_t_composition
          have selectFCFS_decision_pre_hd : selectFCFS (arrival_stream (n + 1)) = pre_hd
            := by
            rw [selectFCFS_head]
            use (pre_tl ++ p :: suf)
          rw [selectFCFS_decision_pre_hd]
          simp only [Option.some.injEq]
          left
          rw [arrival_t_composition]
          use pre_tl
          refine ⟨?_, ?_⟩
          · use suf
            simp
          · apply List.not_mem_of_not_mem_cons at h_p_not_pre
            assumption
      · rename_i prev_running_process h_running_some
        split
        · rename_i prev_process_remaining_zero
          split
          · rename_i ready_plus_arrival_selected_none
            exfalso
            have ready_plus_arrival_none : ((runSteps arrival_stream (stepNonPreemptive selectFCFS) n).ready ++ arrival_stream (n + 1)) = []
              := by
                rw [selectFCFS_none_iff_empty] at ready_plus_arrival_selected_none
                exact ready_plus_arrival_selected_none
            rw [arrival_t_composition] at ready_plus_arrival_none
            simp at ready_plus_arrival_none
          · rename_i selected_process ready_plus_arrival_selected_some
            simp only [exists_and_right, Option.some.injEq]
            cases pre with
            | nil =>
              cases h_prev_ready : (runSteps arrival_stream (stepNonPreemptive selectFCFS) n).ready with
              | nil =>
                right
                rw [h_prev_ready, List.nil_append] at ready_plus_arrival_selected_some
                rw [selectFCFS_head] at ready_plus_arrival_selected_some
                obtain ⟨_rest, ready_plus_arrival_selected_some ⟩ := ready_plus_arrival_selected_some
                simp only [List.nil_append] at arrival_t_composition
                rw [arrival_t_composition] at ready_plus_arrival_selected_some
                simp at ready_plus_arrival_selected_some
                tauto

              | cons rh rt =>
                left
                rw [arrival_t_composition]
                use rt
                constructor
                · use suf
                  simp
                  rw [h_prev_ready] at ready_plus_arrival_selected_some
                  rw [selectFCFS_head] at ready_plus_arrival_selected_some
                  obtain ⟨_rest, h_selected_process_eq_rh⟩ := ready_plus_arrival_selected_some
                  simp at h_selected_process_eq_rh
                  simp [h_selected_process_eq_rh.left]
                · rw [h_prev_ready] at h_p_not_prev_ready
                  clear * - h_p_not_prev_ready
                  grind
            | cons pre_hd pre_tl =>
              left
              simp only [List.cons_append] at arrival_t_composition
              have selectFCFS_decision_pre_hd : selectFCFS (arrival_stream (n + 1)) = pre_hd
                := by
                rw [selectFCFS_head]
                use (pre_tl ++ p :: suf)
              rw [arrival_t_composition] at ready_plus_arrival_selected_some ⊢
              cases h_prev_ready : (runSteps arrival_stream (stepNonPreemptive selectFCFS) n).ready with
              | nil =>
                use pre_tl
                rw [h_prev_ready, List.nil_append] at ready_plus_arrival_selected_some
                rw [selectFCFS_head] at ready_plus_arrival_selected_some
                obtain ⟨_rest, ready_plus_arrival_selected_some ⟩ := ready_plus_arrival_selected_some
                simp at ready_plus_arrival_selected_some
                rw [← ready_plus_arrival_selected_some.left]
                constructor
                · use suf
                  simp
                · apply List.not_mem_of_not_mem_cons at h_p_not_pre
                  assumption
              | cons rh rt =>
                use rt ++ pre_hd :: pre_tl
                constructor
                · use suf
                  rw [h_prev_ready] at ready_plus_arrival_selected_some
                  rw [selectFCFS_head] at ready_plus_arrival_selected_some
                  obtain ⟨_rest, h_selected_process_eq_rh⟩ := ready_plus_arrival_selected_some
                  simp only [List.cons_append, List.cons.injEq] at h_selected_process_eq_rh
                  obtain ⟨rh_is_selected_process, contents_of_rest_of_ready⟩ := h_selected_process_eq_rh
                  simp [rh_is_selected_process]
                · grind
        · rename_i no_complete_this_tick
          left
          cases pre with
          | nil =>
            cases h_prev_ready : (runSteps arrival_stream (stepNonPreemptive selectFCFS) n).ready with
            | nil =>
              use []
              rw [arrival_t_composition]
              simp
            | cons rh rt =>
              rw [arrival_t_composition]
              use rh :: rt, suf
              apply And.intro
              · simp
              · rw [h_prev_ready] at h_p_not_prev_ready
                exact h_p_not_prev_ready
          | cons pre_hd pre_tl =>
            simp only [List.cons_append] at arrival_t_composition
            have selectFCFS_decision_pre_hd : selectFCFS (arrival_stream (n + 1)) = pre_hd
              := by
              rw [selectFCFS_head]
              use (pre_tl ++ p :: suf)
            rw [arrival_t_composition]
            cases h_prev_ready : (runSteps arrival_stream (stepNonPreemptive selectFCFS) n).ready with
            | nil =>
              use pre_hd :: pre_tl, suf
              constructor
              · simp
              · assumption
            | cons rh rt =>
              use rh :: rt ++ pre_hd :: pre_tl
              use suf
              constructor
              · simp
              · grind

theorem running_eventually_completes
  (arrival_stream : ℕ → List AperiodicProcess) (t : ℕ) (p : AperiodicProcess)
  (h_running : (runSteps arrival_stream stepFCFS t).running = some p) :
  ∃ k, ∃ q ∈ (runSteps arrival_stream stepFCFS (t + k)).completed, Process.id q = Process.id p

theorem target_eventually_runs
  (arrival_stream : ℕ → List AperiodicProcess) (target : AperiodicProcess)
  (h_arrival_fresh : ...) (t : ℕ) (pre suf : List AperiodicProcess)
  (h_split : (runSteps arrival_stream stepFCFS t).ready = pre ++ target :: suf)
  (h_notin : target ∉ pre) :
  ∃ k, (runSteps arrival_stream stepFCFS (t + k)).running = some target := by
  induction hn : pre.length using Nat.strong_induction_on generalizing t pre suf with
  | _ n ih =>
    obtain ⟨k, h_k_pos, h_concl⟩ := target_progresses ...
    rcases h_concl with h_run | ⟨pre', suf', h_ready', h_notin', h_lt⟩
    · exact ⟨k, h_run⟩
    · obtain ⟨k', h_k'⟩ := ih pre'.length (by omega) (t + k) pre' suf' h_ready' h_notin' rfl
      exact ⟨k + k', by rw [show t + (k + k') = t + k + k' by omega]; exact h_k'⟩

theorem FCFSStarvationFree
  (arrival_stream : Nat → List AperiodicProcess)
  (h_arrival_unique : ∀ p1 p2 t1 t2, p1 ∈ arrival_stream t1 → p2 ∈ arrival_stream t2 → p1 = p2 → t1 = t2):
  ∀ arrival_time process, process ∈ arrival_stream arrival_time →
  ∃ completion_time, ∃ finished_process ∈ (runSteps arrival_stream stepFCFS completion_time).completed,
    Process.id finished_process = Process.id process -- cannot directly compare a process via == since the `remaining` field changes
  := by
  intro arrival_time process h_arrived
  rcases arrived_is_ready_or_running arrival_stream arrival_time process h_arrived with
    ⟨pre, suf, h_split, h_notin⟩ | h_running
  · obtain ⟨k, h_running⟩ := target_eventually_runs ...
    obtain ⟨k', q, h_q_mem, h_q_id⟩ := running_eventually_completes ... h_running
    exact ⟨arrival_time + k + k', q, h_q_mem, h_q_id⟩
  · obtain ⟨k, q, h_q_mem, h_q_id⟩ := running_eventually_completes ... h_running
    exact ⟨arrival_time + k, q, h_q_mem, h_q_id⟩



-- Proof that Starvation occurs in Shortest Job First, Shortest Remaining Time First schedulers

-- Proof that in the First Come First Serve, Round Robin scheduler every process will run
