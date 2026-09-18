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
  (h_wf : WellFormedStream arrival_stream)
  (t : ℕ) :
  (∀ q ∈ (runSteps arrival_stream stepFCFS t).ready, Process.remaining q > 0) ∧
  (∀ q, (runSteps arrival_stream stepFCFS t).running = some q → Process.remaining q > 0) := by
  have fresh_pos : ∀ (p : AperiodicProcess) (s : ℕ), p ∈ arrival_stream s → Process.remaining p > 0 := by
    intro p s hp
    simp only [AperiodicProcess.process_remaining, gt_iff_lt]
    rw [h_wf.fresh p s hp]
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
  (h_wf : WellFormedStream arrival_stream)
  (t : ℕ) :
  (∀ q ∈ (runSteps arrival_stream stepFCFS t).ready, Process.arrival q ≤ t) ∧
  (∀ q, (runSteps arrival_stream stepFCFS t).running = some q → Process.arrival q ≤ t) := by
  induction t with
  | zero =>
    have h_init_running : (SchedStateMethods.init : SchedStateG AperiodicProcess).running = none := rfl
    simp only [runSteps, stepFCFS, stepNonPreemptive, h_init_running]
    split
    · refine ⟨?_, ?_⟩
      · intro q hq; exact le_of_eq (h_wf.consistent q 0 hq)
      · intro q hq; simp at hq
    · rename_i q₀ h_select
      refine ⟨?_, ?_⟩
      · intro q hq
        exact le_of_eq (h_wf.consistent q 0 (List.mem_of_mem_erase hq))
      · intro q hq; simp only [Option.some.injEq] at hq; subst hq
        exact le_of_eq (h_wf.consistent q₀ 0 (selectFCFS_mem h_select))
  | succ t ih =>
    obtain ⟨ih_ready, ih_running⟩ := ih
    simp only [runSteps, stepFCFS, stepNonPreemptive]
    have ready_src : ∀ q ∈ (runSteps arrival_stream stepFCFS t).ready ++ arrival_stream (t + 1),
        Process.arrival q ≤ t + 1 := by
      intro q hq
      rcases List.mem_append.mp hq with h | h
      · exact le_trans (ih_ready q h) (by omega)
      · exact le_of_eq (h_wf.consistent q (t + 1) h)
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
  (h_wf : WellFormedStream arrival_stream)
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

  have stream_sorted t := uniform_pairwise _ t (fun p hp => h_wf.consistent p t hp)

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
      have h_a : Process.arrival a ≤ t := (system_arrival_bound arrival_stream h_wf t).1 a ha
      have h_b : Process.arrival b = t + 1 := h_wf.consistent b (t + 1) hb
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
  (h_wf : WellFormedStream arrival_stream)
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
      have := (ready_running_remaining_pos arrival_stream h_wf t').2 q h_running
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

lemma erase_head_split {α : Type*} {rest pre suf : List α} {hd p : α}
    (h_split : hd :: rest = pre ++ p :: suf) (h_notin : p ∉ pre) :
    (pre = [] ∧ hd = p)
    ∨ (∃ pre', rest = pre' ++ p :: suf ∧ p ∉ pre' ∧ pre'.length < pre.length) := by
  cases pre with
  | nil => left; simp only [List.nil_append, List.cons.injEq] at h_split; exact ⟨rfl, h_split.1⟩
  | cons a tl =>
    right
    simp only [List.cons_append, List.cons.injEq] at h_split
    exact ⟨tl, h_split.2, List.not_mem_of_not_mem_cons h_notin, by simp⟩

theorem arrived_is_ready_or_running
  (arrival_stream : ℕ → List AperiodicProcess) (t : ℕ) (p : AperiodicProcess)
  (h_arrived : p ∈ arrival_stream t)
  (h_wf : WellFormedStream arrival_stream) :
  (∃ pre suf, (runSteps arrival_stream stepFCFS t).ready = pre ++ p :: suf ∧ p ∉ pre)
  ∨ (runSteps arrival_stream stepFCFS t).running = some p := by
  obtain ⟨pre, suf, arrival_t_composition, h_p_not_pre⟩ := mem_split_canonical h_arrived
  cases t with
  | zero =>
    simp only [runSteps, stepFCFS, stepNonPreemptive, SchedStateMethods.init]
    have h_comb : arrival_stream 0 = ([] ++ pre) ++ p :: suf := by
      simpa using arrival_t_composition
    have h_ne : arrival_stream 0 ≠ [] := by
      rw [arrival_t_composition]; simp
    split
    · rename_i h_sel
      rw [selectFCFS_none_iff_empty] at h_sel
      exact absurd h_sel h_ne
    · rename_i sel h_sel
      obtain ⟨rest, h_cons⟩ := selectFCFS_head.mp h_sel
      rw [h_cons] at h_comb
      rcases erase_head_split h_comb (by simpa using h_p_not_pre) with
        ⟨h_pre_nil, h_head⟩ | ⟨pre', h_erase, h_notin', _⟩
      · right; simp [← h_head]
      · left; exact ⟨pre', suf, by simpa [h_cons] using h_erase, h_notin'⟩
  | succ n =>
    have h_p_not_prev_ready : p ∉ (runSteps arrival_stream stepFCFS n).ready := by
      intro h_mem
      have h_le := (system_arrival_bound arrival_stream h_wf n).1 p h_mem
      have h_eq := h_wf.consistent p (n + 1) h_arrived
      simp at h_le; omega
    have h_p_not_comb : p ∉ (runSteps arrival_stream stepFCFS n).ready ++ pre := by
      simp [h_p_not_prev_ready, h_p_not_pre]
    have h_comb : (runSteps arrival_stream stepFCFS n).ready ++ arrival_stream (n + 1)
        = ((runSteps arrival_stream stepFCFS n).ready ++ pre) ++ p :: suf := by
      rw [arrival_t_composition, List.append_assoc]
    have h_ne : (runSteps arrival_stream stepFCFS n).ready ++ arrival_stream (n + 1) ≠ [] := by
      rw [h_comb]; simp
    simp only [runSteps, stepFCFS, stepNonPreemptive]
    split
    · -- prev.running = none
      split
      · rename_i h_sel
        rw [selectFCFS_none_iff_empty] at h_sel
        exact absurd h_sel h_ne
      · rename_i sel h_sel
        obtain ⟨rest, h_cons⟩ := selectFCFS_head.mp h_sel
        simp only [stepFCFS] at h_comb; rw [h_cons] at h_comb
        rcases erase_head_split h_comb h_p_not_comb with
          ⟨h_pre_nil, h_head⟩ | ⟨pre', h_rest, h_notin', _⟩
        · right; simp [h_head]
        · left; exact ⟨pre', suf, by rw [h_cons]; simpa using h_rest, h_notin'⟩
    · -- prev.running = some q
      split
      · -- q finished, select fires
        split
        · rename_i h_sel
          rw [selectFCFS_none_iff_empty] at h_sel
          exact absurd h_sel h_ne
        · rename_i sel h_sel
          obtain ⟨rest, h_cons⟩ := selectFCFS_head.mp h_sel
          simp only [stepFCFS] at h_comb; rw [h_cons] at h_comb
          rcases erase_head_split h_comb h_p_not_comb with
            ⟨h_pre_nil, h_head⟩ | ⟨pre', h_rest, h_notin', _⟩
          · right; simp [← h_head]
          · left; exact ⟨pre', suf, by simpa [h_cons] using h_rest, h_notin'⟩
      · -- q continues: ready is the combined list untouched
        left
        exact ⟨(runSteps arrival_stream stepFCFS n).ready ++ pre, suf, h_comb, h_p_not_comb⟩

theorem running_eventually_completes
  (arrival_stream : ℕ → List AperiodicProcess) (t : ℕ) (p : AperiodicProcess)
  (h_running : (runSteps arrival_stream stepFCFS t).running = some p)
  (h_wf : WellFormedStream arrival_stream):
  ∃ k ≥ 1, ∃ q ∈ (runSteps arrival_stream stepFCFS (t + k)).completed, Process.id q = Process.id p := by
    have process_tick_mt_1 : (Process.tick p).remaining ≥ 1 := by
      have := system_provenance -- doesnt work provenance talks about id but not remaining
      -- have to induct over how running executes and deduce its remaining more than 0 Check if this is in another theorem later
      sorry
    use p.remaining - 1
    induction h_p_remaining : (Process.tick p).remaining with
    | zero =>

      cases t with
      | zero =>
        have h_init_running : (SchedStateMethods.init : SchedStateG AperiodicProcess).running = none := by rfl
        simp [runSteps, stepFCFS, stepNonPreemptive, h_init_running] at h_running ⊢
        rcases h_arrival_stream: selectFCFS (arrival_stream 0) with _ | p_selected
        · simp only [h_arrival_stream] at h_running
          grind
        · simp only [h_arrival_stream] at h_running
          have selected_eq_p: p = p_selected := by exact Option.some_inj.mp (symm h_running)
          subst selected_eq_p; clear h_running
          have p_mem_of_arrival_0 : p ∈ arrival_stream 0 := by exact selectFCFS_mem h_arrival_stream
          have p_remaining_eq_burst :=h_wf.fresh p 0 p_mem_of_arrival_0
          have p_burst_mt_0 := Process.burst_exceed_zero p
          simp at p_burst_mt_0 h_p_remaining
          rw [h_p_remaining]
          simp [runSteps, stepFCFS, stepNonPreemptive, h_init_running]



      | succ n =>
        use p
        simp only [runSteps, stepFCFS, stepNonPreemptive]
        simp only [stepFCFS] at h_running
        rw [h_running]

        a
    | succ n ih=>
      a
      -- induct over remaining time

    -- If remaining was 0 then (stepNonPreemptive select)^[process.remaining] s would be ill defined
    -- need to induct over remaining_minus_one rather than remaining
    -- need to convert the problem to be written over remaining_minus_one rather than remaining
    obtain ⟨remain_minus_one, h_remain_minus_one⟩ : ∃ remain_minus_one, process.remaining = remain_minus_one + 1 := ⟨process.remaining - 1, by omega⟩
    rw [h_remain_minus_one]

    induction remain_minus_one generalizing s process with
    | zero =>
    -- remain minus one = 0 meaning last tick
        simp only [zero_add, Function.iterate_one]
        have h_finishing : process.remaining ≤ 1 := by omega
        have ticked_process_in_completed_queue := stepNonPreemptive_completes_head_of_queue (select := select) s process h_running h_finishing |> And.right
        use Process.tick process
        apply And.intro
        · rw [Process.id_invariant_wrt_tick process]
        exact ticked_process_in_completed_queue
    | succ remain_minus_two ih =>
    -- remain minus one ≠ 0 meaning more than 1 tick left
      rw [Function.iterate_succ, Function.comp_apply]
      let one_step_state := stepNonPreemptive select s
      -- before ticking, the remaining seconds > 1
      have h_remaining_more_than_one : process.remaining > 1 := by omega -- from h_remain_minus_one : process.remaining = (remain_minus_two + 1) + 1

      -- After 1 tick, still running same process
      have h_next_running := stepNonPreemptive_continues_running (select := select) s process h_running h_remaining_more_than_one
      -- After 1 tick, running process's remaining >= 1
      have h_one_step_state_run_more_steps_remaining : one_step_state.running = some { process with remaining := remain_minus_two + 1 } := by
        unfold one_step_state
        -- same as tick_decrements -- just that tick_decrements defined in terms of Process.remaining process rather than process.remaining directly
        have h_tick_eq : Process.tick process = { process with remaining := process.remaining - 1 } := rfl
        rw [h_next_running, h_tick_eq, h_remain_minus_one]
        congr 1
      -- apply ih at h_one_step_state_run_more_steps_remaining
      have result := ih one_step_state { process with remaining := remain_minus_two + 1 }
        h_one_step_state_run_more_steps_remaining
        (by simp)
        rfl
      exact result


theorem target_eventually_runs
  (arrival_stream : ℕ → List AperiodicProcess) (target : AperiodicProcess)
  (h_wf : WellFormedStream arrival_stream) (t : ℕ) (pre suf : List AperiodicProcess)
  (h_split : (runSteps arrival_stream stepFCFS t).ready = pre ++ target :: suf)
  (h_notin : target ∉ pre) :
  ∃ k, (runSteps arrival_stream stepFCFS (t + k)).running = some target := by
  induction hn : pre.length using Nat.strong_induction_on generalizing t pre suf with
  | _ n ih =>
    obtain ⟨k, h_k_pos, h_concl⟩ := target_progresses arrival_stream h_wf target t pre suf h_split h_notin
    rcases h_concl with h_run | ⟨pre', suf', h_ready', h_notin', h_lt⟩
    · exact ⟨k, h_run⟩
    · obtain ⟨k', h_k'⟩ := ih pre'.length (by omega) (t + k) pre' suf' h_ready' h_notin' rfl
      exact ⟨k + k', by rw [show t + (k + k') = t + k + k' by omega]; exact h_k'⟩

theorem FCFSStarvationFree
  (arrival_stream : Nat → List AperiodicProcess)
  (h_wf : WellFormedStream arrival_stream) :
  ∀ arrival_time process, process ∈ arrival_stream arrival_time →
  ∃ completion_time, ∃ finished_process ∈ (runSteps arrival_stream stepFCFS completion_time).completed,
    Process.id finished_process = Process.id process -- cannot directly compare a process via == since the `remaining` field changes
  := by
  intro arrival_time process h_arrived
  rcases arrived_is_ready_or_running arrival_stream arrival_time process h_arrived h_wf with
    ⟨pre, suf, h_split, h_notin⟩ | h_running
  · obtain ⟨k, h_running⟩ := target_eventually_runs arrival_stream process h_wf arrival_time pre suf h_split h_notin
    obtain ⟨k', q, h_q_mem, h_q_id⟩ := running_eventually_completes arrival_stream (arrival_time + k) process h_running
    exact ⟨arrival_time + k + k', q, h_q_mem, h_q_id⟩
  · obtain ⟨k, q, h_q_mem, h_q_id⟩ := running_eventually_completes arrival_stream arrival_time process h_running
    exact ⟨arrival_time + k, q, h_q_mem, h_q_id⟩



-- Proof that Starvation occurs in Shortest Job First, Shortest Remaining Time First schedulers

-- Proof that in the First Come First Serve, Round Robin scheduler every process will run
