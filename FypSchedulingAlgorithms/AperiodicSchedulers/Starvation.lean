/-
Copyright (c) 2026 Choo Kye Yong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Choo Kye Yong
-/
-- Starvation: When a process is put into the ready queue but never gets to run because it keeps being deprioritized compared to newer arriving processes.

import FypSchedulingAlgorithms.Process
import FypSchedulingAlgorithms.Step
import FypSchedulingAlgorithms.SchedState
import FypSchedulingAlgorithms.AperiodicSchedulers.AperiodicStep
import Mathlib.Tactic.Linarith

theorem stepNonPreemptive_ready_nonempty_implies_running
    (select : List AperiodicProcess → Option AperiodicProcess)
    (s : SchedState) (h_running_none : s.running = none)
    (h_select_finds : select s.ready ≠ none) :
    ∃ p, (stepNonPreemptive select s).running = some p := by
  unfold stepNonPreemptive
  simp only [h_running_none]
  cases h : select s.ready with
  | none => exact absurd h h_select_finds
  | some p => exact ⟨p, by simp⟩

theorem stepNonPreemptive_completes_head_of_queue
    (select : List AperiodicProcess → Option AperiodicProcess)
    (state_before : SchedState) (p : AperiodicProcess)
    (h_running : state_before.running = some p)
    (h_finishes : Process.remaining p ≤ 1) :
    (stepNonPreemptive select state_before).running = select state_before.ready ∧
    Process.tick p ∈ (stepNonPreemptive select state_before).completed := by
    apply And.intro
    · unfold stepNonPreemptive
      simp only [h_running]
      split
      · split
        · rename_i heq
          rw [heq]
        · rename_i heq
          rw [heq]
      · rename_i h_contradiction
        exfalso
        rw [Process.tick_decrements p] at h_contradiction
        omega
    · unfold stepNonPreemptive
      simp only [h_running]
      split
      · split
        · simp
        · simp
      · rename_i h_contradiction
        exfalso
        rw [Process.tick_decrements p] at h_contradiction
        omega

theorem stepNonPreemptive_continues_running
    (select : List AperiodicProcess → Option AperiodicProcess)
    [Process AperiodicProcess]
    (s : SchedState) (p : AperiodicProcess)
    (h_running : s.running = some p) (h_not_finished : Process.remaining p > 1) :
    (stepNonPreemptive select s).running = some (Process.tick p) := by
    unfold stepNonPreemptive
    simp only [h_running]
    rw [Process.tick_decrements p]
    split
    · omega
    · rfl

theorem stepNonPreemptive_runs_until_complete
    (select : List AperiodicProcess → Option AperiodicProcess)
    (s : SchedState) (process : AperiodicProcess)
    (h_running : s.running = some process) (h_non_zero_remaining_time : process.remaining > 0) :
    ∃ completed_process: AperiodicProcess, Process.id completed_process = Process.id process ∧
    completed_process ∈ ((stepNonPreemptive select)^[process.remaining] s |>.completed):= by
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

theorem mem_removeFirst_of_ne
  [BEq α] [LawfulBEq α]
  (l : List α) (p process : α)
  (h_ne : process ≠ p)
  (h_mem : process ∈ l) :
  process ∈ l.removeFirst p := by
  induction l with
  | nil => exact absurd h_mem List.not_mem_nil
  | cons hd tl ih =>
    unfold List.removeFirst
    split
    · rename_i h_beq
      rw [beq_iff_eq] at h_beq
      simp only [List.mem_cons] at h_mem
      rcases h_mem with rfl | h_tl
      · exact absurd h_beq h_ne
      · tauto
    · simp only [List.mem_cons] at h_mem ⊢
      rcases h_mem with rfl | h_tl
      · left; rfl
      · right; exact ih h_tl

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
              unfold List.removeFirst
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
                  exact mem_removeFirst_of_ne tl p process h_selected_process_eq_target_process h_tl
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
              simp [List.mem_append, mem_removeFirst_of_ne, h_ready, h_eq]
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
                apply mem_removeFirst_of_ne _ _ _ h_eq
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
                simp [List.mem_append, mem_removeFirst_of_ne, h_mem, h_eq]
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
                  simp [List.mem_append, mem_removeFirst_of_ne, h_mem, h_eq]
            · -- remaining > 0, process in ready
              left
              simp [List.mem_append, h_mem]
        · -- still unarrived
          right; right; right
          exact ⟨arrival_time, by omega, h_mem⟩

def FCFSCompletionTime (process_list : List AperiodicProcess): ℕ :=
  -- The following approach which is adding up all burst times, fail in case of
  -- 2 processes separated by arbitrarily big gap
  -- since the true completion time includes waiting for the second process
  -- to arrive
  -- process_list.foldl (fun running_total p => running_total + p.burst) 0
  process_list.foldl
    (fun completion_so_far p => max completion_so_far (Process.arrival p) + Process.burst p) 0

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

theorem FCFSCompletionTime_take_le_FCFSCompletionTime_whole
  (processes : List AperiodicProcess)
  (n : ℕ) :
  FCFSCompletionTime (processes.take n) ≤ FCFSCompletionTime processes
    := by
      unfold FCFSCompletionTime
      apply foldl_prefix_le
      -- prove each step is non-decreasing
      intro acc p
      omega  -- max acc p.arrival + p.burst ≥ acc

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

theorem FCFSCompletionTime_last_element
  (processes : List AperiodicProcess)
  (n : ℕ)
  (h : n < processes.length) :
  FCFSCompletionTime (processes.take (n + 1)) =
    max (FCFSCompletionTime (processes.take n)) (processes[n].arrival) + processes[n].burst := by

  unfold FCFSCompletionTime
  have h_take : processes.take (n + 1) = processes.take n ++ [processes[n]] := by
    rw [List.take_add_one]
    simp [List.getElem?_eq_getElem h]
  rw [h_take, List.foldl_append]
  simp [List.foldl]
  rfl


-- for all time
theorem FCFS_completed_matches_prefix
  -- states that for any time, processes at the front will have completed and
  -- the next process will not have begun
  (arrival_stream : Nat → List AperiodicProcess)
  (h_arrival_unique : ∀ p1 p2 t1 t2, p1 ∈ arrival_stream t1 → p2 ∈ arrival_stream t2 → p1 = p2 → t1 = t2)
  (processes : List AperiodicProcess)
  -- process must be part of the stream
  (h_processes_from_stream : ∀ p ∈ processes, ∃ arrival_time, p ∈ arrival_stream arrival_time)
  (time : ℕ) :
  -- some processes will have completed
  ∃ num_processes_completed, (∀ process_arrival_stream ∈ processes.take num_processes_completed,
    ∃ process_completed ∈ (runSteps arrival_stream stepFCFS time).completed,
    Process.id process_completed = Process.id process_arrival_stream) ∧
    -- Current time will be no less than time taken for all processes to complete
    FCFSCompletionTime (processes.take num_processes_completed) ≤ time ∧
    -- Current time will not be enough to complete the next process
    (num_processes_completed < processes.length →
      time < FCFSCompletionTime (processes.take (num_processes_completed + 1))) ∧
    num_processes_completed ≤ processes.length
      := by
  induction time with
  | zero =>
    unfold runSteps
    simp only [Nat.le_zero_eq]
    use 0
    simp only [List.take_zero, zero_add]
    apply And.intro
    · tauto
    apply And.intro
    · unfold FCFSCompletionTime
      rfl
    induction processes with
    | nil =>
      simp
    | cons head tails ih =>
      simp only [List.length_cons, Nat.zero_lt_succ, List.take_succ_cons, List.take_zero, forall_const]
      unfold FCFSCompletionTime
      simp
      have h_process_burst_exceed_zero : Process.burst head > 0 := Process.burst_exceed_zero head
      omega
  | succ t_minus_one ih =>
    obtain ⟨num_completed_processes_at_t_minus_one, h_completed_eq, h_lower, h_upper, h_num_processes_completed_le_processes_length⟩ := ih
    set prev := runSteps arrival_stream stepFCFS t_minus_one with h_prev_def
    match h_running_state : prev.running with
    | none =>
      -- nobody was running; after arrivals + 1 step, check if someone starts
      match arrival_list_during_t : arrival_stream (t_minus_one + 1) with
      | List.nil =>
        -- noone arrived this tick
        use num_completed_processes_at_t_minus_one
        apply And.intro
        · have h_next : (runSteps arrival_stream stepFCFS (t_minus_one + 1)).completed = prev.completed := by
            change (stepFCFS { prev with ready := prev.ready ++ arrival_stream (t_minus_one + 1) }).completed = prev.completed
            rw [arrival_list_during_t]
            simp only [stepFCFS, h_running_state]
            unfold stepNonPreemptive
            simp
            split
            · rfl
            · rfl
          rw [h_next]
          omega
        apply And.intro
        -- time just increased without new processes added, use h lower
        · omega

        apply And.intro
        intro h_exists_unarrived_processes
        have h_prev_bound := h_upper h_exists_unarrived_processes
        let next_process := processes[num_completed_processes_at_t_minus_one]
        have h_next_arrives :
          ∃ arrival_time, next_process ∈ arrival_stream arrival_time :=
          h_processes_from_stream next_process
          (List.getElem_mem h_exists_unarrived_processes)

        have h_unarrived : ∃ arrival_time, arrival_time > t_minus_one + 1 ∧
          next_process ∈ arrival_stream arrival_time := by
          have h_status := non_preemptive_processes_are_ready_running_completed_or_unarrived
                  selectFCFS arrival_stream next_process h_next_arrives t_minus_one
          obtain ⟨arrival_time, h_arrival⟩ := h_next_arrives
          refine ⟨arrival_time, ?_, h_arrival⟩
          -- arrival_time must be > t_minus_one + 1 because:
          -- arrival_stream (t_minus_one + 1) = [] so arrival_time ≠ t_minus_one + 1
          -- anything ≤ t_minus_one would have been in prev.ready, but prev.ready = []
          have h_not_current : arrival_time ≠ t_minus_one + 1 := by
            intro h_eq
            simp [h_eq, arrival_list_during_t] at h_arrival
          have h_ready_empty : prev.ready = [] := by
            exact idle_implies_empty_ready arrival_stream t_minus_one h_running_state

          rcases h_status with h_ready | h_running | h_completed | ⟨t, h_t_gt, h_t_mem⟩
          · -- next_process in ready, but prev.ready = []
            simp [stepFCFS] at h_prev_def
            rw [← h_prev_def] at h_ready
            simp [h_ready_empty] at h_ready
          · -- next_process running, but prev.running = none
            simp [stepFCFS] at h_prev_def
            rw [← h_prev_def] at h_running
            simp [h_running_state] at h_running
          · -- next_process completed, but completed only contains processes
            -- that started before next_process in FCFS order - contradiction

          · -- next_process unarrived at t_minus_one, so arrival_time > t_minus_one
            -- combined with h_not_current gives arrival_time > t_minus_one + 1
            have h_arrival_eq : t = arrival_time :=
              h_arrival_unique next_process next_process t arrival_time h_t_mem h_arrival rfl
            omega


        have h_arrival_late : next_process.arrival > t_minus_one + 1 := by
          obtain ⟨arrival_time, h_gt, h_mem⟩ := h_unarrived
          -- arrival_time is when it arrives, and arrival_time > t_minus_one + 1
          -- need: next_process.arrival = arrival_time
          sorry
        have h_foldl := FCFSCompletionTime_last_element
                          processes
                          num_completed_processes_at_t_minus_one
        -- FCFSCompletionTime (take (n+1)) ≥ next_process.arrival + burst
        have h_foldl_inst := h_foldl h_exists_unarrived_processes
        -- h_foldl_inst : FCFSCompletionTime (take (n+1) ps) = max (...) next_process.arrival + next_process.burst
        -- h_arrival_late : next_process.arrival > t_minus_one + 1
        -- max (...) next_process.arrival ≥ next_process.arrival > t_minus_one + 1
        -- so FCFSCompletionTime (take (n+1) ps) ≥ next_process.arrival + burst > t_minus_one + 1
        have h_max : max (FCFSCompletionTime (List.take num_completed_processes_at_t_minus_one processes))
                        processes[num_completed_processes_at_t_minus_one].arrival
                     ≥ processes[num_completed_processes_at_t_minus_one].arrival := by
          exact Nat.le_max_right _ _
        linarith [Process.burst_exceed_zero next_process]

      | List.cons heads tails =>
        -- ready: same proof as above
        -- running
        -- completed same proof as above
        -- unarrived same proof as above
        sorry
    | some p =>
      by_cases h_finishes : p.remaining ≤ 1
      · -- p uses this tick: num_processes_completed becomes k + 1
        use num_completed_processes_at_t_minus_one + 1
        sorry
      · -- p continues running: num_processes_completed stays k
        use num_completed_processes_at_t_minus_one
        sorry
        -- have process_status_choices := non_preemptive_processes_are_ready_running_completed_or_unarrived selectFCFS arrival_stream next_process h_next_arrives (t_minus_one + 1)
        -- have h_ready_empty : prev.ready = [] := by
        --   exact idle_implies_empty_ready arrival_stream t_minus_one h_running_state
        -- rcases process_status_choices with h_ready | h_running | h_completed | h_unarrived
        -- -- ⊢ t_minus_one + 1 < FCFSCompletionTime (List.take (num_completed_processes_at_t_minus_one + 1) processes)
        -- · -- next_process in ready - next_process is the immediate next process which arrived, not the arbitrarily future process.
        --   -- All previous processes are in the completed list, so the process to be run must be next_process so it cant still be in ready
        --   have h_next_ready : (runSteps arrival_stream (stepNonPreemptive selectFCFS) (t_minus_one + 1)).ready = [] := by
        --     simp only [runSteps, stepNonPreemptive]
        --     unfold stepFCFS at h_prev_def
        --     rw [← h_prev_def]
        --     simp only [h_running_state, h_ready_empty, arrival_list_during_t]
        --     simp [selectFCFS]
        --   rw [h_next_ready] at h_ready
        --   tauto

        -- · -- next process in running
        --   -- contradicts no new arrivals
        --   have h_next_state : (runSteps arrival_stream (stepNonPreemptive selectFCFS) (t_minus_one + 1)).running = none := by
        --     simp only [runSteps, stepNonPreemptive]
        --     unfold stepFCFS at h_prev_def
        --     rw [← h_prev_def]
        --     simp only [h_running_state, h_ready_empty, arrival_list_during_t]
        --     simp [selectFCFS]

        --   simp [h_next_state] at h_running
        -- · -- next_process in completed

        -- · -- next_process unarrived - need to unfold FCFSCompletionTime - it takes into account the arrival time. If this has not arrived yet it means the arrival time must be more than 1
        --   unfold FCFSCompletionTime

theorem FCFSStarvationFree
  (arrival_stream : Nat → List AperiodicProcess)
  (h_arrival_unique : ∀ p1 p2 t1 t2, p1 ∈ arrival_stream t1 → p2 ∈ arrival_stream t2 → p1 = p2 → t1 = t2):
  ∀ arrival_time process, process ∈ arrival_stream arrival_time →
  ∃ completion_time, ∃ finished_process ∈ (runSteps arrival_stream stepFCFS completion_time).completed,
    Process.id finished_process = Process.id process -- cannot directly compare a process via == since the `remaining` field changes
  := by
    -- Proof idea: describe the time by which the process must have completed, characterized by FCFSCompletionTime

    intro arrival_time process hyp_process_is_member_of_arrival_stream_at_arrival_time
    -- completion time number is the sum of run duration of that process + all preceding processes
    -- note that even at t = 0 there may be multiple processes arriving
    let processes_arrived_up_to_target_process :=
      -- processes in previous ticks
      ((List.range arrival_time).flatMap arrival_stream)
      ++
      -- processes in same tick's list, strictly before target process
      (arrival_stream arrival_time).takeWhile (· != process)
      ++
      -- target process itself
      [process]
    have processes_list_is_generated_from_arrival_stream :
      ∀ (p : AperiodicProcess),
      p ∈ processes_arrived_up_to_target_process
      → ∃ arrival_time, p ∈ arrival_stream arrival_time
      := by
        intro p hp
        unfold processes_arrived_up_to_target_process at hp
        simp only [List.mem_append] at hp
        rcases hp with (hp | hp) | hp
        · simp only [List.mem_flatMap] at hp
          obtain ⟨t, _, hp_arrived⟩ := hp
          exact ⟨t, hp_arrived⟩
        · have h_sub : p ∈ arrival_stream arrival_time := by
            have := List.takeWhile_sublist (· != process) (l := arrival_stream arrival_time)
            exact this.mem hp
          exact ⟨arrival_time, h_sub⟩
        · simp only [List.mem_singleton] at hp
          rw [hp]
          exact ⟨arrival_time, hyp_process_is_member_of_arrival_stream_at_arrival_time⟩

    let time_taken := FCFSCompletionTime processes_arrived_up_to_target_process
    use time_taken
    have h_target_process_in_processes : process ∈ processes_arrived_up_to_target_process := by
      unfold processes_arrived_up_to_target_process
      simp

    have match_prefix_theorem :=
      FCFS_completed_matches_prefix
        arrival_stream
        h_arrival_unique
        processes_arrived_up_to_target_process
        processes_list_is_generated_from_arrival_stream
        time_taken

    obtain ⟨num_processes_completed, match_prefix_theorem⟩ := match_prefix_theorem
    obtain ⟨h_process_in_completed_queue, h_completion_time_no_less_than_time_taken, h_next_process_yet_to_run, h_num_processes_completed_le_processes_arrived_up_to_target_process⟩ := match_prefix_theorem
    -- h_process_in_completed_queue has the answer, just need to prove
    -- process ∈ List.take num_processes_completed processes_arrived_up_to_target_process
    -- Note already proved h_target_process_in_processes : process ∈ processes_arrived_up_to_target_process
    -- prove processes_arrived_up_to_target_process = List.take num_processes_completed processes_arrived_up_to_target_process
    -- need to squeeze with h_completion_time_no_less_than_time_taken, h_next_process_yet_to_run

    -- idea:
    -- show contradiction with postcondition of h_next_process_yet_to_run, thereby prove num_processes_completed ≥ processes_arrived_up_to_target_process.length
    -- time_taken < FCFSCompletionTime (take (n+1) processes_arrived_up_to_target_process) ≤ FCFSCompletionTime processes_arrived_up_to_target_process = time_taken
    -- num_processes_completed ≥ processes_arrived_up_to_target_process
    -- take will cap at length so num_processes_completed = processes_arrived_up_to_target_process

    -- num_processes_completed must be the full list length
    have h_all_completed : num_processes_completed = processes_arrived_up_to_target_process.length := by
      rcases Nat.lt_or_ge num_processes_completed processes_arrived_up_to_target_process.length with h_lt | h_ge
      · have h_time_lt := h_next_process_yet_to_run h_lt
        have h_mono := FCFSCompletionTime_take_le_FCFSCompletionTime_whole
                        processes_arrived_up_to_target_process
                        (num_processes_completed + 1)
        -- h_time_lt  : time_taken < FCFSCompletionTime (take (n+1) ps)
        -- h_mono     : FCFSCompletionTime (take (n+1) ps) ≤ FCFSCompletionTime ps
        -- time_taken = FCFSCompletionTime ps by definition
        linarith
      · omega  -- n ≤ length from the match_prefix_theorem

    -- now the take is the full list
    have h_take_full : List.take num_processes_completed processes_arrived_up_to_target_process
                      = processes_arrived_up_to_target_process := by
      rw [h_all_completed]
      simp

    -- process is a member of the take
    have h_process_in_take : process ∈ List.take num_processes_completed processes_arrived_up_to_target_process := by
      rw [h_take_full]
      exact h_target_process_in_processes

    -- now apply h_process_in_completed_queue
    exact h_process_in_completed_queue process h_process_in_take


-- Proof that Starvation occurs in Shortest Job First, Shortest Remaining Time First schedulers

-- Proof that in the First Come First Serve, Round Robin scheduler every process will run
