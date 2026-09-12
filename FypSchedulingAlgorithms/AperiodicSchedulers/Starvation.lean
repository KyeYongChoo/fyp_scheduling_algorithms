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
import Mathlib.Tactic

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

-- Links FCFSCompletionTime to FCFS completed queue
theorem FCFS_completed_matches_prefix
  -- states that for any time, processes at the front will have completed and
  -- the next process will not have begun
  (arrival_stream : Nat → List AperiodicProcess)
  (h_arrival_unique : ∀ p1 p2 t1 t2, p1 ∈ arrival_stream t1 → p2 ∈ arrival_stream t2 → p1 = p2 → t1 = t2)
  (processes : List AperiodicProcess)
  -- following 2 establish a bijection between arrival stream and processes
  (h_processes_from_stream : ∀ p ∈ processes, ∃ arrival_time, p ∈ arrival_stream arrival_time)
  (h_stream_in_processes : ∀ p t, p ∈ arrival_stream t → p ∈ processes)

  /- <+: is List.IsPrefix. This says processes and the
  time-ordered flatMap are prefix-comparable at every t
  - ie "processes is an initial segment of the arrival stream
  in time order", without pinning down where it stops.
  -/
  (h_processes_prefix : ∀ t : ℕ,
    (List.range t).flatMap arrival_stream <+: processes
    ∨ processes <+: (List.range t).flatMap arrival_stream)

  -- same id implies same object --> sidesteps the problem of this being untrue during execution (remaining decrements)
  -- by only specifying it in terms of arrival queue's processes
  (h_distinct_ids : ∀ (i j : Fin processes.length),
  processes[i].id = processes[j].id → i = j)
  (h_arrival_consistent : ∀ (p : AperiodicProcess) (t : ℕ), p ∈ arrival_stream t → p.arrival = t)
  (time : ℕ) :

  ∃ num_processes_completed,

  -- Invariant contains 6 conjuncts, 1, 2, 4, 5 were the ones used in the main Starvation free proof
  -- though 3 6 were added later when i realised its kinda important
  -- conjunct 5 is the one that varies the most between branches, and the key part used for the final Starvation proof

  -- conjunct 1: some processes will have completed
  (∀ process_arrival_stream ∈ processes.take num_processes_completed,
    ∃ process_completed ∈ (runSteps arrival_stream stepFCFS time).completed,
    Process.id process_completed = Process.id process_arrival_stream)  ∧

  -- conjunct 2: cant complete more processes than total processes
    num_processes_completed ≤ processes.length ∧

  -- conjunct 3: everything in completed matches something in take n processes
    (∀ process_completed ∈ (runSteps arrival_stream stepFCFS time).completed,
      ∃ process_arrival_stream ∈ processes.take num_processes_completed,
      Process.id process_arrival_stream = Process.id process_completed) ∧

  -- conjunct 4: time taken bounded below by FCFSCompletionTime
    FCFSCompletionTime (processes.take num_processes_completed) ≤ time ∧

  -- conjunct 5: time taken bounded above by FCFSCompletionTime
    (num_processes_completed < processes.length →
      time < FCFSCompletionTime (processes.take (num_processes_completed + 1))) ∧

  -- conjunct 6: any running process must be processes[num_processes_completed]
  -- and Recurrence relation for FCFSCompletionTime
  (∀ p, (runSteps arrival_stream stepFCFS time).running = some p →
    ∃ (h : num_processes_completed < processes.length),
    Process.id p = Process.id processes[num_processes_completed] ∧
    max (FCFSCompletionTime (processes.take num_processes_completed))
        (processes[num_processes_completed]'h).arrival ≤ time)

      := by
  induction time with
  | zero =>
    use 0
    simp only [List.take_zero]

    -- split the ∧ goals
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro p h; cases h
    · omega
    · intro p h_mem
      simp only [runSteps, stepFCFS, stepNonPreemptive] at h_mem
      have h_init_running : (SchedStateMethods.init : SchedStateG AperiodicProcess).running = none := rfl
      simp only [h_init_running] at h_mem
      split at h_mem
      · -- select = none, completed = init.completed = []
        simp [SchedStateMethods.init] at h_mem
      · -- select = some p, completed = init.completed = []
        simp [SchedStateMethods.init] at h_mem
    · unfold FCFSCompletionTime; rfl
    · intro h
      simp only [zero_add]
      rw [FCFSCompletionTime_last_element processes 0 h]
      simp only [List.take_zero, FCFSCompletionTime]
      have h_burst := Process.burst_exceed_zero processes[0]
      simp only [List.foldl]
      simp only [Nat.max_def]
      split
      · have h_0th_process_bounded_above_by_burst : 0 < processes[0].burst := by omega
        omega
      omega
    · intro p h_running
      -- p is running at time 0, so it was the first to arrive in the first arrival batch
      have h_head : ∃ tail, arrival_stream 0 = p :: tail
        := by
        simp only [runSteps, stepFCFS, stepNonPreemptive] at h_running
        have h_init_running : (SchedStateMethods.init : SchedStateG AperiodicProcess).running = none := rfl
        simp only [h_init_running] at h_running
        split at h_running
        · simp at h_running  -- select = none contradicts running = some p
        · rename_i q h_select
          -- selectFCFS picked q from arrival_stream 0, and running = some q = some p
          simp at h_running
          subst h_running
          -- q ∈ arrival_stream 0 since selectFCFS returns a member
          unfold selectFCFS at h_select
          grind
      have h_p_in_arrivals : p ∈ arrival_stream 0 := by
        grind
      have h_p_in_processes : p ∈ processes := h_stream_in_processes p 0 h_p_in_arrivals
      have h_len : 0 < processes.length := List.length_pos_of_mem h_p_in_processes
      have p_is_processes_zero : p = processes[0] := by
        obtain ⟨tail, h_head⟩ := h_head
        have h_pref := h_processes_prefix 1
        rw [List.range_succ] at h_pref          -- range 1 = range 0 ++ [0]
        simp only [List.range_zero, List.nil_append,
                  List.flatMap_cons, List.flatMap_nil,
                  List.append_nil, h_head] at h_pref
        -- h_pref : p :: tail <+: processes ∨ processes <+: p :: tail
        have h_zero : processes[0]? = some p := by
          rcases h_pref with ⟨rest, h_eq⟩ | ⟨rest, h_eq⟩
          · -- processes = (p :: tail) ++ rest
            rw [← h_eq]; rfl
          · -- p :: tail = processes ++ rest; processes ≠ [] so it starts with p

            cases hp : processes with
            | nil => rw [hp] at h_len; simp at h_len
            | cons a as =>
              rw [hp] at h_eq
              simp only [List.cons_append, List.cons.injEq] at h_eq
              grind
        grind
      refine ⟨h_len, ?_, ?_⟩
      ·  -- p.id = processes[0].id
        grind
      · simp [FCFSCompletionTime]
        grind

        -- max 0 processes[0].arrival ≤ 0 requires processes[0].arrival = 0



  | succ t_minus_one ih =>
    obtain
      ⟨num_completed_processes_at_t_minus_one,
        h_completed_eq,
        h_num_processes_completed_le_processes_length,
        h_reverse,
        h_lower,
        h_upper,
        h_running_p_implications
        ⟩ := ih
    set prev := runSteps arrival_stream stepFCFS t_minus_one with h_prev_def
    match h_running_state : prev.running with
    | none =>
      -- nobody was running

      -- ready queue must be empty
      have h_ready_empty : prev.ready = [] :=
            idle_implies_empty_ready arrival_stream t_minus_one h_running_state

      -- the completed queue did not expand due to running state none
      have h_completed_unchanged : (runSteps arrival_stream stepFCFS (t_minus_one + 1)).completed = prev.completed := by
        simp only [runSteps, stepFCFS, stepNonPreemptive]
        rw [h_prev_def, stepFCFS] at h_running_state
        simp only [h_running_state]
        rw [h_prev_def, stepFCFS]
        split
        · simp
        · simp

      use num_completed_processes_at_t_minus_one

      -- shared proof for both empty and nonempty arrival list cases
      have h_prove_shared_conjuncts : ∀ h_next_process_completion_constraint : ∃ arrival_time, arrival_time > t_minus_one + 1 ∧
            next_process ∈ arrival_stream arrival_time →
        (num_completed_processes_at_t_minus_one < processes.length →
          t_minus_one + 1 < FCFSCompletionTime (processes.take (num_completed_processes_at_t_minus_one + 1))) ∧
        (∀ p, (runSteps arrival_stream stepFCFS (t_minus_one + 1)).running = some p →
          ∃ (h : num_completed_processes_at_t_minus_one < processes.length),
          Process.id p = Process.id processes[num_completed_processes_at_t_minus_one] ∧
          max (FCFSCompletionTime (processes.take num_completed_processes_at_t_minus_one))
              (processes[num_completed_processes_at_t_minus_one]'h).arrival ≤ t_minus_one + 1)
        := fun ⟨arrival_time, h_arrival_gt, h_arrival_mem⟩ ↦ by
        refine ⟨fun h_exists_unarrived => ?_, fun p h_p_running_contradiction => ?_⟩
        · have h_arrival_late : next_process.arrival > t_minus_one + 1 := by
            have h_arrival_eq := h_arrival_consistent next_process arrival_time h_arrival_mem
            omega
          have h_foldl_inst := FCFSCompletionTime_last_element processes
                                num_completed_processes_at_t_minus_one h_exists_unarrived
          have h_max : max (FCFSCompletionTime (List.take num_completed_processes_at_t_minus_one processes))
                          processes[num_completed_processes_at_t_minus_one].arrival
                      ≥ processes[num_completed_processes_at_t_minus_one].arrival :=
            Nat.le_max_right _ _
          linarith [Process.burst_exceed_zero next_process]
        · have h_not_running : (runSteps arrival_stream stepFCFS (t_minus_one + 1)).running = none := by
            simp only [runSteps, stepFCFS, stepNonPreemptive, h_running_state]
            split <;> rfl
          grind

      -- check if someone arrives
      match arrival_list_during_t : arrival_stream (t_minus_one + 1) with
      | List.nil =>
        -- noone arrived
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩

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

        · omega

        · rwa [h_completed_unchanged]

        · omega

        · intro h_exists_unarrived_processes
          have h_prev_bound := h_upper h_exists_unarrived_processes
          set next_process := processes[num_completed_processes_at_t_minus_one]
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
            by_contra h_le
            push Not at h_le
            have h_not_current : arrival_time = t_minus_one + 1 := by omega
            simp only [h_not_current] at h_arrival
            rcases h_status with h_ready | h_running | h_completed | ⟨t, h_t_gt, h_t_mem⟩
            · simp only [stepFCFS] at h_prev_def
              rw [← h_prev_def] at h_ready
              simp [h_ready_empty] at h_ready
            · simp only [stepFCFS] at h_prev_def
              rw [← h_prev_def] at h_running
              simp [h_running_state] at h_running
            · obtain ⟨np_completed, h_np_completed_in_completed_queue, h_np_completed_has_same_id_as_next_process⟩ := h_completed
              obtain ⟨np_in_processes, h_np_in_take, h_np_id⟩ := h_reverse np_completed h_np_completed_in_completed_queue
              have h_id_eq : np_in_processes.id = next_process.id := by rw [h_np_id]; omega
              have h_next_not_in_take : next_process ∉ processes.take num_completed_processes_at_t_minus_one := by
                intro h_in_take
                rw [List.mem_iff_getElem] at h_in_take
                obtain ⟨i, h_i_lt_n, h_i_eq⟩ := h_in_take
                have h_i_lt_len : i < processes.length := omega
                have h_getElem_eq : processes[i]'h_i_lt_len = next_process := by
                  rw [← List.getElem_take (h := h_i_lt_n)]; exact h_i_eq
                have h_fin_eq := h_distinct_ids ⟨i, h_i_lt_len⟩ ⟨num_completed_processes_at_t_minus_one, h_exists_unarrived_processes⟩
                  (by simp [h_getElem_eq])
                simp [Fin.ext_iff] at h_fin_eq; omega
              rw [List.mem_iff_getElem] at h_np_in_take
              obtain ⟨i, h_i_lt_n, h_i_eq⟩ := h_np_in_take
              have h_i_lt_len : i < processes.length := omega
              have h_getElem_eq : processes[i]'h_i_lt_len = np_in_processes := by
                rw [← List.getElem_take (h := h_i_lt_n)]; exact h_i_eq
              have h_fin_eq := h_distinct_ids ⟨i, h_i_lt_len⟩ ⟨num_completed_processes_at_t_minus_one, h_exists_unarrived_processes⟩
                (by simp [h_getElem_eq, h_id_eq])
              simp [Fin.ext_iff] at h_fin_eq
              have h_eq : np_in_processes = next_process := by simp [← h_getElem_eq, h_fin_eq]
              rw [h_eq] at h_np_in_take
              exact absurd h_np_in_take h_next_not_in_take
            · have h_arrival_eq : t = arrival_time :=
                h_arrival_unique next_process next_process t arrival_time h_t_mem h_arrival rfl
              omega

          exact (h_prove_shared_conjuncts h_unarrived).1 h_exists_unarrived_processes

        · intro p h_p_running
          exact (h_prove_shared_conjuncts ⟨_, by omega, sorry⟩).2 p h_p_running

      | List.cons arrival_head arrival_tails =>
        -- someone arrived
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩

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

        · omega

        · rwa [h_completed_unchanged]

        · omega

        · intro h_exists_unarrived_processes
          have h_prev_bound := h_upper h_exists_unarrived_processes
          set next_process := processes[num_completed_processes_at_t_minus_one]
          have h_next_arrives :
            ∃ arrival_time, next_process ∈ arrival_stream arrival_time :=
            h_processes_from_stream next_process
            (List.getElem_mem h_exists_unarrived_processes)

          have h_unarrived_or_arrives_now : next_process.arrival ≥ t_minus_one + 1 := by
            have h_status := non_preemptive_processes_are_ready_running_completed_or_unarrived
                    selectFCFS arrival_stream next_process h_next_arrives t_minus_one
            have h_ready_empty : prev.ready = [] :=
              idle_implies_empty_ready arrival_stream t_minus_one h_running_state
            rcases h_status with h_ready | h_running | h_completed | ⟨t, h_t_gt, h_t_mem⟩
            · rw [← stepFCFS, ← h_prev_def] at h_ready
              simp [h_ready_empty] at h_ready
            · rw [← stepFCFS, ← h_prev_def] at h_running
              simp [h_running_state] at h_running
            · obtain ⟨np_completed, h_np_completed_in_completed_queue, h_np_completed_has_same_id_as_next_process⟩ := h_completed
              obtain ⟨np_in_processes, h_np_in_take, h_np_id⟩ := h_reverse np_completed h_np_completed_in_completed_queue
              have h_id_eq : np_in_processes.id = next_process.id := by rw [h_np_id]; omega
              have h_next_not_in_take : next_process ∉ processes.take num_completed_processes_at_t_minus_one := by
                intro h_in_take
                rw [List.mem_iff_getElem] at h_in_take
                obtain ⟨i, h_i_lt_n, h_i_eq⟩ := h_in_take
                have h_i_lt_len : i < processes.length := omega
                have h_getElem_eq : processes[i]'h_i_lt_len = next_process := by
                  rw [← List.getElem_take (h := h_i_lt_n)]; exact h_i_eq
                have h_fin_eq := h_distinct_ids ⟨i, h_i_lt_len⟩ ⟨num_completed_processes_at_t_minus_one, h_exists_unarrived_processes⟩
                  (by simp [h_getElem_eq])
                simp [Fin.ext_iff] at h_fin_eq; omega
              rw [List.mem_iff_getElem] at h_np_in_take
              obtain ⟨i, h_i_lt_n, h_i_eq⟩ := h_np_in_take
              have h_i_lt_len : i < processes.length := omega
              have h_getElem_eq : processes[i]'h_i_lt_len = np_in_processes := by
                rw [← List.getElem_take (h := h_i_lt_n)]; exact h_i_eq
              have h_fin_eq := h_distinct_ids ⟨i, h_i_lt_len⟩ ⟨num_completed_processes_at_t_minus_one, h_exists_unarrived_processes⟩
                (by simp [h_getElem_eq, h_id_eq])
              simp [Fin.ext_iff] at h_fin_eq
              have h_eq : np_in_processes = next_process := by simp [← h_getElem_eq, h_fin_eq]
              rw [h_eq] at h_np_in_take
              exact absurd h_np_in_take h_next_not_in_take
            · have h_arr := h_arrival_consistent next_process t h_t_mem
              omega

          have h_foldl_inst := FCFSCompletionTime_last_element processes
                                num_completed_processes_at_t_minus_one h_exists_unarrived_processes
          have h_max := Nat.le_max_right
                          (FCFSCompletionTime (processes.take num_completed_processes_at_t_minus_one))
                          processes[num_completed_processes_at_t_minus_one].arrival
          have h_goal : t_minus_one + 1 < next_process.arrival + next_process.burst := by
            change t_minus_one + 1 < next_process.arrival + Process.burst next_process
            have h_burst := Process.burst_exceed_zero next_process
            omega
          linarith [h_goal, h_max, h_foldl_inst]

        · intro p h_p_running
          sorry



    | some p =>
      by_cases h_finishes : Process.remaining p ≤ 1
      · -- p uses this tick: num_processes_completed becomes k + 1
        use num_completed_processes_at_t_minus_one + 1
        -- When p finishes, we need to show all 5 conjuncts hold for the incremented count
        -- This follows similar logic to the "none" case but with p completing instead of a new arrival
        sorry
      · -- p continues running: num_processes_completed stays k
        use num_completed_processes_at_t_minus_one

        -- used when unfolding step execution, will not complete next_process
        have process_after_tick_gt_zero : Not (Process.remaining (Process.tick p) = 0)
          := by
            have := Process.tick_decrements p
            omega

        -- the completed queue did not expand due to not completing next_process
        have h_completed_unchanged : (runSteps arrival_stream stepFCFS (t_minus_one + 1)).completed = prev.completed := by
          simp only [runSteps, stepFCFS, stepNonPreemptive]
          rw [h_prev_def, stepFCFS] at h_running_state
          simp only [h_running_state]
          rw [h_prev_def, stepFCFS]
          simp [process_after_tick_gt_zero]


        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩

        · have h_next : (runSteps arrival_stream stepFCFS (t_minus_one + 1)).completed = prev.completed := by
            change (stepFCFS { prev with ready := prev.ready ++ arrival_stream (t_minus_one + 1) }).completed = prev.completed
            simp only [stepFCFS, h_running_state]
            unfold stepNonPreemptive
            simp [process_after_tick_gt_zero]
          rw [h_next]
          omega

        -- num_completed_processes_at_t_minus_one ≤ processes.length
        · omega

        · rwa [h_completed_unchanged]

        -- time just increased without new processes added, use h lower
        · omega

        · have t_minus_one + 1 <  FCFSCompletionTime (List.take num_completed_processes_at_t_minus_one processes) ≤ t_minus_one

          intro h_exists_unarrived_processes
          have h_prev_bound := h_upper h_exists_unarrived_processes
          -- In case 2 (p continues), the bound from IH says t_minus_one < FCFSCompletionTime (take (n+1))
          -- Since p hasn't finished, process n+1 can't have started running yet
          -- So process n+1's completion time is still strictly bounded below by t_minus_one + 1
          sorry





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
