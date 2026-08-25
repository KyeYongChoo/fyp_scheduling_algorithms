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

theorem selectFCFS_serves_earliest_arrival
    (ready : List AperiodicProcess) (p q : AperiodicProcess)
    (h_p_in : p ∈ ready) (h_q_in : q ∈ ready) (h_order : <p arrived before q in ready's ordering>) :
    selectFCFS ready ≠ some q  -- or similar: FCFS won't pick q while p (earlier) is still waiting

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
    process = (runSteps arrival_stream (stepNonPreemptive select) current_time).running ∨
    -- completed
    process ∈ (runSteps arrival_stream (stepNonPreemptive select) current_time).completed ∨
    -- unarrived
    (∃ arrival_time, arrival_time > current_time ∧ process ∈ arrival_stream arrival_time)
  := by
    intro current_time
    induction current_time with
    | zero =>
      sorry
    | succ current_time_minus_one ih =>
      sorry



def FCFSCompletionTime (process_list : List AperiodicProcess): ℕ :=
  -- The following approach which is adding up all burst times, fail in case of
  -- 2 processes separated by arbitrarily big gap
  -- since the true completion time includes waiting for the second process
  -- to arrive
  -- process_list.foldl (fun running_total p => running_total + p.burst) 0
  process_list.foldl
    (fun completion_so_far p => max completion_so_far p.arrival + p.burst) 0

theorem FCFS_completed_matches_prefix
  (select : List AperiodicProcess → Option AperiodicProcess)
  (arrival_stream : Nat → List AperiodicProcess) (processes : List AperiodicProcess)
  -- process must be part of the stream
  (h_processes_from_stream : ∀ p ∈ processes, ∃ arrival_time, p ∈ arrival_stream arrival_time)
  (time : ℕ) :
  ∃ num_processes_completed, ∀ process_arrival_stream ∈ processes.take num_processes_completed,
    ∃ process_completed ∈ (runSteps arrival_stream stepFCFS time).completed,
    Process.id process_completed = Process.id process_arrival_stream ∧
    FCFSCompletionTime (processes.take num_processes_completed) ≤ time ∧
    (num_processes_completed < processes.length →
      time < FCFSCompletionTime (processes.take (num_processes_completed + 1))) := by
  induction time with
  | zero =>
    unfold runSteps
    simp only [Nat.le_zero_eq]
    use 0
    simp only [List.take_zero, zero_add]
    tauto
    -- apply And.intro
    -- · rfl
    -- apply And.intro
    -- · unfold FCFSCompletionTime
    --   rfl
    -- induction processes with
    -- | nil =>
    --   simp
    -- | cons head tails ih =>
    --   simp only [List.length_cons, Nat.zero_lt_succ, List.take_succ_cons, List.take_zero, forall_const]
    --   unfold FCFSCompletionTime
    --   simp
    --   have h_process_burst_exceed_zero : head.burst > 0 := Process.burst_exceed_zero head
    --   omega
  | succ t_minus_one ih =>
    obtain ⟨num_completed_processes_at_t_minus_one, h_completed_eq, h_lower, h_upper⟩ := ih
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
          rw [h_next, h_completed_eq]
        apply And.intro
        -- time just increased without new processes added, use h lower
        · omega
        -- unfold FCFSCompletionTime
        -- unfold FCFSCompletionTime at h_upper
        intro h_exists_unarrived_processes
        have h_prev_bound := h_upper h_exists_unarrived_processes
        let next_process := processes[num_completed_processes_at_t_minus_one]
        have h_next_arrives :
          ∃ arrival_time, next_process ∈ arrival_stream arrival_time :=
          h_processes_from_stream next_process
          (List.getElem_mem h_exists_unarrived_processes)
        have process_status_choices := non_preemptive_processes_are_ready_running_completed_or_unarrived selectFCFS arrival_stream next_process h_next_arrives (t_minus_one + 1)
        sorry
        -- rcases process_status_choices with h_ready | h_running | h_completed | h_unarrived
        -- · sorry -- argue by contradiction with ready nonempty and running empty -- if noone arrived this tick, anything in ready queue must have arrived earlier! If it had arrived earlier, then it should have been running now!

      | List.cons heads tails =>
        sorry
    | some p =>
      by_cases h_finishes : p.remaining ≤ 1
      · -- p uses this tick: num_processes_completed becomes k + 1
        use num_completed_processes_at_t_minus_one + 1
        sorry
      · -- p continues running: num_processes_completed stays k
        use num_completed_processes_at_t_minus_one
        sorry


theorem FCFSStarvationFree
  (arrival_stream : Nat → List AperiodicProcess):
  ∀ arrival_time process, process ∈ arrival_stream arrival_time →
  ∃ completion_time, ∃ finished_process ∈ (runSteps arrival_stream stepFCFS completion_time).completed,
    Process.id finished_process = Process.id process -- cannot directly compare a process via == since the `remaining` field changes
  := by
    intro arrival_time
    intro process
    intro hyp_process_is_member_of_arrival_stream_at_arrival_time
    -- completion time number is the sum of run duration of that process + all preceding processes
    -- note that even at t = 0 there may be multiple processes arriving
    let processes_arrived_up_to_target_process :=
      -- processes in previous ticks
      ((List.range arrival_time).flatMap arrival_stream)
      ++
      -- processes in same tick's list, strictly before target process
      (arrival_stream arrival_time).takeWhile (. != process)
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

    -- -- cries in spaghetti code
    -- have process_generated_from_arrival_stream :
    --   ∃ arrival_time, process ∈ arrival_stream arrival_time
    --   := by
    --     sorry

    -- have processes_either_ready_running_completed_unarrived := non_preemptive_processes_are_ready_running_completed_or_unarrived
    --       selectFCFS
    --       arrival_stream
    --       process
    --       process_generated_from_arrival_stream

    have match_prefix_theorem :=
      FCFS_completed_matches_prefix
        selectFCFS
        arrival_stream
        processes_arrived_up_to_target_process
        processes_list_is_generated_from_arrival_stream
        time_taken

    obtain ⟨num_processes_completed, match_prefix_theorem⟩ := match_prefix_theorem
    obtain ⟨h_process_in_completed_queue, h_completion_time_no_less_than_time_taken, _h_next_process_yet_to_run⟩ := match_prefix_theorem




-- theorem FCFS_completed_matches_prefix
--   (arrival_stream : Nat → List AperiodicProcess) (processes : List AperiodicProcess)
--   -- process must be part of the stream
--   (h_processes_from_stream : ∀ p ∈ processes, ∃ arrival_time, p ∈ arrival_stream arrival_time)
--   -- if the system is idle at time t, no arrived-but-unprocessed process exists, so anyone still to come must arrive after t
--   (h_idle : ∀t, (runSteps arrival_stream stepFCFS t).running = none → ∀p ∈ processes,
--     p ∈ (runSteps arrival_stream stepFCFS t).completed
--     ∨ (∀arrival_time, p ∈ (arrival_stream arrival_time) → arrival_time > t) )
--   (time : ℕ) :
--   ∃ num_processes_completed,
--     (runSteps arrival_stream stepFCFS time).completed = processes.take num_processes_completed ∧
--     FCFSCompletionTime (processes.take num_processes_completed) ≤ time ∧
--     (num_processes_completed < processes.length →
--       time < FCFSCompletionTime (processes.take (num_processes_completed + 1))) := by


    -- process ∈ (runSteps arrival_stream stepFCFS time_taken).completed
    -- unfold runSteps

-- Proof that Starvation occurs in Shortest Job First, Shortest Remaining Time First schedulers

-- Proof that in the First Come First Serve, Round Robin scheduler every process will run
