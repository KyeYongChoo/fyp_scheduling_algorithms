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

theorem stepNonPreemptive_completes_head_of_queue
    {select}
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
    {select} [Process AperiodicProcess]
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
    {select}
    (s : SchedState) (process : AperiodicProcess)
    (h_running : s.running = some process) (h_non_zero_remaining_time : process.remaining > 0) :
    ∃ completed_process: AperiodicProcess, completed_process.id = process.id ∧
    ((stepNonPreemptive select)^[process.remaining] s |>.completed.contains completed_process):= by
    -- induct over remaining time

    -- If remaining was 0 then (stepNonPreemptive select)^[process.remaining] s would be ill defined
    -- need to induct over remaining_minus_one rather than remaining
    -- need to convert the problem to be written over remaining_minus_one rather than remaining
    let remain_minus_one := process.remaining - 1
    have h_remain_minus_one : process.remaining = remain_minus_one + 1 := by omega
    rw [h_remain_minus_one]

    induction remain_minus_one with
    | zero =>
        simp
        have h_finishing : process.remaining ≤ 1 := by omega
        have ticked_process_in_completed_queue := stepNonPreemptive_completes_head_of_queue s process h_running h_finishing |> And.right

    | succ remain_minus_two ih =>


theorem stepNonPreemptive_is_non_preemptive
    (arrivalStream : ℕ → List AperiodicProcess) (t k : ℕ) :
    runSteps arrivalStream stepNonPreemptive (t + k) =
      (stepNonPreemptive select)^[k] (runSteps arrivalStream stepNonPreemptive t)
    -- likely needs a side condition, e.g. arrivals in the window don't
    -- change who's *running*, only append to `ready`
    := by
  induction k with
  | zero => rfl
  | succ n ih =>
    simp [runSteps, ih]
    -- key fact needed: appending arrivals to `ready` doesn't change `.running`
    sorry

theorem FCFSStarvationFree
  (arrival_stream : Nat → List AperiodicProcess):
  ∀ arrival_time process, process ∈ arrival_stream arrival_time →
  ∃ completion_time, ∃ finished_process ∈ (runSteps arrival_stream stepFCFS completion_time).completed,
    finished_process.id = process.id -- cannot directly compare a process via == since the `remaining` field changes
  := by
    intro arrival_time
    intro process
    intro hyp_process_is_member_of_arrival_stream_at_arrival_time
    -- completion time number is the sum of run duration of that process + all preceding processes
    -- note that even at t = 0 there may be multiple processes arriving
    let processes_executed_up_to_target_process :=
      -- processes in previous ticks
      ((List.range arrival_time).flatMap arrival_stream)
      ++
      -- processes in same tick's list, strictly before target process
      (arrival_stream arrival_time).takeWhile (. != process)
      ++
      -- target process itself
      [process]
    let time_taken := processes_executed_up_to_target_process.foldl (fun running_total p => running_total + p.burst) 0
    use time_taken

    -- process ∈ (runSteps arrival_stream stepFCFS time_taken).completed
    -- unfold runSteps

-- Proof that Starvation occurs in Shortest Job First, Shortest Remaining Time First schedulers

-- Proof that in the First Come First Serve, Round Robin scheduler every process will run
