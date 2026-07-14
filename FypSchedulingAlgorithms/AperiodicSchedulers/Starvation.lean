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

theorem stepFCFS_completes_head_of_queue(s : SchedState) (p : AperiodicProcess):
  -- if p is at the front of the FCFS ordering and has been running for p.burst ticks, it ends up in .completed
  ∃ rest_of_list, s.ready == p :: rest_of_list →
  ∀ arrival_stream : (Nat → List AperiodicProcess),
  p ∈ (runSteps arrival_stream stepFCFS p.burst).completed
  := by
    use []
    intro p_is_start_of_ready_list
    intro arrival_stream
    unfold runSteps
    unfold stepFCFS
    unfold selectFCFS
  --   ⊢ p ∈
  -- (match p.burst with
  --   | 0 =>
  --     have __src := SchedStateMethods.init;
  --     { time := __src.time, ready := arrival_stream 0, running := __src.running, completed := __src.completed }
  --   | n.succ =>
  --     have prev :=
  --       runSteps arrival_stream
  --         (stepNonPreemptive fun x ↦
  --           match x with
  --           | [] => none
  --           | p :: tail => some p)
  --         n;
  --     stepNonPreemptive
  --       (fun x ↦
  --         match x with
  --         | [] => none
  --         | p :: tail => some p)
  --       { time := prev.time, ready := prev.ready ++ arrival_stream (n + 1), running := prev.running,
  --         completed := prev.completed }).completed



theorem FCFSStarvationFree
  (arrival_stream : Nat → List AperiodicProcess):
  ∀ arrival_time process, process ∈ arrival_stream arrival_time →
  ∃ completion_time, process ∈ (runSteps arrival_stream stepFCFS completion_time).completed
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



-- def runSteps {process_type} [SchedStateMethods process_type] (arrivalStream : ℕ → List process_type)
--     (scheduler : SchedStateG process_type → SchedStateG process_type) : ℕ → SchedStateG process_type
--   | 0     => {SchedStateMethods.init with ready := arrivalStream 0 }
--   | n + 1 =>
--     let prev := runSteps arrivalStream scheduler n
--     scheduler { prev with ready := prev.ready ++ arrivalStream (n + 1) }

    -- cases arrival_time with
    --   | zero =>
    --     use process.burst
    --     apply And.intro
    --     -- case h.left: process.burst ≥ 0, note that process.burst ∈ Nat
    --     omega
    --     -- case h.right: process ∈ (runSteps arrival_stream stepFCFS process.burst).completed

    --   | succ n =>

-- Proof that Starvation occurs in Shortest Job First, Shortest Remaining Time First schedulers

-- Proof that in the First Come First Serve, Round Robin scheduler every process will run
