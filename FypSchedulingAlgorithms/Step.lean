/-
Copyright (c) 2026 Choo Kye Yong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Choo Kye Yong
-/
import FypSchedulingAlgorithms.Process
import FypSchedulingAlgorithms.SchedState
import Mathlib

/-!
# Scheduling Generic Functions

This file defines `stepNonPreemptive` and `stepPreemptive`,
which are used to define more specific scheduling algorithms and takes
an argument `select` or `priority_fun`.

`select` is used for `stepNonPreemptive` rather than `priority_fun`
because FCFS priority is not dependent on the processes but rather the
order in which it arrives.

The preemptive version of FCFS, which is Round Robin, differs enough from
other preemptive algorithms that it is built independently from
`stepNonPreemptive` and `stepPreemptive`
-/

-- Non-preemptive schedulers
def stepNonPreemptive (select : List AperiodicProcess → Option AperiodicProcess) :
  SchedState → SchedState :=
  fun s =>
    match s.running with
    | none =>
      match select s.ready with          -- ask the policy for a choice
      | none   => { s with time := s.time + 1 }   -- idle tick (ready is empty)
      | some p => { s with time    := s.time + 1,
                           running := some p,
                           ready   := s.ready.removeFirst p }
    | some p =>
      if p.remaining ≤ 1 then
        { s with time      := s.time + 1,
                 running   := none,
                 completed := s.completed ++ [{ p with remaining := 0 }] }
      else
        { s with time    := s.time + 1,
                 running := some { p with remaining := p.remaining - 1 } }

-- preemptive schedulers:
-- Higher periority number means execute first
def stepPreemptive (process_type : Type) [Process process_type]
  (priority_func : process_type → ℚ) :
  SchedStateG process_type → SchedStateG process_type :=
  fun state_before =>
    let candidates := state_before.ready ++ (state_before.running.toList)
    let next_run := candidates.foldl (fun best p =>
      match best with
       | none => some p
       | some b => if priority_func p < priority_func b then some b else some p)
       none
    match next_run with
      | none =>
        {state_before with time := state_before.time + 1}
      | some p =>
        let newReady :=
          match state_before.running with
            | none => state_before.ready.removeFirst p
            | some b =>
              if b == p then state_before.ready
              else
                state_before.ready.removeFirst p ++ [b]
        if Process.remaining p ≤ 1 then
          {
            state_before with
              time := state_before.time + 1
              ready := newReady
              running := none
              completed := state_before.completed ++ [Process.tick p]
          }
        else
          {
            state_before with
              time := state_before.time + 1
              ready := newReady
              running := some (Process.tick p)
          }

-- Run scheduler for n steps, adding arrivals dynamically
def runSteps {α} [SchedStateMethods α] (scheduler : SchedStateG α → SchedStateG α) (n : Nat)
             (processes : List α) : List (SchedStateG α) :=
  let state_type := SchedStateG α
  let rec loop (steps : Nat) (state : state_type) (states : List state_type) : List state_type :=
    if steps = 0 then states
    else
      let newState := SchedStateMethods.add_arrival state processes
      let nextState := scheduler newState
      loop (steps - 1) nextState (states ++ [nextState])
  loop n SchedStateMethods.init [SchedStateMethods.init]
