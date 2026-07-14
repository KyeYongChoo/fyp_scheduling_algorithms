/-
Copyright (c) 2026 Choo Kye Yong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Choo Kye Yong
-/
import FypSchedulingAlgorithms.Process
import FypSchedulingAlgorithms.SchedState
import Mathlib.Data.Rat.Init
import Mathlib.Algebra.Order.Ring.Rat -- <, ≤, LT, LE instances for ℚ

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

def default_num_steps := 30

def selectByPriority {process_type} (priority_func : process_type → ℚ) (candidates : List process_type) : Option process_type :=
  candidates.foldl (fun best p =>
    match best with
    | none   => some p
    | some b => if priority_func p < priority_func b then some b else some p)
    none

-- Non-preemptive schedulers
def stepNonPreemptive [Process AperiodicProcess] (select : List AperiodicProcess → Option AperiodicProcess) :
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
      let p := Process.tick p
      if Process.remaining p ≤ 0 then
        -- immediately look for next process - no context switch time
        match select s.ready with          -- ask the policy for a choice
        | none   => { s with
                      time      := s.time + 1
                      running   := none
                      completed := s.completed ++ [p]
                    }
        | some q => { s with
                      time := s.time + 1
                      running := some q
                      ready   := s.ready.removeFirst q
                      completed := s.completed ++ [p]
                    }
      else
        { s with time    := s.time + 1,
                 running := some p }

-- preemptive schedulers:
-- Higher priority number means execute first
def stepPreemptive (process_type : Type) [Process process_type]
  (priority_func : process_type → ℚ) :
  SchedStateG process_type → SchedStateG process_type :=
  fun state_before =>
    let candidates := state_before.ready ++ (state_before.running.toList)
    let next_run := selectByPriority priority_func candidates
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
        let p := Process.tick p
        if Process.remaining p ≤ 0 then
          -- immediately look for next process - no context switch time
          let nextUp := selectByPriority priority_func newReady
          match nextUp with
          | none =>
            { state_before with
                time      := state_before.time + 1
                ready     := newReady
                running   := none
                completed := state_before.completed ++ [p] }
          | some q =>
            { state_before with
                time      := state_before.time + 1
                ready     := newReady.removeFirst q
                running   := some q
                completed := state_before.completed ++ [p] }
        else
          {
            state_before with
              time := state_before.time + 1
              ready := newReady
              running := some (p)
          }

def runSteps {process_type} [SchedStateMethods process_type] (arrivalStream : ℕ → List process_type)
    (scheduler : SchedStateG process_type → SchedStateG process_type) : ℕ → SchedStateG process_type
  | 0     => {SchedStateMethods.init with ready := arrivalStream 0 }
  | n + 1 =>
    let prev := runSteps arrivalStream scheduler n
    scheduler { prev with ready := prev.ready ++ arrivalStream (n + 1) }

def runStepsAccumulateResults {process_type} [SchedStateMethods process_type] [Process process_type]
    (arrivalStream : ℕ → List process_type)
    (scheduler : SchedStateG process_type → SchedStateG process_type)
    (n : Nat := default_num_steps):
    List (SchedStateG process_type) :=
  (List.range (n + 1)).map (runSteps arrivalStream scheduler)
