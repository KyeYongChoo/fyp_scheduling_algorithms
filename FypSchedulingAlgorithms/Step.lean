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

## Tick convention

Every step function (`stepNonPreemptive`, `stepPreemptive`, and `stepRR` in
`AperiodicStep`) follows the same convention, one tick of CPU time per step:

1. tick the job that was running at the start of the step, if any;
2. if that finished it, move it to `completed`;
3. decide who runs next (keep it, preempt it, or dispatch into an idle CPU).

A job newly put on the CPU in a step -- dispatched from idle, after a completion,
or by preemption -- is **not** ticked in that step; its first tick is in the next
step.  So the state after a step shows who holds the CPU *going into* the next tick.

This file also defines the runSteps function which simulates a time step and
Arrival stream to simulate arrivals, since i'm modelling infinite processes arriving
in total, though at any time step only a finite amount of processes arrive
-/

structure WellFormedStream (arrival_stream : ℕ → List AperiodicProcess) : Prop where
  consistent : ∀ (p : AperiodicProcess) (t : ℕ), p ∈ arrival_stream t → p.arrival = t
  fresh : ∀ (p : AperiodicProcess) (t : ℕ), p ∈ arrival_stream t → p.remaining = p.burst
  unique : ∀ (p1 p2 : AperiodicProcess) (t1 t2 : ℕ),
    p1 ∈ arrival_stream t1 → p2 ∈ arrival_stream t2 →
    Process.id p1 = Process.id p2 → t1 = t2 ∧ p1 = p2

def default_num_steps := 30

/-- The candidate with the *highest* `priority_func` value; among equal-priority
candidates the **earliest** in the list wins (FIFO ties): a later candidate replaces
the best so far only if its priority is strictly higher. -/
def selectByPriority {process_type} (priority_func : process_type → ℚ) (candidates : List process_type) : Option process_type :=
  candidates.foldl (fun best p =>
    match best with
    | none   => some p
    | some b => if priority_func b < priority_func p then some p else some b)
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
                           ready   := s.ready.erase p }
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
                      ready   := s.ready.erase q
                      completed := s.completed ++ [p]
                    }
      else
        { s with time    := s.time + 1,
                 running := some p }

/-- **Online non-preemptive scheduler.** Like `stepNonPreemptive`, but the policy
`select` sees the whole state at the start of the step -- time, ready queue, the
running job (which may be finishing this step) and the completed jobs, i.e.
everything known so far -- rather than just the ready queue.  It may also leave
the CPU idle on purpose, by returning `none` while jobs are waiting.  Jobs are
still never preempted, and the tick convention is the same.  Every
`stepNonPreemptive sel` is an instance (`stepNonPreemptive_eq_online`). -/
def stepNonPreemptiveOnline (select : SchedState → Option AperiodicProcess) :
  SchedState → SchedState :=
  fun s =>
    match s.running with
    | none =>
      match select s with
      | none   => { s with time := s.time + 1 }   -- idle tick
      | some p => { s with time    := s.time + 1,
                           running := some p,
                           ready   := s.ready.erase p }
    | some p =>
      let p := Process.tick p
      if Process.remaining p ≤ 0 then
        match select s with
        | none   => { s with
                      time      := s.time + 1
                      running   := none
                      completed := s.completed ++ [p]
                    }
        | some q => { s with
                      time := s.time + 1
                      running := some q
                      ready   := s.ready.erase q
                      completed := s.completed ++ [p]
                    }
      else
        { s with time    := s.time + 1,
                 running := some p }

/-- A policy that looks only at the ready queue is an online policy. -/
theorem stepNonPreemptive_eq_online (select : List AperiodicProcess → Option AperiodicProcess) :
    stepNonPreemptive select = stepNonPreemptiveOnline (fun s => select s.ready) := rfl

/-- **Preemptive scheduler** driven by a priority function: the candidate with the
*highest* `priority_func` value gets the CPU.  It follows the tick convention in the
module docstring:

1. the job running at the start of the step (if any) is ticked;
2. if that finished it, it moves to `completed` and the best job in `ready` (if any) is
   dispatched;
3. otherwise the best job in `ready` preempts it only if it has *strictly* higher
   priority than the ticked job, which then goes to the back of `ready`.

Step 3 is the same as choosing `selectByPriority priority_func (running :: ready)`
with ties going to the running job (it is scanned first, and ties go to the earliest
candidate), see `Preemptive.selectByPriority_cons`; spelling it as a comparison avoids
testing jobs for equality.  Among the jobs in `ready`, ties go to the one nearest the
front of the queue.  A job newly put on the CPU is not ticked until the next
step. -/
def stepPreemptive (process_type : Type) [Process process_type]
  (priority_func : process_type → ℚ) :
  SchedStateG process_type → SchedStateG process_type :=
  fun s =>
    match s.running with
    | none =>
      match selectByPriority priority_func s.ready with
      | none   => { s with time := s.time + 1 }   -- idle tick (ready is empty)
      | some p => { s with time    := s.time + 1,
                           running := some p,
                           ready   := s.ready.erase p }
    | some b =>
      let b := Process.tick b
      if Process.remaining b ≤ 0 then
        -- immediately look for next process - no context switch time
        match selectByPriority priority_func s.ready with
        | none   => { s with
                      time      := s.time + 1
                      running   := none
                      completed := s.completed ++ [b] }
        | some q => { s with
                      time      := s.time + 1
                      running   := some q
                      ready     := s.ready.erase q
                      completed := s.completed ++ [b] }
      else
        match selectByPriority priority_func s.ready with
        | none   => { s with time := s.time + 1, running := some b }
        | some q =>
          if priority_func b < priority_func q then
            -- preemption: `q` takes the CPU unticked, `b` rejoins the queue
            { s with
                time    := s.time + 1
                running := some q
                ready   := s.ready.erase q ++ [b] }
          else
            { s with time := s.time + 1, running := some b }

def runSteps {process_type} [SchedStateMethods process_type] (arrivalStream : ℕ → List process_type)
    (scheduler : SchedStateG process_type → SchedStateG process_type) : ℕ → SchedStateG process_type
  -- fold over the time stream
  | 0     => scheduler {SchedStateMethods.init with ready := arrivalStream 0 }
  | n + 1 =>
    let prev := runSteps arrivalStream scheduler n
    scheduler { prev with ready := prev.ready ++ arrivalStream (n + 1) }

def runStepsAccumulateResults {process_type} [SchedStateMethods process_type] [Process process_type]
    (arrivalStream : ℕ → List process_type)
    (scheduler : SchedStateG process_type → SchedStateG process_type)
    (n : Nat := default_num_steps):
    List (SchedStateG process_type) :=
  (List.range (n + 1)).map (runSteps arrivalStream scheduler)
