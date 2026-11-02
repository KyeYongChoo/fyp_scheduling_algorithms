/-
Copyright (c) 2026 Choo Kye Yong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Choo Kye Yong
-/
import FypSchedulingAlgorithms.Process
import FypSchedulingAlgorithms.SchedState
import FypSchedulingAlgorithms.Step

/-!
# Aperiodic scheduling algorithms

The step functions for the classic aperiodic schedulers, built on the shared machinery of
`FypSchedulingAlgorithms.Step` (see its tick convention):

* `stepFCFS` -- First Come First Served, non-preemptive (`stepNonPreemptive selectFCFS`);
* `stepSJF` -- Shortest Job First, non-preemptive (`stepNonPreemptive selectSJF`);
* `stepSRTF` -- Shortest Remaining Time First, preemptive (`stepPreemptive`, priority
  `-remaining`);
* `stepRR` -- Round Robin with a quantum.  It carries a slice counter, so it acts on an
  `RRState` and has its own run, `runStepsRR`.
-/

-- ─── SRTF (preemptive: on every tick, run the shortest remaining time) ─────────
/-- **Shortest Remaining Time First**, the preemptive form of SJF: `stepPreemptive`
with priority `-remaining`, so a job with the least work left gets the CPU.  A waiting
job preempts the running one (as it stands after this step's tick) only if it has
strictly less work left; ties keep the running job. -/
def stepSRTF : SchedState -> SchedState:=
  stepPreemptive AperiodicProcess (fun p => -(p.remaining : ℤ))

-- ─── Round Robin ─────────────────────────────────────────────────────────────
-- RR needs a quantum counter; hence the repeated code

/-- **Round Robin** with time quantum `quantum`.  It follows the tick convention of
`FypSchedulingAlgorithms.Step` (tick the running job; retire it if done; then decide
who runs next):

* idle CPU: the head of `ready` is dispatched, unticked, with `ticksUsed := 0`;
* the running job's last tick (`remaining ≤ 1`): it completes and the head of
  `ready` is dispatched, unticked;
* the tick that uses up the quantum: the ticked job goes to the back of `ready`
  and the head of `ready` is dispatched, unticked (if `ready` is empty the job
  keeps the CPU with a fresh quantum, `ticksUsed := 0`, so every slice is
  `quantum` ticks long);
* otherwise the running job is ticked and keeps the CPU.

`ticksUsed` counts the ticks of the current slice taken before this step. -/
def stepRR (quantum : Nat) : RRState → RRState :=
  fun rs =>
    let s := rs.sched
    match s.running with
    | none =>
      match s.ready with
      | []      => { rs with sched := { s with time := s.time + 1 } }
      | p :: ps =>
        { rs with
            sched     := { s with time := s.time + 1, running := some p, ready := ps }
            ticksUsed := 0 }
    | some p =>
      if p.remaining ≤ 1 then
        -- process finishes: immediately dispatch next, no idle gap
        let completedProcess := { p with remaining := 0 }
        match s.ready with
        | []      =>
          { rs with
              sched     := { s with
                              time      := s.time + 1
                              running   := none
                              completed := s.completed ++ [completedProcess] }
              ticksUsed := 0 }
        | nx :: ps =>
          { rs with
              sched     := { s with
                              time      := s.time + 1
                              running   := some nx
                              ready     := ps
                              completed := s.completed ++ [completedProcess] }
              ticksUsed := 0 }
      else if rs.ticksUsed ≥ quantum - 1 then
        match s.ready with
        | [] =>
          { rs with
              sched     := { s with
                              time    := s.time + 1
                              running := some { p with remaining := p.remaining - 1 } }
              ticksUsed := 0 }
        | nx :: ps =>
          { rs with
              sched     := { s with
                              time    := s.time + 1
                              running := some nx
                              ready   := ps ++ [{ p with remaining := p.remaining - 1 }] }
              ticksUsed := 0 }
      else
        { rs with
            sched     := { s with
                            time    := s.time + 1
                            running := some { p with remaining := p.remaining - 1 } }
            ticksUsed := rs.ticksUsed + 1 }

/-- The run of Round Robin, as `runSteps` but over `RRState`, so that the slice counter
`ticksUsed` is carried from step to step.  The quantum is an argument of the run, while
`ticksUsed` lives in the state.  `(runStepsRR quantum arrival_stream t).sched` is the state after
step `t`, numbered as in `runSteps`. -/
def runStepsRR [SchedStateMethods AperiodicProcess] (quantum : Nat)
               (arrivalStream : ℕ → List AperiodicProcess)
               (num_steps: ℕ): RRState :=
  match num_steps with
  | 0 =>
    stepRR quantum
      { sched := { SchedStateMethods.init with ready := arrivalStream 0 }
        , ticksUsed := 0 }
  | n + 1 =>
    let prev := runStepsRR quantum arrivalStream n
    stepRR quantum
      {prev with sched := {prev.sched with ready := prev.sched.ready ++ arrivalStream (n + 1)} }

def runStepsRRAccumulateResults [SchedStateMethods AperiodicProcess] (quantum : Nat)
  (num_steps := default_num_steps)
  (arrivalStream : ℕ → List AperiodicProcess): List (SchedState) :=
  ((List.range (num_steps + 1)).map (runStepsRR quantum arrivalStream)).map
    fun rr_state : RRState => rr_state.sched

/-- **FCFS** selection: the head of the ready queue.  The queue holds jobs in arrival
order, since a run appends each time's arrivals at the back (`runSteps`). -/
def selectFCFS : List AperiodicProcess → Option AperiodicProcess
  | [] => none
  | p :: _ => some p

/-- **First Come First Served**: non-preemptive, dispatches the head of the queue
whenever the CPU is free. -/
def stepFCFS : SchedState → SchedState :=
  stepNonPreemptive selectFCFS

/-- **SJF** selection: a job of least `burst` in the queue; among equal bursts the one
nearest the front wins (a later job replaces the best so far only if it is strictly
shorter).  It compares `burst`, not `remaining`; in a non-preemptive run the two agree
for every waiting job (`nonPreemptiveStateSelect_ready_fresh`). -/
def selectSJF : List AperiodicProcess → Option AperiodicProcess :=
  fun ps =>
    ps.foldl (fun best p =>
      match best with
      | none   => some p
      | some b => if p.burst < b.burst then some p else some b)
      none

/-- **Shortest Job First**, non-preemptive: whenever the CPU is free, dispatch a job of
least burst (`selectSJF`).  A dispatched job runs to completion, even if a shorter one
arrives meanwhile (`sjf_late_convoy_waiting`). -/
def stepSJF : SchedState → SchedState :=
  stepNonPreemptive selectSJF
