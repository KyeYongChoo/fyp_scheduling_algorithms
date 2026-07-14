/-
Copyright (c) 2026 Choo Kye Yong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Choo Kye Yong
-/
import FypSchedulingAlgorithms.Process
import FypSchedulingAlgorithms.SchedState
import FypSchedulingAlgorithms.Step

-- ─── SRTF (preemptive: on every tick, pick shortest remaining time) ───────────
def stepSRTF : SchedState -> SchedState:=
  stepPreemptive AperiodicProcess (fun p => 1/(p.remaining))

-- ─── Round Robin ─────────────────────────────────────────────────────────────
-- RR needs a quantum counter; hence the repeated code

def stepRR (q : Nat) : RRState → RRState :=
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
      else if rs.ticksUsed ≥ q - 1 then
        match s.ready with
        | [] =>
          { rs with
              sched     := { s with
                              time    := s.time + 1
                              running := some { p with remaining := p.remaining - 1 } }
              ticksUsed := 1 }
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

def runStepsRR [SchedStateMethods AperiodicProcess] (quantum : Nat)
               (arrivalStream : ℕ → List AperiodicProcess)
               (num_steps: ℕ): RRState :=
  match num_steps with
  | 0     =>
    {sched := SchedStateMethods.init, quantum := quantum, ticksUsed := 0 }
  | n + 1 =>
    let prev := runStepsRR quantum arrivalStream n
    stepRR quantum {prev with sched := {prev.sched with ready := prev.sched.ready ++ arrivalStream (n + 1)} }

def runStepsRRAccumulateResults [SchedStateMethods AperiodicProcess] (quantum : Nat)
  (num_steps := default_num_steps)
  (arrivalStream : ℕ → List AperiodicProcess): List (SchedState) :=
  ((List.range (num_steps + 1)).map (runStepsRR quantum arrivalStream)).map fun rr_state: RRState => rr_state.sched

def selectFCFS : List AperiodicProcess → Option AperiodicProcess
  | [] => none
  | p :: _ => some p

def stepFCFS : SchedState → SchedState :=
  stepNonPreemptive selectFCFS

def selectSJF : List AperiodicProcess → Option AperiodicProcess :=
  fun ps =>
    ps.foldl (fun best p =>
      match best with
      | none   => some p
      | some b => if p.burst < b.burst then some p else some b)
      none

def stepSJF : SchedState → SchedState :=
  stepNonPreemptive selectSJF
