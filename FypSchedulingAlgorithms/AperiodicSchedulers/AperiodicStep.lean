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
-- RR needs a quantum counter; extend SchedState or use a wrapper

def stepRR (q : Nat) : RRState → RRState :=
  fun rs =>
    let s := rs.sched
    match s.running with
    | none =>
      match s.ready with
      | []      => { rs with sched := { s with time := s.time + 1 } }   -- idle
      | p :: ps => { rs with sched     := { s with time    := s.time + 1,
                                                   running := some p,
                                                   ready   := ps },
                             ticksUsed := 1 }
    | some p =>
      if p.remaining ≤ 1 then                           -- process finishes
        { rs with sched     := { s with time      := s.time + 1,
                                        running   := none,
                                        completed := s.completed ++
                                                       [{ p with remaining := 0 }] },
                  ticksUsed := 0 }
      else if rs.ticksUsed ≥ q then                     -- quantum expired → preempt
        match s.ready with
        | []      =>                                     -- no one else: keep running
          { rs with sched     := { s with time    := s.time + 1,
                                          running := some { p with remaining :=
                                                              p.remaining - 1 } },
                    ticksUsed := 1 }
        | nx :: ps =>                                    -- rotate
          { rs with sched     := { s with time    := s.time + 1,
                                          running := some nx,
                                          ready   := ps ++ [{ p with remaining :=
                                                                p.remaining - 1 }] },
                    ticksUsed := 1 }
      else                                               -- normal tick
        { rs with sched     := { s with time    := s.time + 1,
                                        running := some { p with remaining :=
                                                            p.remaining - 1 } },
                  ticksUsed := rs.ticksUsed + 1 }

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
