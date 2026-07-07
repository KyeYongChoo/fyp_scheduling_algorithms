/-
Copyright (c) 2026 Choo Kye Yong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Choo Kye Yong
-/
import FypSchedulingAlgorithms.Process
import FypSchedulingAlgorithms.SchedState
import FypSchedulingAlgorithms.Step

-- Rate Monotonic (RM) scheduler - Preemptively runs the process with the shortest period
def stepRMS : PeriodicSchedState → PeriodicSchedState :=
  stepPreemptive PeriodicProcess (fun p => 1/(p.burst))

-- def stepRMS : PeriodicSchedState → PeriodicSchedState :=
--   fun s =>
--     -- gather all candidates: currently running (if any) + ready queue
--     let candidates : List PeriodicProcess :=
--       s.ready ++ (s.running.toList)
--     let shortest : Option PeriodicProcess :=
--       candidates.foldl (fun best p =>
--         match best with
--         | none   => some p
--         | some b => if p.period < b.period then some p else some b)
--         none
--     match shortest with
--     | none =>                                        -- nothing to run
--       { s with time := s.time + 1 }
--     | some p =>
--       -- preempt: put the old runner back in ready (if it's different)
--       let newReady : List PeriodicProcess :=
--         match s.running with
--         | none      => s.ready.removeFirst p
--         | some curr =>
--           if curr == p then s.ready                 -- same process keeps running
--           else s.ready.removeFirst p ++ [curr]      -- preempt: evict curr
--       if p.remaining ≤ 1 then
--         { s with time      := s.time + 1,
--                  running   := none,
--                  ready     := newReady }
--       else
--         { s with time    := s.time + 1,
--                  running := some { p with remaining := p.remaining - 1},
--                  ready   := newReady }

-- Earliest Deadline First (EDF) Scheduler - Preemptively picks the earliest deadline to run
def stepEDF : PeriodicSchedState -> PeriodicSchedState :=
  stepPreemptive PeriodicProcess (fun p => 1/(p.remaining))
