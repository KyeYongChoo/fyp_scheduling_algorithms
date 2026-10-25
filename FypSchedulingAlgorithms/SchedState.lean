/-
Copyright (c) 2026 Choo Kye Yong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Choo Kye Yong
-/
import FypSchedulingAlgorithms.Process

structure SchedStateG (α : Type) where
  time      : Nat
  ready     : List α
  running   : Option α
  completed : List α
deriving Repr

abbrev SchedState := SchedStateG AperiodicProcess
abbrev PeriodicSchedState := SchedStateG PeriodicProcess

class SchedStateMethods(process_type : Type) where
  init                  : SchedStateG process_type
  add_arrival           : SchedStateG process_type → List process_type → SchedStateG process_type
  -- the unfinished jobs that have missed their deadline; late jobs are not aborted, so a
  -- job that misses its deadline is listed again at every step until it finishes.  A job
  -- released at time `r` is not ticked before step `r+1` (the tick convention in Step.lean),
  -- so with relative deadline `D` it gets the `D` ticks of steps `r+1 … r+D` and is late
  -- once it is unfinished in a state with `time > r + D`
  get_missed_processes  : SchedStateG process_type → List process_type
  extra_csv_field_names : String -- of form ",field_name1,field_name2" for new fields
  extra_csv_content     : SchedStateG process_type → String -- of form ",content1,content2" for new fields

instance : SchedStateMethods AperiodicProcess where
  init := {time := 0, ready := [], running := none, completed := []}
  add_arrival s processes := {s with ready := s.ready ++ (processes.filter fun p => p.arrival = s.time)}
  get_missed_processes _ := []
  extra_csv_field_names := ""
  extra_csv_content _ := ""

/-- The unfinished (ready or running) periodic jobs of `s` that have missed their deadline.

The rule absorbs the one-tick dispatch latency of the step functions.  A job released at time
`r` enters the system in step `r`, and a job put on the CPU in a step is not ticked in that step
(tick convention in Step.lean), so its first possible tick is in step `r+1`.  With relative
deadline `D` it therefore gets the `D` usable ticks of steps `r+1 … r+D`.  The state after step
`t` has `time = t+1`, so the job meets its deadline iff it is finished in the state with
`time = r + D + 1`, and it is late in a state `s` iff it is still unfinished and
`r + D < s.time`.  This is the textbook discrete model shifted by one tick: a lone task with
`burst = deadline` meets its deadline.

Late jobs are not aborted, so a missed job stays in this list until it finishes. -/
def PeriodicProcess.missedDeadlines (s : SchedStateG PeriodicProcess) : List PeriodicProcess :=
  (s.ready ++ s.running.toList).filter fun p => p.arrival + p.deadline < s.time

instance : SchedStateMethods PeriodicProcess where
  init := {time := 0, ready := [], running := none, completed := []}
  -- the same releases as `Process.convert_to_arrival_stream`
  add_arrival s processes := {s with ready := s.ready ++ PeriodicProcess.releasesAt processes s.time}
  get_missed_processes := PeriodicProcess.missedDeadlines
  extra_csv_field_names := " with deadline,missed_deadlines"
  extra_csv_content s :=
    -- the same filter as `get_missed_processes`
    let missed_processes := PeriodicProcess.missedDeadlines s
    let tickInfo :=
      missed_processes.map fun p =>
      "P" ++ Process.label p ++ ":" ++ toString (Process.ticksUsed p) ++ "/" ++ toString (Process.burst p) ++ toString (Process.deadline_info p)
    let tickField := "|".intercalate tickInfo
    s!",\"{tickField}\""

-- # For RR, need to track quantum usage, so there is a separate function

structure RRState where
  sched      : SchedState
  ticksUsed  : Nat          -- ticks the current process has used this slice
  deriving Repr

-- Add arrivals to the SchedState inside RRState
def addArrivalsRR [SchedStateMethods AperiodicProcess] (rs : RRState) (processes : List AperiodicProcess): RRState :=
  let newSched := SchedStateMethods.add_arrival rs.sched processes
  { rs with sched := newSched }
