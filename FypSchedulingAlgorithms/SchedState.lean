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
  get_missed_processes  : SchedStateG process_type → List process_type
  extra_csv_field_names : String -- of form ",field_name1,field_name2" for new fields
  extra_csv_content     : SchedStateG process_type → String -- of form ",content1,content2" for new fields

instance : SchedStateMethods AperiodicProcess where
  init := {time := 0, ready := [], running := none, completed := []}
  add_arrival s processes := {s with ready := s.ready ++ (processes.filter fun p => p.arrival = s.time)}
  get_missed_processes _ := []
  extra_csv_field_names := ""
  extra_csv_content _ := ""

instance : SchedStateMethods PeriodicProcess where
  init := {time := 0, ready := [], running := none, completed := []}
  add_arrival s processes :=
    let processes_to_add := processes.filter fun p => s.time % p.period = 0
    let arrival_updated_processes := processes_to_add.map (fun p => {p with arrival := s.time})
    {s with ready := s.ready ++ (arrival_updated_processes)}
  get_missed_processes s := (s.ready ++ s.running.toList).filter (fun p => s.time > (p.arrival + p.deadline))
  extra_csv_field_names := " with deadline,missed_deadlines"
  extra_csv_content s :=
    -- Lean doesnt support `self` or calling other methods within own class during class definition
    let missed_processes := (s.ready ++ s.running.toList).filter (fun p => s.time > (p.arrival + p.deadline))
    let tickInfo :=
      missed_processes.map fun p =>
      "P" ++ toString (Process.id p) ++ ":" ++ toString (Process.ticksUsed p) ++ "/" ++ toString (Process.burst p) ++ toString (Process.deadline_info p)
    let tickField := ",".intercalate tickInfo
    s!",{tickField}"

-- # For RR, need to track quantum usage, so there is a separate function

structure RRState where
  sched      : SchedState
  quantum    : Nat          -- max ticks per slice
  ticksUsed  : Nat          -- ticks the current process has used this slice
  deriving Repr

-- Add arrivals to the SchedState inside RRState
def addArrivalsRR [SchedStateMethods AperiodicProcess] (rs : RRState) (processes : List AperiodicProcess): RRState :=
  let newSched := SchedStateMethods.add_arrival rs.sched processes
  { rs with sched := newSched }

-- remove the first matching element from a list - Used for preemptive scheduling
def List.removeFirst [BEq α] (a : α) : List α → List α
  | []      => []
  | x :: xs => if x == a then xs else x :: xs.removeFirst a
