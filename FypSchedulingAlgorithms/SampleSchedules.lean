/-
Copyright (c) 2026 Choo Kye Yong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Choo Kye Yong
-/

import FypSchedulingAlgorithms.SchedState
import FypSchedulingAlgorithms.AperiodicSchedulers.AperiodicStep
import FypSchedulingAlgorithms.PeriodicSchedulers.PeriodicStep
import Std.Data.String
/-!
# Sample schedules

The file defines sample process sets and the CSV rendering of a run, so the user can check
that the scheduling algorithms behave as intended.  Nothing here writes files: the CSVs in
`SampleSchedules/` are written by `writeSampleSchedules` in `Main.lean`, which `lake build` runs
through the `SampleSchedulesGen` library whenever this file or a scheduler changes (manual
fallback: `lake env lean --run Main.lean` from the repository root).
-/

-- # Sample data

-- Aperiodic sample data
def aperiodicArrivals [Process AperiodicProcess]: Nat → List AperiodicProcess :=
  Process.convert_to_arrival_stream
  [
    { id := 1, arrival := 0, burst := 1, remaining := 1, burst_exceed_zero := (by omega) },
    { id := 2, arrival := 1, burst := 4, remaining := 4, burst_exceed_zero := (by omega)  },
    { id := 3, arrival := 2, burst := 2, remaining := 2, burst_exceed_zero := (by omega)  },
    { id := 4, arrival := 3, burst := 6, remaining := 6, burst_exceed_zero := (by omega)  },
    { id := 5, arrival :=5, burst := 3, remaining := 3, burst_exceed_zero := (by omega)  },
    { id := 6, arrival := 27, burst := 1, remaining := 1, burst_exceed_zero := (by omega)  },
  ]

-- Periodic sample data
def singleRecurrentProcess [Process PeriodicProcess]: Nat → List PeriodicProcess :=
  Process.convert_to_arrival_stream
  [
    { id := 1, arrival := 0, period := 6,  burst := 3, deadline := 4,  remaining := 3, burst_exceed_zero := (by omega)  }
  ]

-- Utilization = 1/4 + 2/6 ≈ 0.583, under the 2-task RM bound (2(2^(1/2)−1) ≈ 0.828)
def rmsSucceedsEdfSucceeds [Process PeriodicProcess]: Nat → List PeriodicProcess :=
  Process.convert_to_arrival_stream
  [
    { id := 1, arrival := 0, period := 4,  burst := 1, deadline := 4,  remaining := 1, burst_exceed_zero := (by omega)  },
    { id := 2, arrival := 0, period := 6,  burst := 2, deadline := 6,  remaining := 2, burst_exceed_zero := (by omega)  }
  ]

-- Utilization = 2/5 + 4/7 ≈ 0.971, above the 2-task RM bound (2(2^(1/2)−1) ≈ 0.828)
-- and will trigger rms deadline miss
def rmsFailsEdfSucceeds [Process PeriodicProcess]: Nat → List PeriodicProcess :=
  Process.convert_to_arrival_stream
  [
    { id := 1, arrival := 0, period := 5, burst := 2, deadline := 5, remaining := 2, burst_exceed_zero := (by omega)  },
    { id := 2, arrival := 0, period := 7, burst := 4, deadline := 7, remaining := 4, burst_exceed_zero := (by omega)  }
  ]

-- Utilization = 3/4 + 3/5 = 1.35 > 1, impossible to schedule
def bothFail [Process PeriodicProcess]: Nat → List PeriodicProcess :=
  Process.convert_to_arrival_stream
  [
    { id := 1, arrival := 0, period := 4, burst := 3, deadline := 4, remaining := 3, burst_exceed_zero := (by omega)  },
    { id := 2, arrival := 0, period := 5, burst := 3, deadline := 5, remaining := 3, burst_exceed_zero := (by omega)  }
  ]

-- run SRTF for 30 (default 30) ticks
#eval (runStepsAccumulateResults aperiodicArrivals stepSRTF).map fun s =>
  (s.time, s.running.map (·.id), s.ready.map (·.id), s.completed.length)

-- # CSV output

def stateToCSV {process_type: Type} [Process process_type] [SchedStateMethods process_type] (s : SchedStateG process_type) : String :=
  let running := s.running.map Process.label |>.getD "0"
  let readyIds := ",".intercalate (s.ready.map Process.label)
  let completedIds := ",".intercalate (s.completed.map Process.label)

  -- Tick information for all processes, sorted by id, then release time
  let allProcesses := s.ready ++ s.completed ++ (s.running.toList)
  let sortedProcesses := List.mergeSort allProcesses (fun p1 p2 =>
    Process.id p1 < Process.id p2 ||
      (Process.id p1 = Process.id p2 && Process.arrival p1 ≤ Process.arrival p2))
  let tickInfo := sortedProcesses.map fun p =>
    "P" ++ Process.label p ++ ":" ++ toString (Process.ticksUsed p) ++ "/" ++ toString (Process.burst p) ++ toString (Process.deadline_info p)
  let tickField := "|".intercalate tickInfo

  -- Wrap lists in quotes
  let readyField := "\"" ++ readyIds ++ "\""
  let completedField := "\"" ++ completedIds ++ "\""
  let ticksField := "\"" ++ tickField ++ "\""

  toString s.time ++ "," ++ running ++ "," ++ readyField ++ "," ++ completedField
  ++ "," ++ ticksField ++ (SchedStateMethods.extra_csv_content s)

def outputCSV {α} [Process α] [SchedStateMethods α] (states : List (SchedStateG α)) : String :=
  let header := "time,running,ready_queue,completed,process_ticks" ++ toString (SchedStateMethods.extra_csv_field_names (process_type := α))
  let rows := states.map stateToCSV
  (header :: rows) |> "\n".intercalate

/-- Write `content` to `dir ++ subdir ++ "/" ++ filename`, creating the directory if needed.
Paths are relative to the working directory, so run the generator from the repository root. -/
def writeCSV (filename : String) (content : String) (dir: String := "SampleSchedules/") (subdir: String := ""): IO Unit := do
  IO.FS.createDirAll (dir ++ subdir)
  IO.FS.writeFile (dir ++ subdir ++ "/" ++ filename) content
