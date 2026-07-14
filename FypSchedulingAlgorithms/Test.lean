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
# Test scheduling algorithms

The file generates processes, executes them via the different scheduling algorithms and
generates a csv file for the user to check whether the scheduling algorithms are working as
intended.
-/

-- # Test Data

-- Aperiodic Test data
def aperiodicArrivals [Process AperiodicProcess]: Nat → List AperiodicProcess :=
  Process.convert_to_arrival_stream
  [
    { id := 1, arrival := 0, burst := 8, remaining := 8 },
    { id := 2, arrival := 1, burst := 4, remaining := 4 },
    { id := 3, arrival := 2, burst := 2, remaining := 2 },
    { id := 4, arrival := 3, burst := 6, remaining := 6 },
    { id := 5, arrival := 5, burst := 3, remaining := 3 },
  ]

-- Periodic Test data
def singleRecurrentProcess [Process PeriodicProcess]: Nat → List PeriodicProcess :=
  Process.convert_to_arrival_stream
  [
    { id := 1, arrival := 0, period := 6,  burst := 3, deadline := 4,  remaining := 3 }
  ]

-- Utilization = 1/4 + 2/6 ≈ 0.583, under the 2-task RM bound (2(2^(1/2)−1) ≈ 0.828)
def rmsSucceedsEdfSucceeds [Process PeriodicProcess]: Nat → List PeriodicProcess :=
  Process.convert_to_arrival_stream
  [
    { id := 1, arrival := 0, period := 4,  burst := 1, deadline := 4,  remaining := 1 },
    { id := 2, arrival := 0, period := 6,  burst := 2, deadline := 6,  remaining := 2 }
  ]

-- Utilization = 2/5 + 4/7 ≈ 0.971, above the 2-task RM bound (2(2^(1/2)−1) ≈ 0.828)
-- and will trigger rms deadline miss
def rmsFailsEdfSucceeds [Process PeriodicProcess]: Nat → List PeriodicProcess :=
  Process.convert_to_arrival_stream
  [
    { id := 1, arrival := 0, period := 5, burst := 2, deadline := 5, remaining := 2 },
    { id := 2, arrival := 0, period := 7, burst := 4, deadline := 7, remaining := 4 }
  ]

-- Utilization = 3/4 + 3/5 = 1.35 > 1, impossible to schedule
def bothFail [Process PeriodicProcess]: Nat → List PeriodicProcess :=
  Process.convert_to_arrival_stream
  [
    { id := 1, arrival := 0, period := 4, burst := 3, deadline := 4, remaining := 3 },
    { id := 2, arrival := 0, period := 5, burst := 3, deadline := 5, remaining := 3 }
  ]

-- run SRTF for 30 (default 30) ticks
#eval (runStepsAccumulateResults aperiodicArrivals stepSRTF).map fun s =>
  (s.time, s.running.map (·.id), s.ready.map (·.id), s.completed.length)

-- # CSV output

def stateToCSV {process_type: Type} [Process process_type] [SchedStateMethods process_type] (s : SchedStateG process_type) : String :=
  let running := s.running.map (fun p => (Process.id p)) |>.getD 0 |> toString
  let readyIds := ",".intercalate (s.ready.map (fun p => (Process.id p)) |> List.map toString)
  let completedIds := ",".intercalate (s.completed.map (fun p => (Process.id p)) |> List.map toString)

  -- Tick information for all processes, sorted by ID
  let allProcesses := s.ready ++ s.completed ++ (s.running.toList)
  let sortedProcesses := List.mergeSort allProcesses (fun p1 p2 => Process.id p1 < Process.id p2)
  let tickInfo := sortedProcesses.map fun p =>
    "P" ++ toString (Process.id p) ++ ":" ++ toString (Process.ticksUsed p) ++ "/" ++ toString (Process.burst p) ++ toString (Process.deadline_info p)
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

def writeCSV (filename : String) (content : String) (dir: String := "SampleSchedules/") (subdir: String := ""): IO Unit := do
  IO.FS.createDirAll (dir ++ subdir)
  IO.FS.writeFile (dir ++ subdir ++ "/" ++ filename) content

set_option linter.hashCommand false

#eval writeCSV "SRTFschedule.csv" (outputCSV (runStepsAccumulateResults aperiodicArrivals stepSRTF))

#eval writeCSV "SJFschedule.csv" (outputCSV (runStepsAccumulateResults aperiodicArrivals stepSJF))

#eval writeCSV "FCFSschedule.csv" (outputCSV (runStepsAccumulateResults aperiodicArrivals stepFCFS))

#eval writeCSV "RRschedule_q3.csv" (outputCSV (runStepsRRAccumulateResults (quantum:=3) (arrivalStream := aperiodicArrivals) (num_steps:= 30)))

-- # Periodic Schedulers
#eval writeCSV "EDFscheduleSingleRecurrent.csv" (outputCSV (runStepsAccumulateResults singleRecurrentProcess stepEDF)) (subdir := "EDF")
#eval writeCSV "EDFscheduleRmsSucceedsEdfSucceeds.csv" (outputCSV (runStepsAccumulateResults rmsSucceedsEdfSucceeds stepEDF)) (subdir := "EDF")
#eval writeCSV "EDFscheduleRmsFailsEdfSucceeds.csv" (outputCSV (runStepsAccumulateResults rmsFailsEdfSucceeds stepEDF)) (subdir := "EDF")
#eval writeCSV "EDFscheduleBothFail.csv" (outputCSV (runStepsAccumulateResults bothFail stepEDF)) (subdir := "EDF")

#eval writeCSV "RMSscheduleSingleRecurrent.csv" (outputCSV (runStepsAccumulateResults singleRecurrentProcess stepRMS)) (subdir := "RMS")
#eval writeCSV "RMSscheduleRmsSucceedsEdfSucceeds.csv" (outputCSV (runStepsAccumulateResults rmsSucceedsEdfSucceeds stepRMS)) (subdir := "RMS")
#eval writeCSV "RMSscheduleRmsFailsEdfSucceeds.csv" (outputCSV (runStepsAccumulateResults rmsFailsEdfSucceeds stepRMS)) (subdir := "RMS")
#eval writeCSV "RMSscheduleBothFail.csv" (outputCSV (runStepsAccumulateResults bothFail stepRMS)) (subdir := "RMS")
