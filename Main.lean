/-
Copyright (c) 2026 Choo Kye Yong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Choo Kye Yong
-/

import FypSchedulingAlgorithms.SampleSchedules

/-!
# Sample schedule generator

Writes the sample-schedule CSVs in `SampleSchedules/`: one file per (scheduler, scenario)
pair, using the test data and the CSV rendering in `FypSchedulingAlgorithms.SampleSchedules`.

This is not part of the library and `lake build` never runs it.  Run it from the repository
root (the output paths are relative) with

    lake build && lake env lean --run Main.lean

It runs in the Lean interpreter on purpose: a compiled `lake exe` would first have to compile
every transitively imported Mathlib module to native code.
-/

/-- Regenerate every sample-schedule CSV under `SampleSchedules/`. -/
def main : IO Unit := do
  -- # Aperiodic schedulers
  writeCSV "SRTFschedule.csv" (outputCSV (runStepsAccumulateResults aperiodicArrivals stepSRTF))
  writeCSV "SJFschedule.csv" (outputCSV (runStepsAccumulateResults aperiodicArrivals stepSJF))
  writeCSV "FCFSschedule.csv" (outputCSV (runStepsAccumulateResults aperiodicArrivals stepFCFS))
  writeCSV "RRschedule_q3.csv" (outputCSV (runStepsRRAccumulateResults (quantum := 3)
    (arrivalStream := aperiodicArrivals) (num_steps := 30)))

  -- # Periodic schedulers
  writeCSV "EDFscheduleSingleRecurrent.csv"
    (outputCSV (runStepsAccumulateResults singleRecurrentProcess stepEDF)) (subdir := "EDF")
  writeCSV "EDFscheduleRmsSucceedsEdfSucceeds.csv"
    (outputCSV (runStepsAccumulateResults rmsSucceedsEdfSucceeds stepEDF)) (subdir := "EDF")
  writeCSV "EDFscheduleRmsFailsEdfSucceeds.csv"
    (outputCSV (runStepsAccumulateResults rmsFailsEdfSucceeds stepEDF)) (subdir := "EDF")
  writeCSV "EDFscheduleBothFail.csv"
    (outputCSV (runStepsAccumulateResults bothFail stepEDF)) (subdir := "EDF")

  writeCSV "RMSscheduleSingleRecurrent.csv"
    (outputCSV (runStepsAccumulateResults singleRecurrentProcess stepRMS)) (subdir := "RMS")
  writeCSV "RMSscheduleRmsSucceedsEdfSucceeds.csv"
    (outputCSV (runStepsAccumulateResults rmsSucceedsEdfSucceeds stepRMS)) (subdir := "RMS")
  writeCSV "RMSscheduleRmsFailsEdfSucceeds.csv"
    (outputCSV (runStepsAccumulateResults rmsFailsEdfSucceeds stepRMS)) (subdir := "RMS")
  writeCSV "RMSscheduleBothFail.csv"
    (outputCSV (runStepsAccumulateResults bothFail stepRMS)) (subdir := "RMS")
  IO.println "Wrote the sample schedules to SampleSchedules/"
