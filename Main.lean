/-
Copyright (c) 2026 Choo Kye Yong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Choo Kye Yong
-/

import FypSchedulingAlgorithms.SampleSchedules

/-!
# Sample schedule generator

Writes the sample-schedule CSVs in `SampleSchedules/`: one file per (scheduler, scenario)
pair, using the sample data and the CSV rendering in `FypSchedulingAlgorithms.SampleSchedules`.

`lake build` normally does this for you: the module `SampleSchedulesGen` (library
`SampleSchedulesGen`, a default target) runs `writeSampleSchedules` while it is elaborated,
which Lake does again whenever the schedulers, the sample data or this file change.  `main` is
the manual fallback, e.g. to restore CSVs that were edited or deleted by hand.  Run it from the
repository root (its output paths are relative to the working directory) with

    lake build && lake env lean --run Main.lean

It runs in the Lean interpreter on purpose: a compiled `lake exe` would first have to compile
every transitively imported Mathlib module to native code.
-/

/-- Write every sample-schedule CSV under `dir` (default `SampleSchedules/`, relative to the
working directory): the aperiodic traces in `dir` itself, the periodic ones in `dir/EDF/` and
`dir/RMS/`. -/
def writeSampleSchedules (dir : String := "SampleSchedules/") : IO Unit := do
  -- # Aperiodic schedulers
  writeCSV "SRTFschedule.csv" (outputCSV (runStepsAccumulateResults aperiodicArrivals stepSRTF))
    (dir := dir)
  writeCSV "SJFschedule.csv" (outputCSV (runStepsAccumulateResults aperiodicArrivals stepSJF))
    (dir := dir)
  writeCSV "FCFSschedule.csv" (outputCSV (runStepsAccumulateResults aperiodicArrivals stepFCFS))
    (dir := dir)
  writeCSV "RRschedule_q3.csv" (outputCSV (runStepsRRAccumulateResults (quantum := 3)
    (arrivalStream := aperiodicArrivals) (num_steps := 30))) (dir := dir)

  -- # Periodic schedulers
  writeCSV "EDFscheduleSingleRecurrent.csv"
    (outputCSV (runStepsAccumulateResults singleRecurrentProcess stepEDF)) (dir := dir)
    (subdir := "EDF")
  writeCSV "EDFscheduleRmsSucceedsEdfSucceeds.csv"
    (outputCSV (runStepsAccumulateResults rmsSucceedsEdfSucceeds stepEDF)) (dir := dir)
    (subdir := "EDF")
  writeCSV "EDFscheduleRmsFailsEdfSucceeds.csv"
    (outputCSV (runStepsAccumulateResults rmsFailsEdfSucceeds stepEDF)) (dir := dir)
    (subdir := "EDF")
  writeCSV "EDFscheduleBothFail.csv"
    (outputCSV (runStepsAccumulateResults bothFail stepEDF)) (dir := dir) (subdir := "EDF")

  writeCSV "RMSscheduleSingleRecurrent.csv"
    (outputCSV (runStepsAccumulateResults singleRecurrentProcess stepRMS)) (dir := dir)
    (subdir := "RMS")
  writeCSV "RMSscheduleRmsSucceedsEdfSucceeds.csv"
    (outputCSV (runStepsAccumulateResults rmsSucceedsEdfSucceeds stepRMS)) (dir := dir)
    (subdir := "RMS")
  writeCSV "RMSscheduleRmsFailsEdfSucceeds.csv"
    (outputCSV (runStepsAccumulateResults rmsFailsEdfSucceeds stepRMS)) (dir := dir)
    (subdir := "RMS")
  writeCSV "RMSscheduleBothFail.csv"
    (outputCSV (runStepsAccumulateResults bothFail stepRMS)) (dir := dir) (subdir := "RMS")

/-- Regenerate every sample-schedule CSV under `SampleSchedules/` (relative to the working
directory). -/
def main : IO Unit := do
  writeSampleSchedules
  IO.println "Wrote the sample schedules to SampleSchedules/"
