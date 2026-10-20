/-
Copyright (c) 2026 Choo Kye Yong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Choo Kye Yong
-/

import FypSchedulingAlgorithms.SampleSchedules

/-!
# Sample schedules on `lake build`

Writes the sample-schedule CSVs in `SampleSchedules/`: one file per (scheduler, scenario) pair,
using the sample data and the CSV rendering in `FypSchedulingAlgorithms.SampleSchedules`.

Elaborating this module rewrites every CSV with `writeSampleSchedules`.  It is the root of the
`SampleSchedulesGen` library, which `lakefile.toml` lists in `defaultTargets`, so `lake build`
elaborates it again, and so refreshes the CSVs, exactly when this file or one of its imports
changes (the schedulers, the sample data, the CSV rendering); otherwise Lake reuses its cached
build and writes nothing.  The proof library `FypSchedulingAlgorithms` does not import it.

The output directory is taken from this file's own path rather than the working directory, so
the CSVs land in `SampleSchedules/` next to this file.  Opening this file in an editor also
rewrites them.  The manual fallback, e.g. to restore CSVs that were edited or deleted by hand,
is to elaborate this file directly, from the repository root:

    lake build && lake env lean SampleSchedulesGen.lean

(build first, so the imported modules are current).  There is no `main` and no `lake exe`: a
compiled executable would first have to compile every transitively imported Mathlib module to
native code, whereas elaborating this file runs the generator in the Lean interpreter.

A CSV that cannot be written (e.g. one held open, and so locked, by a spreadsheet on Windows)
only produces a warning, so the build still succeeds.  Lake then caches this module as built,
so close the file and rerun `lake env lean SampleSchedulesGen.lean` to catch up.  A plain
`lake build` keeps replaying that cached warning until this module is next rebuilt; once the
manual command has run, the warning is stale and harmless.
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

open Lean Elab Command in
run_cmd do
  let root := (System.FilePath.mk (← getFileName)).parent.getD "."
  try
    writeSampleSchedules (dir := (root / "SampleSchedules").toString ++ "/")
  catch e =>
    logWarning m!"sample schedules not written: {e.toMessageData}\n\
      Close the file and run `lake env lean SampleSchedulesGen.lean` to regenerate them."
