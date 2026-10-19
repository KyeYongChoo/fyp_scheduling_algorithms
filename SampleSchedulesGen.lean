/-
Copyright (c) 2026 Choo Kye Yong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Choo Kye Yong
-/

import Main

/-!
# Sample schedules on `lake build`

Elaborating this module rewrites every CSV in `SampleSchedules/` with `writeSampleSchedules`
from `Main.lean`.  It is the root of the `SampleSchedulesGen` library, which `lakefile.toml`
lists in `defaultTargets`, so `lake build` elaborates it again, and so refreshes the CSVs,
exactly when this file or one of its imports changes (the schedulers, the sample data, the CSV
rendering, `Main.lean`); otherwise Lake reuses its cached build and writes nothing.  The proof
library `FypSchedulingAlgorithms` does not import it.

The output directory is taken from this file's own path rather than the working directory, so
the CSVs land in `SampleSchedules/` next to this file.  Opening this file in an editor also
rewrites them.

A CSV that cannot be written (e.g. one held open, and so locked, by a spreadsheet on Windows)
only produces a warning, so the build still succeeds.  Lake then caches this module as built,
so close the file and rerun `lake env lean --run Main.lean` to catch up.  A plain `lake build`
keeps replaying that cached warning until this module is next rebuilt; once the manual command
has run, the warning is stale and harmless.
-/

open Lean Elab Command in
run_cmd do
  let root := (System.FilePath.mk (← getFileName)).parent.getD "."
  try
    writeSampleSchedules (dir := (root / "SampleSchedules").toString ++ "/")
  catch e =>
    logWarning m!"sample schedules not written: {e.toMessageData}\n\
      Close the file and run `lake env lean --run Main.lean` to regenerate them."
