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
-/

open Lean Elab Command in
run_cmd do
  let root := (System.FilePath.mk (← getFileName)).parent.getD "."
  writeSampleSchedules (dir := (root / "SampleSchedules").toString ++ "/")
