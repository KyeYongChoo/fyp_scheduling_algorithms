/-
Copyright (c) 2026 Choo Kye Yong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Choo Kye Yong
-/
import FypSchedulingAlgorithms.Process
import FypSchedulingAlgorithms.SchedState
import FypSchedulingAlgorithms.Step

/-!
# Periodic Scheduling Algorithms

This file defines the step functions for the two classic periodic schedulers,
`stepRMS` and `stepEDF`.  Both are preemptive, so both are obtained by handing a
priority function to `stepPreemptive`; see `FypSchedulingAlgorithms.Step` for the
shared machinery.

`stepPreemptive` runs the candidate with the *highest* priority, an integer, so a
policy that wants the *smallest* value of some natural-number field `f` passes its
negation, `fun p => -(f p : ℤ)`.  Negation reverses the order on all of `ℕ`, `0`
included, so comparing priorities needs no positivity side conditions.

* `stepRMS` -- Rate Monotonic: the shortest period gets the CPU.
* `stepEDF` -- Earliest Deadline First: the nearest deadline gets the CPU.

Neither has a starvation or schedulability proof yet; they are currently only
exercised by the simulator in `FypSchedulingAlgorithms.SampleSchedules`.
-/

-- Rate Monotonic (RM) scheduler - Preemptively runs the process with the shortest period
def stepRMS : PeriodicSchedState → PeriodicSchedState :=
  stepPreemptive PeriodicProcess (fun p => -(p.period : ℤ))

-- Earliest Deadline First (EDF) Scheduler - Preemptively picks the earliest deadline to run
def stepEDF : PeriodicSchedState -> PeriodicSchedState :=
  stepPreemptive PeriodicProcess (fun p => -((p.arrival + p.deadline : ℕ) : ℤ))
