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

This file defines the step functions for the classic periodic schedulers, `stepRMS`,
`stepDM` and `stepEDF`.  All are preemptive, so each is obtained by handing a
priority function to `stepPreemptive`; see `FypSchedulingAlgorithms.Step` for the
shared machinery.

`stepPreemptive` runs the candidate with the *highest* priority, an integer, so a
policy that wants the *smallest* value of some natural-number field `f` passes its
negation, `fun p => -(f p : ℤ)`.  Negation reverses the order on all of `ℕ`, `0`
included, so comparing priorities needs no positivity side conditions.

* `stepRMS` -- Rate Monotonic: the shortest period gets the CPU.
* `stepDM` -- Deadline Monotonic: the shortest relative deadline gets the CPU.
* `stepEDF` -- Earliest Deadline First: the nearest absolute deadline gets the CPU.

`stepRMS` and `stepDM` are fixed-priority schedulers: the priority of a job is that of
its task (`FixedPriorityBacklog`).  `stepEDF` is optimal (`EDFOptimality`).  RMS and EDF
are also exercised by the simulator in `FypSchedulingAlgorithms.SampleSchedules`.
-/

-- Rate Monotonic (RM) scheduler - Preemptively runs the process with the shortest period
def stepRMS : PeriodicSchedState → PeriodicSchedState :=
  stepPreemptive PeriodicProcess (fun p => -(p.period : ℤ))

/-- Deadline Monotonic (DM) scheduler: preemptively runs the job whose task has the
shortest relative deadline.  With `deadline = period` it orders jobs as `stepRMS` does. -/
def stepDM : PeriodicSchedState → PeriodicSchedState :=
  stepPreemptive PeriodicProcess (fun p => -(p.deadline : ℤ))

-- Earliest Deadline First (EDF) Scheduler - Preemptively picks the earliest deadline to run
def stepEDF : PeriodicSchedState -> PeriodicSchedState :=
  stepPreemptive PeriodicProcess (fun p => -((p.arrival + p.deadline : ℕ) : ℤ))
