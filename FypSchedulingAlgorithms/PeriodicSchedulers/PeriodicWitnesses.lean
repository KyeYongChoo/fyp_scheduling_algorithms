/-
Copyright (c) 2026 Choo Kye Yong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Choo Kye Yong
-/
import FypSchedulingAlgorithms.PeriodicSchedulers.EDFOptimality
import FypSchedulingAlgorithms.PeriodicSchedulers.FixedPriorityOptimality
import FypSchedulingAlgorithms.PeriodicSchedulers.Hyperperiod
import FypSchedulingAlgorithms.PeriodicSchedulers.SampleTaskSets

/-!
# EDF against fixed priorities: domination and a strict gap

* **EDF dominates every preemptive priority scheduler** (`edf_dominates`): for any priority
  function `f`, fixed or not, if `stepPreemptive f` never misses a deadline then `stepEDF`
  never does.  `stepRMS` and `stepDM` are instances (`edf_dominates_rms`,
  `edf_dominates_dm`).  The run of `stepPreemptive f` is an admissible schedule that is
  never late, so EDF's optimality (`edf_never_late`) applies.
* **The gap is strict** on `SampleTaskSets.rmsFailsEdfSucceeds` (periods 5 and 7, bursts 2
  and 4, `D = T`, utilisation 34/35):
  - `stepRMS` misses a deadline: the run lists one after step 7 (`rms_misses_rmsFails`);
  - `stepEDF` never does, at any step (`edf_never_misses_rmsFails`).  This is an all-time
    statement: EDF's first hyperperiod (35 steps) is checked by `decide`, it ends with an
    idle CPU and an empty queue, and the run then repeats (`Hyperperiod`);
  - no strict fixed-priority scheduler (distinct priorities per task) meets every
    deadline there either (`no_strict_fixedPriority_rmsFails`), by `rm_optimal`;
  - strictness matters: the constant priority `fun _ => 0`, which is `FixedPriority` but
    ties every pair of tasks, never misses a deadline there
    (`tied_priority_never_misses_rmsFails`).  `stepPreemptive` breaks ties dynamically
    (the running job stays, the queue is FIFO), so a tied priority is not a classical
    fixed-priority assignment.
* **RMS never misses on `SampleTaskSets.rmsSucceedsEdfSucceeds`** (periods 4 and 6), at
  any step (`rms_never_misses_rmsSucceeds`): by the first-job test (`rm_firstJob_test`;
  the periods are distinct and `D = T`) and a check of the two first jobs; so EDF never
  misses there either (`edf_never_misses_rmsSucceeds`).
-/

namespace Periodic

open PreemptiveRuns SampleTaskSets

/-! ## EDF dominates every priority scheduler -/

/-- **EDF dominates every preemptive priority scheduler**: if the run of
`stepPreemptive f` never lists a missed deadline, neither does the run of `stepEDF`.  `f`
need not be a fixed priority. -/
theorem edf_dominates (f : PeriodicProcess → ℤ) {tasks : List PeriodicProcess}
    (h_ids : (tasks.map PeriodicProcess.id).Nodup)
    (h_f : ∀ t, PeriodicProcess.missedDeadlines
      (runSteps (PeriodicProcess.releasesAt tasks) (stepPreemptive PeriodicProcess f) t) = [])
    (t : ℕ) :
    PeriodicProcess.missedDeadlines (runSteps (PeriodicProcess.releasesAt tasks) stepEDF t) =
      [] :=
  edf_never_late h_ids (runSchedule_stepPreemptive_isAdmissible f h_ids)
    (fun t' h => (missedDeadlines_ne_nil_iff_preemptive f h_ids t').mpr h (h_f t')) t

/-- EDF dominates RMS. -/
theorem edf_dominates_rms {tasks : List PeriodicProcess}
    (h_ids : (tasks.map PeriodicProcess.id).Nodup)
    (h_rms : ∀ t, PeriodicProcess.missedDeadlines
      (runSteps (PeriodicProcess.releasesAt tasks) stepRMS t) = []) (t : ℕ) :
    PeriodicProcess.missedDeadlines (runSteps (PeriodicProcess.releasesAt tasks) stepEDF t) =
      [] :=
  edf_dominates _ h_ids h_rms t

/-- EDF dominates DM. -/
theorem edf_dominates_dm {tasks : List PeriodicProcess}
    (h_ids : (tasks.map PeriodicProcess.id).Nodup)
    (h_dm : ∀ t, PeriodicProcess.missedDeadlines
      (runSteps (PeriodicProcess.releasesAt tasks) stepDM t) = []) (t : ℕ) :
    PeriodicProcess.missedDeadlines (runSteps (PeriodicProcess.releasesAt tasks) stepEDF t) =
      [] :=
  edf_dominates _ h_ids h_dm t

/-! ## The strict gap on `rmsFailsEdfSucceeds` -/

/-- **RMS misses a deadline on `rmsFailsEdfSucceeds`**: after step 7 the run lists task
2's first job (released at 0, deadline 7, 3 of its 4 ticks done). -/
theorem rms_misses_rmsFails :
    PeriodicProcess.missedDeadlines
      (runSteps (PeriodicProcess.releasesAt rmsFailsEdfSucceeds) stepRMS 7) ≠ [] := by
  decide

/-- **EDF never misses a deadline on `rmsFailsEdfSucceeds`**, at any step.  The first
hyperperiod is checked by `decide`; EDF is idle with an empty queue after step 34, so its
run repeats every 35 steps (`missedDeadlines_eq_nil_of_hyperperiod`). -/
theorem edf_never_misses_rmsFails (t : ℕ) :
    PeriodicProcess.missedDeadlines
      (runSteps (PeriodicProcess.releasesAt rmsFailsEdfSucceeds) stepEDF t) = [] :=
  missedDeadlines_eq_nil_of_hyperperiod _ (n := 34) (edf_shift_order 35)
    (by decide) (by decide) (by decide) (by decide) t

/-- **The gap is strict**: on `rmsFailsEdfSucceeds`, EDF never misses a deadline and RMS
does. -/
theorem edf_beats_rms_rmsFails :
    (∀ t, PeriodicProcess.missedDeadlines
        (runSteps (PeriodicProcess.releasesAt rmsFailsEdfSucceeds) stepEDF t) = []) ∧
      ∃ t, PeriodicProcess.missedDeadlines
        (runSteps (PeriodicProcess.releasesAt rmsFailsEdfSucceeds) stepRMS t) ≠ [] :=
  ⟨edf_never_misses_rmsFails, 7, rms_misses_rmsFails⟩

/-- **No strict fixed-priority scheduler meets every deadline on `rmsFailsEdfSucceeds`**:
if one did, so would RMS (`rm_optimal`; the set has `D = T`). -/
theorem no_strict_fixedPriority_rmsFails {f : PeriodicProcess → ℤ} (hf : FixedPriority f)
    (h_strict : ∀ τ ∈ rmsFailsEdfSucceeds, ∀ τ' ∈ rmsFailsEdfSucceeds, f τ = f τ' → τ = τ') :
    ¬ ∀ t, PeriodicProcess.missedDeadlines
      (runSteps (PeriodicProcess.releasesAt rmsFailsEdfSucceeds)
        (stepPreemptive PeriodicProcess f) t) = [] := fun h_f =>
  rms_misses_rmsFails (rm_optimal hf (by decide) h_strict (by decide) h_f 7)

/-- **A tied priority can beat every strict one**: the constant priority never misses a
deadline on `rmsFailsEdfSucceeds`, at any step (first hyperperiod by `decide`, then
`missedDeadlines_eq_nil_of_hyperperiod`).  It satisfies `FixedPriority` but is not strict,
so `rm_optimal` does not apply to it (`fixedPriority_const`). -/
theorem tied_priority_never_misses_rmsFails (t : ℕ) :
    PeriodicProcess.missedDeadlines
      (runSteps (PeriodicProcess.releasesAt rmsFailsEdfSucceeds)
        (stepPreemptive PeriodicProcess (fun _ => 0)) t) = [] :=
  missedDeadlines_eq_nil_of_hyperperiod _ (n := 34) (fun _ _ => Iff.rfl)
    (by decide) (by decide) (by decide) (by decide) t

/-! ## RMS never misses on `rmsSucceedsEdfSucceeds` -/

/-- **RMS never misses a deadline on `rmsSucceedsEdfSucceeds`**, at any step: the periods
are distinct and `D = T`, so the first-job test applies, and both first jobs meet their
deadlines. -/
theorem rms_never_misses_rmsSucceeds (t : ℕ) :
    PeriodicProcess.missedDeadlines
      (runSteps (PeriodicProcess.releasesAt rmsSucceedsEdfSucceeds) stepRMS t) = [] :=
  (rm_firstJob_test (by decide) (by decide) (by decide)).mpr (by decide) t

/-- EDF never misses a deadline on `rmsSucceedsEdfSucceeds` either. -/
theorem edf_never_misses_rmsSucceeds (t : ℕ) :
    PeriodicProcess.missedDeadlines
      (runSteps (PeriodicProcess.releasesAt rmsSucceedsEdfSucceeds) stepEDF t) = [] :=
  edf_dominates_rms (by decide) rms_never_misses_rmsSucceeds t

end Periodic
