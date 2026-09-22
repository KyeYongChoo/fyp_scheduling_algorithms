import FypSchedulingAlgorithms.Process
import FypSchedulingAlgorithms.Step
import FypSchedulingAlgorithms.SchedState
import FypSchedulingAlgorithms.AperiodicSchedulers.AperiodicStep
import FypSchedulingAlgorithms.ProcessSimpLemmas
import Mathlib.Tactic.Linarith
import FypSchedulingAlgorithms.ListLemmas

namespace SJFStarvation

def pathologic_arrival_stream (t : ℕ) : List AperiodicProcess :=
  if t = 0 ∨ t = 1 then
    [AperiodicProcess.mk t 0 5 5 (by omega)]
  else
    [AperiodicProcess.mk t 0 1 1 (by omega)]
-- process 0 will occupy the running slot while process 1 goes into the ready slot,
-- then process 2,3,4,5... will perpetually delay the slot

theorem Starvation
  (arrival_stream : Nat → List AperiodicProcess)
  (quantum : ℕ)
  (h_wf : WellFormedStream arrival_stream) :
  ∀ arrival_time process, process ∈ arrival_stream arrival_time →
  ¬(∃ completion_time, ∃ finished_process ∈ (runStepsRR quantum arrival_stream completion_time).sched.completed,
    Process.id finished_process = Process.id process)
  := by
  push Not

namespace SJFStarvation
