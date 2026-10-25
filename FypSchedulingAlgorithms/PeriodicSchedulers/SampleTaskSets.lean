/-
Copyright (c) 2026 Choo Kye Yong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Choo Kye Yong
-/
import FypSchedulingAlgorithms.Process

/-!
# Sample periodic task sets

The bare task lists behind the periodic sample schedules.  They live in the proof library
so that theorems can be stated about them (`PeriodicWitnesses`); the CSV code in
`SampleSchedules.lean` imports this file and turns each list into an arrival stream with
`Process.convert_to_arrival_stream`.  All four sets have `deadline = period` except
`singleRecurrent`.
-/

namespace SampleTaskSets

/-- One task, period 6, burst 3, relative deadline 4. -/
def singleRecurrent : List PeriodicProcess :=
  [
    { id := 1, arrival := 0, period := 6,  burst := 3, deadline := 4,  remaining := 3, burst_exceed_zero := (by omega)  }
  ]

/-- Utilization = 1/4 + 2/6 ≈ 0.583, under the 2-task RM bound (2(2^(1/2)−1) ≈ 0.828). -/
def rmsSucceedsEdfSucceeds : List PeriodicProcess :=
  [
    { id := 1, arrival := 0, period := 4,  burst := 1, deadline := 4,  remaining := 1, burst_exceed_zero := (by omega)  },
    { id := 2, arrival := 0, period := 6,  burst := 2, deadline := 6,  remaining := 2, burst_exceed_zero := (by omega)  }
  ]

/-- Utilization = 2/5 + 4/7 ≈ 0.971, above the 2-task RM bound (2(2^(1/2)−1) ≈ 0.828):
RMS misses a deadline, EDF does not. -/
def rmsFailsEdfSucceeds : List PeriodicProcess :=
  [
    { id := 1, arrival := 0, period := 5, burst := 2, deadline := 5, remaining := 2, burst_exceed_zero := (by omega)  },
    { id := 2, arrival := 0, period := 7, burst := 4, deadline := 7, remaining := 4, burst_exceed_zero := (by omega)  }
  ]

/-- Utilization = 3/4 + 3/5 = 1.35 > 1, impossible to schedule. -/
def bothFail : List PeriodicProcess :=
  [
    { id := 1, arrival := 0, period := 4, burst := 3, deadline := 4, remaining := 3, burst_exceed_zero := (by omega)  },
    { id := 2, arrival := 0, period := 5, burst := 3, deadline := 5, remaining := 3, burst_exceed_zero := (by omega)  }
  ]

end SampleTaskSets
