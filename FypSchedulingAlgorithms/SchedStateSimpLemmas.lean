/-
Copyright (c) 2026 Choo Kye Yong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Choo Kye Yong
-/
import FypSchedulingAlgorithms.SchedState

/-!
# Simp lemmas for `SchedStateMethods`

Unfolding `SchedStateMethods.init` to a literal record is enough for `simp` to
discharge every field projection (`.time`, `.ready`, `.running`, `.completed`),
since `simp` reduces a projection applied to a constructor on its own.  So there
is no need for one lemma per field.
-/

namespace SchedStateG

@[simp]
theorem init_aperiodic :
    (SchedStateMethods.init : SchedStateG AperiodicProcess)
      = { time := 0, ready := [], running := none, completed := [] } :=
  rfl

@[simp]
theorem init_periodic :
    (SchedStateMethods.init : SchedStateG PeriodicProcess)
      = { time := 0, ready := [], running := none, completed := [] } :=
  rfl

end SchedStateG

-- sanity checks: the field lemmas come for free
example : (SchedStateMethods.init : SchedStateG AperiodicProcess).completed = [] := by simp
example : (SchedStateMethods.init : SchedStateG AperiodicProcess).ready = [] := by simp
example : (SchedStateMethods.init : SchedStateG AperiodicProcess).running = none := by simp
example : (SchedStateMethods.init : SchedStateG AperiodicProcess).time = 0 := by simp
example : (SchedStateMethods.init : SchedStateG PeriodicProcess).completed = [] := by simp
example : (SchedStateMethods.init : SchedStateG PeriodicProcess).ready = [] := by simp
example : (SchedStateMethods.init : SchedStateG PeriodicProcess).running = none := by simp
example : (SchedStateMethods.init : SchedStateG PeriodicProcess).time = 0 := by simp
