import FypSchedulingAlgorithms.Process

structure SchedStateG (α : Type) where
  time      : Nat
  ready     : List α
  running   : Option α
  completed : List α
deriving Repr

abbrev SchedState := SchedStateG AperiodicProcess
abbrev PeriodicSchedState := SchedStateG PeriodicProcess

-- remove the first matching element from a list - Used for preemptive scheduling
def List.removeFirst [BEq α] (a : α) : List α → List α
  | []      => []
  | x :: xs => if x == a then xs else x :: xs.removeFirst a
