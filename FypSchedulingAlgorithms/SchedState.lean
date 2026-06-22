import FypSchedulingAlgorithms.Process

structure SchedState where
  time      : Nat
  ready     : List Process
  running   : Option Process
  completed : List Process
deriving Repr
