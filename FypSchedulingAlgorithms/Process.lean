structure AperiodicProcess where
  id        : Nat
  arrival   : Nat -- arrival time of the process
  burst     : Nat
  remaining : Nat
deriving BEq, Repr

#eval AperiodicProcess.mk 1 0 5 5

structure PeriodicProcess where
  id        : Nat
  period    : Nat -- Process arrives at time 0, then every `period` thereafter
  burst     : Nat
  deadline  : Nat
  remaining : Nat
  -- Add `valid` back in if turns out the inequalities are useful in the proof
  -- valid     : remaining ≤ burst ∧ burst ≤ deadline ∧ deadline ≤ period
deriving BEq, Repr

-- #eval PeriodicProcess.mk 1 10 5 7 5 ⟨by omega, by omega, by omega⟩

#eval PeriodicProcess.mk 1 10 5 7 5

class Process (α : Type) extends BEq α where
  remaining   : α → Nat
  onComplete  : α → List α → List α

instance : Process AperiodicProcess where
  remaining p := p.remaining
  onComplete p completed := completed ++ [{p with remaining := 0}]

instance : Process PeriodicProcess where
  remaining p := p.remaining
  onComplete _ completed := completed -- no-op because periodic processes can't complete
