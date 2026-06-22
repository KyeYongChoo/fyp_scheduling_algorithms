structure Process where
  id        : Nat
  arrival   : Nat
  burst     : Nat
  remaining : Nat
deriving BEq, Repr

#eval Process.mk 1 0 5 5
