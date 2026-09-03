/-
Copyright (c) 2026 Choo Kye Yong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Choo Kye Yong
-/
structure AperiodicProcess where
  id        : Nat
  arrival   : Nat
  burst     : Nat
  remaining : Nat
  burst_exceed_zero : burst > 0
deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

-- #eval AperiodicProcess.mk 1 0 5 5

structure PeriodicProcess where
  id        : Nat
  arrival   : Nat
  period    : Nat -- Process arrives at time 0, then every `period` thereafter
  burst     : Nat
  deadline  : Nat
  remaining : Nat
  burst_exceed_zero : burst > 0
  -- Add `valid` back in if turns out the inequalities are useful in the proof
  -- valid     : 0 < burst ∧ remaining ≤ burst ∧ burst ≤ deadline ∧ deadline ≤ period
deriving BEq, Repr

-- #eval PeriodicProcess.mk 1 0 10 5 7 5 (by omega) ⟨by omega, by omega, by omega, by omega⟩

#eval PeriodicProcess.mk 1 0 10 5 7 5 (by omega)

class Process (α : Type) extends BEq α where
  id            : α → Nat
  arrival       : α → Nat
  remaining     : α → Nat
  burst         : α → Nat
  ticksUsed     : α → Nat
  tick          : α → α
  deadline_info : α → String
  -- Let arrival stream be a function that takes time as argument and returns list of arriving processes
  convert_to_arrival_stream : List α → Nat → List α
  tick_decrements : ∀ p, remaining (tick p) = remaining p - 1
  id_invariant_wrt_tick : ∀ p, id (tick p) = id (p)
  burst_exceed_zero : ∀ p, burst (p) > 0

instance : Process AperiodicProcess where
  id p := p.id
  arrival p := p.arrival
  remaining p := p.remaining
  burst p := p.burst
  ticksUsed p := p.burst - p.remaining
  tick p := {p with remaining := p.remaining - 1}
  deadline_info _ := ""
  convert_to_arrival_stream original_process_list :=
    fun current_time =>
      original_process_list.filter (fun p => current_time = p.arrival)
  tick_decrements _p := rfl
  id_invariant_wrt_tick _p := rfl
  burst_exceed_zero p := p.burst_exceed_zero

instance : Process PeriodicProcess where
  id p := p.id
  remaining p := p.remaining
  arrival p := p.arrival
  burst p := p.burst
  ticksUsed p := p.burst - p.remaining
  tick p := {p with remaining := p.remaining - 1}
  deadline_info p := s!"d{p.deadline + p.arrival}"
  convert_to_arrival_stream original_process_list :=
    fun current_time =>
      original_process_list.filter (fun p => current_time % p.arrival = 0)
  tick_decrements _p := rfl
  id_invariant_wrt_tick _p := rfl
  burst_exceed_zero p := p.burst_exceed_zero
