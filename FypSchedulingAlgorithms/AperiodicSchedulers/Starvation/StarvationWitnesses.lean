/-
Copyright (c) 2026 Choo Kye Yong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Choo Kye Yong
-/
import FypSchedulingAlgorithms.Process
import FypSchedulingAlgorithms.Step
import FypSchedulingAlgorithms.SchedState
import FypSchedulingAlgorithms.ProcessSimpLemmas

/-!
# Shared counterexample streams

Arrival streams used to *disprove* starvation-freedom, kept separate from the
proofs that use them so that several schedulers can share one witness (and one
`WellFormedStream` proof) without importing each other's files.

`starvation_stream` defeats both SJF (`SJFStarvation`) and SRTF
(`SRTFStarvation`), by quite different routes -- see those files.
-/

namespace StarvationWitnesses

/-- The long job that gets starved: burst 2, arrives at time 0, id 0. -/
def victim : AperiodicProcess := ⟨0, 0, 2, 2, by omega⟩

/-- The queue-jumpers: at each time `t` a fresh unit-burst job arrives, with id
`t + 1` so that all ids across the stream stay distinct. -/
def flood (t : ℕ) : AperiodicProcess := ⟨t + 1, t, 1, 1, by omega⟩

/-- `victim` arrives at time 0 alongside the first `flood` job; after that one
`flood` job arrives per tick, forever. -/
def starvation_stream : ℕ → List AperiodicProcess
  | 0     => [victim, flood 0]
  | t + 1 => [flood (t + 1)]

theorem starvation_stream_wf : WellFormedStream starvation_stream where
  consistent p t h_mem := by
    cases t <;>
      simp only [starvation_stream, List.mem_cons, List.not_mem_nil, or_false] at h_mem
    · rcases h_mem with rfl | rfl <;> rfl
    · subst h_mem; rfl
  fresh p t h_mem := by
    cases t <;>
      simp only [starvation_stream, List.mem_cons, List.not_mem_nil, or_false] at h_mem
    · rcases h_mem with rfl | rfl <;> rfl
    · subst h_mem; rfl
  unique p1 p2 t1 t2 h_mem1 h_mem2 h_id := by
    -- every member of the stream is either the victim (only at time 0) or that tick's flood job
    have key : ∀ (p : AperiodicProcess) (t : ℕ), p ∈ starvation_stream t →
        (p = victim ∧ t = 0) ∨ p = flood t := by
      intro p t hp
      cases t with
      | zero =>
        simp only [starvation_stream, List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl
        · exact Or.inl ⟨rfl, rfl⟩
        · exact Or.inr rfl
      | succ n =>
        simp only [starvation_stream, List.mem_cons, List.not_mem_nil, or_false] at hp
        exact Or.inr hp
    rcases key p1 t1 h_mem1 with ⟨rfl, rfl⟩ | rfl <;> rcases key p2 t2 h_mem2 with ⟨rfl, rfl⟩ | rfl
    · exact ⟨rfl, rfl⟩
    · simp [victim, flood] at h_id          -- victim id 0 vs flood id t + 1
    · simp [victim, flood] at h_id
    · simp only [flood, AperiodicProcess.process_id] at h_id
      have : t1 = t2 := by omega
      subst this
      exact ⟨rfl, rfl⟩

end StarvationWitnesses
