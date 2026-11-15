/-
Copyright (c) 2026 Choo Kye Yong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Choo Kye Yong
-/
import FypSchedulingAlgorithms.Process
import FypSchedulingAlgorithms.Step
import FypSchedulingAlgorithms.ProcessSimpLemmas

/-!
# Shared convoy witnesses

Jobs and arrival streams used by the per-scheduler convoy files, kept separate
so that several schedulers can be compared on one stream without importing each
other's files (as `StarvationWitnesses` does for starvation).

* `leader`, `shortJob`: a fixed long job and a unit job, both arriving at 0.
* `convoyArrivalStream L`: `longJob L` ahead of `shortJob`, both at time 0 --
  the classic convoy (`FCFSConvoy`, `RRConvoy`).
* `lateConvoyArrivalStream L`: `longJob L` at time 0, `lateShortJob` at time 1
  -- the late-arrival convoy that separates non-preemptive SJF from SRTF.
* `equalPair`: two equal jobs, where a smaller RR quantum does worse.
-/

namespace ConvoyEffect

/-- The convoy leader: a long job (burst 5) at the head of the queue. -/
def leader : AperiodicProcess := ⟨0, 0, 5, 5, by omega⟩

/-- A short job (burst 1) waiting behind it. -/
def shortJob : AperiodicProcess := ⟨1, 0, 1, 1, by omega⟩

/-- The convoy leader, with an arbitrary burst `L`. -/
def longJob (L : ℕ) (hL : 0 < L) : AperiodicProcess := ⟨0, 0, L, L, hL⟩

/-- A unit job that arrives at time 1, after the long job has started. -/
def lateShortJob : AperiodicProcess := ⟨1, 1, 1, 1, by omega⟩

/-- The late-arrival convoy: `longJob L` at time 0, `lateShortJob` at time 1. -/
def lateConvoyArrivalStream (L : ℕ) (hL : 0 < L) : ℕ → List AperiodicProcess
  | 0 => [longJob L hL]
  | 1 => [lateShortJob]
  | _ => []

/-- The convoy: `longJob L` ahead of `shortJob`, both arriving at time 0. -/
def convoyArrivalStream (L : ℕ) (hL : 0 < L) : ℕ → List AperiodicProcess
  | 0 => [longJob L hL, shortJob]
  | _ => []

/-- Two equal jobs of burst 2, arriving together. -/
def equalPair : ℕ → List AperiodicProcess
  | 0 => [⟨0, 0, 2, 2, by omega⟩, ⟨1, 0, 2, 2, by omega⟩]
  | _ => []

/-- Every job in the late-arrival convoy is either the long job at time 0 or
the short job at time 1. -/
theorem mem_lateConvoyArrivalStream {L : ℕ} {hL : 0 < L} {p : AperiodicProcess} {t : ℕ}
    (h : p ∈ lateConvoyArrivalStream L hL t) :
    (p = longJob L hL ∧ t = 0) ∨ (p = lateShortJob ∧ t = 1) := by
  rcases t with _ | _ | t <;> simp_all [lateConvoyArrivalStream]

theorem lateConvoyArrivalStream_wf (L : ℕ) (hL : 0 < L) :
    WellFormedStream (lateConvoyArrivalStream L hL) where
  consistent p t h := by
    rcases mem_lateConvoyArrivalStream h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  fresh p t h := by
    rcases mem_lateConvoyArrivalStream h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  unique p1 p2 t1 t2 h1 h2 h_id := by
    rcases mem_lateConvoyArrivalStream h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases mem_lateConvoyArrivalStream h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp_all [longJob, lateShortJob]

/-- Every job in the convoy arrives at time 0, and is the long or the short job. -/
theorem mem_convoyArrivalStream {L : ℕ} {hL : 0 < L} {p : AperiodicProcess} {t : ℕ}
    (h : p ∈ convoyArrivalStream L hL t) :
    t = 0 ∧ (p = longJob L hL ∨ p = shortJob) := by
  rcases t with _ | t <;> simp_all [convoyArrivalStream]

theorem convoyArrivalStream_wf (L : ℕ) (hL : 0 < L) :
    WellFormedStream (convoyArrivalStream L hL) where
  consistent p t h := by
    rcases mem_convoyArrivalStream h with ⟨rfl, rfl | rfl⟩ <;> rfl
  fresh p t h := by
    rcases mem_convoyArrivalStream h with ⟨rfl, rfl | rfl⟩ <;> rfl
  unique p1 p2 t1 t2 h1 h2 h_id := by
    rcases mem_convoyArrivalStream h1 with ⟨rfl, rfl | rfl⟩ <;>
      rcases mem_convoyArrivalStream h2 with ⟨rfl, rfl | rfl⟩ <;>
      simp_all [longJob, shortJob]

end ConvoyEffect
