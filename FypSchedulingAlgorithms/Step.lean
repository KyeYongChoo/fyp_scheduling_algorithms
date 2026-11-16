/-
Copyright (c) 2026 Choo Kye Yong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Choo Kye Yong
-/
import FypSchedulingAlgorithms.Process
import FypSchedulingAlgorithms.SchedState
-- The linear order on ℤ, the type of priorities.  It is the only Mathlib import of the base
-- modules, so it also brings basic Mathlib to the files that import `Step`.  Files known to
-- need more (`split_ifs`, `push`, `tauto`, `f^[n]`) import those modules themselves.
import Mathlib.Data.Int.Order.Basic

/-!
# Scheduling Generic Functions

This file defines `stepNonPreemptive` and `stepPreemptive`,
which are used to define more specific scheduling algorithms and takes
an argument `select` or `priority_fun`.

`select` is used for `stepNonPreemptive` rather than `priority_fun`
because FCFS priority is not dependent on the processes but rather the
order in which it arrives.

The preemptive version of FCFS, which is Round Robin, differs enough from
other preemptive algorithms that it is built independently from
`stepNonPreemptive` and `stepPreemptive`

## Tick convention

Every step function (`stepNonPreemptive`, `stepPreemptive`, and `stepRR` in
`AperiodicStep`) follows the same convention, one tick of CPU time per step:

1. tick the job that was running at the start of the step, if any;
2. if that finished it, move it to `completed`;
3. decide who runs next (keep it, preempt it, or dispatch into an idle CPU).

A job newly put on the CPU in a step -- dispatched from idle, after a completion,
or by preemption -- is **not** ticked in that step; its first tick is in the next
step.  So the state after a step shows who holds the CPU *going into* the next tick.

## Runs

`runSteps arrival_stream step` runs a step function on an *arrival stream*
`ℕ → List α`, the jobs arriving at each time: infinitely many in total, finitely
many at a time.  `runSteps arrival_stream step t` is the state **after** step `t`,
so step 0 is already a step and the state after step `t` reads `time = t + 1`; see
the docstring of `runSteps`.

## Arrival streams

`arrivedBy` collects the jobs released by a given time, and `WellFormedStream` says
when a stream is a plausible input.  A *batch* (`AllArrivalsAtZero`) is a list of fresh
jobs with distinct ids, all present at time 0; `allArrivalsAtZeroStream` releases one at
time 0 and nothing afterwards, which is a well-formed stream
(`allArrivalsAtZeroStream_wf`).
-/

/-- The jobs released by time `t`, in order of release. -/
def arrivedBy (arrival_stream : ℕ → List AperiodicProcess) (t : ℕ) : List AperiodicProcess :=
  (List.range (t + 1)).flatMap arrival_stream

/-- Step 0 has seen the releases of time 0. -/
@[simp] theorem arrivedBy_zero (arrival_stream : ℕ → List AperiodicProcess) :
    arrivedBy arrival_stream 0 = arrival_stream 0 := by
  simp [arrivedBy]

/-- One more step, one more release. -/
theorem arrivedBy_succ (arrival_stream : ℕ → List AperiodicProcess) (t : ℕ) :
    arrivedBy arrival_stream (t + 1) = arrivedBy arrival_stream t ++ arrival_stream (t + 1) := by
  simp [arrivedBy, List.range_succ, List.flatMap_append]

/-- The jobs released by time `t` are those of the releases at times `t' ≤ t`. -/
theorem mem_arrivedBy {arrival_stream : ℕ → List AperiodicProcess} {t : ℕ}
    {p : AperiodicProcess} : p ∈ arrivedBy arrival_stream t ↔ ∃ t' ≤ t, p ∈ arrival_stream t' := by
  simp [arrivedBy, Nat.lt_succ_iff]

/-- The release at time `t` is part of the jobs released by time `t`. -/
theorem sublist_arrivedBy (arrival_stream : ℕ → List AperiodicProcess) (t : ℕ) :
    (arrival_stream t).Sublist (arrivedBy arrival_stream t) := by
  cases t with
  | zero => simp
  | succ t => rw [arrivedBy_succ]; exact List.sublist_append_right _ _

/-- An arrival stream is **well formed** when it is a plausible input: every job
arriving at time `t` carries `arrival = t` (`consistent`), arrives untouched, with
`remaining = burst` (`fresh`), and no id is released twice: the ids of the jobs released
by any time are distinct (`ids_nodup`).  So a job is never announced twice, neither at
two times (`WellFormedStream.unique`) nor twice in one release
(`WellFormedStream.nodup`); results that name jobs by id need both.  Most results
assume a well-formed stream: an ill-formed one can re-announce a job forever, or hand it
a `remaining` that disagrees with its `burst`.  `WellFormedStream.of_unique_of_nodup`
builds one from the two separate facts. -/
structure WellFormedStream (arrival_stream : ℕ → List AperiodicProcess) : Prop where
  consistent : ∀ (p : AperiodicProcess) (t : ℕ), p ∈ arrival_stream t → p.arrival = t
  fresh : ∀ (p : AperiodicProcess) (t : ℕ), p ∈ arrival_stream t → p.remaining = p.burst
  ids_nodup : ∀ t, ((arrivedBy arrival_stream t).map AperiodicProcess.id).Nodup

namespace WellFormedStream

variable {arrival_stream : ℕ → List AperiodicProcess}

/-- In a list whose ids are distinct, two jobs with the same id are the same job. -/
theorem eq_of_mem_of_ids_nodup {l : List AperiodicProcess} (h : (l.map AperiodicProcess.id).Nodup)
    {p q : AperiodicProcess} (hp : p ∈ l) (hq : q ∈ l) (h_id : p.id = q.id) : p = q := by
  induction l with
  | nil => simp at hp
  | cons a l ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at h
    rcases List.mem_cons.mp hp with rfl | hp' <;> rcases List.mem_cons.mp hq with rfl | hq'
    · rfl
    · exact absurd h_id.symm (h.1 q hq')
    · exact absurd h_id (h.1 p hp')
    · exact ih h.2 hp' hq'

/-- No job is released twice by any time. -/
theorem arrivedBy_nodup (h_wf : WellFormedStream arrival_stream) (t : ℕ) :
    (arrivedBy arrival_stream t).Nodup :=
  (List.pairwise_map.mp (h_wf.ids_nodup t)).imp fun h_ne h_eq =>
    h_ne (congrArg AperiodicProcess.id h_eq)

/-- No job is listed twice in one release. -/
theorem nodup (h_wf : WellFormedStream arrival_stream) (t : ℕ) : (arrival_stream t).Nodup :=
  (h_wf.arrivedBy_nodup t).sublist (sublist_arrivedBy arrival_stream t)

/-- An id is never announced twice except as the same job at the same time. -/
theorem unique (h_wf : WellFormedStream arrival_stream) (p1 p2 : AperiodicProcess) (t1 t2 : ℕ)
    (h1 : p1 ∈ arrival_stream t1) (h2 : p2 ∈ arrival_stream t2)
    (h_id : Process.id p1 = Process.id p2) : t1 = t2 ∧ p1 = p2 := by
  have hp1 : p1 ∈ arrivedBy arrival_stream (max t1 t2) :=
    mem_arrivedBy.mpr ⟨t1, Nat.le_max_left _ _, h1⟩
  have hp2 : p2 ∈ arrivedBy arrival_stream (max t1 t2) :=
    mem_arrivedBy.mpr ⟨t2, Nat.le_max_right _ _, h2⟩
  have h_eq : p1 = p2 := eq_of_mem_of_ids_nodup (h_wf.ids_nodup _) hp1 hp2 h_id
  subst h_eq
  exact ⟨(h_wf.consistent p1 t1 h1).symm.trans (h_wf.consistent p1 t2 h2), rfl⟩

/-- **Building a well-formed stream** from the two halves of `ids_nodup`: an id is never
announced at two times or as two jobs (`unique`), and no release lists a job twice
(`nodup`). -/
theorem of_unique_of_nodup
    (consistent : ∀ (p : AperiodicProcess) (t : ℕ), p ∈ arrival_stream t → p.arrival = t)
    (fresh : ∀ (p : AperiodicProcess) (t : ℕ), p ∈ arrival_stream t → p.remaining = p.burst)
    (unique : ∀ (p1 p2 : AperiodicProcess) (t1 t2 : ℕ),
      p1 ∈ arrival_stream t1 → p2 ∈ arrival_stream t2 →
      Process.id p1 = Process.id p2 → t1 = t2 ∧ p1 = p2)
    (nodup : ∀ t, (arrival_stream t).Nodup) :
    WellFormedStream arrival_stream := by
  refine ⟨consistent, fresh, fun t => ?_⟩
  have h_nodup : (arrivedBy arrival_stream t).Nodup := by
    induction t with
    | zero => simpa using nodup 0
    | succ t ih =>
      rw [arrivedBy_succ]
      refine List.nodup_append.mpr ⟨ih, nodup _, fun p hp q hq h_eq => ?_⟩
      subst h_eq
      obtain ⟨t', ht', hp⟩ := mem_arrivedBy.mp hp
      have h1 := consistent p _ hp
      have h2 := consistent p _ hq
      omega
  rw [List.Nodup, List.pairwise_map]
  refine h_nodup.imp_of_mem fun {p q} hp hq h_ne h_id => h_ne ?_
  obtain ⟨t1, -, hp⟩ := mem_arrivedBy.mp hp
  obtain ⟨t2, -, hq⟩ := mem_arrivedBy.mp hq
  exact (unique p q t1 t2 hp hq h_id).2

end WellFormedStream

/-! ## All arrivals at zero -/

/-- A **batch**: jobs that all arrive at time 0, untouched (`remaining = burst`),
with distinct ids.  These are the ready queues a scheduler can actually face at
the start of a well-formed run (`allArrivalsAtZeroStream_wf`). -/
def AllArrivalsAtZero (ready : List AperiodicProcess) : Prop :=
  (∀ p ∈ ready, p.arrival = 0 ∧ p.remaining = p.burst) ∧ (ready.map (·.id)).Nodup

/-- The arrival stream that releases `ready` at time 0 and nothing afterwards. -/
def allArrivalsAtZeroStream (ready : List AperiodicProcess) : ℕ → List AperiodicProcess
  | 0 => ready
  | _ => []

/-- A job of the batch stream is released at time 0 and belongs to the batch. -/
theorem mem_allArrivalsAtZeroStream {ready : List AperiodicProcess} {p : AperiodicProcess} {t : ℕ}
    (h : p ∈ allArrivalsAtZeroStream ready t) : t = 0 ∧ p ∈ ready := by
  rcases t with _ | t <;> simp_all [allArrivalsAtZeroStream]

/-- Releasing a batch at time 0 is a well-formed arrival stream. -/
theorem allArrivalsAtZeroStream_wf {ready : List AperiodicProcess}
    (h_atZero : AllArrivalsAtZero ready) :
    WellFormedStream (allArrivalsAtZeroStream ready) :=
  .of_unique_of_nodup
    (fun p t h => by
      obtain ⟨rfl, hp⟩ := mem_allArrivalsAtZeroStream h
      exact (h_atZero.1 p hp).1)
    (fun p t h => (h_atZero.1 p (mem_allArrivalsAtZeroStream h).2).2)
    (fun p1 p2 t1 t2 h1 h2 h_id => by
      obtain ⟨rfl, hp1⟩ := mem_allArrivalsAtZeroStream h1
      obtain ⟨rfl, hp2⟩ := mem_allArrivalsAtZeroStream h2
      exact ⟨rfl, WellFormedStream.eq_of_mem_of_ids_nodup h_atZero.2 hp1 hp2 h_id⟩)
    (fun t => by
      rcases t with _ | t
      · exact (List.pairwise_map.mp h_atZero.2).imp fun h_ne h_eq =>
          h_ne (congrArg AperiodicProcess.id h_eq)
      · simp [allArrivalsAtZeroStream])

def default_num_steps := 30

/-- The candidate with the *highest* `priority_func` value; among equal-priority
candidates the **earliest** in the list wins (FIFO ties): a later candidate replaces
the best so far only if its priority is strictly higher. -/
def selectByPriority {process_type} (priority_func : process_type → ℤ)
    (candidates : List process_type) : Option process_type :=
  candidates.foldl (fun best p =>
    match best with
    | none   => some p
    | some b => if priority_func b < priority_func p then some p else some b)
    none

-- Non-preemptive schedulers
def stepNonPreemptive [Process AperiodicProcess]
    (select : List AperiodicProcess → Option AperiodicProcess) :
  SchedState → SchedState :=
  fun s =>
    match s.running with
    | none =>
      match select s.ready with          -- ask the policy for a choice
      | none   => { s with time := s.time + 1 }   -- idle tick (ready is empty)
      | some p => { s with time    := s.time + 1,
                           running := some p,
                           ready   := s.ready.erase p }
    | some p =>
      let p := Process.tick p
      if Process.remaining p ≤ 0 then
        -- immediately look for next process - no context switch time
        match select s.ready with          -- ask the policy for a choice
        | none   => { s with
                      time      := s.time + 1
                      running   := none
                      completed := s.completed ++ [p]
                    }
        | some q => { s with
                      time := s.time + 1
                      running := some q
                      ready   := s.ready.erase q
                      completed := s.completed ++ [p]
                    }
      else
        { s with time    := s.time + 1,
                 running := some p }

/-- **Non-preemptive scheduler with a state-select policy.** Like `stepNonPreemptive`,
but the policy
`select` sees the whole state at the start of the step -- time, ready queue, the
running job (which may be finishing this step) and the completed jobs, i.e.
everything known so far -- rather than just the ready queue.  It may also leave
the CPU idle on purpose, by returning `none` while jobs are waiting.  Jobs are
still never preempted, and the tick convention is the same.  Every
`stepNonPreemptive sel` is an instance (`stepNonPreemptive_eq_stateSelect`). -/
def stepNonPreemptiveStateSelect (select : SchedState → Option AperiodicProcess) :
  SchedState → SchedState :=
  fun s =>
    match s.running with
    | none =>
      match select s with
      | none   => { s with time := s.time + 1 }   -- idle tick
      | some p => { s with time    := s.time + 1,
                           running := some p,
                           ready   := s.ready.erase p }
    | some p =>
      let p := Process.tick p
      if Process.remaining p ≤ 0 then
        match select s with
        | none   => { s with
                      time      := s.time + 1
                      running   := none
                      completed := s.completed ++ [p]
                    }
        | some q => { s with
                      time := s.time + 1
                      running := some q
                      ready   := s.ready.erase q
                      completed := s.completed ++ [p]
                    }
      else
        { s with time    := s.time + 1,
                 running := some p }

/-- A policy that looks only at the ready queue is a state-select policy that ignores
the rest of the state. -/
theorem stepNonPreemptive_eq_stateSelect
    (select : List AperiodicProcess → Option AperiodicProcess) :
    stepNonPreemptive select = stepNonPreemptiveStateSelect (fun s => select s.ready) := rfl

/-- **Preemptive scheduler** driven by a priority function: the candidate with the
*highest* `priority_func` value gets the CPU.  It follows the tick convention in the
module docstring:

1. the job running at the start of the step (if any) is ticked;
2. if that finished it, it moves to `completed` and the best job in `ready` (if any) is
   dispatched;
3. otherwise the best job in `ready` preempts it only if it has *strictly* higher
   priority than the ticked job, which then goes to the back of `ready`.

Step 3 is the same as choosing `selectByPriority priority_func (running :: ready)`
with ties going to the running job (it is scanned first, and ties go to the earliest
candidate), see `Preemptive.selectByPriority_cons`; spelling it as a comparison avoids
testing jobs for equality.  Among the jobs in `ready`, ties go to the one nearest the
front of the queue.  A job newly put on the CPU is not ticked until the next
step. -/
def stepPreemptive (process_type : Type) [Process process_type]
  (priority_func : process_type → ℤ) :
  SchedStateG process_type → SchedStateG process_type :=
  fun s =>
    match s.running with
    | none =>
      match selectByPriority priority_func s.ready with
      | none   => { s with time := s.time + 1 }   -- idle tick (ready is empty)
      | some p => { s with time    := s.time + 1,
                           running := some p,
                           ready   := s.ready.erase p }
    | some b =>
      let b := Process.tick b
      if Process.remaining b ≤ 0 then
        -- immediately look for next process - no context switch time
        match selectByPriority priority_func s.ready with
        | none   => { s with
                      time      := s.time + 1
                      running   := none
                      completed := s.completed ++ [b] }
        | some q => { s with
                      time      := s.time + 1
                      running   := some q
                      ready     := s.ready.erase q
                      completed := s.completed ++ [b] }
      else
        match selectByPriority priority_func s.ready with
        | none   => { s with time := s.time + 1, running := some b }
        | some q =>
          if priority_func b < priority_func q then
            -- preemption: `q` takes the CPU unticked, `b` rejoins the queue
            { s with
                time    := s.time + 1
                running := some q
                ready   := s.ready.erase q ++ [b] }
          else
            { s with time := s.time + 1, running := some b }

/-- The **run** of `scheduler` on `arrivalStream`: `runSteps arrivalStream scheduler t`
is the state **after step `t`**.  Step `t` appends the jobs arriving at time `t` to the
back of `ready`, then applies `scheduler` once; step 0 starts from the initial state
(time 0, nothing on the CPU, nothing completed).

So step 0 is already a step.  For every step function in this library the clock
advances by one per step, so the state after step `t` reads `time = t + 1` and has seen
the arrivals of times `0, …, t`.  By the tick convention above, the job on the CPU in
that state receives the tick of step `t + 1`, and the jobs in its `ready` queue wait
through it.  Every statement about "step `t`" or "the state after step `t`" uses this
numbering; the state that step `t` is applied to is `stateBefore` (`RunStepsLemmas`).
The sample-schedule CSVs print the state after step `k` on the row `time = k + 1`. -/
def runSteps {process_type} [SchedStateMethods process_type] (arrivalStream : ℕ → List process_type)
    (scheduler : SchedStateG process_type → SchedStateG process_type) : ℕ → SchedStateG process_type
  -- fold over the time stream
  | 0     => scheduler {SchedStateMethods.init with ready := arrivalStream 0 }
  | n + 1 =>
    let prev := runSteps arrivalStream scheduler n
    scheduler { prev with ready := prev.ready ++ arrivalStream (n + 1) }

def runStepsAccumulateResults {process_type} [SchedStateMethods process_type] [Process process_type]
    (arrivalStream : ℕ → List process_type)
    (scheduler : SchedStateG process_type → SchedStateG process_type)
    (n : Nat := default_num_steps):
    List (SchedStateG process_type) :=
  (List.range (n + 1)).map (runSteps arrivalStream scheduler)
