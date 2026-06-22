import FypSchedulingAlgorithms.Process
import FypSchedulingAlgorithms.SchedState

-- Assumes these exist:
-- structure Process where name : String; remaining : Nat
-- structure SchedState where time : Nat; running : Option Process; ready : List Process; completed : List Process
-- deriving BEq on Process

-- Helper: remove the first matching element from a list
def List.removeFirst [BEq α] (a : α) : List α → List α
  | []      => []
  | x :: xs => if x == a then xs else x :: xs.removeFirst a

-- ─── Vanilla (non-preemptive, policy chosen by `select`) ─────────────────────
def step (select : List Process → Option Process) : SchedState → SchedState :=
  fun s =>
    match s.running with
    | none =>
      match select s.ready with          -- ask the policy for a choice
      | none   => { s with time := s.time + 1 }   -- idle tick (ready is empty)
      | some p => { s with time    := s.time + 1,
                           running := some p,
                           ready   := s.ready.removeFirst p }
    | some p =>
      if p.remaining ≤ 1 then
        { s with time      := s.time + 1,
                 running   := none,
                 completed := s.completed ++ [{ p with remaining := 0 }] }
      else
        { s with time    := s.time + 1,
                 running := some { p with remaining := p.remaining - 1 } }

-- ─── SRTF (preemptive: on every tick, pick shortest remaining time) ───────────
def stepSRTF : SchedState → SchedState :=
  fun s =>
    -- gather all candidates: currently running (if any) + ready queue
    let candidates : List Process :=
      s.ready ++ (s.running.toList)
    let shortest : Option Process :=
      candidates.foldl (fun best p =>
        match best with
        | none   => some p
        | some b => if p.remaining < b.remaining then some p else some b)
        none
    match shortest with
    | none =>                                        -- nothing to run
      { s with time := s.time + 1 }
    | some p =>
      -- preempt: put the old runner back in ready (if it's different)
      let newReady : List Process :=
        match s.running with
        | none      => s.ready.removeFirst p
        | some curr =>
          if curr == p then s.ready                 -- same process keeps running
          else s.ready.removeFirst p ++ [curr]      -- preempt: evict curr
      if p.remaining ≤ 1 then
        { s with time      := s.time + 1,
                 running   := none,
                 ready     := newReady,
                 completed := s.completed ++ [{ p with remaining := 0 }] }
      else
        { s with time    := s.time + 1,
                 running := some { p with remaining := p.remaining - 1 },
                 ready   := newReady }

-- ─── Round Robin ─────────────────────────────────────────────────────────────
-- RR needs a quantum counter; extend SchedState or use a wrapper
structure RRState where
  sched      : SchedState
  quantum    : Nat          -- max ticks per slice
  ticksUsed  : Nat          -- ticks the current process has used this slice
  deriving Repr

def stepRR (q : Nat) : RRState → RRState :=
  fun rs =>
    let s := rs.sched
    match s.running with
    | none =>
      match s.ready with
      | []      => { rs with sched := { s with time := s.time + 1 } }   -- idle
      | p :: ps => { rs with sched     := { s with time    := s.time + 1,
                                                   running := some p,
                                                   ready   := ps },
                             ticksUsed := 1 }
    | some p =>
      if p.remaining ≤ 1 then                           -- process finishes
        { rs with sched     := { s with time      := s.time + 1,
                                        running   := none,
                                        completed := s.completed ++
                                                       [{ p with remaining := 0 }] },
                  ticksUsed := 0 }
      else if rs.ticksUsed ≥ q then                     -- quantum expired → preempt
        match s.ready with
        | []      =>                                     -- no one else: keep running
          { rs with sched     := { s with time    := s.time + 1,
                                          running := some { p with remaining :=
                                                              p.remaining - 1 } },
                    ticksUsed := 1 }
        | nx :: ps =>                                    -- rotate
          { rs with sched     := { s with time    := s.time + 1,
                                          running := some nx,
                                          ready   := ps ++ [{ p with remaining :=
                                                                p.remaining - 1 }] },
                    ticksUsed := 1 }
      else                                               -- normal tick
        { rs with sched     := { s with time    := s.time + 1,
                                        running := some { p with remaining :=
                                                            p.remaining - 1 } },
                  ticksUsed := rs.ticksUsed + 1 }

def selectFCFS : List Process → Option Process
  | [] => none
  | p :: _ => some p

def stepFCFS : SchedState → SchedState :=
  step selectFCFS

def selectSJF : List Process → Option Process :=
  fun ps =>
    ps.foldl (fun best p =>
      match best with
      | none   => some p
      | some b => if p.burst < b.burst then some p else some b)
      none

def stepSJF : SchedState → SchedState :=
  step selectSJF
