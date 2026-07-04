import FypSchedulingAlgorithms.Process
import FypSchedulingAlgorithms.SchedState

-- Non-preemptive schedulers
def step (select : List AperiodicProcess → Option AperiodicProcess) : SchedState → SchedState :=
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

-- preemptive schedulers:
def stepPreemptive (process_type : Type) [Process process_type] (priority_func : process_type -> Nat): SchedStateG process_type -> SchedStateG process_type :=
  fun state_before =>
    let candidates := state_before.ready ++ (state_before.running.toList)
    let next_run := candidates.foldl (fun best p =>
      match best with
       | none => some p
       | some b => if priority_func p < priority_func b then some b else some p)
       none
    match next_run with
      | none =>
        {state_before with time := state_before.time + 1}
      | some p =>
        let newReady :=
          match state_before.running with
            | none => state_before.ready.removeFirst p
            | some b =>
              if b == p then state_before.ready
              else
                state_before.ready.removeFirst p ++ [b]
        if Process.remaining p ≤ 1 then
          {
            state_before with
              time := state_before.time + 1
              ready := newReady
              running := none
              completed := Process.onComplete p state_before.completed
          }
        else
          {
            state_before with
              time := state_before.time + 1
              ready := newReady
              running := some p
          }




-- ─── SRTF (preemptive: on every tick, pick shortest remaining time) ───────────
def stepSRTF : SchedState → SchedState :=
  fun s =>
    -- gather all candidates: currently running (if any) + ready queue
    let candidates : List AperiodicProcess :=
      s.ready ++ (s.running.toList)
    let shortest : Option AperiodicProcess :=
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
      let newReady : List AperiodicProcess :=
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
