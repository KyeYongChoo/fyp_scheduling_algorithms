import FypSchedulingAlgorithms.SchedState
import FypSchedulingAlgorithms.Step
import Std.Data.String

-- Test data: processes arriving at different times with different burst times
def testProcesses : List Process := [
  { id := 1, arrival := 0, burst := 8, remaining := 8 },
  { id := 2, arrival := 1, burst := 4, remaining := 4 },
  { id := 3, arrival := 2, burst := 2, remaining := 2 },
  { id := 4, arrival := 3, burst := 6, remaining := 6 },
  { id := 5, arrival := 5, burst := 3, remaining := 3 },
]

-- Initialize scheduler state with first arriving process
def initState : SchedState := {
  time      := 0
  ready     := []
  running   := none
  completed := []
}

-- Helper: add processes that have arrived by a given time to ready queue
def addArrivals (s : SchedState) (processes : List Process) : SchedState := {
  s with ready := s.ready ++ (processes.filter fun p => p.arrival = s.time)
}

-- Run scheduler for n steps, adding arrivals dynamically
def runSteps (scheduler : SchedState → SchedState) (n : Nat)
             (processes : List Process) : List SchedState :=
  let rec loop (steps : Nat) (state : SchedState) (states : List SchedState) : List SchedState :=
    if steps = 0 then states
    else
      let newState := addArrivals state processes
      let nextState := scheduler newState
      loop (steps - 1) nextState (states ++ [nextState])
  loop n initState [initState]

-- Calculate how many ticks this process has used
def ticksUsed (p : Process) : Nat :=
  p.burst - p.remaining

-- Display state with tick counts
def stateWithTicks (s : SchedState) : String :=
  let allProcesses := s.ready ++ s.completed ++ (s.running.toList)
  let tickInfo := allProcesses.map fun p =>
    toString "P" ++ toString p.id ++ ": " ++ toString (ticksUsed p) ++ "/" ++ toString (p.burst) ++ " ticks"
  let running := s.running.map (toString ·.id) |>.getD "idle" |> toString
  "[t=" ++ toString s.time ++ "] Running: " ++ running ++ " | Ticks: " ++ (" | ".intercalate tickInfo)

#eval (runSteps stepSRTF 30 testProcesses).map stateWithTicks

-- run SRTF for 30 ticks
#eval (runSteps stepSRTF 30 testProcesses).map fun s =>
  (s.time, s.running.map (·.id), s.ready.map (·.id), s.completed.length)

-- CSV output

def stateToCSV (s : SchedState) : String :=
  let running := s.running.map (·.id) |>.getD 0 |> toString
  let readyIds := ",".intercalate (s.ready.map (·.id) |> List.map toString)
  let completedIds := ",".intercalate (s.completed.map (·.id) |> List.map toString)

  -- Tick information for all processes, sorted by ID
  let allProcesses := s.ready ++ s.completed ++ (s.running.toList)
  let sortedProcesses := List.mergeSort allProcesses (fun p1 p2 => p1.id < p2.id)
  let tickInfo := sortedProcesses.map fun p =>
    "P" ++ toString p.id ++ ":" ++ toString (ticksUsed p) ++ "/" ++ toString (p.burst)
  let tickField := "|".intercalate tickInfo

  -- Wrap lists in quotes
  let readyField := "\"" ++ readyIds ++ "\""
  let completedField := "\"" ++ completedIds ++ "\""
  let ticksField := "\"" ++ tickField ++ "\""

  toString s.time ++ "," ++ running ++ "," ++ readyField ++ "," ++ completedField ++ "," ++ ticksField

def outputCSV (states : List SchedState) : String :=
  let header := "time,running,ready_queue,completed,process_ticks"
  let rows := states.map stateToCSV
  (header :: rows) |> "\n".intercalate

def writeCSV (filename : String) (content : String) : IO Unit := do
  IO.FS.writeFile filename content

#eval writeCSV "SRTFschedule.csv" (outputCSV (runSteps stepSRTF 30 testProcesses))

#eval writeCSV "SJFschedule.csv" (outputCSV (runSteps stepSJF 30 testProcesses))

#eval writeCSV "FCFSschedule.csv" (outputCSV (runSteps stepFCFS 30 testProcesses))

-- For RR, need to track quantum usage, so there is a separate function

-- Add arrivals to the SchedState inside RRState
def addArrivalsRR (rs : RRState) (processes : List Process) : RRState :=
  let newSched := addArrivals rs.sched processes
  { rs with sched := newSched }

def runStepsRR (quantum : Nat) (n : Nat)
               (processes : List Process) : List SchedState :=
  let rec loop (steps : Nat) (rrState : RRState) (states : List SchedState) : List SchedState :=
    if steps = 0 then states
    else
      let newRRState := addArrivalsRR rrState processes
      let nextRRState := stepRR quantum newRRState
      loop (steps - 1) nextRRState (states ++ [nextRRState.sched])
  let initialRR : RRState := { sched := initState, quantum := quantum, ticksUsed := 0 }
  loop n initialRR [initState]

#eval writeCSV "RRschedule_q3.csv" (outputCSV (runStepsRR 3 30 testProcesses))
