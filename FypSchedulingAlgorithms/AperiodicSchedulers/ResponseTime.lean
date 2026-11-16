/-
Copyright (c) 2026 Choo Kye Yong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Choo Kye Yong
-/
import FypSchedulingAlgorithms.AperiodicSchedulers.ResponseTime.ResponseTimeSpec
import FypSchedulingAlgorithms.AperiodicSchedulers.ResponseTime.RRResponseTime
import FypSchedulingAlgorithms.AperiodicSchedulers.ResponseTime.FCFSResponseTime

/-!
# Response time: reading order

*Response time* is the time from a job's arrival until it first gets the CPU.  It is the
third property of a scheduler studied here, next to waiting (`ConvoyEffect/`) and whether
every job eventually runs (`Starvation/`).

1. **`ResponseTimeSpec` -- what is response time?**  `IsFirstDispatchAt σ i t`: schedule `σ`
   puts job `i` on the CPU after step `t`, and never before.  It is stated on schedules, so it
   applies to every scheduler through the schedule its run follows (`scheduleOfRun`,
   `runSchedule`).  A first dispatch is unique (`IsFirstDispatchAt.unique`); response time
   counts from the job's arrival (`HasResponseTime`).

2. **`RRResponseTime` -- Round Robin on a batch.**  Job `i` is first dispatched at step
   `sumOfFirstSlicesAhead quantum l i`, the sum of the first-round slices ahead of it
   (`rr_allArrivalsAtZero_isFirstDispatchAt`), and this step is monotone in the quantum
   (`rr_allArrivalsAtZero_firstDispatch_mono`).

3. **`FCFSResponseTime` -- FCFS on a batch, and RR with a large quantum.**  FCFS first
   dispatches job `i` at step `sumOfBurstsAhead l i` (`fcfs_allArrivalsAtZero_isFirstDispatchAt`);
   once the quantum covers every burst, RR first dispatches every job exactly when FCFS does
   (`rr_isFirstDispatchAt_iff_fcfs_of_large_quantum`).

## Round Robin's three properties

Response time is where Round Robin's quantum pays off; the other two properties do not see it.

* **No starvation** (`Starvation/`): every job of every well-formed stream completes, for every
  quantum (`RRStarvation.StarvationFree`).
* **Still a convoy effect** (`ConvoyEffect/`): RR dispatches the head of the queue whatever its
  burst, so it has the convoy effect at some dispatch for every quantum
  (`rr_hasConvoyEffectAtSomeDispatch`), and its waiting time is not monotone in the quantum: a
  smaller quantum can finish jobs later (`rr_smaller_quantum_not_better`).
* **Response time monotone in the quantum** (`ResponseTime/`): on a batch, a smaller quantum
  never delays any job's first dispatch (`rr_allArrivalsAtZero_firstDispatch_mono`), and the
  largest quanta give FCFS's (`rr_isFirstDispatchAt_iff_fcfs_of_large_quantum`).
-/
