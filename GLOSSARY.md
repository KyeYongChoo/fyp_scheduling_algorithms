# Glossary

The terms the proofs use, each with the Lean name that defines it and the file it lives in.
The docstring at the definition is the precise version; this page is a map to it. Paths are
relative to `FypSchedulingAlgorithms/`.

## Time, steps and runs

**Step.** One call of a step function: one tick of CPU time. Steps are numbered from 0.

**State after step `t`.** `runSteps arrival_stream step t` (`Step.lean`). Step `t` adds the arrivals of
time `t` to the back of `ready`, then applies `step`. Step 0 is already a step, so the state
after step `t` reads `time = t + 1` and has seen the arrivals of times `0, …, t`. This is the
off-by-one to keep in mind everywhere. The CSVs print it on the row `time = t + 1`.

**State before step `t`.** `stateBefore arrival_stream step t` (`RunStepsLemmas.lean`). The state that
step `t` is applied to, i.e. the state in which the scheduler makes its decision at time `t`.

**Tick convention.** Module doc of `Step.lean`. A step (1) ticks the job that was running,
(2) retires it if that finished it, then (3) decides who runs next. A job put on the CPU in a
step is *not* ticked in that step; its first tick comes in the next step. So the job on the CPU
after step `t` gets the tick of step `t + 1`, and the jobs in `ready` wait through it.

**Dispatch latency.** The tick convention means a job released at time `r` cannot be ticked
before step `r + 1`. Every run and every schedule has this delay, so it shifts the time axis
for everyone and handicaps no one. The periodic miss rule absorbs it (see *Miss rule*).

**Run, run function.** A run is the sequence of states of a scheduler on a stream. A *run
function* `run : (ℕ → List AperiodicProcess) → ℕ → SchedState` gives the state after each step.
Properties are stated over run functions so that Round Robin, whose state is an `RRState`, fits
too (`fun arrival_stream t => (runStepsRR q arrival_stream t).sched`).

**Horizon.** The `T` in `runWait run arrival_stream T`, `schedWait arrival_stream σ T`, `waitFrom step s T`: the number
of steps measured (steps `0, …, T - 1`). Waiting after that is not counted. Results say at which
horizons they hold: *every* `T`, once `T` covers the total work, or from a threshold such as
`T ≥ 4` (`NoOptimalNonPreemptiveOnEveryStream`).

**Drained.** Nothing waits and nothing more arrives. From then on a run's wait stops growing
(`runWait_stateSelect_eq_of_drained`).

## Jobs and arrival streams

**Job, process.** An `AperiodicProcess` or `PeriodicProcess` (`Process.lean`). The README says
"process" and the proofs mostly say "job"; they are the same thing. A periodic *task* releases
many *jobs* (see *Task*).

**`burst`, `remaining`.** Total work, and work still to do. A tick lowers `remaining` by one.
SJF compares `burst`; SRTF and the convoy definitions compare `remaining`, because a preempted
job re-enters the queue part-done.

**Fresh, untouched.** `remaining = burst`: the job has not been ticked yet. Arrivals are fresh,
and in a non-preemptive run every waiting job stays fresh (`nonPreemptiveStateSelect_ready_fresh`).

**Matched by id.** Ticking changes `remaining`, so "the same job later on" means "a job with
the same `id`", not `=`.

**Arrival stream.** `ℕ → List AperiodicProcess`: the jobs arriving at each time. There can be
infinitely many in total, but only finitely many at each time.

**Well-formed stream.** `WellFormedStream` (`Step.lean`). Each arrival has `arrival` equal to
its arrival time, is fresh, and an id is never announced twice except as the same job at the
same time. Most theorems assume it.

**No repeats.** `NoRepeats` (`ConvoyEffect/Schedules.lean`). No job is listed twice *in one
release*, which `WellFormedStream` still allows. It is needed wherever jobs are named by id
(admissible schedules).

**All arrivals at zero (a *batch*).** `AllArrivalsAtZero` (`ConvoyEffect/ConvoySpec.lean`).
Fresh jobs with distinct ids, all present at time 0. `allArrivalsAtZeroStream l` releases `l`
at time 0 and nothing afterwards. The textbook term, and the word the comments use, is
*batch*.

**Instance known at time `t`.** `knownAt arrival_stream t` (`RunStepsLemmas.lean`). The stream with every
arrival after `t` deleted. A run cannot see the future, so up to step `t` it is the same on
`arrival_stream` and on `knownAt arrival_stream t` (`runSteps_knownAt`).

**Witness.** A concrete stream or task set that proves something exists or is a
counterexample, such as `streamA`, `streamB`, `starvation_stream` or `rmsFailsEdfSucceeds`. The
shared ones live in the `*Witnesses.lean` files.

## Schedulers

**Selection policy, `select`.** `List AperiodicProcess → Option AperiodicProcess`: which
waiting job to dispatch. It is handed to `stepNonPreemptive`, which is how FCFS and SJF are
built. `none` means "nothing to dispatch".

**Non-preemptive state-select policy.** A `select : SchedState → Option AperiodicProcess` run by
`stepNonPreemptiveStateSelect` (`runStateSelect` for its run) that only ever picks a waiting job
(`DrawsFromReadyQueue`, `ConvoyEffect/NoOptimalNonPreemptiveOnEveryStream.lean`). It sees the
current state, including the bursts of jobs that have arrived, but not future arrivals; that
comes from its type, not from `DrawsFromReadyQueue`. It may **idle on purpose**, returning
`none` while jobs wait. Every `stepNonPreemptive sel` is one (`stepNonPreemptive_eq_stateSelect`).

**Online (textbook term).** The literature calls a scheduler that cannot see future arrivals
*online*. This repo avoids the word: such policies are called *state-select*, or are said to
see only the current state. The contrast is *clairvoyant*.

**Clairvoyant.** Knows the whole stream in advance. Admissible schedules may be clairvoyant;
step functions are not.

**Priority function.** `f : α → ℤ`, handed to `stepPreemptive`. The **highest** value runs, so
"smallest field wins" is written `fun p => -(field p : ℤ)` (SRTF: `-remaining`; RM: `-period`;
DM: `-deadline`; EDF: `-(arrival + deadline)`).

**Ties.** `selectByPriority` and `selectSJF` prefer the candidate nearest the front of the
queue. `stepPreemptive` keeps the running job unless a waiting one is *strictly* better. These
dynamic tie-breaks matter for fixed priorities (see *Strict*).

**Dispatch, dispatch moment.** `DispatchesAt` (`ConvoyEffect/ConvoySpec.lean`). A job is
dispatched at step `t` if it holds the CPU after step `t` and a different job (or none) held it
after step `t - 1`. This covers dispatch into an idle CPU, after a completion and by preemption.
A job that keeps the CPU is not dispatched again.

**Work-conserving.** The CPU is never idle while a job waits. Preemptive schedulers are
(`runSteps_ready_nil_of_idle`), and so are FCFS and SJF (`idle_implies_empty_ready`).
State-select policies that idle on purpose are not.

**Job-conserving.** `ConservesJobs` (`PreemptiveRuns.lean`, `ConvoyEffect/Schedules.lean`). A
step neither invents nor loses jobs: the jobs in the system afterwards are those before, with
the running job ticked and dropped exactly when it finished. **Not the same as
work-conserving:** a state-select policy that idles on purpose is job-conserving but not
work-conserving. Job conservation is what makes a run an admissible schedule.

**Priority run invariant.** `runSteps_running_max` (`PreemptiveRuns.lean`). In every state of a
`stepPreemptive f` run, the running job's priority is at least that of every waiting job. It
needs no hypothesis on `f`.

**Quantum, slice.** Round Robin's time limit per turn, and one such turn. `ticksUsed` in
`RRState` counts the ticks of the current slice. A quantum of 0 behaves like 1.

## Measuring waiting

Five measures, from pure arithmetic to real runs:

| Name | File | What it counts |
| --- | --- | --- |
| `totalWait bs` | `ConvoyEffect/TotalWait.lean` | A batch run back-to-back from time 0 in list order: each job waits for the bursts ahead of it. No horizon. |
| `truncWait r bs T` | `ConvoyEffect/SJFOptimalityGivenSamePast.lean` | The same, after a job with `r` ticks left finishes, cut off at horizon `T`. |
| `waitFrom step s T` | `ConvoyEffect/RunWait.lean` | The `ready` lengths of `s, step s, step (step s), …`: the wait still to come from state `s`, with no arrivals. |
| `runWait run arrival_stream T` | `ConvoyEffect/RunWait.lean` | The `ready` lengths of the states after steps `0, …, T - 1` of a real run. **The cost in every headline theorem.** |
| `schedWait arrival_stream σ T` | `ConvoyEffect/Schedules.lean` | For an admissible schedule: each step, every unfinished job not on the CPU waits. Equal to `runWait` on runs (`runWait_eq_schedWait`). |

The bridges between them are `runWait_allArrivalsAtZero_eq_totalWait` (a batch run waits `totalWait` of its
dispatch order), `waitFrom_eq_truncWait` and `runWait_eq_schedWait`.

**Dispatch order.** `dispatchOrder select l` (`ConvoyEffect/RunWait.lean`). The order in which a
policy would dispatch the queue `l` with nothing else arriving. It is a permutation of `l`.

**Response time.** The time until a job first gets the CPU (`rrResponse`,
`ConvoyEffect/RRResponse.lean`). **Turnaround** is the time until it completes. Neither waiting
nor turnaround time is monotone in RR's quantum, but response time is.

## Comparing schedulers

**Admissible schedule.** `IsAdmissible` (`ConvoyEffect/Schedules.lean`;
`PeriodicSchedulers/PeriodicSchedules.lean`). A schedule `σ` says which job (by id, or by key
for periodic jobs) holds the CPU after each step. It is *admissible* if it only runs jobs that
have been released and still have work left. Anything else is allowed: preemption, idling, any
order, clairvoyance. This is the "every possible way of running the jobs" that optimality
theorems compare against.

**Run as schedule.** `runSchedule step arrival_stream` is the schedule a run follows. For a job-conserving
step it is admissible, and the run waits what the schedule waits. The invariant behind this is
`inSystem_perm`.

**Optimal.** Weak: waits *no longer than* (`≤`) every competitor in the stated class. The class
is always stated (non-preemptive state-select policies, admissible schedules, fixed
priorities…), and so is the horizon. **Beaten** and **strict** mean `<`.

**Optimal / beaten over the first `T` steps.** `IsOptimalOverSteps T select` and
`IsBeatenOverSteps T select` (`ConvoyEffect/NoOptimalNonPreemptiveOnEveryStream.lean`). The
first definition of optimality for non-preemptive policies: wait least *on every stream*.
`not_isOptimalOverSteps_iff` says "not optimal" is exactly "beaten": some competitor waits
strictly less on some stream. No non-preemptive policy is optimal in this sense once `T ≥ 4`;
for `T ≤ 3` SJF is (`exists_optimal_iff`, `ConvoyEffect/ShortHorizon.lean`).

**Optimal given the same past.** The second definition, which SJF meets
(`ConvoyEffect/SJFOptimalityGivenSamePast.lean`): on the instance known at time `t`, wait least
against every competitor whose run agrees with yours before `t`.

**Shares the past, agrees before `t`.** Two runs whose states are equal at every step `< t`. In
`SJFOptimalityGivenSamePast`, SJF is compared only with competitors that took the same decisions before
`t`.

**Majorisation.** The proof technique behind SRTF's and EDF's optimality. It compares lists of
remaining work through `smallSum x k` (the sum of the `k` smallest entries, `ListLemmas.lean`),
or through the work owed by jobs with deadline at most `d` (`workDue`, `EDFOptimality.lean`).
The comparison is shown to hold after every step, for every `k` or `d`.

## Convoy effect and starvation

There are two competing definitions of the convoy effect, plus a special case. Each bad
property says "at **some**" moment; its negation, the good property, says "at **every**":

| Bad property | Good property (its negation) | Who has the bad one |
| --- | --- | --- |
| `HasConvoyEffectAtSomeDispatch` | `ShortestAtEveryDispatchRun` | FCFS, RR |
| `HasConvoyEffectAtSomeStep` | `ShortestAtEveryStepRun` | FCFS, RR, SJF |

Every dispatch is a step, so *at some dispatch* implies *at some step*, and *at every step*
implies *at every dispatch*.

**Convoy effect at some dispatch.** `HasConvoyEffectAtSomeDispatch`
(`ConvoyEffect/ConvoySpec.lean`). At some dispatch moment, a job with strictly less work left
is waiting. FCFS and RR have it; SJF and SRTF do not.

**Convoy effect at some step.** `HasConvoyEffectAtSomeStep`. At some step, dispatch or not, a
shorter job waits behind the running one. This is weaker: SJF has it on a late arrival without
having the convoy effect at some dispatch (`atSomeStep_not_imp_atSomeDispatch`). SRTF never
has it.

**Convoy effect on all arrivals at zero.** `HasConvoyEffectAllArrivalsAtZero`. The convoy
effect at step 0 of a run whose jobs all arrive at time 0, judged on one decision of a
selection policy. It is equivalent to waiting strictly longer than SJF on some such list
(`hasConvoyEffectAllArrivalsAtZero_iff_runWait`). Its negation is
`RunsShortestAllArrivalsAtZero`.

**Starvation-free.** `StarvationFree` (`Starvation/StarvationSpec.lean`). On every well-formed
stream, every job that arrives eventually completes (matched by id). FCFS and RR are; SJF and
SRTF are not. This is independent of the convoy effect.

## Periodic tasks

**Task, job, release.** A `PeriodicProcess` in the task list is a *task*. At time `t`, every
task whose period divides `t` *releases* a fresh *job*, a copy with `arrival := t`
(`PeriodicProcess.releasesAt`, `Process.lean`). Releases are **synchronous**: every task
releases at time 0. A task with period 0 releases once, at time 0.

**Key.** `key p = (id, arrival)` (`PeriodicSchedulers/PeriodicSchedules.lean`). All jobs of a
task share its id, so a job is named by its key. This needs distinct task ids.

**Relative and absolute deadline.** `deadline` (`D`) is relative to the release.
`absDeadline p = arrival + deadline`. Deadlines are **constrained** when `D ≤ T` (period) and
**implicit** when `D = T`.

**Miss rule.** `PeriodicProcess.missedDeadlines` (`SchedState.lean`). Because of dispatch
latency, a job released at `r` gets the `D` ticks of steps `r + 1, …, r + D`. It is late iff it
is still unfinished after step `r + D`, i.e. in any state with `time > r + D`. Late jobs are not
aborted, so they stay listed until they finish.

**`missedDeadlines` and `LateAt`.** The same miss rule, on a run's state and on a schedule
respectively. `LateAt tasks σ t` means some job with `absDeadline ≤ t` is unfinished after
step `t`. They are bridged by `missedDeadlines_ne_nil_iff_preemptive`.

**Meets its deadline, first job.** `MeetsDeadline σ p`: the job has had its whole burst by the
state after step `absDeadline p`. `firstJob m` is task `m`'s job released at time 0.

**Fixed priority.** `FixedPriority f` (`PeriodicSchedulers/FixedPriorityBacklog.lean`). A job's
priority is its task's: it ignores release time and work left. RM and DM are fixed; EDF is not.

**Strict.** Distinct tasks get distinct priorities. The DM/RM optimality class is the strict
fixed priorities. A priority with ties is still `FixedPriority`, but `stepPreemptive`'s dynamic
tie-breaks make it more than a classical fixed-priority assignment. It can even beat every strict
one (`tied_priority_never_misses_rmsFails`).

**Level set, upward-closed, deadline-closed.** `levelSet tasks f m` contains the tasks with
priority at least `f m`. A set of tasks is *upward-closed* (`UpClosed`) if every task at least
as urgent as a member is a member. `g`'s level sets are *deadline-closed* if a task at least as
urgent under `g` never has a longer deadline (DM always; RM when `D = T`).

**Level backlog, drain point, busy period.** `levelBacklog tasks S t`: the work released by the
tasks in `S`, less one per step down to 0. This is pure arithmetic, with no schedule. `pre S e`
is the backlog of jobs released before `e`. `e` is a **drain point** when `pre S e = 0`. A
**busy period** runs between drain points. The *synchronous* one, from time 0, is the longest
(`exists_pre_eq_zero_of_window`).

**Hyperperiod.** A common multiple `H` of all periods. Releases repeat every `H` steps, so a run
that ends its first `H` steps with nothing in the system repeats. Then a finite check (by
`decide`) proves "never misses" for all time (`missedDeadlines_eq_nil_of_hyperperiod`,
`PeriodicSchedulers/Hyperperiod.lean`).
