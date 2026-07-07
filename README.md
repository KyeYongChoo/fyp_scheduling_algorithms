# fyp\_scheduling\_algorithms

## TODO

organise the csv files

refactor the Process and Schedstate to just use Typeclasses more consistently

1. generalise to periodic/recurrent processes that arrive repeatedly infinitely
1.1 Rate Monotonic Scheduler
1.2 Earliest Deadline First Scheduler
2. prove starvation freedom for some algorithms - no process can be infinitely delayed, all processes must complete <- can a finite statement of this problem be posed?
3. prove no convoy effect for some algorithms - process wait time before being partially serviced is bounded above by some amount which is independent of any processes
4. Try to generalise to global scheduling and partitioned scheduling?

## AI suggestions:

1. Prove FCFS is starvation-free but exhibits convoy effect (a quantitative lower bound on waiting time as a function of preceding burst sizes)
2. Prove Round Robin is starvation-free and bounded-wait (waiting ≤ (n-1) \* Q ticks) — same safety, better fairness
3. Prove SJF minimizes average waiting time (the exchange argument) — shows there's a tradeoff: SJF is optimal by one metric but can starve (prove that too, with a counterexample workload as a #eval)

## List of scheduling properties:

### Safety Properties (nothing bad ever happens)

#### Mutual exclusion on the CPU — at most one process runs at any tick. Sounds trivial but is the baseline sanity check your model needs before anything else.

#### No work conservation violation — if the ready queue is non-empty, the CPU is never idle. Some algorithms violate this subtly in corner cases.

#### No priority inversion — a high-priority process is never blocked waiting while a lower-priority process runs, unless some explicit protocol (Priority Ceiling, Priority Inheritance) permits it. This is the classic bug that caused the Mars Pathfinder reset in 1997.

#### Preemption consistency — if you model a non-preemptive scheduler, a running process is never evicted before its burst is done. Trivial to state, useful to check your step function doesn't accidentally preempt.

## Liveness Properties (something good eventually happens)

#### Starvation freedom — every arrived process is eventually scheduled. The interesting variant: show this fails for pure Priority scheduling with dynamic arrivals (a stream of high-priority jobs can block a low one forever).

#### Termination / finite completion — if no new processes arrive after time T, the system eventually drains the queue. You need a well-founded measure over total remaining burst time.

#### Bounded waiting — stronger than starvation freedom: every process is scheduled within f(n) time units of arrival, where n is queue length. For Round Robin this is (n-1) \* quantum; for FCFS it depends on burst sizes.

#### Response time guarantees — for periodic task models, every job meets its deadline. This is the core of real-time scheduling theory (Rate Monotonic, EDF). Proving the utilization bound U ≤ n(2^(1/n) - 1) for RM is a classic formalization target.

## Fairness Properties

#### Progress proportion — over any window of W ticks, process i gets CPU time proportional to its weight. This is the defining property of fair-share schedulers (CFS, WFQ). Hard to state precisely but very satisfying to prove.

#### Max-min fairness — no process gets more than its fair share while another gets less. You can prove CFS satisfies this and FCFS doesn't.

#### Jitter bounds — the variance in when a periodic process actually runs vs. when it was supposed to. Relevant for multimedia and networking schedulers.

## Algorithm-Specific Optimality Properties

#### FCFS has no starvation but has convoy effect — formally: every process completes (liveness ✓), but the expected waiting time of a short process behind a long one is unbounded relative to its own burst. You can quantify this as a ratio.

#### SJF minimizes average waiting time — among all non-preemptive algorithms with the same workload, SJF achieves the minimum sum of waiting times. This is an exchange argument proof — swap any two adjacent jobs out-of-SJF-order and show the sum decreases.

#### SRTF (preemptive SJF) minimizes average response time — same result for the preemptive case. Requires reasoning about preemption points.

#### EDF is optimal for single-processor deadline scheduling — if any algorithm can meet all deadlines, EDF can. The proof is a classic exchange argument; very doable to formalize.

#### Round Robin convergence — with quantum Q → 0, RR approaches Processor Sharing, where each process gets an equal instantaneous fraction of the CPU. A limit argument.

## Compositional / System-Level Properties

#### Work-conserving schedulers dominate non-work-conserving ones — for any metric (latency, throughput), a work-conserving variant of any algorithm is at least as good. Good exercise in building a simulation preorder.

#### Idempotency of scheduling decisions — running step twice from an idle state gives the same result as running it once (no phantom context switches). Checks your model doesn't have spurious state changes.

#### Monotonicity — adding a process to the ready queue never improves the waiting time of existing processes (expected, but fails for some feedback schedulers).

#### Simulation / refinement — your abstract model (pure state machine) refines to a more concrete model (with context-switch overhead, cache effects). A bisimulation proof connecting the two levels.





Maybe could act on these ideas later

\-- show that a priority function is static or dynamic 

