/-
Copyright (c) 2026 Choo Kye Yong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Choo Kye Yong
-/
import FypSchedulingAlgorithms.AperiodicSchedulers.ConvoyEffect.Spec.TotalWait
import FypSchedulingAlgorithms.AperiodicSchedulers.ConvoyEffect.Spec.ConvoySpec
import FypSchedulingAlgorithms.AperiodicSchedulers.ConvoyEffect.Spec.ConvoyWitnesses
import FypSchedulingAlgorithms.AperiodicSchedulers.ConvoyEffect.Convoy.FCFSConvoy
import FypSchedulingAlgorithms.AperiodicSchedulers.ConvoyEffect.Convoy.SJFConvoy
import FypSchedulingAlgorithms.AperiodicSchedulers.ConvoyEffect.Convoy.RRConvoy
import FypSchedulingAlgorithms.AperiodicSchedulers.ConvoyEffect.Convoy.SRTFConvoy
import FypSchedulingAlgorithms.AperiodicSchedulers.ConvoyEffect.RRResponse
import FypSchedulingAlgorithms.AperiodicSchedulers.ConvoyEffect.Optimality.RunWait
import FypSchedulingAlgorithms.AperiodicSchedulers.ConvoyEffect.Optimality.NoOptimalNonPreemptiveOnEveryStream
import FypSchedulingAlgorithms.AperiodicSchedulers.ConvoyEffect.Optimality.ShortHorizon
import FypSchedulingAlgorithms.AperiodicSchedulers.ConvoyEffect.Optimality.SJFOptimalityGivenSamePast
import FypSchedulingAlgorithms.AperiodicSchedulers.ConvoyEffect.Optimality.Schedules
import FypSchedulingAlgorithms.AperiodicSchedulers.ConvoyEffect.Optimality.PreemptiveOptimality
import FypSchedulingAlgorithms.AperiodicSchedulers.ConvoyEffect.Optimality.SRTFOptimality

/-!
# The convoy effect: reading order

The folder answers two questions, in this order.

1. **`Spec/` -- what is the convoy effect?**  `TotalWait` (waiting time of a batch run in
   list order), `ConvoySpec` (the definitions: `HasConvoyEffectAtSomeDispatch` and its
   relatives), `ConvoyWitnesses` (the streams used as counterexamples).

2. **`Convoy/` -- does a policy's *rule* produce a convoy?**  One file per policy:
   `FCFSConvoy`, `SJFConvoy`, `RRConvoy`, `SRTFConvoy`.  These are properties of the rule
   (which job is dispatched), shown on a few streams.  `RRResponse` is the neighbouring
   question of response time for Round Robin.

3. **`Optimality/` -- which policy *waits least*?**  The cost is `runWait`, compared against
   other policies and then against every admissible schedule.
   * `RunWait`: the cost, and SJF on batches (`AllArrivalsAtZero`).
   * `NoOptimalNonPreemptiveOnEveryStream`: with later arrivals, no non-preemptive
     state-select policy is optimal.
   * `ShortHorizon`: the bound is sharp, SJF is optimal over the first `T ≤ 3` steps.
   * `SJFOptimalityGivenSamePast`: what does hold for SJF.
   * `Schedules`: admissible schedules, the yardstick that includes preemption.
   * `PreemptiveOptimality`: preemption removes the impossibility (two witness streams).
   * `SRTFOptimality`: SRTF waits least on every stream (Schrage 1968).
-/
