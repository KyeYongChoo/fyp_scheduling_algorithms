/-
Copyright (c) 2026 Choo Kye Yong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Choo Kye Yong
-/
import FypSchedulingAlgorithms.AperiodicSchedulers.ConvoyEffect.OnlineImpossibility

/-!
# SJF is optimal given only the past

`OnlineImpossibility` shows that no online non-preemptive policy waits least
on every stream: at time 0 nobody can know whether a short job is about to
arrive.  This file shows that the future is the *only* thing SJF lacks: judged
on what has arrived so far, its decisions are the best possible.

**The known instance.**  `knownAt as t` keeps the arrivals of `as` up to time
`t` and drops the later ones.  A run cannot see the future, so up to step `t` it
is the same on `as` and on `knownAt as t` (`runSteps_knownAt`).  On the known
instance nothing arrives after `t`, so the wait over `t + T` steps splits into
the wait up to `t` and the wait of the decision at `t` and its continuation
(`runWait_knownAt`, with `stateBefore as step t` the state step `t` starts
from).

**What is proved.**  Competitors are the online non-preemptive policies of
`OnlineImpossibility` (`IsOnlinePolicy`): they may idle on purpose and read the
whole state.  The cost is `runWait`, at *every* horizon, not just once the work
is done.

* `runWait_sjf_le_knownAt` (headline): on every well-formed stream `as`, at
  every time `t`, for every competitor whose run agrees with SJF's before `t`,
  `runWait SJF (knownAt as t) (t + T) ≤ runWait competitor (knownAt as t) (t + T)`
  for all `T`.  `runWait_sjf_le_sjfUntil` is the same with the agreement built
  in: any policy taking over from SJF at `t` (`sjfUntil t select`).
* `runWait_switchToSJF_le_knownAt` (the general form): the same holds from
  *any* past.  For any policy `select`, "follow `select` before `t`, then SJF"
  (`switchToSJF t select`) waits no longer on the known instance than any
  competitor that shares `select`'s past.  The headline is the case
  `select = SJF`.
* `runWait_sjf_le_online_batch` (`t = 0`): on a batch SJF waits least among
  all online non-preemptive policies, idling ones included, at every horizon.
  `RunWait`'s `runWait_sjf_le` follows (`runWait_sjf_le_batch`), without its
  never-idle and horizon assumptions.

**What is not claimed.**  The competitors share the past of the run they are
compared with: they took the same decisions before `t` and decide for
themselves at `t` and after.  Against a competitor with a different past SJF
can lose even on the known instance: stream B is its own instance known at time
1 (`knownAt_streamB_one`), and "idle at time 0, then SJF" beats SJF there
(`sjf_not_optimal_online`) -- by deciding differently at time 0, which is
exactly the decision SJF had to make without knowing about time 1.  Nor is
anything claimed on the real stream after `t`: a later arrival can make SJF's
choice at `t` a poor one (`OnlineImpossibility`).

A weaker reading, a competitor that starts from SJF's state *after* SJF's
decision at `t`, is also covered: `waitFrom_sjf_le` compares SJF with any
competitor from any state whose waiting jobs are untouched (as in every
non-preemptive run, `nonPreemptiveOnline_ready_fresh`), so in particular from
`runSteps as stepSJF t`.  The theorems above are the stronger claim, which
includes SJF's decision at `t` itself (`waitFrom_sjf_step_le`).

**The cost of the convoy effect, off batches.**  `HasConvoyEffect` is judged at
dispatch moments of real runs, with no cost in its definition.  On batches the
cost shows through `hasBatchConvoyEffect_iff_runWait`.  On general streams this
file supplies it: if any online policy's run dispatches a job while a strictly
shorter one waits, switching to SJF at that moment waits strictly less on the
known instance, once the horizon leaves time for the waiting work
(`runWait_switchToSJF_lt_of_convoy`); so every online policy with the convoy
effect has such a moment (`hasConvoyEffect_switchToSJF_lt`).

**How.**  With no arrivals, a non-idling non-preemptive policy waits
`truncWait r` of its dispatch order, at every horizon (`waitFrom_eq_truncWait`;
the `i`-th job waits until the work dispatched before it is done,
`truncWait_eq_sum`).  SJF's order is sorted, and sorted has the least prefix
sums (`sum_take_sorted_le`), so it waits least at every horizon
(`truncWait_sorted_le`).  One step at a time (`waitFrom_sjf_step_le_sjf_after`):
when the competitor dispatches some other job, SJF from there is a reordering of
SJF's own continuation; when it idles, everything is a step later
(`truncWait_succ_le`); otherwise both steps coincide.  Induction on the horizon
then gives `waitFrom_sjf_le`.
-/

namespace ConvoyEffect

open scoped List
open NonPreemptive

/-! ## Waiting over a horizon, back to back -/

/-- Adding a constant to every term adds it once per term. -/
theorem sum_map_const_add {α : Type} (l : List α) (c : ℕ) (f : α → ℕ) :
    (l.map fun i => c + f i).sum = c * l.length + (l.map f).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp only [List.map_cons, List.sum_cons, ih, List.length_cons]; ring

/-- Termwise `≤` gives `≤` of the sums. -/
theorem sum_map_le_sum_map {α : Type} (l : List α) {f g : α → ℕ} (h : ∀ i ∈ l, f i ≤ g i) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (h x (List.mem_cons_self ..))
      (ih fun i hi => h i (List.mem_cons_of_mem _ hi))

/-- Waiting time over the first `T` steps when a job with `r` ticks left holds
the CPU and the jobs with bursts `bs` then run back to back, in list order.
Each job of `bs` waits until it is dispatched, so while the first `r` steps last
all `bs.length` of them wait; the count is cut off at the horizon `T`. -/
def truncWait : ℕ → List ℕ → ℕ → ℕ
  | _, [], _ => 0
  | r, b :: bs, T => min r T * (bs.length + 1) + truncWait b bs (T - r)

@[simp] theorem truncWait_nil (r T : ℕ) : truncWait r [] T = 0 := rfl

theorem truncWait_cons (r b : ℕ) (bs : List ℕ) (T : ℕ) :
    truncWait r (b :: bs) T = min r T * (bs.length + 1) + truncWait b bs (T - r) := rfl

/-- Over a zero horizon nobody waits. -/
@[simp] theorem truncWait_zero_right (r : ℕ) (bs : List ℕ) : truncWait r bs 0 = 0 := by
  induction bs generalizing r with
  | nil => rfl
  | cons b bs ih => simp [truncWait_cons, ih]

/-- With nothing on the CPU, the queue starts at once. -/
theorem truncWait_zero_cons (b : ℕ) (bs : List ℕ) (T : ℕ) :
    truncWait 0 (b :: bs) T = truncWait b bs T := by
  simp [truncWait_cons]

/-- One more step of the current job: everybody waits one more tick. -/
theorem truncWait_succ_succ (r : ℕ) (bs : List ℕ) (T : ℕ) :
    truncWait (r + 1) bs (T + 1) = bs.length + truncWait r bs T := by
  cases bs with
  | nil => rfl
  | cons b bs =>
    rw [truncWait_cons, truncWait_cons, show T + 1 - (r + 1) = T - r by omega,
      show min (r + 1) (T + 1) = min r T + 1 by omega, List.length_cons]
    ring

/-- **The dispatch times.** The `i`-th job of `bs` is dispatched at time
`r + (bs.take i).sum` and waits until then, cut off at the horizon. -/
theorem truncWait_eq_sum (r : ℕ) (bs : List ℕ) (T : ℕ) :
    truncWait r bs T =
      ((List.range bs.length).map fun i => min (r + (bs.take i).sum) T).sum := by
  induction bs generalizing r T with
  | nil => rfl
  | cons b bs ih =>
    rw [truncWait_cons, ih, List.length_cons, List.range_succ_eq_map, List.map_cons,
      List.sum_cons, List.map_map]
    have h : ∀ j, min (r + (b + (bs.take j).sum)) T =
        min r T + min (b + (bs.take j).sum) (T - r) := fun j => by omega
    simp only [Function.comp_def, List.take_succ_cons, List.sum_cons, List.take_zero,
      List.sum_nil, Nat.add_zero, h, sum_map_const_add, List.length_range]
    ring

/-- One more step costs at most one tick per job. -/
theorem truncWait_succ_le (r : ℕ) (bs : List ℕ) (T : ℕ) :
    truncWait r bs (T + 1) ≤ bs.length + truncWait r bs T := by
  rw [truncWait_eq_sum, truncWait_eq_sum]
  calc ((List.range bs.length).map fun i => min (r + (bs.take i).sum) (T + 1)).sum
      ≤ ((List.range bs.length).map fun i => min (r + (bs.take i).sum) T + 1).sum :=
        sum_map_le_sum_map _ fun i _ => by omega
    _ = bs.length + ((List.range bs.length).map fun i => min (r + (bs.take i).sum) T).sum := by
        simp only [Nat.add_comm _ 1, sum_map_const_add, List.length_range, Nat.one_mul]

/-- Once the horizon covers all the work, `truncWait` is the current job's
wait plus `totalWait`. -/
theorem truncWait_of_le (r : ℕ) (bs : List ℕ) (T : ℕ) (hT : r + bs.sum ≤ T) :
    truncWait r bs T = r * bs.length + totalWait bs := by
  induction bs generalizing r T with
  | nil => simp
  | cons b bs ih =>
    rw [truncWait_cons, ih b (T - r) (by simp at hT; omega), Nat.min_eq_left (by simp at hT; omega),
      totalWait_cons, List.length_cons]

/-- Moving a job no longer than every job ahead of it to the front lowers every
prefix sum. -/
theorem sum_take_cons_le (m : ℕ) (pre post : List ℕ) (h : ∀ a ∈ pre, m ≤ a) (i : ℕ) :
    ((m :: (pre ++ post)).take i).sum ≤ ((pre ++ m :: post).take i).sum := by
  induction pre generalizing i with
  | nil => simp
  | cons a pre ih =>
    have ha := h a (List.mem_cons_self ..)
    rcases i with _ | _ | i
    · simp
    · simpa using ha
    · have := ih (fun x hx => h x (List.mem_cons_of_mem _ hx)) (i + 1)
      simp only [List.cons_append, List.take_succ_cons, List.sum_cons] at this ⊢
      omega

/-- **Shortest first has the least prefix sums**: the first `i` jobs of the
sorted order are the `i` shortest. -/
theorem sum_take_sorted_le {bs cs : List ℕ} (h_sorted : bs.Pairwise (· ≤ ·)) (h_perm : bs ~ cs)
    (i : ℕ) : (bs.take i).sum ≤ (cs.take i).sum := by
  induction bs generalizing cs i with
  | nil => rw [List.nil_perm.mp h_perm]
  | cons m rest ih =>
    obtain ⟨h_min, h_rest⟩ := List.pairwise_cons.mp h_sorted
    obtain ⟨pre, post, rfl⟩ := List.append_of_mem (h_perm.subset (List.mem_cons_self ..))
    have h_rest_perm : rest ~ pre ++ post := (h_perm.trans List.perm_middle).cons_inv
    have h_pre : ∀ a ∈ pre, m ≤ a := fun a ha =>
      h_min a (h_rest_perm.symm.subset (List.mem_append_left _ ha))
    refine le_trans ?_ (sum_take_cons_le m pre post h_pre i)
    cases i with
    | zero => simp
    | succ i =>
      simp only [List.take_succ_cons, List.sum_cons]
      exact Nat.add_le_add_left (ih h_rest h_rest_perm i) m

/-- **Shortest first is optimal at every horizon.** Running the jobs in
non-decreasing order of burst waits no longer than any other order, over any
number of steps: every job of the sorted order is dispatched no later than the
job in the same position of the other order. -/
theorem truncWait_sorted_le {bs cs : List ℕ} (h_sorted : bs.Pairwise (· ≤ ·)) (h_perm : bs ~ cs)
    (r T : ℕ) : truncWait r bs T ≤ truncWait r cs T := by
  rw [truncWait_eq_sum, truncWait_eq_sum, h_perm.length_eq]
  refine sum_map_le_sum_map _ fun i _ => ?_
  have := sum_take_sorted_le h_sorted h_perm i
  omega

/-! ## Draining a state, at every horizon -/

/-- **Draining a state, at every horizon.** Arrivals have stopped, a job with
`r > 0` ticks left holds the CPU, and the jobs `R` waiting in `ready` are
untouched.  Over *any* number of steps `T`, the run of `stepNonPreemptive select`
waits `truncWait r` of `R`'s bursts in the order the policy dispatches them.
(`waitFrom_drain` is the case of a horizon long enough to finish everything,
see `truncWait_of_le`.) -/
theorem waitFrom_eq_truncWait {select : List AperiodicProcess → Option AperiodicProcess}
    (h_mem : ∀ l p, select l = some p → p ∈ l) (h_none : ∀ l, select l = none → l = [])
    (s : SchedState) (p : AperiodicProcess) (h_run : s.running = some p)
    (h_pos : 0 < p.remaining) (h_fresh : ∀ q ∈ s.ready, q.remaining = q.burst) (T : ℕ) :
    waitFrom (stepNonPreemptive select) s T =
      truncWait p.remaining ((dispatchOrder select s.ready).map (·.burst)) T := by
  induction T generalizing s p with
  | zero => simp
  | succ T ih =>
    rw [waitFrom_succ]
    by_cases h_left : 1 < p.remaining
    · -- the current job ticks and keeps the CPU
      obtain ⟨h1, h2⟩ := stepNonPreemptive_tick select s h_run h_left
      rw [ih (stepNonPreemptive select s) _ h1 (by simp only; omega) (by rw [h2]; exact h_fresh),
        h2]
      obtain ⟨r, hr⟩ : ∃ r, p.remaining = r + 1 := ⟨p.remaining - 1, by omega⟩
      simp only [hr, Nat.add_sub_cancel, truncWait_succ_succ, List.length_map,
        (dispatchOrder_perm h_mem h_none s.ready).length_eq]
    · -- the current job finishes
      have h_one : p.remaining = 0 + 1 := by omega
      cases h_sel : select s.ready with
      | none =>
        obtain ⟨h1, h2⟩ := stepNonPreemptive_complete_idle select s h_run (by omega) h_sel
        have h_nil := h_none _ h_sel
        rw [waitFrom_idle h_mem _ h1 (by rw [h2, h_nil]), h_nil]
        simp
      | some q =>
        -- `q` takes over, untouched, and the rest of `ready` waits on
        obtain ⟨h1, h2⟩ := stepNonPreemptive_complete_dispatch select s h_run (by omega) h_sel
        have hq := h_mem _ _ h_sel
        have hq_fresh := h_fresh q hq
        rw [ih (stepNonPreemptive select s) q h1 (by rw [hq_fresh]; exact q.burst_exceed_zero)
          (by rw [h2]; exact fun r hr => h_fresh r (List.mem_of_mem_erase hr)), h2,
          dispatchOrder_of_select h_mem h_sel, List.map_cons, h_one, truncWait_succ_succ,
          truncWait_zero_cons, hq_fresh, List.length_cons, List.length_map,
          (dispatchOrder_perm h_mem h_none (s.ready.erase q)).length_eq,
          List.length_erase_of_mem hq]
        have := List.length_pos_of_mem hq
        omega

/-! ## SJF against any online non-preemptive policy, from a common state -/

/-- SJF's dispatch order of a queue lists its bursts in non-decreasing order. -/
theorem sjf_dispatchOrder_sorted (l : List AperiodicProcess) :
    ((dispatchOrder selectSJF l).map (·.burst)).Pairwise (· ≤ ·) :=
  dispatchOrder_sorted_of_min selectSJF_mem selectSJF_none_imp_empty selectSJF_min l

/-- Putting any waiting job `q` first, then SJF's order of the rest, only
reorders SJF's order of the queue. -/
theorem sjf_dispatchOrder_perm_cons {l : List AperiodicProcess} {q : AperiodicProcess}
    (hq : q ∈ l) :
    (dispatchOrder selectSJF l).map (·.burst) ~
      q.burst :: (dispatchOrder selectSJF (l.erase q)).map (·.burst) :=
  calc (dispatchOrder selectSJF l).map (·.burst)
      ~ l.map (·.burst) := (dispatchOrder_perm selectSJF_mem selectSJF_none_imp_empty _).map _
    _ ~ (q :: l.erase q).map (·.burst) := (List.perm_cons_erase hq).map _
    _ ~ q.burst :: (dispatchOrder selectSJF (l.erase q)).map (·.burst) := by
        rw [List.map_cons]
        exact ((dispatchOrder_perm selectSJF_mem selectSJF_none_imp_empty _).symm.map _).cons _

/-- SJF's continuation from a state where an untouched job `q` has just been put
on the CPU: `q` runs, then SJF's order of the queue. -/
theorem waitFrom_sjf_of_running (x : SchedState) (q : AperiodicProcess)
    (h_run : x.running = some q) (hq : q.remaining = q.burst)
    (h_fresh : ∀ r ∈ x.ready, r.remaining = r.burst) (T : ℕ) :
    waitFrom stepSJF x T =
      truncWait 0 (q.burst :: (dispatchOrder selectSJF x.ready).map (·.burst)) T := by
  rw [truncWait_zero_cons, ← hq]
  exact waitFrom_eq_truncWait selectSJF_mem selectSJF_none_imp_empty x q h_run
    (by rw [hq]; exact q.burst_exceed_zero) h_fresh T

/-- When a step makes a decision -- the CPU is idle, or its job is on its last
tick -- the policy's choice goes on the CPU, unticked, and leaves the queue; with
no choice the CPU is left idle. -/
theorem stepNonPreemptiveOnline_decide (select : SchedState → Option AperiodicProcess)
    (s : SchedState) (h_dec : ∀ p, s.running = some p → p.remaining ≤ 1) :
    (∀ q, select s = some q → (stepNonPreemptiveOnline select s).running = some q ∧
        (stepNonPreemptiveOnline select s).ready = s.ready.erase q) ∧
      (select s = none → (stepNonPreemptiveOnline select s).running = none ∧
        (stepNonPreemptiveOnline select s).ready = s.ready) := by
  cases h_run : s.running with
  | none =>
    exact ⟨fun q h => stepNonPreemptiveOnline_dispatch select s h_run h,
      fun h => stepNonPreemptiveOnline_idle select s h_run h⟩
  | some p =>
    have h_done := h_dec p h_run
    exact ⟨fun q h => stepNonPreemptiveOnline_complete_dispatch select s h_run h_done h,
      fun h => stepNonPreemptiveOnline_complete_idle select s h_run h_done h⟩

/-- When the running job has more than one tick left, the step does not consult
the policy: every non-preemptive policy takes the same step. -/
theorem stepNonPreemptiveOnline_eq_of_tick (select select' : SchedState → Option AperiodicProcess)
    (s : SchedState) {p : AperiodicProcess} (h_run : s.running = some p)
    (h_left : 1 < p.remaining) :
    stepNonPreemptiveOnline select s = stepNonPreemptiveOnline select' s := by
  simp [stepNonPreemptiveOnline, h_run, show ¬ p.remaining - 1 = 0 by omega]

/-- SJF's continuation after it decides at `s` and dispatches `m`: `m`, then
SJF's order of the rest -- that is, SJF's order of the whole queue. -/
theorem waitFrom_sjf_step_of_decide (s : SchedState)
    (h_dec : ∀ p, s.running = some p → p.remaining ≤ 1)
    (h_fresh : ∀ q ∈ s.ready, q.remaining = q.burst) {m : AperiodicProcess}
    (h_m : selectSJF s.ready = some m) (T : ℕ) :
    waitFrom stepSJF (stepSJF s) T =
      truncWait 0 ((dispatchOrder selectSJF s.ready).map (·.burst)) T := by
  have hm := selectSJF_mem _ _ h_m
  obtain ⟨hm_run, hm_ready⟩ := (stepNonPreemptiveOnline_decide (fun s => selectSJF s.ready) s
    h_dec).1 m h_m
  change (stepSJF s).running = some m at hm_run
  change (stepSJF s).ready = s.ready.erase m at hm_ready
  rw [waitFrom_sjf_of_running _ m hm_run (h_fresh m hm)
      (by rw [hm_ready]; exact fun r hr => h_fresh r (List.mem_of_mem_erase hr)) T, hm_ready,
    dispatchOrder_of_select selectSJF_mem h_m, List.map_cons]

/-- **One decision against SJF's.** From any state whose waiting jobs are
untouched, let SJF take one step, or let any online non-preemptive policy take
one step; if SJF then runs on from either state with no further arrivals, it
waits no longer after its own step, at every horizon.  Either nothing is
decided (both take the same step), or SJF dispatches a shortest job `m` while
the other policy dispatches some `q` (then SJF's order of the queue is sorted
and `q` first is a permutation of it, `truncWait_sorted_le`) or idles (which
delays everything by a step, `truncWait_succ_le`). -/
theorem waitFrom_sjf_step_le_sjf_after (select : SchedState → Option AperiodicProcess)
    (h_online : IsOnlinePolicy select) (s : SchedState)
    (h_fresh : ∀ q ∈ s.ready, q.remaining = q.burst) (T : ℕ) :
    waitFrom stepSJF (stepSJF s) T ≤ waitFrom stepSJF (stepNonPreemptiveOnline select s) T := by
  -- `stepSJF` is the online policy that reads only the ready queue
  have h_sjf : stepSJF = stepNonPreemptiveOnline (fun s => selectSJF s.ready) := rfl
  -- nothing to decide: both take the same step
  by_cases h_tick : ∃ p, s.running = some p ∧ 1 < p.remaining
  · obtain ⟨p, h_run, h_left⟩ := h_tick
    rw [h_sjf, stepNonPreemptiveOnline_eq_of_tick _ select s h_run h_left]
  push Not at h_tick
  have h_dec : ∀ p, s.running = some p → p.remaining ≤ 1 := h_tick
  obtain ⟨-, h_sjf_none⟩ := h_sjf ▸ stepNonPreemptiveOnline_decide _ s h_dec
  obtain ⟨h_sel_some, h_sel_none⟩ := stepNonPreemptiveOnline_decide select s h_dec
  cases h_m : selectSJF s.ready with
  | none =>
    -- nothing waits, so SJF's continuation waits nothing
    have h_nil := selectSJF_none_imp_empty _ h_m
    have h0 : (stepSJF s).ready = [] := by rw [(h_sjf_none h_m).2, h_nil]
    rw [show waitFrom stepSJF (stepSJF s) T = 0 from
      waitFrom_online_nil (fun s => selectSJF s.ready) _ h0 T]
    exact Nat.zero_le _
  | some m =>
    have hm := selectSJF_mem _ _ h_m
    rw [waitFrom_sjf_step_of_decide s h_dec h_fresh h_m]
    cases h_q : select s with
    | some q =>
      -- the policy dispatches `q`: a permutation of SJF's sorted order
      have hq := h_online s q h_q
      obtain ⟨hq_run, hq_ready⟩ := h_sel_some q h_q
      rw [waitFrom_sjf_of_running _ q hq_run (h_fresh q hq)
        (by rw [hq_ready]; exact fun r hr => h_fresh r (List.mem_of_mem_erase hr)) T, hq_ready]
      exact truncWait_sorted_le (sjf_dispatchOrder_sorted s.ready)
        (sjf_dispatchOrder_perm_cons hq) 0 T
    | none =>
      -- the policy idles: SJF then dispatches `m` one step late
      obtain ⟨hi_run, hi_ready⟩ := h_sel_none h_q
      cases T with
      | zero => simp
      | succ T =>
        obtain ⟨h1, h2⟩ :=
          stepNonPreemptive_dispatch selectSJF _ hi_run (by rw [hi_ready]; exact h_m)
        rw [waitFrom_succ, show stepNonPreemptive selectSJF = stepSJF from rfl] at *
        rw [waitFrom_sjf_of_running _ m h1 (h_fresh m hm)
          (by rw [h2, hi_ready]; exact fun r hr => h_fresh r (List.mem_of_mem_erase hr)) T,
          h2, hi_ready, ← List.map_cons, ← dispatchOrder_of_select selectSJF_mem h_m]
        have := truncWait_succ_le 0 ((dispatchOrder selectSJF s.ready).map (·.burst)) T
        rw [List.length_map, (dispatchOrder_perm selectSJF_mem selectSJF_none_imp_empty _).length_eq]
          at this
        exact this

/-- **SJF's continuation waits least.** From any state whose waiting jobs are
untouched, with no further arrivals, SJF waits no longer than any online
non-preemptive policy -- including ones that idle on purpose or read the whole
state -- over every horizon `T`. -/
theorem waitFrom_sjf_le (select : SchedState → Option AperiodicProcess)
    (h_online : IsOnlinePolicy select) (s : SchedState)
    (h_fresh : ∀ q ∈ s.ready, q.remaining = q.burst) (T : ℕ) :
    waitFrom stepSJF s T ≤ waitFrom (stepNonPreemptiveOnline select) s T := by
  induction T generalizing s with
  | zero => exact le_rfl
  | succ T ih =>
    rw [waitFrom_succ, waitFrom_succ]
    have h1 := waitFrom_sjf_step_le_sjf_after select h_online s h_fresh T
    have h2 := ih (stepNonPreemptiveOnline select s)
      fun q hq => h_fresh q (stepNonPreemptiveOnline_ready_subset select s q hq)
    omega

/-- **SJF's decision and continuation wait least.** From any state whose waiting
jobs are untouched, with no further arrivals, the states after SJF's step wait
no longer than the states after any online non-preemptive policy's step, over
every horizon `T`.  This includes the decision taken at `s` itself. -/
theorem waitFrom_sjf_step_le (select : SchedState → Option AperiodicProcess)
    (h_online : IsOnlinePolicy select) (s : SchedState)
    (h_fresh : ∀ q ∈ s.ready, q.remaining = q.burst) (T : ℕ) :
    waitFrom stepSJF (stepSJF s) T ≤
      waitFrom (stepNonPreemptiveOnline select) (stepNonPreemptiveOnline select s) T :=
  (waitFrom_sjf_step_le_sjf_after select h_online s h_fresh T).trans
    (waitFrom_sjf_le select h_online _
      (fun q hq => h_fresh q (stepNonPreemptiveOnline_ready_subset select s q hq)) T)

/-- **A convoy dispatch strictly costs.** From a state whose waiting jobs are
untouched, suppose an online non-preemptive policy puts `p` on the CPU while a
strictly shorter job `q` is left waiting.  With no further arrivals, once the
horizon covers the work waiting at `s`, SJF's step and continuation wait
strictly less than the policy's step and continuation, whatever the policy does
afterwards.  (Swap `p` and `q`: strictly better, `totalWait_swap_far_lt`; SJF's
sorted order is no worse than that, `totalWait_sorted_le`.) -/
theorem waitFrom_sjf_step_lt_of_convoy (select : SchedState → Option AperiodicProcess)
    (h_online : IsOnlinePolicy select) (s : SchedState)
    (h_fresh : ∀ q ∈ s.ready, q.remaining = q.burst) {p q : AperiodicProcess}
    (h_run : (stepNonPreemptiveOnline select s).running = some p)
    (h_ready : (stepNonPreemptiveOnline select s).ready = s.ready.erase p)
    (hp : p ∈ s.ready) (hq : q ∈ s.ready.erase p) (h_lt : q.burst < p.burst)
    (T : ℕ) (hT : (s.ready.map (·.burst)).sum ≤ T) :
    waitFrom stepSJF (stepSJF s) T <
      waitFrom (stepNonPreemptiveOnline select) (stepNonPreemptiveOnline select s) T := by
  -- the step was a decision: a job that only ticks leaves the queue alone
  have h_dec : ∀ r, s.running = some r → r.remaining ≤ 1 := by
    intro r hr
    by_contra h_left
    have h := congrArg List.length
      (h_ready.symm.trans (stepNonPreemptiveOnline_tick select s hr (by omega)).2)
    have h1 := List.length_erase_of_mem hp
    have h2 := List.length_pos_of_mem hp
    omega
  obtain ⟨m, h_m⟩ : ∃ m, selectSJF s.ready = some m := by
    cases h : selectSJF s.ready with
    | none => rw [selectSJF_none_imp_empty _ h] at hp; simp at hp
    | some m => exact ⟨m, rfl⟩
  have h_fresh' : ∀ r ∈ (stepNonPreemptiveOnline select s).ready, r.remaining = r.burst := by
    rw [h_ready]; exact fun r hr => h_fresh r (List.mem_of_mem_erase hr)
  -- whatever the policy does next, it waits at least as long as SJF would from there
  have h_after := waitFrom_sjf_le select h_online _ h_fresh' T
  rw [waitFrom_sjf_of_running _ p h_run (h_fresh p hp) h_fresh' T, h_ready] at h_after
  rw [waitFrom_sjf_step_of_decide s h_dec h_fresh h_m]
  refine lt_of_lt_of_le ?_ h_after
  -- the horizon covers the work, so both are `totalWait`s
  have h_perm := sjf_dispatchOrder_perm_cons hp
  have h_sum : ((dispatchOrder selectSJF s.ready).map (·.burst)).sum ≤ T := by
    rw [((dispatchOrder_perm selectSJF_mem selectSJF_none_imp_empty _).map _).sum_nat]
    exact hT
  rw [truncWait_of_le 0 _ T (by simpa using h_sum),
    truncWait_of_le 0 _ T (by rw [← h_perm.sum_nat]; simpa using h_sum),
    Nat.zero_mul, Nat.zero_add, Nat.zero_mul, Nat.zero_add]
  -- `q` runs somewhere after `p`
  have hq' : q.burst ∈ (dispatchOrder selectSJF (s.ready.erase p)).map (·.burst) :=
    List.mem_map_of_mem
      ((dispatchOrder_perm selectSJF_mem selectSJF_none_imp_empty _).symm.subset hq)
  obtain ⟨mid, post, h_split⟩ := List.append_of_mem hq'
  rw [h_split] at h_perm ⊢
  calc totalWait ((dispatchOrder selectSJF s.ready).map (·.burst))
      ≤ totalWait (q.burst :: (mid ++ p.burst :: post)) :=
        totalWait_sorted_le (sjf_dispatchOrder_sorted _)
          (h_perm.trans (perm_swap_far _ _ mid post))
    _ < totalWait (p.burst :: (mid ++ q.burst :: post)) := totalWait_swap_far_lt mid post h_lt

/-! ## The instance known at time `t` -/

/-- **The instance known at time `t`**: the arrivals of `arrival_stream` up to
time `t`, and nothing afterwards. -/
def knownAt (arrival_stream : ℕ → List AperiodicProcess) (t : ℕ) : ℕ → List AperiodicProcess :=
  fun t' => if t' ≤ t then arrival_stream t' else []

/-- Nothing is known to arrive after time `t`. -/
theorem knownAt_of_lt (arrival_stream : ℕ → List AperiodicProcess) {t j : ℕ} (h : t < j) :
    knownAt arrival_stream t j = [] := by
  simp [knownAt, show ¬ j ≤ t by omega]

/-- The known instance of a well-formed stream is well formed. -/
theorem knownAt_wf {arrival_stream : ℕ → List AperiodicProcess}
    (h_wf : WellFormedStream arrival_stream) (t : ℕ) : WellFormedStream (knownAt arrival_stream t) := by
  have h_mem : ∀ p j, p ∈ knownAt arrival_stream t j → p ∈ arrival_stream j := fun p j hp => by
    unfold knownAt at hp
    split at hp
    · exact hp
    · simp at hp
  exact ⟨fun p j hp => h_wf.consistent p j (h_mem p j hp),
    fun p j hp => h_wf.fresh p j (h_mem p j hp),
    fun p1 p2 t1 t2 h1 h2 h_id => h_wf.unique p1 p2 t1 t2 (h_mem _ _ h1) (h_mem _ _ h2) h_id⟩

/-- **A run cannot see the future**: up to time `t` it is the same on the
stream and on the instance known at `t`. -/
theorem runSteps_knownAt (arrival_stream : ℕ → List AperiodicProcess)
    (step : SchedState → SchedState) {t t' : ℕ} (h : t' ≤ t) :
    runSteps (knownAt arrival_stream t) step t' = runSteps arrival_stream step t' := by
  induction t' with
  | zero => simp [runSteps, knownAt]
  | succ k ih =>
    simp only [runSteps]
    rw [ih (by omega)]
    simp [knownAt, h]

/-- The state step `t` of a run starts from: the state after step `t - 1` (or
the initial state) with the arrivals of time `t` added to `ready`.  This is
the state on which the scheduler makes its decision at time `t`. -/
def stateBefore (arrival_stream : ℕ → List AperiodicProcess) (step : SchedState → SchedState) :
    ℕ → SchedState
  | 0 => { SchedStateMethods.init with ready := arrival_stream 0 }
  | t + 1 => { runSteps arrival_stream step t with
      ready := (runSteps arrival_stream step t).ready ++ arrival_stream (t + 1) }

/-- Each run step is one `step` from the state it starts from. -/
theorem runSteps_eq_step_stateBefore (arrival_stream : ℕ → List AperiodicProcess)
    (step : SchedState → SchedState) (t : ℕ) :
    runSteps arrival_stream step t = step (stateBefore arrival_stream step t) := by
  cases t <;> rfl

/-- Two runs that agree before time `t` start step `t` from the same state. -/
theorem stateBefore_congr (arrival_stream : ℕ → List AperiodicProcess)
    {step step' : SchedState → SchedState} {t : ℕ}
    (h : ∀ k < t, runSteps arrival_stream step k = runSteps arrival_stream step' k) :
    stateBefore arrival_stream step t = stateBefore arrival_stream step' t := by
  cases t with
  | zero => rfl
  | succ k => simp only [stateBefore, h k (by omega)]

/-- In a non-preemptive run on a well-formed stream, the jobs waiting when step
`t` starts are untouched. -/
theorem stateBefore_ready_fresh (select : SchedState → Option AperiodicProcess)
    (arrival_stream : ℕ → List AperiodicProcess) (h_wf : WellFormedStream arrival_stream)
    (t : ℕ) : ∀ q ∈ (stateBefore arrival_stream (stepNonPreemptiveOnline select) t).ready,
      q.remaining = q.burst := by
  intro q hq
  cases t with
  | zero => exact h_wf.fresh q 0 (by simpa [stateBefore] using hq)
  | succ t =>
    rcases List.mem_append.mp hq with hq | hq
    · exact nonPreemptiveOnline_ready_fresh select arrival_stream h_wf t q hq
    · exact h_wf.fresh q _ hq

/-- **Waiting on the known instance.** Over `t + T` steps on the instance known
at `t`, a run waits what it waited on the stream up to `t`, plus the wait still
to come once it has made its decision at time `t`. -/
theorem runWait_knownAt (arrival_stream : ℕ → List AperiodicProcess)
    (step : SchedState → SchedState) (t T : ℕ) :
    runWait (runSteps · step) (knownAt arrival_stream t) (t + T) =
      runWait (runSteps · step) arrival_stream t +
        waitFrom step (step (stateBefore arrival_stream step t)) T := by
  rw [runWait_add _ _ t T fun j h _ => knownAt_of_lt arrival_stream h,
    runSteps_knownAt _ _ le_rfl, runSteps_eq_step_stateBefore]
  congr 1
  unfold runWait
  congr 1
  refine List.map_congr_left fun k hk => ?_
  dsimp only
  rw [runSteps_knownAt _ _ (List.mem_range.mp hk).le]

/-- Two runs that agree before time `t` have waited the same up to `t`. -/
theorem runWait_eq_of_agree (arrival_stream : ℕ → List AperiodicProcess)
    {step step' : SchedState → SchedState} {t : ℕ}
    (h : ∀ k < t, runSteps arrival_stream step k = runSteps arrival_stream step' k) :
    runWait (runSteps · step) arrival_stream t = runWait (runSteps · step') arrival_stream t := by
  unfold runWait
  congr 1
  refine List.map_congr_left fun k hk => ?_
  dsimp only
  rw [h k (List.mem_range.mp hk)]

/-! ## Switching policy at a given time -/

/-- A step depends on the policy only through its choice at the current state. -/
theorem stepNonPreemptiveOnline_congr {select select' : SchedState → Option AperiodicProcess}
    {s : SchedState} (h : select s = select' s) :
    stepNonPreemptiveOnline select s = stepNonPreemptiveOnline select' s := by
  simp only [stepNonPreemptiveOnline, h]

/-- After step `k` of a non-preemptive run the clock reads `k + 1`. -/
theorem runSteps_online_time (arrival_stream : ℕ → List AperiodicProcess)
    (select : SchedState → Option AperiodicProcess) (k : ℕ) :
    (runSteps arrival_stream (stepNonPreemptiveOnline select) k).time = k + 1 := by
  induction k with
  | zero => simp [runSteps, stepNonPreemptiveOnline_time]
  | succ k ih => simp [runSteps, stepNonPreemptiveOnline_time, ih]

/-- Step `t` of a non-preemptive run starts with the clock at `t`. -/
theorem stateBefore_online_time (arrival_stream : ℕ → List AperiodicProcess)
    (select : SchedState → Option AperiodicProcess) (t : ℕ) :
    (stateBefore arrival_stream (stepNonPreemptiveOnline select) t).time = t := by
  cases t with
  | zero => rfl
  | succ k => simp [stateBefore, runSteps_online_time]

/-- Two policies that choose alike whenever the clock reads less than `t` have
the same run before time `t`. -/
theorem onlineRun_agree_of_time_lt (arrival_stream : ℕ → List AperiodicProcess) (t : ℕ)
    {select select' : SchedState → Option AperiodicProcess}
    (h : ∀ s : SchedState, s.time < t → select s = select' s) :
    ∀ k < t, onlineRun select arrival_stream k = onlineRun select' arrival_stream k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    change runSteps arrival_stream (stepNonPreemptiveOnline select) k =
      runSteps arrival_stream (stepNonPreemptiveOnline select') k
    rw [runSteps_eq_step_stateBefore, runSteps_eq_step_stateBefore,
      ← stateBefore_congr arrival_stream fun j hj => ih j hj (by omega)]
    exact stepNonPreemptiveOnline_congr (h _ (by rw [stateBefore_online_time]; exact hk))

/-- The policy that follows `select` before time `t` and SJF from then on. -/
def switchToSJF (t : ℕ) (select : SchedState → Option AperiodicProcess) :
    SchedState → Option AperiodicProcess :=
  fun s => if s.time < t then select s else selectSJF s.ready

/-- Switching to SJF keeps a policy online. -/
theorem switchToSJF_isOnlinePolicy (t : ℕ) {select : SchedState → Option AperiodicProcess}
    (h_online : IsOnlinePolicy select) : IsOnlinePolicy (switchToSJF t select) := by
  intro s p h
  unfold switchToSJF at h
  split at h
  · exact h_online s p h
  · exact selectSJF_mem _ p h

/-- From time `t` on, the switched policy steps like SJF. -/
theorem waitFrom_switchToSJF (t : ℕ) (select : SchedState → Option AperiodicProcess)
    (x : SchedState) (hx : t ≤ x.time) (T : ℕ) :
    waitFrom (stepNonPreemptiveOnline (switchToSJF t select)) x T = waitFrom stepSJF x T := by
  induction T generalizing x with
  | zero => rfl
  | succ T ih =>
    have h_step : stepNonPreemptiveOnline (switchToSJF t select) x = stepSJF x :=
      stepNonPreemptiveOnline_congr (select' := fun s => selectSJF s.ready)
        (by simp [switchToSJF, show ¬ x.time < t by omega])
    rw [waitFrom_succ, waitFrom_succ, h_step,
      ih _ (by rw [show stepSJF x = stepNonPreemptiveOnline (fun s => selectSJF s.ready) x from rfl,
        stepNonPreemptiveOnline_time]; omega)]

/-- **The switched run on the known instance**: the wait of `select`'s run up to
`t`, then SJF's decision at time `t`, from the state `select`'s run reached, and
SJF's continuation. -/
theorem runWait_switchToSJF_knownAt (arrival_stream : ℕ → List AperiodicProcess) (t : ℕ)
    (select : SchedState → Option AperiodicProcess) (T : ℕ) :
    runWait (onlineRun (switchToSJF t select)) (knownAt arrival_stream t) (t + T) =
      runWait (onlineRun select) arrival_stream t +
        waitFrom stepSJF (stepSJF (stateBefore arrival_stream (stepNonPreemptiveOnline select) t)) T := by
  have h_agree := onlineRun_agree_of_time_lt arrival_stream t (select := switchToSJF t select)
    (select' := select) fun s hs => by simp [switchToSJF, hs]
  have h_before := stateBefore_congr arrival_stream h_agree
  have h_time := stateBefore_online_time arrival_stream select t
  change runWait (runSteps · (stepNonPreemptiveOnline (switchToSJF t select))) _ _ =
    runWait (runSteps · (stepNonPreemptiveOnline select)) _ _ + _
  rw [runWait_knownAt, runWait_eq_of_agree arrival_stream h_agree, h_before,
    stepNonPreemptiveOnline_congr (select' := fun s => selectSJF s.ready)
      (by simp [switchToSJF, h_time]),
    waitFrom_switchToSJF t select _ (by
      rw [stepNonPreemptiveOnline_time, h_time]; omega)]
  rfl

/-! ## SJF is the best continuation of any past -/

/-- **SJF is the best continuation of any past.** Take a well-formed stream, a
time `t`, and an online non-preemptive policy `select` -- any one, with any
past.  Switching to SJF at time `t` waits no longer, on the instance known at
`t` and over every horizon `t + T`, than *any* online non-preemptive policy
`select'` that shares `select`'s past (its run agrees with `select`'s before
time `t`), `select` itself included.  The competitors may idle on purpose and
read the whole state; they make their own decision at time `t` and after. -/
theorem runWait_switchToSJF_le_knownAt (arrival_stream : ℕ → List AperiodicProcess)
    (h_wf : WellFormedStream arrival_stream) (t : ℕ)
    (select select' : SchedState → Option AperiodicProcess) (h_online' : IsOnlinePolicy select')
    (h_agree : ∀ k < t, onlineRun select' arrival_stream k = onlineRun select arrival_stream k)
    (T : ℕ) :
    runWait (onlineRun (switchToSJF t select)) (knownAt arrival_stream t) (t + T) ≤
      runWait (onlineRun select') (knownAt arrival_stream t) (t + T) := by
  rw [runWait_switchToSJF_knownAt]
  change _ ≤ runWait (runSteps · (stepNonPreemptiveOnline select')) _ _
  rw [runWait_knownAt, runWait_eq_of_agree arrival_stream h_agree,
    stateBefore_congr arrival_stream h_agree]
  exact Nat.add_le_add_left (waitFrom_sjf_step_le select' h_online' _
    (stateBefore_ready_fresh select arrival_stream h_wf t) T) _

/-- **Switching to SJF never hurts**, on the instance known at the switch. -/
theorem runWait_switchToSJF_le (arrival_stream : ℕ → List AperiodicProcess)
    (h_wf : WellFormedStream arrival_stream) (t : ℕ)
    (select : SchedState → Option AperiodicProcess) (h_online : IsOnlinePolicy select) (T : ℕ) :
    runWait (onlineRun (switchToSJF t select)) (knownAt arrival_stream t) (t + T) ≤
      runWait (onlineRun select) (knownAt arrival_stream t) (t + T) :=
  runWait_switchToSJF_le_knownAt arrival_stream h_wf t select select h_online (fun _ _ => rfl) T

/-- **SJF is optimal given only the past.** Take any well-formed stream, any
time `t`, and any online non-preemptive policy (it may idle on purpose and read
the whole state) whose run agrees with SJF's before time `t`.  On the instance
known at `t` -- the same arrivals up to `t`, none after -- SJF's run waits no
longer than the policy's, over every horizon `t + T`.

This is `runWait_switchToSJF_le_knownAt` for SJF's own past.  The competitors
share SJF's past; against a competitor with a *different* past, SJF can lose
even on the known instance (`sjf_not_optimal_online`: stream B is its own
instance known at time 1, `knownAt_streamB_one`, and idling at time 0 beats SJF
there). -/
theorem runWait_sjf_le_knownAt (arrival_stream : ℕ → List AperiodicProcess)
    (h_wf : WellFormedStream arrival_stream) (t : ℕ)
    (select : SchedState → Option AperiodicProcess) (h_online : IsOnlinePolicy select)
    (h_agree : ∀ k < t, onlineRun select arrival_stream k = runSteps arrival_stream stepSJF k)
    (T : ℕ) :
    runWait (runSteps · stepSJF) (knownAt arrival_stream t) (t + T) ≤
      runWait (onlineRun select) (knownAt arrival_stream t) (t + T) := by
  have h := runWait_switchToSJF_le_knownAt arrival_stream h_wf t (fun s => selectSJF s.ready)
    select h_online h_agree T
  have h_sw : switchToSJF t (fun s => selectSJF s.ready) = fun s => selectSJF s.ready := by
    funext s
    simp [switchToSJF]
  rwa [h_sw] at h

/-- The policy that follows SJF before time `t` and `select` from then on. -/
def sjfUntil (t : ℕ) (select : SchedState → Option AperiodicProcess) :
    SchedState → Option AperiodicProcess :=
  fun s => if s.time < t then selectSJF s.ready else select s

/-- Following SJF for a while keeps a policy online. -/
theorem sjfUntil_isOnlinePolicy (t : ℕ) {select : SchedState → Option AperiodicProcess}
    (h_online : IsOnlinePolicy select) : IsOnlinePolicy (sjfUntil t select) := by
  intro s p h
  unfold sjfUntil at h
  split at h
  · exact selectSJF_mem _ p h
  · exact h_online s p h

/-- **SJF against any policy that takes over from it.** Let any online
non-preemptive policy take over from SJF at time `t`.  On the instance known at
`t`, SJF's own run waits no longer, over every horizon `t + T`. -/
theorem runWait_sjf_le_sjfUntil (arrival_stream : ℕ → List AperiodicProcess)
    (h_wf : WellFormedStream arrival_stream) (t : ℕ)
    (select : SchedState → Option AperiodicProcess) (h_online : IsOnlinePolicy select) (T : ℕ) :
    runWait (runSteps · stepSJF) (knownAt arrival_stream t) (t + T) ≤
      runWait (onlineRun (sjfUntil t select)) (knownAt arrival_stream t) (t + T) :=
  runWait_sjf_le_knownAt arrival_stream h_wf t _ (sjfUntil_isOnlinePolicy t h_online)
    (onlineRun_agree_of_time_lt arrival_stream t (select' := fun s => selectSJF s.ready)
      fun s hs => by simp [sjfUntil, hs]) T

/-! ## The cost of a convoy, on any stream -/

/-- **A convoy dispatch strictly costs, on any stream.** Take a well-formed
stream and any online non-preemptive policy.  If at step `t` its run dispatches
`p` while a job `q` with strictly less work left waits -- a convoy at a dispatch
moment, as in `HasConvoyEffect` -- then switching to SJF at time `t` waits
strictly less on the instance known at `t`, over every horizon `t + T` that
leaves time for the work waiting when step `t` starts. -/
theorem runWait_switchToSJF_lt_of_convoy (arrival_stream : ℕ → List AperiodicProcess)
    (h_wf : WellFormedStream arrival_stream) (t : ℕ)
    (select : SchedState → Option AperiodicProcess) (h_online : IsOnlinePolicy select)
    {p q : AperiodicProcess} (h_disp : DispatchesAt (onlineRun select) arrival_stream t p)
    (hq : q ∈ (onlineRun select arrival_stream t).ready) (h_lt : q.remaining < p.remaining)
    (T : ℕ)
    (hT : ((stateBefore arrival_stream (stepNonPreemptiveOnline select) t).ready.map
      (·.burst)).sum ≤ T) :
    runWait (onlineRun (switchToSJF t select)) (knownAt arrival_stream t) (t + T) <
      runWait (onlineRun select) (knownAt arrival_stream t) (t + T) := by
  set s := stateBefore arrival_stream (stepNonPreemptiveOnline select) t with hs
  have h_fresh : ∀ r ∈ s.ready, r.remaining = r.burst :=
    stateBefore_ready_fresh select arrival_stream h_wf t
  -- the policy's step `t`, from `s`, is a dispatch of `p`
  have h_step : onlineRun select arrival_stream t = stepNonPreemptiveOnline select s :=
    runSteps_eq_step_stateBefore _ _ t
  obtain ⟨h_p_run, h_new⟩ := h_disp
  rw [h_step] at h_p_run hq
  have h_s_new : s.running.map (·.id) ≠ some p.id := by
    cases t with
    | zero => simp [hs, stateBefore]
    | succ k => exact h_new k rfl
  obtain ⟨h_sel, h_ready⟩ := stepNonPreemptiveOnline_dispatch_cases select s h_p_run h_s_new
  have hp := h_online s p h_sel
  rw [h_ready] at hq
  rw [h_fresh p hp, h_fresh q (List.mem_of_mem_erase hq)] at h_lt
  rw [runWait_switchToSJF_knownAt]
  change _ < runWait (runSteps · (stepNonPreemptiveOnline select)) _ _
  rw [runWait_knownAt]
  exact Nat.add_lt_add_left (waitFrom_sjf_step_lt_of_convoy select h_online s h_fresh h_p_run
    h_ready hp hq h_lt T hT) _

/-- **The convoy effect costs, on general streams.** An online non-preemptive
policy with the convoy effect waits strictly longer, on some well-formed stream
known up to some time `t`, than the same policy switched to SJF at `t`, at
every long enough horizon.  (On batches, `hasBatchConvoyEffect_iff_runWait`
says this against SJF itself.) -/
theorem hasConvoyEffect_switchToSJF_lt (select : SchedState → Option AperiodicProcess)
    (h_online : IsOnlinePolicy select) (h : HasConvoyEffect (stepNonPreemptiveOnline select)) :
    ∃ arrival_stream, WellFormedStream arrival_stream ∧ ∃ t T₀, ∀ T, T₀ ≤ T →
      runWait (onlineRun (switchToSJF t select)) (knownAt arrival_stream t) (t + T) <
        runWait (onlineRun select) (knownAt arrival_stream t) (t + T) := by
  obtain ⟨as, h_wf, t, p, h_disp, q, hq, h_lt⟩ :=
    (hasConvoyEffectRun_iff (onlineRun select)).mp h
  exact ⟨as, h_wf, t, _, fun T hT =>
    runWait_switchToSJF_lt_of_convoy as h_wf t select h_online h_disp hq h_lt T hT⟩

/-! ## The batch case: `t = 0` -/

/-- **The batch case** (`t = 0`).  On a batch released at time 0, SJF waits no
longer than any online non-preemptive policy, idling or not, over every
horizon.  This strengthens `runWait_sjf_le`, which compares only with
ready-queue policies that never idle, and only once the horizon covers the
total work. -/
theorem runWait_sjf_le_online_batch (l : List AperiodicProcess) (h_batch : IsBatch l)
    (select : SchedState → Option AperiodicProcess) (h_online : IsOnlinePolicy select) (T : ℕ) :
    runWait (runSteps · stepSJF) (batchStream l) T ≤ runWait (onlineRun select) (batchStream l) T := by
  have h_known : knownAt (batchStream l) 0 = batchStream l := by
    funext j
    cases j <;> rfl
  have := runWait_sjf_le_knownAt (batchStream l) (batchStream_wf h_batch) 0 select h_online
    (fun k hk => absurd hk (Nat.not_lt_zero k)) T
  rwa [h_known, Nat.zero_add] at this

/-- `runWait_sjf_le` again, as a corollary of the batch case: no `h_none` and
no horizon assumption are needed. -/
theorem runWait_sjf_le_batch {select : List AperiodicProcess → Option AperiodicProcess}
    (h_mem : ∀ l p, select l = some p → p ∈ l) (l : List AperiodicProcess) (h_batch : IsBatch l)
    (T : ℕ) :
    runWait (runSteps · stepSJF) (batchStream l) T ≤
      runWait (runSteps · (stepNonPreemptive select)) (batchStream l) T := by
  have := runWait_sjf_le_online_batch l h_batch (fun s => select s.ready)
    (fun s p h => h_mem s.ready p h) T
  rwa [onlineRun_ready] at this

/-! ## Sanity check: a different past -/

/-- Stream B is its own instance known at time 1: its last arrival is at time 1. -/
theorem knownAt_streamB_one : knownAt streamB 1 = streamB := by
  funext j
  rcases j with _ | _ | j
  · rfl
  · rfl
  · rw [knownAt_of_lt streamB (by omega), streamB_nil _ (by omega)]

/-- `idleThenSJF`, which beats SJF on stream B (`sjf_not_optimal_online`), does
not share SJF's past: at step 0 it idles while SJF dispatches.  So it is not a
competitor in `runWait_sjf_le_knownAt`. -/
example : (onlineRun idleThenSJF streamB 0).running ≠ (runSteps streamB stepSJF 0).running := by
  decide

end ConvoyEffect
