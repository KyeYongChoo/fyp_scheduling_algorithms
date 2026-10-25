/-
Copyright (c) 2026 Choo Kye Yong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Choo Kye Yong
-/
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# List lemmas

General facts about lists: their statements mention nothing about scheduling
(some docstrings say where a scheduler uses them).

* Folds: a fold of a monotone accumulator never drops below its start, nor
  below the fold over a prefix (`foldl_ge_init`, `foldl_prefix_le`; currently
  unused).
* Ready-queue facts, used by the Starvation files: a member splits a list at
  its first occurrence (`mem_split_canonical`), and taking the head off either
  removes that member or shortens the split before it (`erase_head_split`); a
  per-element invariant survives a dispatch or a preemption
  (`dispatch_preserves`, `expire_swap_preserves`).
* Sums of lists of naturals: termwise bounds on mapped sums
  (`sum_map_le_sum_map`, `sum_map_lt_sum_map`, `sum_map_const_add`), filtered
  sums grow with the filter (`sum_map_filter_le_of_imp`), a nonempty list has an
  entry of least image (`exists_min_image_of_ne_nil`), and sorted
  order has the least prefix sums among the list's permutations
  (`sum_take_sorted_le`).
* The sum of the `k` smallest entries (`smallSum`): it is the least `k`-prefix
  sum over all orderings, how it changes when one entry is lowered by 1 or the
  same entries are added to two lists, and how it bounds the number of positive
  entries (`length_filter_pos_le`).
* Updating one entry of a list without repeats under a filter and a map: the
  rest is common to both sides (`filter_map_update`; used by the schedule
  bridges, `Schedules` and `PeriodicSchedules`), and a mapped sum changes by the
  change at that entry (`sum_map_update`; used by `EDFOptimality`).
-/

/-- Folding a monotone accumulator function never drops below the initial
value: if `f acc x ≥ acc` for every `acc, x`, then `l.foldl f init ≥ init`. -/
theorem foldl_ge_init
  {α}
  (f : ℕ → α → ℕ)
  (h_mono : ∀ acc x, acc ≤ f acc x)
  (l : List α) (init : ℕ) :
  init ≤ l.foldl f init := by
  induction l generalizing init with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl]
    exact le_trans (h_mono init hd) (ih (f init hd))

/-- Folding a monotone accumulator function over a prefix of a list never
exceeds folding it over the whole list: `(l.take n).foldl f init ≤
l.foldl f init`. -/
theorem foldl_prefix_le
  {α}
  (f : ℕ → α → ℕ)
  (h_mono : ∀ acc x, acc ≤ f acc x)
  (l : List α) (n : ℕ) (init : ℕ) :
  (l.take n).foldl f init ≤ l.foldl f init := by
  induction l generalizing n init with
  | nil => simp
  | cons hd tl ih =>
    cases n with
    | zero =>
      simp only [List.foldl]
      exact le_trans (h_mono init hd) (foldl_ge_init f h_mono tl (f init hd))
    | succ n =>
      simp only [List.take, List.foldl]
      apply ih

/-- Any membership witness `p ∈ l` can be presented canonically as
`l = pre ++ p :: suf` with `p` not repeated anywhere in `pre` (split at `p`'s
first occurrence). -/
theorem mem_split_canonical {α} {l : List α} {p : α} (h : p ∈ l) :
    ∃ pre suf, l = pre ++ p :: suf ∧ p ∉ pre := by
  induction l with
  | nil => simp at h
  | cons hd tl ih =>
    by_cases h_eq : hd = p
    · exact ⟨[], tl, by grind, by simp⟩
    · have h_tl : p ∈ tl := by
        rcases List.mem_cons.mp h with rfl | h'
        · exact absurd rfl h_eq
        · exact h'
      obtain ⟨pre, suf, h_split, h_notin⟩ := ih h_tl
      exact ⟨hd :: pre, suf, by rw [h_split]; rfl, by simp [h_notin, Ne.symm h_eq]⟩

/-- Removing the head of a list `hd :: rest` that canonically decomposes as
`pre ++ p :: suf` (`p ∉ pre`) either removes `p` itself (when `pre = []` and
`hd = p`), or leaves the same canonical split one element shorter on the
`pre` side. This is the one-step version of a "distance to `p`" measure. -/
lemma erase_head_split {α : Type*} {rest pre suf : List α} {hd p : α}
    (h_split : hd :: rest = pre ++ p :: suf) (h_notin : p ∉ pre) :
    (pre = [] ∧ hd = p)
    ∨ (∃ pre', rest = pre' ++ p :: suf ∧ p ∉ pre' ∧ pre'.length < pre.length) := by
  cases pre with
  | nil => left; simp only [List.nil_append, List.cons.injEq] at h_split; exact ⟨rfl, h_split.1⟩
  | cons a tl =>
    right
    simp only [List.cons_append, List.cons.injEq] at h_split
    exact ⟨tl, h_split.2, List.not_mem_of_not_mem_cons h_notin, by simp⟩

/-- Taking the head off a list whose every element satisfies `P` leaves both pieces
satisfying `P`: the head itself, and every element of the tail. Schedulers use this
for dispatch, where the head becomes the running process and the tail the new queue.
`P` is left general so one lemma serves every per-element invariant. -/
lemma dispatch_preserves {α} {P : α → Prop} (p : α) (ps : List α)
    (h : ∀ q ∈ p :: ps, P q) :
    (∀ q ∈ ps, P q) ∧ P p :=
  ⟨fun q hq => h q (List.mem_cons_of_mem _ hq), h p List.mem_cons_self⟩

/-- `dispatch_preserves` with an extra element pushed onto the far end: the head `nx`
comes off the front and `x` joins the back. Schedulers use this for preemption, where
the process losing the CPU goes to the back of the queue, so the caller supplies `P x`
separately (what survives a preemption depends on the invariant). -/
lemma expire_swap_preserves {α} {P : α → Prop} (x nx : α) (ps : List α)
    (h : ∀ q ∈ nx :: ps, P q) (h_x : P x) :
    (∀ q ∈ ps ++ [x], P q) ∧ P nx := by
  refine ⟨fun q hq => ?_, h nx List.mem_cons_self⟩
  rcases List.mem_append.mp hq with hq' | hq'
  · exact h q (List.mem_cons_of_mem _ hq')
  · simp only [List.mem_singleton] at hq'
    subst hq'
    exact h_x

/-! ## Sums of lists of naturals -/

section Sums

open scoped List

/-- Adding a constant to every term adds it once per term. -/
theorem sum_map_const_add {α : Type} (l : List α) (c : ℕ) (f : α → ℕ) :
    (l.map fun i => c + f i).sum = c * l.length + (l.map f).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp only [List.map_cons, List.sum_cons, ih, List.length_cons]; ring

/-- A nonempty list has an entry of least image. -/
theorem exists_min_image_of_ne_nil {α β : Type} [LinearOrder β] (l : List α) (f : α → β)
    (h : l ≠ []) : ∃ a ∈ l, ∀ b ∈ l, f a ≤ f b := by
  induction l with
  | nil => exact absurd rfl h
  | cons x xs ih =>
    by_cases h_xs : xs = []
    · subst h_xs
      exact ⟨x, List.mem_singleton_self x, fun b hb => by simp_all⟩
    obtain ⟨a, ha, h_min⟩ := ih h_xs
    by_cases h_le : f x ≤ f a
    · refine ⟨x, List.mem_cons_self .., fun b hb => ?_⟩
      rcases List.mem_cons.mp hb with rfl | hb
      · exact le_rfl
      · exact h_le.trans (h_min b hb)
    · refine ⟨a, List.mem_cons_of_mem _ ha, fun b hb => ?_⟩
      rcases List.mem_cons.mp hb with rfl | hb
      · exact (lt_of_not_ge h_le).le
      · exact h_min b hb

/-- A filtered sum grows with the filter. -/
theorem sum_map_filter_le_of_imp {α : Type} (l : List α) (g : α → ℕ) {P Q : α → Prop}
    [DecidablePred P] [DecidablePred Q] (h : ∀ x, P x → Q x) :
    ((l.filter (P ·)).map g).sum ≤ ((l.filter (Q ·)).map g).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    by_cases hP : P x
    · simp [hP, h x hP]
      omega
    · by_cases hQ : Q x
      · simp [hP, hQ]
        omega
      · simpa [hP, hQ] using ih

/-- Termwise `≤` gives `≤` of the sums. -/
theorem sum_map_le_sum_map {α : Type} (l : List α) {f g : α → ℕ} (h : ∀ i ∈ l, f i ≤ g i) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (h x (List.mem_cons_self ..))
      (ih fun i hi => h i (List.mem_cons_of_mem _ hi))

/-- Termwise `≤`, strict at one term, gives `<` of the sums. -/
theorem sum_map_lt_sum_map {α : Type} (l : List α) {f g : α → ℕ} (h : ∀ i ∈ l, f i ≤ g i)
    {j : α} (hj : j ∈ l) (h_lt : f j < g j) : (l.map f).sum < (l.map g).sum := by
  induction l with
  | nil => simp at hj
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons]
    have hx := h x (List.mem_cons_self ..)
    have hl := sum_map_le_sum_map l fun i hi => h i (List.mem_cons_of_mem _ hi)
    rcases List.mem_cons.mp hj with rfl | hj
    · omega
    · have := ih (fun i hi => h i (List.mem_cons_of_mem _ hi)) hj
      omega

/-- Moving an entry no larger than every entry ahead of it to the front lowers
every prefix sum. -/
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

/-- **Sorted order has the least prefix sums**: the first `i` entries of the
sorted order are the `i` smallest. -/
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

/-! ## The sum of the `k` smallest entries -/

/-- The sum of the `k` smallest entries of `x` (all of them if `k ≥ x.length`). -/
def smallSum (x : List ℕ) (k : ℕ) : ℕ :=
  ((x.mergeSort fun a b => decide (a ≤ b)).take k).sum

/-- `mergeSort` sorts. -/
theorem mergeSort_pairwise_le (x : List ℕ) :
    (x.mergeSort fun a b => decide (a ≤ b)).Pairwise (· ≤ ·) :=
  (List.pairwise_mergeSort (fun a b c hab hbc => by simp at *; omega)
    (fun a b => by simp; omega) x).imp (by simp)

/-- **The `k` smallest entries sum to the least `k`-prefix sum** over all
orderings of the list. -/
theorem smallSum_le {x c : List ℕ} (h : x ~ c) (k : ℕ) : smallSum x k ≤ (c.take k).sum :=
  sum_take_sorted_le (mergeSort_pairwise_le x) ((List.mergeSort_perm _ _).trans h) k

/-- `smallSum` only depends on the entries, not their order. -/
theorem smallSum_perm {x y : List ℕ} (h : x ~ y) (k : ℕ) : smallSum x k = smallSum y k :=
  Nat.le_antisymm (smallSum_le (h.trans (List.mergeSort_perm y _).symm) k)
    (smallSum_le (h.symm.trans (List.mergeSort_perm x _).symm) k)

/-- A list of zeros has nothing to sum. -/
theorem smallSum_eq_zero {x : List ℕ} (h : ∀ u ∈ x, u = 0) (k : ℕ) : smallSum x k = 0 := by
  have := smallSum_le (List.Perm.refl x) k
  have h0 : (x.take k).sum = 0 :=
    List.sum_eq_zero_iff_forall_eq_nat.mpr fun u hu => h u (List.mem_of_mem_take hu)
  omega

/-- Changing one entry of a list, as seen from the rest of a permutation. -/
theorem perm_middle_replace {A R X : List ℕ} {v : ℕ} (h : A ++ v :: R ~ v :: X) (w : ℕ) :
    A ++ w :: R ~ w :: X :=
  List.perm_middle.trans ((List.perm_middle.symm.trans h).cons_inv.cons w)

/-- Lowering one entry by 1 lowers each prefix sum by at most 1. -/
theorem sum_take_sub_one_le (A R : List ℕ) (v k : ℕ) :
    ((A ++ v :: R).take k).sum ≤ ((A ++ (v - 1) :: R).take k).sum + 1 := by
  induction A generalizing k with
  | nil =>
    cases k with
    | zero => simp
    | succ k => simp only [List.nil_append, List.take_succ_cons, List.sum_cons]; omega
  | cons a A ih =>
    cases k with
    | zero => simp
    | succ k =>
      simp only [List.cons_append, List.take_succ_cons, List.sum_cons]
      have := ih k
      omega

/-- Lowering a positive entry inside the prefix lowers the prefix sum by exactly 1. -/
theorem sum_take_sub_one_eq (A R : List ℕ) {v k : ℕ} (hv : 0 < v) (hk : A.length < k) :
    ((A ++ (v - 1) :: R).take k).sum + 1 = ((A ++ v :: R).take k).sum := by
  induction A generalizing k with
  | nil =>
    obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by simp at hk; omega⟩
    simp only [List.nil_append, List.take_succ_cons, List.sum_cons]
    omega
  | cons a A ih =>
    obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by simp at hk; omega⟩
    simp only [List.cons_append, List.take_succ_cons, List.sum_cons]
    have := ih (k := k) (by simp at hk; omega)
    omega

/-- **Lowering one entry by 1 lowers the sum of the `k` smallest by at most 1**,
whichever entry it is (a tick of any schedule, in `SRTFOptimality`). -/
theorem smallSum_cons_le (v : ℕ) (X : List ℕ) (k : ℕ) :
    smallSum (v :: X) k ≤ smallSum ((v - 1) :: X) k + 1 := by
  set c := ((v - 1) :: X).mergeSort fun a b => decide (a ≤ b)
  have hc : c ~ (v - 1) :: X := List.mergeSort_perm _ _
  obtain ⟨A, B, hAB⟩ := List.append_of_mem (hc.symm.subset (List.mem_cons_self ..))
  rw [hAB] at hc
  calc smallSum (v :: X) k ≤ ((A ++ v :: B).take k).sum :=
        smallSum_le (perm_middle_replace hc v).symm k
    _ ≤ ((A ++ (v - 1) :: B).take k).sum + 1 := sum_take_sub_one_le A B v k
    _ = smallSum ((v - 1) :: X) k + 1 := by rw [← hAB]; rfl

/-- **Lowering a least positive entry by 1 lowers the sum of the `k` smallest by
at least 1** (so by exactly 1, with `smallSum_cons_le`), unless that sum is 0
afterwards (SRTF's tick, in `SRTFOptimality`). -/
theorem smallSum_cons_sub_one {v : ℕ} {X : List ℕ} (hv : 0 < v)
    (h_min : ∀ u ∈ X, 0 < u → v ≤ u) (k : ℕ) :
    smallSum ((v - 1) :: X) k + 1 ≤ smallSum (v :: X) k ∨ smallSum ((v - 1) :: X) k = 0 := by
  set c := (v :: X).mergeSort fun a b => decide (a ≤ b) with hc_def
  have hc : c ~ v :: X := List.mergeSort_perm _ _
  have h_sorted : c.Pairwise (· ≤ ·) := mergeSort_pairwise_le _
  have h_split := List.take_append_drop k c
  by_cases hP : v ∈ c.take k
  · -- `v` is among the `k` smallest: lower it there
    left
    obtain ⟨A, B, hAB⟩ := List.append_of_mem hP
    have hc' : c = A ++ v :: (B ++ c.drop k) := by
      calc c = c.take k ++ c.drop k := h_split.symm
        _ = _ := by rw [hAB]; simp
    have hlen : A.length < k := by
      have := List.length_take_le k c
      rw [hAB] at this
      simp at this
      omega
    rw [hc'] at hc
    have h1 := smallSum_le (perm_middle_replace hc (v - 1)).symm k
    have h2 := sum_take_sub_one_eq A (B ++ c.drop k) hv hlen
    have h3 : smallSum (v :: X) k = ((A ++ v :: (B ++ c.drop k)).take k).sum := by
      rw [← hc']
      rfl
    omega
  · -- the `k` smallest are all 0, and `v` lies beyond them
    right
    have hv_c : v ∈ c := hc.symm.subset (List.mem_cons_self ..)
    have hv_drop : v ∈ c.drop k := by
      rw [← h_split] at hv_c
      exact (List.mem_append.mp hv_c).resolve_left hP
    have h_le : ∀ a ∈ c.take k, ∀ b ∈ c.drop k, a ≤ b := by
      have := h_sorted
      rw [← h_split] at this
      exact (List.pairwise_append.mp this).2.2
    have h_zero : ∀ u ∈ c.take k, u = 0 := by
      intro u hu
      have hu_ne : u ≠ v := fun h => hP (h ▸ hu)
      have hu_X : u ∈ X := by
        have := hc.subset (List.mem_of_mem_take hu)
        exact (List.mem_cons.mp this).resolve_left hu_ne
      have := h_le u hu v hv_drop
      by_contra h0
      have := h_min u hu_X (by omega)
      omega
    obtain ⟨A, B, hAB⟩ := List.append_of_mem hv_drop
    have hc' : c = (c.take k ++ A) ++ v :: B := by
      rw [List.append_assoc, ← hAB, h_split]
    have h_len : (c.take k).length = k := by
      have : c.drop k ≠ [] := by rw [hAB]; simp
      rw [List.length_take]
      have := List.drop_eq_nil_iff.not.mp this
      omega
    rw [hc'] at hc
    have h1 := smallSum_le (perm_middle_replace hc (v - 1)).symm k
    rw [List.append_assoc, List.take_append_of_le_length (by omega),
      List.take_of_length_le (by omega),
      List.sum_eq_zero_iff_forall_eq_nat.mpr h_zero] at h1
    omega

/-- **Adding the same entry keeps the majorisation**: if, for every `k`, the `k`
smallest entries of `y` sum to no more than those of `x` (two lists of the same
length), the same holds after adding one entry to both (a release, in
`SRTFOptimality`). -/
theorem smallSum_cons_mono {x y : List ℕ} (hlen : y.length = x.length)
    (h : ∀ j, smallSum y j ≤ smallSum x j) (b k : ℕ) :
    smallSum (b :: y) k ≤ smallSum (b :: x) k := by
  set c := (b :: x).mergeSort fun a b => decide (a ≤ b)
  have hc : c ~ b :: x := List.mergeSort_perm _ _
  obtain ⟨A, B, hAB⟩ := List.append_of_mem (hc.symm.subset (List.mem_cons_self ..))
  rw [hAB] at hc
  have hx : A ++ B ~ x := (List.perm_middle.symm.trans hc).cons_inv
  have hA : A.length ≤ x.length := by rw [← hx.length_eq]; simp
  have h_eq : smallSum (b :: x) k = ((A ++ b :: B).take k).sum := by rw [← hAB]; rfl
  set s := y.mergeSort fun a b => decide (a ≤ b)
  have hs : s ~ y := List.mergeSort_perm _ _
  rw [h_eq]
  by_cases hk : k ≤ A.length
  · -- the new entry is not among the `k` smallest of `b :: x`
    have h1 := smallSum_le ((hs.append_right [b]).trans (List.perm_append_singleton b y)).symm k
    rw [List.take_append_of_le_length (by rw [hs.length_eq]; omega)] at h1
    have h2 := smallSum_le hx.symm k
    rw [List.take_append_of_le_length hk] at h2
    rw [List.take_append_of_le_length hk]
    have := h k
    change smallSum (b :: y) k ≤ smallSum y k at h1
    omega
  · -- it is: the rest are the `k - 1` smallest of `x`, at best
    obtain ⟨m, rfl⟩ : ∃ m, k = A.length + 1 + m := ⟨k - A.length - 1, by omega⟩
    have h1 := smallSum_le (List.Perm.cons b hs).symm (A.length + 1 + m)
    rw [show A.length + 1 + m = (m + A.length) + 1 by omega, List.take_succ_cons,
      List.sum_cons] at h1
    have h2 := smallSum_le hx.symm (A.length + m)
    have h3 := h (A.length + m)
    rw [List.take_append, List.take_of_length_le (by omega), show A.length + m - A.length = m by
      omega] at h2
    rw [List.take_append, List.take_of_length_le (by omega),
      show A.length + 1 + m - A.length = m + 1 by omega, List.take_succ_cons, List.sum_append,
      List.sum_cons]
    rw [List.sum_append] at h2
    change smallSum (b :: y) (m + A.length + 1) ≤ b + smallSum y (m + A.length) at h1
    rw [show m + A.length + 1 = A.length + 1 + m by omega, Nat.add_comm m A.length] at h1
    omega

/-- Appending the same list to two lists of the same length keeps the
majorisation (`∀ k, smallSum y k ≤ smallSum x k`): the releases of one step. -/
theorem smallSum_append_mono {x y : List ℕ} (hlen : y.length = x.length)
    (h : ∀ j, smallSum y j ≤ smallSum x j) (L : List ℕ) (k : ℕ) :
    smallSum (y ++ L) k ≤ smallSum (x ++ L) k := by
  induction L generalizing x y with
  | nil => simpa using h k
  | cons b L ih =>
    have h' : ∀ j, smallSum (y ++ [b]) j ≤ smallSum (x ++ [b]) j := fun j => by
      rw [smallSum_perm (List.perm_append_singleton b y),
        smallSum_perm (List.perm_append_singleton b x)]
      exact smallSum_cons_mono hlen h b j
    have := ih (x := x ++ [b]) (y := y ++ [b]) (by simp [hlen]) h'
    simpa using this

/-- **Counting positive entries.** If, for every `k`, the `k` smallest entries
of `y` sum to no more than those of `x` (two lists of the same length), then `y`
has no more positive entries than `x`: the `z` zeros of `x` force `z` zeros on
`y` (SRTF's unfinished jobs, in `SRTFOptimality`). -/
theorem length_filter_pos_le {x y : List ℕ} (hlen : y.length = x.length)
    (h : ∀ k, smallSum y k ≤ smallSum x k) :
    (y.filter fun a => 0 < a).length ≤ (x.filter fun a => 0 < a).length := by
  set p : ℕ → Bool := fun a => decide (0 < a)
  have hx := (List.filter_append_perm p x).length_eq
  have hy := (List.filter_append_perm p y).length_eq
  simp only [List.length_append] at hx hy
  set z := (x.filter fun a => !p a).length
  -- the zeros of `x` come first in some ordering, so its `z` smallest sum to 0
  have hx0 : smallSum x z = 0 := by
    have := smallSum_le ((List.perm_append_comm.trans (List.filter_append_perm p x))).symm z
    rw [List.take_append_of_le_length le_rfl, List.take_of_length_le le_rfl,
      List.sum_eq_zero_iff_forall_eq_nat.mpr fun u hu => by
        simpa [p] using (List.mem_filter.mp hu).2] at this
    omega
  -- so the `z` smallest entries of `y` are zeros
  set s := y.mergeSort fun a b => decide (a ≤ b)
  have hs : s ~ y := List.mergeSort_perm _ _
  have hy0 : (s.take z).sum = 0 := by have := h z; change (s.take z).sum ≤ _ at this; omega
  have h_all : ∀ u ∈ s.take z, u = 0 := List.sum_eq_zero_iff_forall_eq_nat.mp hy0
  have h_take_len : (s.take z).length = z := by
    rw [List.length_take, hs.length_eq]
    omega
  have h_sub : (s.take z).filter (fun a => !p a) <+ s.filter (fun a => !p a) :=
    (List.take_sublist z s).filter _
  rw [List.filter_eq_self.mpr fun u hu => by simp [p, h_all u hu]] at h_sub
  have := h_sub.length_le
  rw [h_take_len, (hs.filter _).length_eq] at this
  change (y.filter p).length ≤ (x.filter p).length
  omega

end Sums

/-! ## Updating one entry under a filter and a map -/

section Update

open scoped List

/-- Updating one entry `q` of a list without repeats: if `P'` and `J'` agree with
`P` and `J` away from `q`, the two filtered and mapped lists differ at most in
`q`'s image, and the rest is common to both sides. -/
theorem filter_map_update {α β : Type} {L : List α} (h_nodup : L.Nodup)
    {q : α} (hq : q ∈ L) (P P' : α → Bool) (J J' : α → β)
    (h : ∀ p ∈ L, p ≠ q → P' p = P p ∧ J' p = J p) :
    ∃ rest, (L.filter P).map J ~ (if P q then [J q] else []) ++ rest ∧
      (L.filter P').map J' ~ (if P' q then [J' q] else []) ++ rest := by
  classical
  have h_perm := List.perm_cons_erase hq
  have h_rest : ((L.erase q).filter P').map J' = ((L.erase q).filter P).map J := by
    have h' : ∀ p ∈ L.erase q, P' p = P p ∧ J' p = J p := fun p hp =>
      h p (List.mem_of_mem_erase hp) ((h_nodup.mem_erase_iff).mp hp).1
    rw [List.filter_congr fun p hp => (h' p hp).1]
    exact List.map_congr_left fun p hp => (h' p (List.mem_filter.mp hp).1).2
  refine ⟨((L.erase q).filter P).map J, ?_, ?_⟩
  · refine ((h_perm.filter P).map J).trans ?_
    rw [List.filter_cons]
    split <;> simp
  · refine ((h_perm.filter P').map J').trans ?_
    rw [List.filter_cons, ← h_rest]
    split <;> simp

/-- Changing one entry `q` of a list without repeats changes the sum of a map by the
change at `q`: if `f` and `g` agree away from `q`, then
`(L.map f).sum + g q = (L.map g).sum + f q`. -/
theorem sum_map_update {α : Type} {L : List α} (h_nodup : L.Nodup) {q : α} (hq : q ∈ L)
    (f g : α → ℕ) (h : ∀ p ∈ L, p ≠ q → f p = g p) :
    (L.map f).sum + g q = (L.map g).sum + f q := by
  classical
  have h_perm := List.perm_cons_erase hq
  have h_rest : (L.erase q).map f = (L.erase q).map g :=
    List.map_congr_left fun p hp =>
      h p (List.mem_of_mem_erase hp) ((h_nodup.mem_erase_iff).mp hp).1
  rw [(h_perm.map f).sum_nat, (h_perm.map g).sum_nat, List.map_cons, List.map_cons,
    List.sum_cons, List.sum_cons, h_rest]
  omega

end Update
