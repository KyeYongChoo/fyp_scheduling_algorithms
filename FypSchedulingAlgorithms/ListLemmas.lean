import Mathlib.Tactic.Linarith

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
