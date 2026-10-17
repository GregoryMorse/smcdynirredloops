module

public import SmcIrred.Spec.LNF
public import SmcIrred.Graph.DfsInv

public section

namespace SmcIrred

/-- One round of backward search: add every vertex satisfying `S` with an edge into the set `R`. -/
@[expose] def pathStep (g : Digraph) (S : Nat → Bool) (R : List Nat) : List Nat :=
  R ++ (List.range g.n).filter fun a => !R.contains a && S a && (g.succ a).any fun c => R.contains c

@[expose] def pathIter (g : Digraph) (S : Nat → Bool) : Nat → List Nat → List Nat
  | 0, R => R
  | k + 1, R => pathIter g S k (pathStep g S R)

/-- The vertices that reach `b` inside `S` (computed with `g.n + 1` rounds). -/
@[expose] def pathSet (g : Digraph) (S : Nat → Bool) (b : Nat) : List Nat :=
  pathIter g S (g.n + 1) (if b < g.n ∧ S b = true then [b] else [])

variable {g : Digraph} {S : Nat → Bool}

theorem pathIter_succ (k : Nat) : ∀ R, pathIter g S (k + 1) R = pathStep g S (pathIter g S k R) := by
  induction k with
  | zero => intro R; rfl
  | succ k ih => intro R; show pathIter g S (k + 1) (pathStep g S R) = _; rw [ih]; rfl

theorem sub_pathStep (R : List Nat) : ∀ x, x ∈ R → x ∈ pathStep g S R := fun x hx => by
  simp [pathStep, hx]

theorem sub_pathIter (k : Nat) : ∀ R x, x ∈ R → x ∈ pathIter g S k R := by
  induction k with
  | zero => intro R x h; exact h
  | succ k ih => intro R x h; exact ih _ _ (sub_pathStep R x h)

theorem mem_pathStep {R : List Nat} {x : Nat} :
    x ∈ pathStep g S R ↔ x ∈ R ∨ (x < g.n ∧ x ∉ R ∧ S x = true ∧ ∃ c, c ∈ g.succ x ∧ c ∈ R) := by
  simp only [pathStep, List.mem_append, List.mem_filter, List.mem_range, Bool.and_eq_true, Bool.not_eq_true',
    List.any_eq_true, List.contains_iff_mem]
  constructor
  · rintro (h | ⟨h1, ⟨h2, h3⟩, c, h4, h5⟩)
    · exact Or.inl h
    · exact Or.inr ⟨h1, by simpa using h2, h3, c, h4, by simpa using h5⟩
  · rintro (h | ⟨h1, h2, h3, c, h4, h5⟩)
    · exact Or.inl h
    · exact Or.inr ⟨h1, ⟨by simpa using h2, h3⟩, c, h4, by simpa using h5⟩

theorem lt_pathStep {R : List Nat} (h : ∀ x ∈ R, x < g.n) : ∀ x ∈ pathStep g S R, x < g.n := by
  intro x hx
  rcases mem_pathStep.1 hx with hx | ⟨hn, -⟩
  · exact h x hx
  · exact hn

theorem lt_pathIter (k : Nat) : ∀ R : List Nat, (∀ x ∈ R, x < g.n) → ∀ x ∈ pathIter g S k R, x < g.n := by
  induction k with
  | zero => intro R h; exact h
  | succ k ih => intro R h; exact ih _ (lt_pathStep h)

/-- Soundness: everything collected reaches `b`. -/
theorem good_pathStep {b : Nat} {R : List Nat}
    (h : ∀ x ∈ R, x < g.n ∧ PathIn g (fun z => S z = true) x b) :
    ∀ x ∈ pathStep g S R, x < g.n ∧ PathIn g (fun z => S z = true) x b := by
  intro x hx
  rcases mem_pathStep.1 hx with hx | ⟨hxn, -, hs, c, hc, hcR⟩
  · exact h x hx
  · obtain ⟨hcn, hp⟩ := h c hcR
    exact ⟨hxn, .step hs ⟨hxn, hcn, hc⟩ hp⟩

theorem good_pathIter {b : Nat} (k : Nat) : ∀ R : List Nat,
    (∀ x ∈ R, x < g.n ∧ PathIn g (fun z => S z = true) x b) →
    ∀ x ∈ pathIter g S k R, x < g.n ∧ PathIn g (fun z => S z = true) x b := by
  induction k with
  | zero => intro R h; exact h
  | succ k ih => intro R h; exact ih _ (good_pathStep h)

/-- Measure: the number of vertices not yet collected. -/
@[expose] def missing (g : Digraph) (R : List Nat) : Nat := ((List.range g.n).filter fun x => !R.contains x).length

theorem missing_le (R : List Nat) : missing g R ≤ g.n := by
  have := List.length_filter_le (fun x => !R.contains x) (List.range g.n)
  simpa [missing] using this

theorem pathStep_lt (R : List Nat) (hne : pathStep g S R ≠ R) : missing g (pathStep g S R) < missing g R := by
  have hex : ∃ a, a ∈ pathStep g S R ∧ a ∉ R := by
    by_cases hall : ∀ a, a ∈ pathStep g S R → a ∈ R
    · exfalso
      apply hne
      have hF : ∀ a ∈ (List.range g.n).filter (fun a => !R.contains a && S a && (g.succ a).any fun c => R.contains c), False := by
        intro a ha
        have h1 : a ∈ pathStep g S R := by simp only [pathStep]; exact List.mem_append_right _ ha
        have h2 := hall a h1
        simp only [List.mem_filter, Bool.and_eq_true, Bool.not_eq_true'] at ha
        have := ha.2
        simp_all
      show R ++ _ = R
      cases hl : (List.range g.n).filter (fun a => !R.contains a && S a && (g.succ a).any fun c => R.contains c) with
      | nil => exact List.append_nil R
      | cons a l => exact absurd (by rw [hl]; simp) (hF a)
    · exact Classical.byContradiction fun hc => hall fun a ha => Classical.byContradiction fun hn => hc ⟨a, ha, hn⟩
  obtain ⟨a, ha, haR⟩ := hex
  have han : a < g.n := by
    rcases mem_pathStep.1 ha with h | ⟨h, -⟩
    · exact absurd h haR
    · exact h
  unfold missing
  refine filter_len_lt (v := a) ?_ (List.mem_range.2 han) ?_ ?_
  · intro x hx
    cases hc : R.contains x with
    | true =>
      have : (pathStep g S R).contains x = true := List.contains_iff_mem.2 (sub_pathStep R x (List.contains_iff_mem.1 hc))
      rw [this] at hx; exact absurd hx (by simp)
    | false => rfl
  · simp [ha]
  · simpa using haR

/-- After `g.n + 1` rounds nothing is added any more. -/
theorem pathSet_stable (R0 : List Nat) :
    pathStep g S (pathIter g S (g.n + 1) R0) = pathIter g S (g.n + 1) R0 := by
  have key : ∀ j, pathStep g S (pathIter g S j R0) = pathIter g S j R0 ∨ missing g (pathIter g S j R0) + j ≤ g.n := by
    intro j
    induction j with
    | zero => exact Or.inr (show missing g R0 + 0 ≤ g.n from missing_le R0)
    | succ j ih =>
      rw [pathIter_succ]
      by_cases hs : pathStep g S (pathIter g S j R0) = pathIter g S j R0
      · rw [hs]; exact Or.inl hs
      · right
        have := pathStep_lt (g := g) (S := S) _ hs
        rcases ih with h | h
        · exact absurd h hs
        · omega
  rcases key (g.n + 1) with h | h
  · exact h
  · omega

theorem PathIn.target {P : Nat → Prop} {a b : Nat} (h : PathIn g P a b) : b < g.n ∧ P b := by
  induction h with
  | refl hn hs => exact ⟨hn, hs⟩
  | step _ _ _ ih => exact ih

theorem complete_aux {R : List Nat} (hst : pathStep g S R = R) {a c : Nat}
    (h : PathIn g (fun z => S z = true) a c) : c ∈ R → a ∈ R := by
  induction h with
  | refl _ _ => exact id
  | @step a b' c hs he _ ih =>
    intro hc
    have hb := ih hc
    by_cases hin : a ∈ R
    · exact hin
    · have : a ∈ pathStep g S R := mem_pathStep.2 (Or.inr ⟨he.1, hin, hs, b', he.2.2, hb⟩)
      rw [hst] at this
      exact this

/-- The decision procedure for paths inside `S` is correct. -/
theorem pathSet_iff {a b : Nat} :
    PathIn g (fun z => S z = true) a b ↔ a ∈ pathSet g S b := by
  unfold pathSet
  generalize hR0 : (if b < g.n ∧ S b = true then [b] else []) = R0
  have h0 : ∀ x ∈ R0, x < g.n := by
    intro x hx
    by_cases hb : b < g.n ∧ S b = true
    · simp [hb] at hR0; subst hR0; simp at hx; omega
    · simp [hb] at hR0; subst hR0; simp at hx
  constructor
  · intro h
    have hst := pathSet_stable (g := g) (S := S) R0
    have hb : b < g.n ∧ S b = true := PathIn.target h
    have hb0 : b ∈ R0 := by simp [hb] at hR0; subst hR0; simp
    exact complete_aux hst h (sub_pathIter _ _ _ hb0)
  · intro h
    refine (good_pathIter (g := g) (S := S) (b := b) (g.n + 1) R0 ?_ a h).2
    intro x hx
    by_cases hb : b < g.n ∧ S b = true
    · simp [hb] at hR0; subst hR0; simp at hx; subst hx; exact ⟨hb.1, .refl hb.1 hb.2⟩
    · simp [hb] at hR0; subst hR0; simp at hx

/-- Reachability inside a decidable set is decidable (finite graph). -/
instance (g : Digraph) (P : Nat → Prop) [DecidablePred P] (a b : Nat) : Decidable (PathIn g P a b) :=
  decidable_of_iff (a ∈ pathSet g (fun z => decide (P z)) b) (by
    have : PathIn g (fun z => decide (P z) = true) a b ↔ PathIn g P a b := by
      have e : (fun z => decide (P z) = true) = P := funext fun z => propext (decide_eq_true_iff)
      rw [e]
    exact (pathSet_iff.symm.trans this))

end SmcIrred
