module

public import SmcIrred.LNF.Reducible

public section

namespace SmcIrred.Lang

/-! # An irreducible flow graph has an irreducible loop in every depth-first jungle

The converse of `reducible_no_irreducible`: if the flow graph is not reducible then, for every valid jungle, some loop is
irreducible (a body vertex has a predecessor outside the subtree of the header). -/

variable {g : Digraph} {r : Nat} {J : Jungle}

/-- An edge that does not lead to an ancestor finishes its target earlier. -/
theorem post_lt_of_edge (hv : J.Valid g r) {a b : Nat} (he : g.edge a b) (hna : ¬ J.Anc b a) : J.post b < J.post a := by
  have hlam := hv.laminar a b he.1 he.2.1
  have hint := hv.interval a he.1
  have hno := hv.no_rightward a b he
  rcases hlam with h | h | h | h
  · by_cases heq : J.post b = J.post a
    · have := hv.post_inj b a he.2.1 he.1 heq
      subst this
      exact absurd ⟨Nat.le_refl _, Nat.le_refl _⟩ hna
    · have := h.2
      omega
  · exact absurd h hna
  · exact absurd h hno
  · omega

/-- A path avoiding the header `w` that ends below it contains a last entry into the subtree of `w`. -/
theorem last_entry {w t : Nat} (ht : J.Anc w t) : ∀ a, PathIn g (fun z => z ≠ w) a t →
    (J.Anc w a → PathIn g (fun z => J.Anc w z ∧ z ≠ w) a t ∨
      ∃ x y, g.edge y x ∧ ¬ J.Anc w y ∧ J.Anc w x ∧ x ≠ w ∧ PathIn g (fun z => J.Anc w z ∧ z ≠ w) x t) ∧
    (¬ J.Anc w a → ∃ x y, g.edge y x ∧ ¬ J.Anc w y ∧ J.Anc w x ∧ x ≠ w ∧ PathIn g (fun z => J.Anc w z ∧ z ≠ w) x t) := by
  intro a hp
  induction hp with
  | @refl a ha hS =>
    exact ⟨fun h => Or.inl (.refl ha ⟨h, hS⟩), fun h => absurd ht h⟩
  | @step a b c hS he hp ih =>
    constructor
    · intro hwa
      by_cases hwb : J.Anc w b
      · rcases (ih ht).1 hwb with h | h
        · exact Or.inl (.step ⟨hwa, hS⟩ he h)
        · exact Or.inr h
      · exact Or.inr ((ih ht).2 hwb)
    · intro hwa
      by_cases hwb : J.Anc w b
      · rcases (ih ht).1 hwb with h | h
        · exact ⟨b, a, he, hwa, hwb, hp.source.2, h⟩
        · exact h
      · exact (ih ht).2 hwb

/-- A back edge whose target does not dominate its source heads an irreducible loop. -/
theorem irreducible_of_backedge (hv : J.Valid g r) {t w : Nat} (he : g.edge t w) (ha : J.Anc w t)
    (hnd : ¬ g.Dom r w t) : g.Irreducible J w := by
  have hreach := reach hv he.1
  have hpath : PathIn g (fun z => z ≠ w) r t := by
    apply Classical.byContradiction
    intro h
    exact hnd ⟨hreach, h⟩
  have hrw : r ≠ w := hpath.source.2
  have hnr : ¬ J.Anc w r := by
    intro h
    have h2 := hv.root w he.2.1
    have := hv.pre_inj r w hpath.source.1 he.2.1 (by have := h.1; have := h2.1; omega)
    exact hrw this
  have htw : t ≠ w := hpath.target.2
  obtain ⟨x, y, hyx, hya, hxa, hxw, hxt⟩ := (last_entry ha r hpath).2 hnr
  exact ⟨⟨t, he, ha⟩, x, y, ⟨⟨t, he, ha⟩, Or.inr ⟨t, htw, ⟨he, ha⟩, hxt⟩⟩, hxw, hyx, hya⟩

/-- The converse of `reducible_no_irreducible`: every valid jungle of a non-reducible flow graph has an irreducible loop. -/
theorem exists_irreducible_loop (hv : J.Valid g r) (hnr : ¬ g.Reducible r) : ∃ w, g.Irreducible J w := by
  apply Classical.byContradiction
  intro hno
  apply hnr
  have hback : ∀ t w, g.edge t w → J.Anc w t → g.Dom r w t := by
    intro t w he ha
    apply Classical.byContradiction
    intro hnd
    exact hno ⟨w, irreducible_of_backedge hv he ha hnd⟩
  have hlt : ∀ a b, g.NonDomPath r a b → J.post b < J.post a := by
    intro a b h
    induction h with
    | single he _ hnd => exact post_lt_of_edge hv he (fun hA => hnd (hback _ _ he hA))
    | step he _ hnd _ ih => exact Nat.lt_trans ih (post_lt_of_edge hv he (fun hA => hnd (hback _ _ he hA)))
  intro v h
  exact Nat.lt_irrefl _ (hlt v v h)

end SmcIrred.Lang
