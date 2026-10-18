module

public import SmcIrred.Lang.MinEdges
public import SmcIrred.TwoSat.Reach
public import SmcIrred.LNF.Facts

public section

namespace SmcIrred.Lang

/-! Inducing an irreducible loop on a reducible loop by an edge from an unreached outside vertex (C75). -/

section
variable {g : Digraph} {r : Nat} {J : Jungle}

/-- An ancestor reaches its descendants along tree edges. -/
theorem anc_reach (hv : J.Valid g r) : ∀ k a b, a < g.n → b < g.n → J.Anc a b → J.pre b - J.pre a ≤ k → g.Reach a b := by
  intro k
  induction k with
  | zero =>
    intro a b ha hb hab hk
    have : a = b := hv.pre_inj a b ha hb (by unfold Jungle.Anc at hab; omega)
    subst this; exact .refl a
  | succ k ih =>
    intro a b ha hb hab hk
    by_cases heq : a = b
    · subst heq; exact .refl a
    · by_cases hbr : b = r
      · subst hbr
        exact absurd (hv.anc_antisymm ha hb hab (hv.root a ha)) heq
      · obtain ⟨u, hp, he⟩ := hv.parent b hb hbr
        have hua : J.Anc u b := hp.2.2.1
        have hune : u ≠ b := hp.2.1
        have hau : J.Anc a u := hp.2.2.2 a ha heq hab
        have hulb : J.pre u < J.pre b := by
          have h1 : J.pre u ≠ J.pre b := fun h => hune (hv.pre_inj u b hp.1 hb h)
          unfold Jungle.Anc at hua; omega
        have hpre : J.pre u - J.pre a ≤ k := by
          unfold Jungle.Anc at hau; omega
        exact (ih a u ha hp.1 hau hpre).trans (.step he (.refl b))

end

/-- Edge-monotone: the body of a loop persists when edges (and vertices) are added, for the same jungle. -/
theorem body_mono {g g' : Digraph} {J : Jungle} (hn : g.n ≤ g'.n) (he : ∀ a b, g.edge a b → g'.edge a b)
    {h y : Nat} (hb : g.Body J h y) : g'.Body J h y := by
  have hp : ∀ {S : Nat → Prop} {a b : Nat}, PathIn g S a b → PathIn g' S a b := by
    intro S a b hpath
    induction hpath with
    | refl ha hS => exact .refl (Nat.lt_of_lt_of_le ha hn) hS
    | step hS hedge _ ih => exact .step hS (he _ _ hedge) ih
  have hbe : ∀ t w, g.BackEdge J t w → g'.BackEdge J t w := fun t w hh => ⟨he _ _ hh.1, hh.2⟩
  obtain ⟨⟨t0, ht0⟩, hx⟩ := hb
  refine ⟨⟨t0, hbe _ _ ht0⟩, ?_⟩
  rcases hx with hx | ⟨t, htne, hte, hpath⟩
  · exact Or.inl hx
  · exact Or.inr ⟨t, htne, hbe _ _ hte, hp hpath⟩

/-- Adding an edge `x → y` from a vertex `x` that is not a descendant of the header `h` into the body of the loop of
`h` at a vertex other than `h` makes that loop irreducible (for the jungle `J`, which is valid for the new graph). -/
theorem induce_irreducible {g' : Digraph} {J : Jungle} {h x y : Nat} (hb : g'.Body J h y) (hy : y ≠ h)
    (hx : g'.edge x y) (hout : ¬ J.Anc h x) : g'.Irreducible J h :=
  ⟨hb.1, y, x, hb, hy, hx, hout⟩

/-- C75. Let `g'` be a graph with a loop (header `h`, body `L`) that the graph `g` already had, and `x → y` an edge
of `g'` from a vertex `x` that no vertex of `L` reaches, into `L` at a vertex other than the header. Then the loop of
`h` is irreducible in every depth-first jungle of `g'`. -/
theorem induce_on_loop {g g' : Digraph} {J : Jungle} {r h x y : Nat} (hv : J.Valid g' r)
    (hn : g.n ≤ g'.n) (he : ∀ a b, g.edge a b → g'.edge a b)
    (hb : g.Body J h y) (hy : y ≠ h) (hx : g'.edge x y) (hh : h < g'.n)
    (hunr : ∀ l, g'.Body J h l → ¬ g'.Reach l x) : g'.Irreducible J h := by
  have hb' : g'.Body J h y := body_mono hn he hb
  have hhh : g'.Body J h h := ⟨hb'.1, Or.inl rfl⟩
  refine induce_irreducible hb' hy hx ?_
  intro hanc
  exact hunr h hhh (anc_reach hv (J.pre x - J.pre h) h x hh hx.1 hanc (Nat.le_refl _))

/-- A reducible loop with entry `0`, header `1`, latch `2` and exit `3`. -/
@[expose] def loopG : Digraph where
  n := 4
  succ k := [[1], [2], [1, 3], []].getD k []

/-- Instance: the edge `0 → 2` from the entry (which no loop vertex reaches) makes the loop irreducible; before the
edge the graph has no irreducible loop. -/
theorem induce_instance :
    NoIrr loopG ∧ ∃ w, w < 4 ∧ (addEdge loopG 0 2).Irreducible (dfsRun (addEdge loopG 0 2) 0 2) w := by decide

/-- The condition is necessary: the edge `3 → 2` from the exit, which the loop reaches, leaves every loop
reducible. -/
theorem induce_needs_unreached : NoIrr (addEdge loopG 3 2) := by decide

end SmcIrred.Lang
