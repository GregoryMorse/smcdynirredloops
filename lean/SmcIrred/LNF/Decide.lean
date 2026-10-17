module

public import SmcIrred.LNF.Path
public import SmcIrred.Graph.Decide

public section

namespace SmcIrred

variable (g : Digraph) (J : Jungle)

theorem Digraph.BackEdge.lt {t w : Nat} (h : g.BackEdge J t w) : t < g.n ∧ w < g.n := ⟨h.1.1, h.1.2.1⟩

instance (t w : Nat) : Decidable (g.BackEdge J t w) :=
  inferInstanceAs (Decidable (g.edge t w ∧ J.Anc w t))

theorem Digraph.isHeader_iff (w : Nat) : g.IsHeader J w ↔ ∃ t, t < g.n ∧ g.BackEdge J t w :=
  ⟨fun ⟨t, h⟩ => ⟨t, h.1.1, h⟩, fun ⟨t, _, h⟩ => ⟨t, h⟩⟩

instance (w : Nat) : Decidable (g.IsHeader J w) := decidable_of_iff _ (g.isHeader_iff J w).symm

theorem Digraph.IsHeader.lt {w : Nat} (h : g.IsHeader J w) : w < g.n := by
  obtain ⟨t, ht⟩ := h
  exact ht.1.2.1

theorem Digraph.body_iff (w x : Nat) : g.Body J w x ↔ g.IsHeader J w ∧ (x = w ∨ ∃ t, t < g.n ∧ t ≠ w ∧
    g.BackEdge J t w ∧ PathIn g (fun z => J.Anc w z ∧ z ≠ w) x t) := by
  unfold Digraph.Body
  constructor
  · rintro ⟨h, h2⟩
    refine ⟨h, h2.imp id fun ⟨t, ht, hb, hp⟩ => ⟨t, hb.1.1, ht, hb, hp⟩⟩
  · rintro ⟨h, h2⟩
    refine ⟨h, h2.imp id fun ⟨t, _, ht, hb, hp⟩ => ⟨t, ht, hb, hp⟩⟩

instance (w x : Nat) : Decidable (g.Body J w x) := decidable_of_iff _ (g.body_iff J w x).symm

theorem Digraph.Body.isHeader {w x : Nat} (h : g.Body J w x) : g.IsHeader J w := h.1

theorem Digraph.irreducible_iff (w : Nat) : g.Irreducible J w ↔ g.IsHeader J w ∧ ∃ x, x < g.n ∧ ∃ y, y < g.n ∧
    g.Body J w x ∧ x ≠ w ∧ g.edge y x ∧ ¬ J.Anc w y := by
  unfold Digraph.Irreducible
  constructor
  · rintro ⟨h, x, y, hb, hx, he, hn⟩
    exact ⟨h, x, he.2.1, y, he.1, hb, hx, he, hn⟩
  · rintro ⟨h, x, _, y, _, hb, hx, he, hn⟩
    exact ⟨h, x, y, hb, hx, he, hn⟩

instance (w : Nat) : Decidable (g.Irreducible J w) := decidable_of_iff _ (g.irreducible_iff J w).symm

theorem Digraph.lnfParent_iff (h x : Nat) : g.LnfParent J h x ↔ g.IsHeader J h ∧ h ≠ x ∧ g.Body J h x ∧
    ∀ h', h' < g.n → g.IsHeader J h' → h' ≠ x → g.Body J h' x → g.Body J h' h := by
  unfold Digraph.LnfParent
  constructor
  · rintro ⟨a, b, c, d⟩
    exact ⟨a, b, c, fun h' _ => d h'⟩
  · rintro ⟨a, b, c, d⟩
    exact ⟨a, b, c, fun h' hh => d h' (hh.lt g J) hh⟩

instance (h x : Nat) : Decidable (g.LnfParent J h x) := decidable_of_iff _ (g.lnfParent_iff J h x).symm

theorem Digraph.isMEE_iff (x y : Nat) : g.IsMEE J x y ↔ g.edge x y ∧ ∃ w, w < g.n ∧ g.Body J w y ∧ y ≠ w ∧
    ¬ J.Anc w x := by
  unfold Digraph.IsMEE
  constructor
  · rintro ⟨he, w, hb, hy, hn⟩
    exact ⟨he, w, hb.1.lt g J, hb, hy, hn⟩
  · rintro ⟨he, w, _, hb, hy, hn⟩
    exact ⟨he, w, hb, hy, hn⟩

instance (x y : Nat) : Decidable (g.IsMEE J x y) := decidable_of_iff _ (g.isMEE_iff J x y).symm

end SmcIrred
