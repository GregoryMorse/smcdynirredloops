module

public import SmcIrred.Extremal.Count
public import SmcIrred.LNF.Facts
public import SmcIrred.Graph.DfsInv

public section

namespace SmcIrred

theorem ite01 (P : Prop) [Decidable P] : (P ∧ (if P then 1 else 0) = 1) ∨ (¬ P ∧ (if P then 1 else 0) = 0) := by
  by_cases h : P <;> simp [h]

theorem count_ne2 (n a b : Nat) (hab : a ≠ b) :
    ((List.range n).filter fun w => decide (w ≠ a ∧ w ≠ b)).length + (if a < n then 1 else 0) + (if b < n then 1 else 0) = n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.filter_append, List.length_append]
    have hf : (([n] : List Nat).filter fun w => decide (w ≠ a ∧ w ≠ b)).length = if n ≠ a ∧ n ≠ b then 1 else 0 := by
      by_cases h : n ≠ a ∧ n ≠ b <;> simp [h]
    rw [hf]
    generalize ((List.range n).filter fun w => decide (w ≠ a ∧ w ≠ b)).length = L at ih ⊢
    have i1 := ite01 (n ≠ a ∧ n ≠ b)
    have i2 := ite01 (a < n)
    have i3 := ite01 (b < n)
    have i4 := ite01 (a < n + 1)
    have i5 := ite01 (b < n + 1)
    omega

theorem exists_max_pre (J : Jungle) : ∀ n, 1 ≤ n → ∃ l, l < n ∧ ∀ v, v < n → J.pre v ≤ J.pre l := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ n ih =>
    intro _
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨0, by omega, fun v hv => by have : v = 0 := by omega
                                         subst this; exact Nat.le_refl _⟩
    · obtain ⟨l, hl, hmax⟩ := ih hn
      by_cases h : J.pre n ≤ J.pre l
      · exact ⟨l, by omega, fun v hv => by
          by_cases e : v = n
          · subst e; exact h
          · exact hmax v (by omega)⟩
      · exact ⟨n, by omega, fun v hv => by
          by_cases e : v = n
          · subst e; exact Nat.le_refl _
          · have := hmax v (by omega); omega⟩

/-- For every CFG with `n ≥ 2` vertices and every depth-first jungle there are at most `n − 2` irreducible loops: neither
the root (whose loop is reducible) nor the vertex with the largest preorder number (a leaf of the tree, which has no
proper descendant in a body) heads one. -/
theorem irrCount_le {g : Digraph} {r : Nat} {J : Jungle} (hcfg : g.IsCFG r) (hv : J.Valid g r) (hn : 2 ≤ g.n) :
    g.irrCount J ≤ g.n - 2 := by
  obtain ⟨l, hl, hmax⟩ := exists_max_pre J g.n (by omega)
  have hr := hcfg.1
  have hrl : r ≠ l := by
    intro e
    subst e
    obtain ⟨v, hvn, hvr⟩ : ∃ v, v < g.n ∧ v ≠ r := by
      by_cases h0 : r = 0
      · exact ⟨1, by omega, by omega⟩
      · exact ⟨0, by omega, by omega⟩
    have h1 := hv.root v hvn
    have h2 := hmax v hvn
    have h3 : J.pre r ≠ J.pre v := fun e => hvr (hv.pre_inj v r hvn hr e.symm)
    unfold Jungle.Anc at h1
    omega
  have hc := count_ne2 g.n r l hrl
  have hsub : g.irrCount J ≤ ((List.range g.n).filter fun w => decide (w ≠ r ∧ w ≠ l)).length := by
    unfold Digraph.irrCount
    apply filter_len_le
    intro w hw
    simp only [decide_eq_true_eq] at hw ⊢
    refine ⟨fun e => hv.root_not_irreducible (e ▸ hw), fun e => ?_⟩
    subst e
    obtain ⟨hh, x, y, hb, hx, he, hna⟩ := hw
    have h1 := Digraph.Body.anc hb
    have h2 := hmax x (Digraph.Body.lt hb)
    have h3 : J.pre w ≠ J.pre x := fun e => hx (hv.pre_inj x w (Digraph.Body.lt hb) (hh.lt g J) e.symm)
    unfold Jungle.Anc at h1
    omega
  simp only [hr, hl, ↓reduceIte] at hc
  omega

end SmcIrred
