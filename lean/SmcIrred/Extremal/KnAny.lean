module

public import SmcIrred.Extremal.Kn
public import SmcIrred.Extremal.MEEBound

public section

namespace SmcIrred

variable {n r : Nat} {J : Jungle}

/-- In any depth-first jungle of `K_n` all vertices are comparable: the DFS tree is a Hamiltonian path. -/
theorem Kn_comparable (hv : J.Valid (Kn n) r) {a b : Nat} (ha : a < n) (hb : b < n) : J.Anc a b ∨ J.Anc b a := by
  by_cases e : a = b
  · subst e; exact Or.inl (Jungle.Anc.refl _)
  · rcases hv.laminar a b ha hb with c | c | c | c
    · exact Or.inl c
    · exact Or.inr c
    · exact absurd c (hv.no_rightward a b ((Kn_edge_iff n a b).2 ⟨ha, hb, fun h => e h.symm⟩))
    · exact absurd c (hv.no_rightward b a ((Kn_edge_iff n b a).2 ⟨hb, ha, e⟩))

/-- The headers of `K_n`: exactly the vertices that are not leaves of the DFS path. -/
theorem Kn_header_iff (w : Nat) : (Kn n).IsHeader J w ↔ w < n ∧ ∃ x, x < n ∧ x ≠ w ∧ J.Anc w x := by
  constructor
  · rintro ⟨t, he, hanc⟩
    have := (Kn_edge_iff n t w).1 he
    exact ⟨this.2.1, t, this.1, fun e => this.2.2 e.symm, hanc⟩
  · rintro ⟨hw, x, hx, hne, hanc⟩
    exact ⟨x, (Kn_edge_iff n x w).2 ⟨hx, hw, fun e => hne e.symm⟩, hanc⟩

theorem Kn_body_iff (w x : Nat) :
    (Kn n).Body J w x ↔ (Kn n).IsHeader J w ∧ J.Anc w x ∧ x < n := by
  constructor
  · intro hb
    exact ⟨hb.1, Digraph.Body.anc hb, Digraph.Body.lt hb⟩
  · rintro ⟨hh, hanc, hx⟩
    refine ⟨hh, ?_⟩
    by_cases e : x = w
    · exact Or.inl e
    · refine Or.inr ⟨x, e, ⟨(Kn_edge_iff n x w).2 ⟨hx, hh.lt (Kn n) J, fun h => e h.symm⟩, hanc⟩, .refl hx ⟨hanc, e⟩⟩

theorem Kn_irreducible_iff (hv : J.Valid (Kn n) r) (hr : r < n) (w : Nat) :
    (Kn n).Irreducible J w ↔ w ≠ r ∧ w < n ∧ ∃ x, x < n ∧ x ≠ w ∧ J.Anc w x := by
  constructor
  · intro hi
    obtain ⟨hw, hx⟩ := (Kn_header_iff w).1 hi.1
    exact ⟨fun e => hv.root_not_irreducible (e ▸ hi), hw, hx⟩
  · rintro ⟨hwr, hw, x, hx, hne, hanc⟩
    have hh : (Kn n).IsHeader J w := (Kn_header_iff w).2 ⟨hw, x, hx, hne, hanc⟩
    have hnr : ¬ J.Anc w r := fun h => hwr (hv.anc_antisymm hw hr h (hv.root w hw))
    have hxr : r ≠ x := fun e => hnr (e ▸ hanc)
    exact ⟨hh, x, r, (Kn_body_iff w x).2 ⟨hh, hanc, hx⟩, hne, (Kn_edge_iff n r x).2 ⟨hr, hx, fun e => hxr e.symm⟩, hnr⟩

theorem root_pre_le (hv : J.Valid g r) {a : Nat} (ha : a < g.n) : J.pre r ≤ J.pre a := (hv.root a ha).1

/-- `K_n` has exactly `n − 2` irreducible loops for **every** DFS and every root (C67). -/
theorem Kn_irrCount_any (hv : J.Valid (Kn n) r) (hr : r < n) (hn : 2 ≤ n) : (Kn n).irrCount J = n - 2 := by
  obtain ⟨l, hl, hmax⟩ := exists_max_pre J n (by omega)
  have hrl : r ≠ l := by
    intro e
    subst e
    obtain ⟨v, hvn, hvr⟩ : ∃ v, v < n ∧ v ≠ r := by
      by_cases h0 : r = 0
      · exact ⟨1, by omega, by omega⟩
      · exact ⟨0, by omega, by omega⟩
    have h1 := hv.root v hvn
    have h2 := hmax v hvn
    have h3 : J.pre r ≠ J.pre v := fun e => hvr (hv.pre_inj v r hvn hr e.symm)
    unfold Jungle.Anc at h1
    omega
  have hc := count_ne2 n r l hrl
  unfold Digraph.irrCount
  simp only [Kn_n]
  refine Eq.trans (congrArg List.length (List.filter_congr (q := fun w => decide (w ≠ r ∧ w ≠ l)) ?_)) ?_
  · intro w hw
    have hw := List.mem_range.1 hw
    simp only [decide_eq_decide, Kn_irreducible_iff hv hr]
    constructor
    · rintro ⟨h1, -, x, hx, hne, hanc⟩
      refine ⟨h1, fun e => ?_⟩
      subst e
      have h2 := hmax x hx
      unfold Jungle.Anc at hanc
      have h3 : J.pre w = J.pre x := by omega
      exact hne (hv.pre_inj x w hx hw h3.symm)
    · rintro ⟨h1, h2⟩
      refine ⟨h1, hw, l, hl, fun e => h2 e.symm, ?_⟩
      rcases Kn_comparable hv hw hl with c | c
      · exact c
      · exfalso
        have h3 := hmax w hw
        unfold Jungle.Anc at c
        have : J.pre w = J.pre l := by omega
        exact h2 (hv.pre_inj w l hw hl this)
  · simp only [hr, hl, ↓reduceIte] at hc
    omega

theorem Kn_per_vertex (hv : J.Valid (Kn n) r) (hr : r < n) {b : Nat} (hb : b < n) :
    meeA (Kn n) J b + meeC (Kn n) J b + (if b = r then 0 else 1) = earlier J n b := by
  have hle := per_vertex hv hb
  simp only [Kn_n] at hle
  by_cases hbr : b = r
  · subst hbr
    have : earlier J n b = 0 := by
      unfold earlier
      apply List.length_eq_zero_iff.2
      apply List.filter_eq_nil_iff.2
      intro a ha
      have := root_pre_le hv (List.mem_range.1 ha)
      simp only [decide_eq_true_eq]; omega
    simp only [↓reduceIte] at hle ⊢
    omega
  · simp only [hbr, ↓reduceIte] at hle ⊢
    obtain ⟨p, hp, -⟩ := hv.parent b hb hbr
    have hpn : p < n := hp.1
    have hlt := hv.parent_nested hpn hb hp
    have hC : meeC (Kn n) J b = 0 := by
      unfold meeC
      apply List.length_eq_zero_iff.2
      apply List.filter_eq_nil_iff.2
      intro y hy
      have hy := List.mem_range.1 hy
      simp only [Kn_n] at hy
      simp only [decide_eq_true_eq, not_and]
      rintro ⟨-, w, hw, hwy, hn⟩ hlt'
      apply hn
      have h1 := Digraph.Body.anc hw
      rcases Kn_comparable hv hy hb with c | c
      · exact h1.trans c
      · exfalso; unfold Jungle.Anc at c; omega
    have hA : ((List.range n).filter fun a => decide (J.pre a < J.pre b ∧ a ≠ p)).length ≤ meeA (Kn n) J b := by
      unfold meeA
      simp only [Kn_n]
      apply filter_len_mono
      intro a ha hq
      have ha := List.mem_range.1 ha
      simp only [decide_eq_true_eq] at hq ⊢
      obtain ⟨h1, h2⟩ := hq
      have hab : a ≠ b := fun e => by subst e; omega
      have hnp : ¬ J.Anc p a := by
        intro hpa
        have hanc : J.Anc a b := by
          rcases Kn_comparable hv ha hb with c | c
          · exact c
          · exfalso; unfold Jungle.Anc at c; omega
        exact h2 (hv.anc_antisymm ha hpn (hp.2.2.2 a ha hab hanc) hpa)
      have hbp : b ≠ p := fun e => hp.2.1 e.symm
      have hh : (Kn n).IsHeader J p := (Kn_header_iff p).2 ⟨hpn, b, hb, hbp, hp.2.2.1⟩
      exact ⟨⟨(Kn_edge_iff n a b).2 ⟨ha, hb, fun e => hab e.symm⟩, p,
        (Kn_body_iff p b).2 ⟨hh, hp.2.2.1, hb⟩, hbp, hnp⟩, h1⟩
    have hsplit : ((List.range n).filter fun a => decide (J.pre a < J.pre b)).length =
        ((List.range n).filter fun a => decide (J.pre a < J.pre b ∧ a ≠ p)).length +
        ((List.range n).filter fun a => decide (a = p)).length := by
      apply filter_len_split
      intro a ha
      have ha := List.mem_range.1 ha
      by_cases e : a = p
      · subst e
        right; left; simp; omega
      · by_cases hl : J.pre a < J.pre b
        · left; simp [hl, e]
        · right; right; simp [hl, e]
    have hone : ((List.range n).filter fun a => decide (a = p)).length = 1 := by
      refine Eq.trans (congrArg List.length (List.filter_congr (q := fun a => decide (p ≤ a ∧ a < p + 1)) ?_)) ?_
      · intro a _; simp only [decide_eq_decide]; omega
      · rw [count_interval]; omega
    unfold earlier at hle ⊢
    omega

/-- `K_n` has exactly `(n−1)(n−2)/2` multiple-entry edges for **every** DFS and every root (C67). -/
theorem Kn_meeCount_any (hv : J.Valid (Kn n) r) (hr : r < n) : 2 * (Kn n).meeCount J = (n - 1) * (n - 2) := by
  rw [meeCount_decomp hv]
  simp only [Kn_n]
  have hsum : ((List.range n).map fun b => meeA (Kn n) J b + meeC (Kn n) J b + (if b = r then 0 else 1)).sum =
      ((List.range n).map fun b => earlier J n b).sum := by
    apply congrArg List.sum; apply List.map_congr_left; intro b hb
    exact Kn_per_vertex hv hr (List.mem_range.1 hb)
  rw [sum_map_add] at hsum
  have hite : ((List.range n).map fun b => if b = r then 0 else 1).sum = n - 1 := by
    have := count_ne n r hr
    rw [count_eq_sum] at this
    rw [← this]
    apply congrArg List.sum; apply List.map_congr_left; intro b _
    by_cases h : b = r <;> simp [h]
  rw [hite] at hsum
  have hT := earlier_sum J n (fun a b ha hb => hv.pre_inj a b ha hb)
  have e : List.map (fun b => earlier J n b) (List.range n) = List.map (earlier J n) (List.range n) := rfl
  generalize ((List.range n).map fun b => meeA (Kn n) J b + meeC (Kn n) J b).sum = M at hsum ⊢
  generalize ((List.range n).map fun b => earlier J n b).sum = T at hsum hT
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have e1 : m + 1 - 1 = m := by omega
  rw [e1] at hsum ⊢
  rcases m with _ | m
  · simp at hsum hT ⊢; omega
  · have e2 : m + 1 + 1 - 2 = m := by omega
    rw [e2]
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul] at hT ⊢
    omega

/-- `K_n` has exactly `n − 1` loop headers for every DFS (a single chain of nested loops; only the last vertex of the DFS
path heads none). -/
theorem Kn_headerCount_any (hv : J.Valid (Kn n) r) (hr : r < n) :
    ((List.range n).filter fun w => decide ((Kn n).IsHeader J w)).length = n - 1 := by
  obtain ⟨l, hl, hmax⟩ := exists_max_pre J n (by omega)
  refine Eq.trans (congrArg List.length (List.filter_congr (q := fun w => decide (w ≠ l)) ?_)) (count_ne n l hl)
  intro w hw
  have hw := List.mem_range.1 hw
  simp only [decide_eq_decide, Kn_header_iff]
  constructor
  · rintro ⟨-, x, hx, hne, hanc⟩ e
    subst e
    have h2 := hmax x hx
    unfold Jungle.Anc at hanc
    exact hne (hv.pre_inj x w hx hw (by omega))
  · intro h2
    refine ⟨hw, l, hl, fun e => h2 e.symm, ?_⟩
    rcases Kn_comparable hv hw hl with c | c
    · exact c
    · exfalso
      have h3 := hmax w hw
      unfold Jungle.Anc at c
      exact h2 (hv.pre_inj w l hw hl (by omega))

end SmcIrred
