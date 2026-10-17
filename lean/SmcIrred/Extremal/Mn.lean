module

public import SmcIrred.Extremal.Kn

public section

namespace SmcIrred

@[simp] theorem Mn_n (n : Nat) : (Mn n).n = n := rfl
@[simp] theorem MnLite_n (n : Nat) : (MnLite n).n = n := rfl

theorem Mn_edge_iff (n a b : Nat) :
    (Mn n).edge a b ↔ a < n ∧ b < n ∧ (b = a + 1 ∨ (a + 1 = n ∧ b + 1 < n) ∨ a + 2 ≤ b) := by
  unfold Digraph.edge
  simp only [Mn, List.mem_filter, List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨h1, h2, _, h4⟩; exact ⟨h1, h2, h4⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, h2, h3⟩

theorem MnLite_edge_iff (n a b : Nat) :
    (MnLite n).edge a b ↔ a < n ∧ b < n ∧ (b = a + 1 ∨ (a + 1 = n ∧ 1 ≤ b ∧ b + 1 < n) ∨ a + 2 ≤ b) := by
  unfold Digraph.edge
  simp only [MnLite, List.mem_filter, List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨h1, h2, _, h4⟩; exact ⟨h1, h2, h4⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, h2, h3⟩

theorem Mn_chain (n : Nat) : ChainGraph (Mn n) 0 where
  lo_le := by omega
  tree := fun i hi => (Mn_edge_iff n _ _).2 ⟨by simp at hi; omega, by simpa using hi, Or.inl rfl⟩
  back := fun i _ hi => (Mn_edge_iff n _ _).2 ⟨by simp at hi ⊢; omega, by simp at hi ⊢; omega,
    Or.inr (Or.inl ⟨by simp at hi ⊢; omega, by simpa using hi⟩)⟩
  backTarget := fun _ _ _ _ => by omega
  noloop := fun i h => by have := (Mn_edge_iff n _ _).1 h; omega
  fwd := fun a b hab hb => (Mn_edge_iff n _ _).2 ⟨by simp at hb; omega, by simpa using hb, Or.inr (Or.inr hab)⟩

theorem MnLite_chain (n : Nat) : ChainGraph (MnLite n) 1 where
  lo_le := by omega
  tree := fun i hi => (MnLite_edge_iff n _ _).2 ⟨by simp at hi; omega, by simpa using hi, Or.inl rfl⟩
  back := fun i h1 hi => (MnLite_edge_iff n _ _).2 ⟨by simp at hi ⊢; omega, by simp at hi ⊢; omega,
    Or.inr (Or.inl ⟨by simp at hi ⊢; omega, h1, by simpa using hi⟩)⟩
  backTarget := fun t w he hw => by have := (MnLite_edge_iff n _ _).1 he; omega
  noloop := fun i h => by have := (MnLite_edge_iff n _ _).1 h; omega
  fwd := fun a b hab hb => (MnLite_edge_iff n _ _).2 ⟨by simp at hb; omega, by simpa using hb, Or.inr (Or.inr hab)⟩

/-- The three edge sets of Definition 4 (tree, back, multiple-entry) are pairwise disjoint (edges inside the vertex set). -/
theorem Mn_classes_disjoint {n a b : Nat} (hb : b < n) :
    ¬ (b = a + 1 ∧ a + 1 = n ∧ b + 1 < n) ∧ ¬ (b = a + 1 ∧ a + 2 ≤ b) ∧ ¬ (a + 1 = n ∧ b + 1 < n ∧ a + 2 ≤ b) := by
  omega

/-- P14 (formal): `M_n` is `K_n` minus exactly the back edges whose source is not the last vertex `v_n`. -/
theorem Mn_eq_Kn_minus_back (n a b : Nat) (h : (Kn n).edge a b) :
    (Mn n).edge a b ↔ ¬ (b < a ∧ a + 1 ≠ n) := by
  have h' := (Kn_edge_iff n a b).1 h
  rw [Mn_edge_iff]
  omega

theorem Mn_sub_Kn {n a b : Nat} (h : (Mn n).edge a b) : (Kn n).edge a b := by
  have := (Mn_edge_iff n a b).1 h
  rw [Kn_edge_iff]; omega

/-- `M_n` has the same multiple-entry edges as `K_n`. -/
theorem Mn_mee {n : Nat} (x y : Nat) : (Mn n).IsMEE (chainJungle n) x y ↔ x + 2 ≤ y ∧ y < n := by
  have := (Mn_chain n).mee_iff x y
  simp only [Mn_n] at this
  rw [this, Mn_edge_iff]
  omega

theorem Mn_irreducible {n : Nat} (w : Nat) : (Mn n).Irreducible (chainJungle n) w ↔ 1 ≤ w ∧ w + 1 < n := by
  have := (Mn_chain n).irreducible_iff w
  simpa using this

theorem Mn_valid {n : Nat} (hn : 1 ≤ n) : (chainJungle n).Valid (Mn n) 0 := (Mn_chain n).valid hn

theorem Mn_irrCount {n : Nat} (hn : 2 ≤ n) : (Mn n).irrCount (chainJungle n) = n - 2 := (Mn_chain n).irrCount hn

theorem Mn_meeCount (n : Nat) : 2 * (Mn n).meeCount (chainJungle n) = (n - 1) * (n - 2) := (Mn_chain n).meeCount

/-- |MEE(M_n)| = |MEE(K_n)| (Definition 4). -/
theorem Mn_meeCount_eq (n : Nat) : (Mn n).meeCount (chainJungle n) = (Kn n).meeCount (chainJungle n) := by
  have h1 := Mn_meeCount n
  have h2 := Kn_meeCount n
  omega

/-- P15: dropping the back edge `v_n → v_1` keeps the multiple-entry edges and the irreducible loops. -/
theorem MnLite_mee {n : Nat} (x y : Nat) : (MnLite n).IsMEE (chainJungle n) x y ↔ x + 2 ≤ y ∧ y < n := by
  have := (MnLite_chain n).mee_iff x y
  simp only [MnLite_n] at this
  rw [this, MnLite_edge_iff]
  omega

theorem MnLite_irrCount {n : Nat} (hn : 2 ≤ n) : (MnLite n).irrCount (chainJungle n) = n - 2 :=
  (MnLite_chain n).irrCount hn

theorem MnLite_meeCount_eq (n : Nat) : (MnLite n).meeCount (chainJungle n) = (Kn n).meeCount (chainJungle n) := by
  have h1 := (MnLite_chain n).meeCount
  have h2 := Kn_meeCount n
  simp only [MnLite_n] at h1
  omega

theorem MnLite_valid {n : Nat} (hn : 1 ≤ n) : (chainJungle n).Valid (MnLite n) 0 := (MnLite_chain n).valid hn

end SmcIrred
