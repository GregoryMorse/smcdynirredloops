module

public import SmcIrred.Extremal.Chain

public section

namespace SmcIrred

theorem Kn_edge_iff (n a b : Nat) : (Kn n).edge a b ↔ a < n ∧ b < n ∧ b ≠ a := by
  unfold Digraph.edge
  simp only [Kn, List.mem_filter, List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨h1, h2, _, h4⟩; exact ⟨h1, h2, h4⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, h2, h3⟩

@[simp] theorem Kn_n (n : Nat) : (Kn n).n = n := rfl

theorem Kn_chain (n : Nat) : ChainGraph (Kn n) 0 where
  lo_le := by omega
  tree := fun i hi => (Kn_edge_iff n _ _).2 ⟨by simp at hi; omega, by simpa using hi, by omega⟩
  back := fun i _ hi => (Kn_edge_iff n _ _).2 ⟨by simp at hi ⊢; omega, by simp at hi ⊢; omega, by simp at hi ⊢; omega⟩
  backTarget := fun _ _ _ _ => by omega
  noloop := fun i h => ((Kn_edge_iff n _ _).1 h).2.2 rfl
  fwd := fun a b hab hb => (Kn_edge_iff n _ _).2 ⟨by simp at hb; omega, by simpa using hb, by omega⟩

/-- `K_n` is a control-flow graph for every choice of the root (C67). -/
theorem Kn_isCFG {n r : Nat} (hr : r < n) : (Kn n).IsCFG r := by
  refine ⟨hr, fun v hv => ?_⟩
  by_cases e : v = r
  · subst e; exact .refl _
  · exact .step ((Kn_edge_iff n _ _).2 ⟨hr, hv, e⟩) (.refl _)

theorem Kn_valid {n : Nat} (hn : 1 ≤ n) : (chainJungle n).Valid (Kn n) 0 := (Kn_chain n).valid hn

theorem count_ne (n : Nat) : ∀ a, a < n → ((List.range n).filter fun b => decide (b ≠ a)).length = n - 1 := by
  induction n with
  | zero => intro a h; omega
  | succ n ih =>
    intro a ha
    rw [List.range_succ, List.filter_append, List.length_append]
    by_cases e : a = n
    · subst e
      have : (List.range a).filter (fun b => decide (b ≠ a)) = List.range a :=
        List.filter_eq_self.2 (fun b hb => by simp only [List.mem_range] at hb; simp; omega)
      rw [this]; simp
    · have := ih a (by omega)
      rw [this]
      have : n ≠ a := fun h => e h.symm
      simp [this]; omega

/-- |E(K_n)| = n² − n (C67). -/
theorem Kn_edgeCount (n : Nat) : (Kn n).edgeCount = n * (n - 1) := by
  unfold Digraph.edgeCount
  refine Eq.trans (congrArg List.sum (List.map_congr_left (g := fun _ => n - 1) ?_)) (sum_map_const n (n - 1))
  intro a ha
  have ha := List.mem_range.1 ha
  have : (Kn n).n = n := rfl
  rw [this]
  refine Eq.trans (congrArg List.length (List.filter_congr (q := fun b => decide (b ≠ a)) ?_)) (count_ne n a ha)
  intro b hb
  have hb := List.mem_range.1 hb
  simp only [decide_eq_decide, Kn_edge_iff]
  omega

/-- In `K_n` with the DFS order `v_1 … v_n`: the headers are `v_1 … v_{n-1}` (a single chain of `n - 1` loops). -/
theorem Kn_headers {n : Nat} (w : Nat) : (Kn n).IsHeader (chainJungle n) w ↔ w + 1 < n :=
  by have := (Kn_chain n).header_iff w; simp only [Kn_n] at this; simpa using this

/-- Every loop body is the tail of the chain: `L(v_i) = {v_i, …, v_n}`. -/
theorem Kn_body {n : Nat} (w x : Nat) : (Kn n).Body (chainJungle n) w x ↔ w + 1 < n ∧ w ≤ x ∧ x < n := by
  have := (Kn_chain n).body_iff w x
  simp only [Kn_n] at this; simpa using this

/-- The entry loop is reducible and the irreducible loops are exactly those of `v_2 … v_{n-1}`. -/
theorem Kn_irreducible {n : Nat} (w : Nat) : (Kn n).Irreducible (chainJungle n) w ↔ 1 ≤ w ∧ w + 1 < n :=
  (Kn_chain n).irreducible_iff w

/-- `K_n` (n ≥ 2) has exactly n − 2 irreducible loops (C67). -/
theorem Kn_irrCount {n : Nat} (hn : 2 ≤ n) : (Kn n).irrCount (chainJungle n) = n - 2 :=
  (Kn_chain n).irrCount hn

/-- The multiple-entry edges of `K_n` are exactly the edges that skip a vertex of the chain. -/
theorem Kn_mee {n : Nat} (x y : Nat) : (Kn n).IsMEE (chainJungle n) x y ↔ x + 2 ≤ y ∧ y < n := by
  have := (Kn_chain n).mee_iff x y
  simp only [Kn_n] at this
  rw [this, Kn_edge_iff]
  omega

/-- |MEE(K_n)| = Σ_{i=0..n-2} i = (n−1)(n−2)/2 (C67, stated as twice the count). -/
theorem Kn_meeCount (n : Nat) : 2 * (Kn n).meeCount (chainJungle n) = (n - 1) * (n - 2) :=
  (Kn_chain n).meeCount

end SmcIrred
