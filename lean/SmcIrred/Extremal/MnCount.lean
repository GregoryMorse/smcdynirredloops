module

public import SmcIrred.Extremal.Mn

public section

namespace SmcIrred

/-- The out-degree of `a` (classical decision, as in `Digraph.edgeCount`). -/
noncomputable def edgeDeg (g : Digraph) (a : Nat) : Nat :=
  ((List.range g.n).filter fun b => @decide (g.edge a b) (Classical.propDecidable _)).length

theorem edgeCount_of_deg (g : Digraph) (d : Nat → Nat) (h : ∀ a, a < g.n → edgeDeg g a = d a) :
    g.edgeCount = ((List.range g.n).map d).sum := by
  unfold Digraph.edgeCount
  exact congrArg List.sum (List.map_congr_left fun a ha => h a (List.mem_range.1 ha))

theorem Mn_deg (n a : Nat) (ha : a < n) :
    edgeDeg (Mn n) a = (n - 1 - a) + (if a + 1 = n then n - 1 else 0) := by
  unfold edgeDeg
  simp only [Mn_n]
  by_cases hl : a + 1 = n
  · refine Eq.trans (congrArg List.length (List.filter_congr (q := fun b => decide (0 ≤ b ∧ b < n - 1)) ?_)) ?_
    · intro b hb
      have hb := List.mem_range.1 hb
      simp only [decide_eq_decide, Mn_edge_iff]; omega
    · rw [count_interval]; simp [hl] <;> omega
  · refine Eq.trans (congrArg List.length (List.filter_congr (q := fun b => decide (a + 1 ≤ b ∧ b < n)) ?_)) ?_
    · intro b hb
      have hb := List.mem_range.1 hb
      simp only [decide_eq_decide, Mn_edge_iff]; omega
    · rw [count_interval]; simp [hl] <;> omega

/-- |E(M_n)| = (n−1)(n+2)/2 (Definition 4; stated as twice the count). -/
theorem Mn_edgeCount (n : Nat) : 2 * (Mn n).edgeCount = (n - 1) * (n + 2) := by
  rw [edgeCount_of_deg (Mn n) (fun a => (n - 1 - a) + (if a + 1 = n then n - 1 else 0)) (fun a ha => Mn_deg n a ha)]
  simp only [Mn_n]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [sum_map_add]
    have h2 : 2 * ((List.range n).map (HSub.hSub (n - 1))).sum = n * (n - 1) := sum_tri n
    have h3 := sum_last n (n - 1) hn
    generalize ((List.range n).map (HSub.hSub (n - 1))).sum = S at h2 ⊢
    generalize ((List.range n).map fun a => if a + 1 = n then n - 1 else 0).sum = T at h3 ⊢
    subst h3
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have e : m + 1 - 1 = m := by omega
    rw [e] at h2 ⊢
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul] at h2 ⊢
    omega

/-- |E(M_n)| = |MEE(M_n)| + 2(n−1): `n − 1` tree edges, `n − 1` back edges (n ≥ 2). -/
theorem Mn_edgeCount_split {n : Nat} (hn : 2 ≤ n) : (Mn n).edgeCount = (Mn n).meeCount (chainJungle n) + 2 * (n - 1) := by
  have h1 := Mn_edgeCount n
  have h2 := Mn_meeCount n
  have e : n + 2 = (n - 2) + 4 := by omega
  rw [e, Nat.mul_add] at h1
  omega

theorem MnLite_deg (n a : Nat) (ha : a < n) :
    edgeDeg (MnLite n) a = (n - 1 - a) + (if a + 1 = n then n - 2 else 0) := by
  unfold edgeDeg
  simp only [MnLite_n]
  by_cases hl : a + 1 = n
  · refine Eq.trans (congrArg List.length (List.filter_congr (q := fun b => decide (1 ≤ b ∧ b < n - 1)) ?_)) ?_
    · intro b hb
      have hb := List.mem_range.1 hb
      simp only [decide_eq_decide, MnLite_edge_iff]; omega
    · rw [count_interval]; simp [hl] <;> omega
  · refine Eq.trans (congrArg List.length (List.filter_congr (q := fun b => decide (a + 1 ≤ b ∧ b < n)) ?_)) ?_
    · intro b hb
      have hb := List.mem_range.1 hb
      simp only [decide_eq_decide, MnLite_edge_iff]; omega
    · rw [count_interval]; simp [hl] <;> omega

theorem MnLite_edgeCount {n : Nat} (hn : 2 ≤ n) : 2 * (MnLite n).edgeCount + 2 = (n - 1) * (n + 2) := by
  rw [edgeCount_of_deg (MnLite n) (fun a => (n - 1 - a) + (if a + 1 = n then n - 2 else 0)) (fun a ha => MnLite_deg n a ha)]
  simp only [MnLite_n]
  rw [sum_map_add]
  have h2 : 2 * ((List.range n).map (HSub.hSub (n - 1))).sum = n * (n - 1) := sum_tri n
  have h3 := sum_last n (n - 2) (by omega)
  generalize ((List.range n).map (HSub.hSub (n - 1))).sum = S at h2 ⊢
  generalize ((List.range n).map fun a => if a + 1 = n then n - 2 else 0).sum = T at h3 ⊢
  subst h3
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have e : m + 2 - 2 = m := by omega
  have e1 : m + 2 - 1 = m + 1 := by omega
  rw [e1] at h2
  rw [e, e1]
  simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul] at h2 ⊢
  omega

/-- P15: without the back edge `v_n → v_1` there are exactly 2n − 3 non-multiple-entry edges (n ≥ 2); the
multiple-entry edges and the irreducible loops are those of `K_n`. -/
theorem MnLite_others {n : Nat} (hn : 2 ≤ n) :
    (MnLite n).edgeCount = (Kn n).meeCount (chainJungle n) + (2 * n - 3) := by
  have h1 := MnLite_edgeCount hn
  have h2 := Kn_meeCount n
  have e : n + 2 = (n - 2) + 4 := by omega
  rw [e, Nat.mul_add] at h1
  omega

end SmcIrred
