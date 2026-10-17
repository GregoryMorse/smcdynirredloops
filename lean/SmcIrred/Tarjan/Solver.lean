module

public import SmcIrred.Spec.TwoSatSolve
public import SmcIrred.Tarjan.Correct
public import SmcIrred.TwoSat.APT

public section

namespace SmcIrred

theorem compIdx_decomp : ∀ (comps : List (List Nat)) (v : Nat), (∃ C ∈ comps, v ∈ C) →
    ∃ L C R, comps = L ++ C :: R ∧ L.length = compIdx comps v ∧ v ∈ C := by
  intro comps v
  induction comps with
  | nil => intro h; obtain ⟨C, hC, -⟩ := h; simp at hC
  | cons C cs ih =>
    intro h
    by_cases hv : v ∈ C
    · exact ⟨[], C, cs, rfl, by simp [compIdx, hv], hv⟩
    · have hcs : ∃ C' ∈ cs, v ∈ C' := by
        obtain ⟨C', hC', hv'⟩ := h
        rcases List.mem_cons.1 hC' with rfl | hC'
        · exact absurd hv' hv
        · exact ⟨C', hC', hv'⟩
      obtain ⟨L, C', R, e, hl, hv'⟩ := ih hcs
      exact ⟨C :: L, C', R, by simp [e], by simp [compIdx, hv, hl], hv'⟩

theorem compIdx_le : ∀ (L : List (List Nat)) (C : List Nat) (R : List (List Nat)) (v : Nat), v ∈ C →
    compIdx (L ++ C :: R) v ≤ L.length := by
  intro L C R v hv
  induction L with
  | nil => simp [compIdx, hv]
  | cons D L ih =>
    by_cases h : v ∈ D
    · simp [compIdx, h]
    · simp [compIdx, h]; exact ih

/-- The Aspvall–Plass–Tarjan rule is correct on every list of components that is a partition into strongly connected
components, each closed under successors up to earlier components (what Tarjan's algorithm emits). -/
theorem twoSatSolveOf_spec (f : TwoSat) (hw : f.Wf) (hne : ∀ c ∈ f.clauses, c ≠ []) (comps : List (List Nat))
    (hscc : ∀ C ∈ comps, ∀ u ∈ C, ∀ w, (w ∈ C ↔ f.graph.SameSCC u w))
    (hcov : ∀ v, v < f.graph.n → ∃ C ∈ comps, v ∈ C)
    (hclosed : ∀ L C R, comps = L ++ C :: R → ∀ u ∈ C, ∀ w, f.graph.edge u w → w ∈ C ∨ ∃ C' ∈ L, w ∈ C') :
    (twoSatSolveOf comps f = none ↔ ∀ a, ¬ f.Sat a) ∧ (∀ a, twoSatSolveOf comps f = some a → f.Sat a) := by
  have hsolve : twoSatSolveOf comps f = if ((List.range f.n).any (fun x =>
      compIdx comps (Lit.node ⟨x, true⟩) == compIdx comps (Lit.node ⟨x, false⟩))) = true then none
      else some (aptAssign (compIdx comps)) := rfl
  have hcover : ∀ u, u < 2 * f.n → ∃ C ∈ comps, u ∈ C := fun u hu => hcov u hu
  have hsame : ∀ u w, u < 2 * f.n → w < 2 * f.n → compIdx comps u = compIdx comps w → f.graph.SameSCC u w := by
    intro u w hu hw' he
    obtain ⟨L, C, R, e, hl, huC⟩ := compIdx_decomp comps u (hcover u hu)
    obtain ⟨L2, C2, R2, e2, hl2, hwC⟩ := compIdx_decomp comps w (hcover w hw')
    have hlen : L.length = L2.length := by rw [hl, hl2]; exact he
    have := List.append_inj (e.symm.trans e2) hlen
    obtain ⟨-, h2⟩ := this
    have hCC : C = C2 := by injection h2
    exact (hscc C (show C ∈ comps by rw [e]; simp) u huC w).1 (hCC ▸ hwC)
  have hmono : ∀ e ∈ f.imps, compIdx comps e.2.node ≤ compIdx comps e.1.node := by
    intro e he
    obtain ⟨h1, h2⟩ := imps_var_lt hw he
    have hedge : f.graph.edge e.1.node e.2.node := (graph_edge_iff f _ _).2 ⟨Lit.node_lt h1, Lit.node_lt h2, e, he, rfl, rfl⟩
    obtain ⟨L, C, R, ec, hl, huC⟩ := compIdx_decomp comps e.1.node (hcover _ (Lit.node_lt h1))
    rcases hclosed L C R ec e.1.node huC e.2.node hedge with hwC | ⟨C', hC', hwC'⟩
    · have := compIdx_le L C R e.2.node hwC
      rw [← ec] at this; omega
    · obtain ⟨L1, L2, eL⟩ := List.append_of_mem hC'
      have ec' : comps = L1 ++ C' :: (L2 ++ C :: R) := by rw [ec, eL]; simp
      have := compIdx_le L1 C' (L2 ++ C :: R) e.2.node hwC'
      rw [← ec'] at this
      have hlen : L.length = L1.length + 1 + L2.length := by rw [eL]; simp; omega
      omega
  constructor
  · constructor
    · intro hn a ha
      rw [hsolve] at hn
      by_cases hany : (List.range f.n).any (fun x => compIdx comps (Lit.node ⟨x, true⟩) == compIdx comps (Lit.node ⟨x, false⟩)) = true
      · obtain ⟨x, hx, hxe⟩ := List.any_eq_true.1 hany
        have hxn : x < f.n := List.mem_range.1 hx
        have hxe' : compIdx comps (Lit.node ⟨x, true⟩) = compIdx comps (Lit.node ⟨x, false⟩) := by simpa using hxe
        exact unsat_of_sameSCC hw hne (hsame _ _ (Lit.node_lt (l := ⟨x, true⟩) hxn) (Lit.node_lt (l := ⟨x, false⟩) hxn) hxe') a ha
      · simp only [hany] at hn
        simp at hn
    · intro hu
      rw [hsolve]
      by_cases hany : (List.range f.n).any (fun x => compIdx comps (Lit.node ⟨x, true⟩) == compIdx comps (Lit.node ⟨x, false⟩)) = true
      · simp [hany]
      · exfalso
        have hd : ∀ x, x < f.n → compIdx comps (Lit.node ⟨x, true⟩) ≠ compIdx comps (Lit.node ⟨x, false⟩) := by
          intro x hx he
          apply hany
          exact List.any_eq_true.2 ⟨x, List.mem_range.2 hx, by simpa using he⟩
        exact hu _ (apt_sat hw hne hmono hd)
  · intro a ha
    rw [hsolve] at ha
    by_cases hany : (List.range f.n).any (fun x => compIdx comps (Lit.node ⟨x, true⟩) == compIdx comps (Lit.node ⟨x, false⟩)) = true
    · simp [hany] at ha
    · have hd : ∀ x, x < f.n → compIdx comps (Lit.node ⟨x, true⟩) ≠ compIdx comps (Lit.node ⟨x, false⟩) := by
        intro x hx he
        apply hany
        exact List.any_eq_true.2 ⟨x, List.mem_range.2 hx, by simpa using he⟩
      have hsat := apt_sat hw hne hmono hd
      simp only [hany] at ha
      simp at ha
      subst ha
      exact hsat



theorem twoSatSolve_spec (f : TwoSat) (hw : f.Wf) (hne : ∀ c ∈ f.clauses, c ≠ []) :
    (twoSatSolve f = none ↔ ∀ a, ¬ f.Sat a) ∧ (∀ a, twoSatSolve f = some a → f.Sat a) := by
  obtain ⟨hscc, hcov, -, -, hclosed⟩ := tarjan_spec f.graph
  exact twoSatSolveOf_spec f hw hne (tarjanSccs f.graph) hscc hcov hclosed

end SmcIrred
