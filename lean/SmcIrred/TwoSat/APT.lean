module

public import SmcIrred.TwoSat.Implication
public import SmcIrred.TwoSat.Reach

public section

namespace SmcIrred

variable {f : TwoSat}

theorem imps_var_lt (hw : f.Wf) {e : Lit × Lit} (he : e ∈ f.imps) : e.1.var < f.n ∧ e.2.var < f.n := by
  obtain ⟨c, hc, hec⟩ := List.mem_flatMap.1 he
  have hv := (hw c hc).2
  match c, hec with
  | [], h => simp [clauseImps] at h
  | [p], h =>
    simp only [clauseImps, List.mem_singleton] at h
    subst h
    have := hv p (by simp)
    exact ⟨this, this⟩
  | [p, q], h =>
    simp only [clauseImps, List.mem_cons, List.not_mem_nil, or_false] at h
    have h1 := hv p (by simp)
    have h2 := hv q (by simp)
    rcases h with rfl | rfl <;> exact ⟨by assumption, by assumption⟩
  | _ :: _ :: _ :: _, h => simp [clauseImps] at h


theorem apt_holds {n : Nat} {lab : Nat → Nat} (hd : ∀ x, x < n → lab (Lit.node ⟨x, true⟩) ≠ lab (Lit.node ⟨x, false⟩))
    {l : Lit} (hl : l.var < n) : l.Holds (aptAssign lab) ↔ lab l.node < lab l.neg.node := by
  cases l with
  | mk x p =>
    cases p
    · have := hd x hl
      simp [Lit.Holds, aptAssign, Lit.neg]
      omega
    · simp [Lit.Holds, aptAssign, Lit.neg]

/-- C21 (APT): if the labels of the literals are in reverse topological order (never increase along an implication) and
no variable has the same label as its negation, then "x true iff label(x) < label(¬x)" satisfies the formula. -/
theorem apt_sat (hw : f.Wf) (hne : ∀ c ∈ f.clauses, c ≠ []) {lab : Nat → Nat}
    (hmono : ∀ e ∈ f.imps, lab e.2.node ≤ lab e.1.node)
    (hd : ∀ x, x < f.n → lab (Lit.node ⟨x, true⟩) ≠ lab (Lit.node ⟨x, false⟩)) : f.Sat (aptAssign lab) := by
  refine (sat_iff_closed hw).2 ⟨hne, fun e he hp => ?_⟩
  obtain ⟨h1, h2⟩ := imps_var_lt hw he
  have hs := imps_skew he
  have m1 := hmono e he
  have m2 : lab e.1.neg.node ≤ lab e.2.neg.node := hmono _ hs
  rw [apt_holds hd h1] at hp
  rw [apt_holds hd h2]
  omega

/-- C22: a formula with an empty clause is unsatisfiable. -/
theorem unsat_of_empty (h : [] ∈ f.clauses) (a : Nat → Bool) : ¬ f.Sat a := by
  intro hs
  obtain ⟨l, hl, -⟩ := hs [] h
  exact absurd hl (by simp)

/-- A variable in the same strongly connected component as its negation makes the formula unsatisfiable. -/
theorem unsat_of_sameSCC (hw : f.Wf) (hne : ∀ c ∈ f.clauses, c ≠ []) {x : Nat}
    (h : f.graph.SameSCC (Lit.node ⟨x, true⟩) (Lit.node ⟨x, false⟩)) (a : Nat → Bool) : ¬ f.Sat a := by
  intro hs
  have hcl := ((sat_iff_closed hw).1 hs).2
  have h1 := closed_reach hcl h.1
  have h2 := closed_reach hcl h.2
  rw [Lit.ofNode_node, Lit.ofNode_node] at h1 h2
  unfold Lit.Holds at h1 h2
  by_cases hax : a x = true
  · have := h1 hax; simp_all
  · have hf : a x = false := by simpa using hax
    have := h2 hf; simp_all

/-- Aspvall–Plass–Tarjan (C21): a 2-SAT formula without empty clause is satisfiable iff no variable lies in the same
strongly connected component of the implication graph as its negation. -/
theorem twoSat_iff_scc (hw : f.Wf) (hne : ∀ c ∈ f.clauses, c ≠ []) :
    (∃ a, f.Sat a) ↔ ∀ x, x < f.n → ¬ f.graph.SameSCC (Lit.node ⟨x, true⟩) (Lit.node ⟨x, false⟩) := by
  constructor
  · rintro ⟨a, ha⟩ x _ h
    exact unsat_of_sameSCC hw hne h a ha
  · intro hx
    refine ⟨aptAssign (sccLabel f.graph), apt_sat hw hne (fun e he => ?_) (fun x hxn hh => hx x hxn ?_)⟩
    · obtain ⟨h1, h2⟩ := imps_var_lt hw he
      have hedge : f.graph.edge e.1.node e.2.node :=
        (graph_edge_iff f _ _).2 ⟨Lit.node_lt h1, Lit.node_lt h2, e, he, rfl, rfl⟩
      exact sccLabel_spec.2 _ _ hedge
    · exact sccLabel_spec.1 _ _ (Lit.node_lt (l := ⟨x, true⟩) hxn) (Lit.node_lt (l := ⟨x, false⟩) hxn) hh

/-- The same, for any labelling in reverse topological order that separates the components (the labels a DFS-based SCC
algorithm emits): either the APT assignment satisfies the formula or some variable shares its label with its negation
and the formula is unsatisfiable. -/
theorem apt_correct (hw : f.Wf) (hne : ∀ c ∈ f.clauses, c ≠ []) {lab : Nat → Nat}
    (hsame : ∀ u w, u < 2 * f.n → w < 2 * f.n → lab u = lab w → f.graph.SameSCC u w)
    (hmono : ∀ e ∈ f.imps, lab e.2.node ≤ lab e.1.node) :
    (∃ x, x < f.n ∧ lab (Lit.node ⟨x, true⟩) = lab (Lit.node ⟨x, false⟩) ∧ ∀ a, ¬ f.Sat a) ∨ f.Sat (aptAssign lab) := by
  by_cases h : ∃ x, x < f.n ∧ lab (Lit.node ⟨x, true⟩) = lab (Lit.node ⟨x, false⟩)
  · obtain ⟨x, hx, hl⟩ := h
    exact Or.inl ⟨x, hx, hl, unsat_of_sameSCC hw hne
      (hsame _ _ (Lit.node_lt (l := ⟨x, true⟩) hx) (Lit.node_lt (l := ⟨x, false⟩) hx) hl)⟩
  · refine Or.inr (apt_sat hw hne hmono fun x hx hh => h ⟨x, hx, hh⟩)

end SmcIrred
