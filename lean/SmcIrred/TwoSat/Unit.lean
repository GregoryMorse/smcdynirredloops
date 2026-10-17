module

public import SmcIrred.TwoSat.APT

public section

namespace SmcIrred

/-- The unsatisfiable formula `(x) ∧ (¬x)`. -/
@[expose] def unitClash : TwoSat := ⟨1, [[⟨0, true⟩], [⟨0, false⟩]]⟩

theorem unitClash_wf : unitClash.Wf := by
  intro c hc
  simp [unitClash] at hc
  rcases hc with rfl | rfl <;> simp [unitClash]

theorem unitClash_unsat (a : Nat → Bool) : ¬ unitClash.Sat a := by
  intro h
  obtain ⟨l, hl, hh⟩ := h [⟨0, true⟩] (by simp [unitClash])
  obtain ⟨l', hl', hh'⟩ := h [⟨0, false⟩] (by simp [unitClash])
  simp at hl hl'
  subst hl; subst hl'
  unfold Lit.Holds at hh hh'
  simp_all

/-- C22/C23, P02: if unit clauses are dropped from the implication graph, or encoded as self-loops, the SCC criterion
accepts an unsatisfiable formula (the variable and its negation are never in one component). -/
theorem noUnit_sccCriterion_fails :
    (∀ a, ¬ unitClash.Sat a) ∧
    ¬ unitClash.graphNoUnit.SameSCC (Lit.node ⟨0, true⟩) (Lit.node ⟨0, false⟩) := by
  refine ⟨unitClash_unsat, ?_⟩
  decide

theorem selfLoop_sccCriterion_fails :
    (∀ a, ¬ unitClash.Sat a) ∧
    ¬ unitClash.graphSelfLoop.SameSCC (Lit.node ⟨0, true⟩) (Lit.node ⟨0, false⟩) := by
  refine ⟨unitClash_unsat, ?_⟩
  decide

/-- With the unit-clause encoding `¬p → p` the criterion is right on the same formula. -/
theorem unitEncoding_sccCriterion_correct :
    unitClash.graph.SameSCC (Lit.node ⟨0, true⟩) (Lit.node ⟨0, false⟩) := by
  decide

end SmcIrred
