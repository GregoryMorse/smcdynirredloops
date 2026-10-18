module

public import SmcIrred.Tarjan.CodeModel
public import SmcIrred.Tarjan.TwoSatLink
public import SmcIrred.Tarjan.Solver

public section

namespace SmcIrred

theorem sat_congr (f : TwoSat) (hw : f.Wf) {a b : Nat → Bool} (h : ∀ x, x < f.n → a x = b x) (hs : f.Sat a) :
    f.Sat b := by
  intro c hc
  obtain ⟨l, hl, hh⟩ := hs c hc
  refine ⟨l, hl, ?_⟩
  have hv : l.var < f.n := (hw c hc).2 l hl
  show b l.var = l.pos
  rw [← h _ hv]; exact hh

/-- **The legacy `twosat` is correct** (L01 closed at the level of the algorithm). The loop of `twosat` run over the vector
`sccs` of the legacy `tarjan_scc` (which re-enters visited vertices) reports unsatisfiable exactly when the formula has no
satisfying assignment, and otherwise its set `sol` (literal `2x` for the variable `x`) is a satisfying assignment. -/
theorem twosat_legacy_correct (f : TwoSat) (hw : f.Wf) (hne : ∀ c ∈ f.clauses, c ≠ []) :
    ((tsFold (ctarjanSccs f.graph)).1 = true ↔ ∀ a, ¬ f.Sat a) ∧
    ((tsFold (ctarjanSccs f.graph)).1 = false → f.Sat (fun x => decide (2 * x ∈ (tsFold (ctarjanSccs f.graph)).2))) := by
  obtain ⟨comps, hdup, hscc, hcov, hnd, hrng, hclosed, hE⟩ := ctarjan_spec f.graph
  have hcov' : ∀ v, v < 2 * f.n → v ∈ comps.flatten := by
    intro v hv
    obtain ⟨C, hC, hvC⟩ := hcov v hv
    exact List.mem_flatten.2 ⟨C, hC, hvC⟩
  have hlink := tsFold_link f.n comps hnd hcov' hrng
  have hsolve := twoSatSolveOf_spec f hw hne comps hscc hcov hclosed
  have hany : ((List.range f.n).any (fun x => compIdx comps (Lit.node ⟨x, true⟩) == compIdx comps (Lit.node ⟨x, false⟩)) = true)
      ↔ ∃ x, x < f.n ∧ compIdx comps (2 * x) = compIdx comps (2 * x + 1) := by
    simp [Lit.node, List.any_eq_true]
  have hflag : (tsFold (ctarjanSccs f.graph)).1 = (tsFold comps).1 := hE.1.symm
  refine ⟨?_, ?_⟩
  · rw [hflag, hlink.1, ← hany, ← hsolve.1]
    unfold twoSatSolveOf
    by_cases h : (List.range f.n).any (fun x => compIdx comps (Lit.node ⟨x, true⟩) == compIdx comps (Lit.node ⟨x, false⟩)) = true
    · simp [h]
    · simp [h]
  · intro hf
    rw [hflag] at hf
    have hno : ¬ ((List.range f.n).any (fun x => compIdx comps (Lit.node ⟨x, true⟩) == compIdx comps (Lit.node ⟨x, false⟩)) = true) := by
      rw [hany, ← hlink.1, hf]; simp
    have hsome : twoSatSolveOf comps f = some (aptAssign (compIdx comps)) := by
      unfold twoSatSolveOf; simp [hno]
    have hsat := hsolve.2 _ hsome
    refine sat_congr f hw (fun x hx => ?_) hsat
    have h1 := hlink.2 hf x hx
    have h2 : 2 * x ∈ (tsFold (ctarjanSccs f.graph)).2 ↔ 2 * x ∈ (tsFold comps).2 := (hE.2 _).symm
    simp only [aptAssign, Lit.node]
    simp only [decide_eq_decide]
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    rw [h2]; exact h1.symm

end SmcIrred
