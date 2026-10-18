module

public import SmcIrred.Smc.Final

public section

namespace SmcIrred

/-- Level 2 of the SMC solver is a correct 2-SAT solver: `none` exactly when the formula is unsatisfiable, and the literal
nodes of a returned solution set form a satisfying assignment. -/
theorem smcSolve_spec (f : TwoSat) (hw : f.Wf) (hne : ∀ c ∈ f.clauses, c ≠ []) :
    (smcSolve f = none ↔ ∀ a, ¬ f.Sat a) ∧ (∀ sol, smcSolve f = some sol → f.Sat (fun x => decide (2 * x ∈ sol))) := by
  have hgn : f.graph.n = 2 * f.n := rfl
  obtain ⟨hscc', hcov', hnd', hrng', hclosed'⟩ := tarjan_spec (revG f.graph)
  have hscc : ∀ C ∈ tarjanSccs (revG f.graph), ∀ u ∈ C, ∀ w, (w ∈ C ↔ f.graph.SameSCC u w) := by
    intro C hC u hu w
    rw [← revG_scc]
    exact hscc' C hC u hu w
  have hcov : ∀ v, v < f.graph.n → ∃ C ∈ tarjanSccs (revG f.graph), v ∈ C := fun v hv => hcov' v hv
  have hclosed : ∀ L C R, tarjanSccs (revG f.graph) = L ++ C :: R → ∀ u ∈ C, ∀ w, f.graph.edge u w →
      w ∈ C ∨ ∃ C' ∈ L, w ∈ C' := by
    intro L C R e u hu w hedge
    exact hclosed' L C R e u hu w ((revG_edge _ _ _).2 hedge)
  have hspec := twoSatSolveOf_spec f hw hne _ hscc hcov hclosed
  have hR := sRun_sim f.graph (f.graph.n - 1) rfl (List.range f.graph.n) TState.init (SState.init f.graph.n)
    (SRel.init f.graph) (by intro v hv; simpa using hv)
  have e : smcSolve f = sSolFold (sRun f.graph (f.graph.n - 1) (List.range f.graph.n) (SState.init f.graph.n)).set
      (tarjanSccs (revG f.graph)).flatten [] := by
    unfold smcSolve
    show sSolFold _ (sRun f.graph (f.graph.n - 1) (List.range f.graph.n) (SState.init f.graph.n)).chain [] = _
    rw [hR.chain]
    rfl
  have hcov2 : ∀ v, v < 2 * f.n → v ∈ (tarjanSccs (revG f.graph)).flatten := by
    intro v hv
    obtain ⟨C, hC, hvC⟩ := hcov' v hv
    exact List.mem_flatten.2 ⟨C, hC, hvC⟩
  have hrng : ∀ C ∈ tarjanSccs (revG f.graph), ∀ w ∈ C, w < 2 * f.n := hrng'
  have hlink := smc_link f.n (tarjanSccs (revG f.graph)) _ hnd' hcov2 hrng hR.set
  have hso : twoSatSolveOf (tarjanSccs (revG f.graph)) f = none ↔
      ∃ x, x < f.n ∧ compIdx (tarjanSccs (revG f.graph)) (2 * x) = compIdx (tarjanSccs (revG f.graph)) (2 * x + 1) := by
    unfold twoSatSolveOf
    by_cases h : ((List.range f.n).any (fun x => compIdx (tarjanSccs (revG f.graph)) (Lit.node ⟨x, true⟩) ==
        compIdx (tarjanSccs (revG f.graph)) (Lit.node ⟨x, false⟩))) = true
    · simp only [h, ↓reduceIte, true_iff]
      obtain ⟨x, hx, hxe⟩ := List.any_eq_true.1 h
      exact ⟨x, List.mem_range.1 hx, by simpa [Lit.node] using hxe⟩
    · simp only [h, ↓reduceIte]
      constructor
      · intro hh; exact absurd hh (by simp)
      · rintro ⟨x, hx, hxe⟩
        exact absurd (List.any_eq_true.2 ⟨x, List.mem_range.2 hx, by simpa [Lit.node] using hxe⟩) h
  refine ⟨?_, ?_⟩
  · rw [e, hlink.1, ← hso]
    exact hspec.1
  · intro sol h
    rw [e] at h
    obtain ⟨hl, hsolr⟩ := hlink.2 sol h
    have hno : ¬ twoSatSolveOf (tarjanSccs (revG f.graph)) f = none := by
      rw [hso]
      intro hex
      have := hlink.1.2 hex
      rw [h] at this
      exact absurd this (by simp)
    have hsm : twoSatSolveOf (tarjanSccs (revG f.graph)) f = some (aptAssign (compIdx (tarjanSccs (revG f.graph)))) := by
      unfold twoSatSolveOf
      have hn : ¬ ((List.range f.n).any (fun x => compIdx (tarjanSccs (revG f.graph)) (Lit.node ⟨x, true⟩) ==
          compIdx (tarjanSccs (revG f.graph)) (Lit.node ⟨x, false⟩))) = true := by
        intro hh
        apply hno
        unfold twoSatSolveOf
        simp only [hh, ↓reduceIte]
      rw [if_neg hn]
    have hsat := hspec.2 _ hsm
    have hfun : (fun x => decide (2 * x ∈ sol)) = aptAssign (compIdx (tarjanSccs (revG f.graph))) := by
      funext x
      unfold aptAssign
      simp only [Lit.node, ite_true, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      by_cases hx : x < f.n
      · exact decide_eq_decide.2 (hl x hx)
      · have h1 : ¬ 2 * x ∈ sol := fun hh => by have := hsolr _ hh; omega
        have h2 : (2 * x) ∉ (tarjanSccs (revG f.graph)).flatten := fun hh => by
          obtain ⟨C, hC, hxC⟩ := List.mem_flatten.1 hh
          have := hrng C hC _ hxC; omega
        have h3 : (2 * x + 1) ∉ (tarjanSccs (revG f.graph)).flatten := fun hh => by
          obtain ⟨C, hC, hxC⟩ := List.mem_flatten.1 hh
          have := hrng C hC _ hxC; omega
        rw [compIdx_not_mem _ _ h2, compIdx_not_mem _ _ h3]
        simp [h1]
    rw [hfun]
    exact hsat

end SmcIrred
