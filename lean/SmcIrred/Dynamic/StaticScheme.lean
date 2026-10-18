module

public import SmcIrred.Lang.Fig5
public import SmcIrred.Lang.Fig6
public import SmcIrred.Lang.Congr
public import SmcIrred.Gen.Planted

public section

namespace SmcIrred.Lang

/-! The static scheme end to end (C15, C76): the opaque conditions of the transformed programs are outputs of the 2-SAT
solver (self-modifying-code machine of Section 3) on a planted formula whose desired assignment makes them false. -/

theorem fig5bS_reads : codeReads (compile fig5bS) = [1, 2] := by decide
theorem fig5cS_reads : codeReads (compile fig5cS) = [1] := by decide
theorem fig6bS_reads : codeReads (compile fig6bS) = [1] := by decide
theorem fig6cS_reads : codeReads (compile fig6cS) = [1] := by decide

/-- If the outputs `1` and `2` are false, the transformed programs execute the blocks of the original programs
(Figure 5: `A; B;`, Figure 6: `if (c) A; B;`), for every generator output elsewhere. -/
theorem static_behaviour (sol : Nat → Bool) (h1 : sol 1 = false) (h2 : sol 2 = false) (c v : Bool) :
    traceS sol fig5bS c v = trace fig5a c v ∧ traceS sol fig5cS c true = trace fig5a c true ∧
    traceS sol fig6bS c v = trace fig6a c v ∧ traceS sol fig6cS c true = trace fig6a c true := by
  have key : ∀ (p : Stmt) (v' : Bool), (∀ i ∈ codeReads (compile p), i = 1 ∨ i = 2) →
      traceS sol p c v' = trace p c v' := by
    intro p v' hr
    unfold trace traceS
    apply exec_congr _ c
    intro i hi
    rcases hr i hi with rfl | rfl
    · exact h1
    · exact h2
  have r5b : ∀ i ∈ codeReads (compile fig5bS), i = 1 ∨ i = 2 := by
    intro i hi; rw [fig5bS_reads] at hi; simpa using hi
  have r5c : ∀ i ∈ codeReads (compile fig5cS), i = 1 ∨ i = 2 := by
    intro i hi; rw [fig5cS_reads] at hi; simp at hi; omega
  have r6b : ∀ i ∈ codeReads (compile fig6bS), i = 1 ∨ i = 2 := by
    intro i hi; rw [fig6bS_reads] at hi; simp at hi; omega
  have r6c : ∀ i ∈ codeReads (compile fig6cS), i = 1 ∨ i = 2 := by
    intro i hi; rw [fig6cS_reads] at hi; simp at hi; omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [key _ v r5b]; cases c <;> cases v <;> decide
  · rw [key _ true r5c]; cases c <;> decide
  · rw [key _ v r6b]; cases c <;> cases v <;> decide
  · rw [key _ true r6c]; cases c <;> decide

/-- The transformed programs have irreducible loops (conditions do not affect the control-flow graph). -/
theorem static_irreducible :
    (∃ w, w < 4 ∧ (cfgOf (compile fig5bS)).Irreducible (dfsRun (cfgOf (compile fig5bS)) 0 2) w) ∧
    (∃ w, w < 5 ∧ (cfgOf (compile fig5cS)).Irreducible (dfsRun (cfgOf (compile fig5cS)) 0 2) w) ∧
    (∃ w, w < 4 ∧ (cfgOf (compile fig6bS)).Irreducible (dfsRun (cfgOf (compile fig6bS)) 0 2) w) ∧
    (∃ w, w < 4 ∧ (cfgOf (compile fig6cS)).Irreducible (dfsRun (cfgOf (compile fig6cS)) 0 2) w) := by decide

end SmcIrred.Lang

namespace SmcIrred

open Lang in
/-- C15, C76 (static scheme end to end): for a planted formula (Section 3.1 generator) whose desired assignment makes the
variables `1` and `2` false, the self-modifying-code solver returns a solution whose outputs `1` and `2` are false; the
transformed programs of Figures 5 and 6 whose opaque conditions are these two outputs execute the same blocks as the
original programs, and their control-flow graphs contain irreducible loops. -/
theorem static_scheme {n : Nat} {σ : Nat → Bool} {req : Nat → Prop} {forest extra : List (Lit × Lit)}
    (hp : Planted n σ req forest) (hx : ∀ e ∈ extra, Respecting σ e) (hwx : ∀ e ∈ extra, e.1.var < n ∧ e.2.var < n)
    (h1n : 1 < n) (h2n : 2 < n) (hr1 : req 1) (hr2 : req 2) (hs1 : σ 1 = false) (hs2 : σ 2 = false) :
    ∃ sol, smcSolve (impFormula n (forest ++ extra)) = some sol ∧
      (let o : Nat → Bool := fun k => decide (2 * k ∈ sol)
       o 1 = false ∧ o 2 = false ∧
       (∀ c v, traceS o fig5bS c v = trace fig5a c v ∧ traceS o fig5cS c true = trace fig5a c true ∧
          traceS o fig6bS c v = trace fig6a c v ∧ traceS o fig6cS c true = trace fig6a c true)) ∧
      ((∃ w, w < 4 ∧ (cfgOf (compile fig5bS)).Irreducible (dfsRun (cfgOf (compile fig5bS)) 0 2) w) ∧
       (∃ w, w < 5 ∧ (cfgOf (compile fig5cS)).Irreducible (dfsRun (cfgOf (compile fig5cS)) 0 2) w) ∧
       (∃ w, w < 4 ∧ (cfgOf (compile fig6bS)).Irreducible (dfsRun (cfgOf (compile fig6bS)) 0 2) w) ∧
       (∃ w, w < 4 ∧ (cfgOf (compile fig6cS)).Irreducible (dfsRun (cfgOf (compile fig6cS)) 0 2) w)) := by
  obtain ⟨sol, hsol, hout⟩ := planted_smc (extra := extra) hp hx hwx
  refine ⟨sol, hsol, ?_, static_irreducible⟩
  have e1 := hout 1 h1n hr1
  have e2 := hout 2 h2n hr2
  rw [hs1] at e1
  rw [hs2] at e2
  refine ⟨e1, e2, fun c v => static_behaviour _ e1 e2 c v⟩

end SmcIrred
