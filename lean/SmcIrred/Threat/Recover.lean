module

public import SmcIrred.Threat.Correct
public import SmcIrred.Tarjan.Cost

public section

namespace SmcIrred.Threat

/-- T3 (limit of the static scheme). An analyzer that implements stamping and the machine semantics reports, for every
predicate cell, the intended planted value, and does so with work (in the clean Tarjan model) at most `2 · |V| + |E|` of the
implication graph of the stamped formula. The opacity of the predicates is relative to analyzers without the machine
semantics; it is not computational hardness. -/
theorem recover {A : Analyzer} (hC : SmcSemCap A) {d : Design} (hA : Assumptions d) :
    (∀ k ∈ d.img.cells, A.predict d.img k = d.σ k) ∧
    recoverWork d.img ≤ 2 * d.img.formula.graph.n + tEdges d.img.formula.graph d.img.formula.graph.n := by
  refine ⟨fun k hk => ?_, tarjan_cost _⟩
  obtain ⟨hn, hr, _⟩ := hA.cells_planted k hk
  rw [hC.runs_machine, rtVal_planted hA hn hr]

/-- Every analyzer of the class reaches the goal on every image of a design satisfying S1 and S2. -/
theorem smcsem_determines {A : Analyzer} (hC : SmcSemCap A) (img : Image) : Determines A img :=
  fun k _ => hC.runs_machine img k

end SmcIrred.Threat
