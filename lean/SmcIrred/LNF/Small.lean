module

public import SmcIrred.LNF.Facts
public import SmcIrred.Graph.DfsValid

public section

namespace SmcIrred

variable {g : Digraph} {r : Nat} {J : Jungle}

/-- C71: a control-flow graph with at most two vertices contains no irreducible loop (for any jungle). -/
theorem no_irreducible_of_small (hn : g.n ≤ 2) (w : Nat) : ¬ g.Irreducible J w := by
  rintro ⟨hh, x, y, hb, hxw, he, hna⟩
  have hw := hh.lt g J
  have hx := he.2.1
  have hy := he.1
  apply hna
  by_cases e : y = w
  · subst e; exact Jungle.Anc.refl _
  · have : y = x := by omega
    subst this
    exact hb.anc

/-- The smallest graph with an irreducible loop: `r → a`, `r → b`, `a ↔ b`. -/
@[expose] def threeNode : Digraph where
  n := 3
  succ
    | 0 => [1, 2]
    | 1 => [2]
    | 2 => [1]
    | _ => []

/-- C71 (witness): in every depth-first jungle of `r → a, r → b, a ↔ b` the loop on a and b is irreducible. -/
theorem threeNode_irreducible (h : J.Valid threeNode 0) : threeNode.Irreducible J 1 ∨ threeNode.Irreducible J 2 := by
  have e12 : threeNode.edge 1 2 := by decide
  have e21 : threeNode.edge 2 1 := by decide
  have e02 : threeNode.edge 0 2 := by decide
  have e01 : threeNode.edge 0 1 := by decide
  have r1 := h.root 1 (by decide)
  have r2 := h.root 2 (by decide)
  have n1 := h.no_rightward 1 2 e12
  have n2 := h.no_rightward 2 1 e21
  have hint1 := h.interval 1 (by decide)
  have hint2 := h.interval 2 (by decide)
  rcases h.laminar 1 2 (by decide) (by decide) with hc | hc | hc | hc
  · left
    have hb : threeNode.BackEdge J 2 1 := ⟨e21, hc⟩
    refine ⟨⟨2, hb⟩, 2, 0, ⟨⟨2, hb⟩, Or.inr ⟨2, by decide, hb, .refl (by decide) ⟨hc, by decide⟩⟩⟩, by decide, e02, ?_⟩
    intro hanc
    have := h.anc_antisymm (by decide) (by decide) r1 hanc
    exact absurd this (by decide)
  · right
    have hb : threeNode.BackEdge J 1 2 := ⟨e12, hc⟩
    refine ⟨⟨1, hb⟩, 1, 0, ⟨⟨1, hb⟩, Or.inr ⟨1, by decide, hb, .refl (by decide) ⟨hc, by decide⟩⟩⟩, by decide, e01, ?_⟩
    intro hanc
    have := h.anc_antisymm (by decide) (by decide) r2 hanc
    exact absurd this (by decide)
  · exfalso; exact n1 hc
  · exfalso; exact n2 hc

/-- The depth-first search of the three-node graph gives a valid jungle, so the witness is not vacuous. -/
theorem threeNode_dfs_valid : (dfsRun threeNode 0 1).Valid threeNode 0 := by
  apply dfsRun_valid _ (by omega)
  refine ⟨by decide, ?_⟩
  intro v hv
  change v < 3 at hv
  obtain (rfl | rfl | rfl) : v = 0 ∨ v = 1 ∨ v = 2 := by omega
  · exact .refl 0
  · exact .step (by decide : threeNode.edge 0 1) (.refl 1)
  · exact .step (by decide : threeNode.edge 0 2) (.refl 2)

end SmcIrred
