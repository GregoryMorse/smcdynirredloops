module

public import SmcIrred.Lang.MinEdges

public section

namespace SmcIrred.Lang

/-! Two-way and n-way conditionals (C76): the same device works for any number of branches. -/

/-- The `n`-way conditional is reducible; the single edge from the join back into the first branch makes an
irreducible loop (the other branches enter the join from outside it), for `2 ≤ k ≤ 6` (two-way to six-way). -/
theorem nway_one_edge : ∀ k, 2 ≤ k → k ≤ 6 →
    NoIrr (nwayG k) ∧ ∃ w, w < k + 2 ∧ (addEdge (nwayG k) (k + 1) 1).Irreducible (dfsRun (addEdge (nwayG k) (k + 1) 1) 0 2) w := by
  have key : ∀ k, k < 7 → 2 ≤ k → NoIrr (nwayG k) ∧ ∃ w, w < k + 2 ∧
      (addEdge (nwayG k) (k + 1) 1).Irreducible (dfsRun (addEdge (nwayG k) (k + 1) 1) 0 2) w := by decide
  intro k h2 h6
  exact key k (by omega) h2

/-- With one branch the same edge gives only a reducible loop. -/
theorem oneway_no_irreducible : NoIrr (addEdge (nwayG 1) 2 1) := by decide

end SmcIrred.Lang
