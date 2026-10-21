module

public import SmcIrred.Lang.Common
public import SmcIrred.Spec.LangFigs
public import SmcIrred.Spec.Edges

public section

namespace SmcIrred.Lang

/-! Minimal edge counts (C73). -/

/-- Number of edges (distinct successor pairs). -/
@[expose] def numEdges (g : Digraph) : Nat := (List.range g.n).foldl (fun s v => s + g.outDeg v) 0

instance (g : Digraph) : Decidable (NoIrr g) := by unfold NoIrr; infer_instance

/-- One added edge never creates an irreducible loop in a path (checked for paths of at most six vertices: every edge
`x → y`, including back edges, forward edges and self-loops). -/
theorem path_one_edge_reducible (n : Nat) (hn : n ≤ 6) : ∀ x, x < n → ∀ y, y < n → NoIrr (addEdge (pathG n) x y) := by
  have key : ∀ n, n ≤ 6 → ∀ x, x < n → ∀ y, y < n → NoIrr (addEdge (pathG n) x y) := by decide
  exact key n hn

/-- Two added edges suffice (Figure 5(b)): the path `entry → A → B` plus `B → A` and `entry → B`. -/
theorem two_edges_irreducible :
    (addEdge (addEdge (pathG 3) 2 1) 0 2).n = fig5bDrawn.n ∧
    (∀ k, k < 3 → (addEdge (addEdge (pathG 3) 2 1) 0 2).succ k = fig5bDrawn.succ k) ∧
    ∃ w, w < 3 ∧ fig5bDrawn.Irreducible (dfsRun fig5bDrawn 0 2) w := by decide

/-- The one-sided conditional `c → A`, `c → B`, `A → B` (Figure 6(a)). -/
@[expose] def condG : Digraph where
  n := 3
  succ k := [[1, 2], [2], []].getD k []

/-- One edge suffices for a one-sided conditional (Figure 6(b), the edge `B → A`) and none does not. -/
theorem cond_one_edge :
    NoIrr condG ∧ (∀ k, k < 3 → (addEdge condG 2 1).succ k = fig6bDrawn.succ k) ∧
    ∃ w, w < 3 ∧ fig6bDrawn.Irreducible (dfsRun fig6bDrawn 0 2) w := by decide

/-- The simulated loop (Figure 5(c)) adds one vertex and three edges to the path `entry → A → B → exit` and the
result has an irreducible loop. -/
theorem simulated_loop_counts :
    (cfgOf (compile fig5c)).n = (pathG 4).n + 1 ∧
    numEdges (cfgOf (compile fig5c)) = numEdges (pathG 4) + 3 ∧
    ∃ w, w < 5 ∧ (cfgOf (compile fig5c)).Irreducible (dfsRun (cfgOf (compile fig5c)) 0 2) w := by decide

end SmcIrred.Lang
