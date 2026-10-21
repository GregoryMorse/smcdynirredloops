module

public import SmcIrred.Spec.LangFigs
public import SmcIrred.Spec.LNF
public import SmcIrred.Spec.RunDFS

public section

namespace SmcIrred.Lang

/-! # Graph shapes of the minimal-edge statements (Section 5)

The path, the graph with one added edge, the `n`-way conditional and the property that no vertex heads an irreducible loop
of the depth-first jungle of the code order. -/

/-- The path `0 → 1 → … → n-1`. -/
@[expose] def pathG (n : Nat) : Digraph where
  n := n
  succ k := if k + 1 < n then [k + 1] else []

/-- Add the edge `x → y` (listed last at `x`). -/
@[expose] def addEdge (g : Digraph) (x y : Nat) : Digraph where
  n := g.n
  succ k := if k = x then g.succ k ++ [y] else g.succ k

/-- No vertex heads an irreducible loop of the depth-first jungle of the code order. -/
@[expose] def NoIrr (g : Digraph) : Prop :=
  ∀ w, w < g.n → ¬ g.Irreducible (dfsRun g 0 2) w

/-- An `n`-way conditional: vertex `0` is the condition, `1 … k` the branches, `k + 1` the join. -/
@[expose] def nwayG (k : Nat) : Digraph where
  n := k + 2
  succ v := if v = 0 then (List.range k).map (· + 1) else if v ≤ k then [k + 1] else []

/-- The `n`-way conditional with the edge from the join back into the first branch. -/
@[expose] def nwayE (k : Nat) : Digraph := addEdge (nwayG k) (k + 1) 1

end SmcIrred.Lang
