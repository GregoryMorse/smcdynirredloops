module

public import SmcIrred.Spec.LNF

public section

namespace SmcIrred

/-- The complete digraph `K_n` without self-loops on the vertices `0 … n-1` (the paper's `v_1 … v_n`, numbered in
depth-first order), successors in ascending order. -/
@[expose] def Kn (n : Nat) : Digraph where
  n := n
  succ i := (List.range n).filter fun j => decide (j ≠ i)

/-- The reduced graph `M_n` (Definition 4): tree edges `v_i → v_{i+1}`, back edges `v_n → v_i` (`i < n`), and the edges
`v_i → v_j` for `j ≥ i + 2`, which are the multiple-entry edges. -/
@[expose] def Mn (n : Nat) : Digraph where
  n := n
  succ i := (List.range n).filter fun j => decide (j = i + 1 ∨ (i + 1 = n ∧ j + 1 < n) ∨ i + 2 ≤ j)

/-- `M_n` without the back edge `v_n → v_1` (which is not needed to keep the maximal number of multiple-entry edges). -/
@[expose] def MnLite (n : Nat) : Digraph where
  n := n
  succ i := (List.range n).filter fun j => decide (j = i + 1 ∨ (i + 1 = n ∧ 1 ≤ j ∧ j + 1 < n) ∨ i + 2 ≤ j)

/-- The depth-first jungle of a chain `0 → 1 → … → n-1` with the clock starting at 2. -/
@[expose] def chainJungle (n : Nat) : Jungle where
  pre i := 2 + i
  post i := 2 * n + 1 - i

open Classical in
/-- The number of edges. -/
@[expose] noncomputable def Digraph.edgeCount (g : Digraph) : Nat :=
  ((List.range g.n).map fun a => ((List.range g.n).filter fun b => decide (g.edge a b)).length).sum

open Classical in
/-- The number of irreducible loops of the jungle `J`. -/
@[expose] noncomputable def Digraph.irrCount (g : Digraph) (J : Jungle) : Nat :=
  ((List.range g.n).filter fun w => decide (g.Irreducible J w)).length

open Classical in
/-- The number of multiple-entry edges of the jungle `J`. -/
@[expose] noncomputable def Digraph.meeCount (g : Digraph) (J : Jungle) : Nat :=
  ((List.range g.n).map fun y => ((List.range g.n).filter fun x => decide (g.IsMEE J x y)).length).sum

end SmcIrred
