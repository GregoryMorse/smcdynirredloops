import SmcIrred.LNF.Decide
import SmcIrred.Extremal.MnCount

namespace SmcIrred

/-! Mechanical cross-check (class M, **not a proof**): enumerate every control-flow graph on `n` vertices together with
every depth-first jungle it admits (vertices numbered in preorder), compute the Lean `Irreducible`, `IsMEE` and edge counts,
and compare the maxima with the statements proved in `Extremal.IrrBound`, `Extremal.MEEBound` and `Extremal.MnCount`.
The planning script `validation/planning/section5_bruteforce.py` reports the same numbers independently. -/

/-- Computable irreducible-loop count (equal to `Digraph.irrCount`). -/
def evIrr (g : Digraph) (J : Jungle) : Nat := ((List.range g.n).filter fun w => decide (g.Irreducible J w)).length

/-- Computable multiple-entry-edge count (equal to `Digraph.meeCount`). -/
def evMee (g : Digraph) (J : Jungle) : Nat :=
  ((List.range g.n).map fun y => ((List.range g.n).filter fun x => decide (g.IsMEE J x y)).length).sum

/-- Computable edge count (equal to `Digraph.edgeCount`). -/
def evEdge (g : Digraph) : Nat :=
  ((List.range g.n).map fun a => ((List.range g.n).filter fun b => decide (g.edge a b)).length).sum

theorem irrC_eq (g : Digraph) (J : Jungle) : evIrr g J = g.irrCount J :=
  congrArg List.length (List.filter_congr fun w _ => by simp only [decide_eq_decide])

theorem meeC_eq (g : Digraph) (J : Jungle) : evMee g J = g.meeCount J := by
  unfold evMee Digraph.meeCount
  exact congrArg List.sum (List.map_congr_left fun y _ =>
    congrArg List.length (List.filter_congr fun x _ => by simp only [decide_eq_decide]))

theorem edgeC_eq (g : Digraph) : evEdge g = g.edgeCount := by
  unfold evEdge Digraph.edgeCount
  exact congrArg List.sum (List.map_congr_left fun a _ =>
    congrArg List.length (List.filter_congr fun b _ => by simp only [decide_eq_decide]))

/-- Ordered trees on `n` vertices in preorder, as parent arrays (the root's parent is `0`). -/
def treeGo (n : Nat) : Nat → Nat → List Nat → List Nat → List (List Nat)
  | 0, _, par, _ => [par]
  | k + 1, v, par, rm =>
    (List.range rm.length).flatMap fun idx =>
      treeGo n k (v + 1) (par ++ [rm.getD idx 0]) (rm.take (idx + 1) ++ [v])

def trees (n : Nat) : List (List Nat) :=
  if n = 0 then [] else treeGo n (n - 1) 1 [0] [0]

/-- `a` is an ancestor of `b` (or `b` itself) in the tree with parent array `par`. -/
def ancWalk (par : List Nat) : Nat → Nat → Nat → Bool
  | 0, _, _ => false
  | f + 1, a, b => if a == b then true else if b == 0 then false else ancWalk par f a (par.getD b 0)

/-- The depth-first jungle of the ordered tree `par` (clock starts at 2): preorder `2 + 2v − depth v`, the interval of `v`
has length `2·size(v) − 1`. -/
def treeJungle (par : List Nat) : Jungle :=
  let n := par.length
  let depth := fun v => ((List.range n).filter fun u => u != v && ancWalk par n u v).length
  let size := fun v => ((List.range n).filter fun u => ancWalk par n v u).length
  { pre := fun v => 2 + 2 * v - depth v
    post := fun v => 2 + 2 * v - depth v + 2 * size v - 1 }

/-- All control-flow graphs whose depth-first jungle is `treeJungle par` (tree edges plus any subset of the non-tree edges
that a DFS with this tree permits), as `(graph, jungle)` pairs. -/
def graphsOf (par : List Nat) : List (Digraph × Jungle) :=
  let n := par.length
  let J := treeJungle par
  let tree := (List.range n).filter (· ≠ 0) |>.map fun v => (par.getD v 0, v)
  let cand := (List.range n).flatMap fun a => (List.range n).filterMap fun b =>
    if a ≠ b ∧ !(tree.contains (a, b)) ∧ !decide (J.post a < J.pre b) then some (a, b) else none
  (List.range (2 ^ cand.length)).map fun mask =>
    let chosen := (List.range cand.length).filterMap fun i => if (mask / 2 ^ i) % 2 = 1 then cand[i]? else none
    let es := tree ++ chosen
    (⟨n, fun v => (es.filter (fun e => e.1 == v)).map (·.2)⟩, J)

/-- `(max irreducible loops, max multiple-entry edges, min non-MEE edges among graphs with the maximum)` over all
graphs on `n` vertices and all their jungles. -/
def extremes (n : Nat) : Nat × Nat × Nat :=
  (trees n).foldl (fun acc par =>
    (graphsOf par).foldl (fun (acc : Nat × Nat × Nat) (gj : Digraph × Jungle) =>
      let irr := evIrr gj.1 gj.2
      let mee := evMee gj.1 gj.2
      let other := evEdge gj.1 - mee
      let mi := max acc.1 irr
      if mee > acc.2.1 then (mi, mee, other)
      else if mee = acc.2.1 then (mi, mee, min acc.2.2 other)
      else (mi, acc.2.1, acc.2.2)) acc) (0, 0, 1000)

-- Expected: `n − 2` irreducible loops, `C(n−1,2)` multiple-entry edges and `2n − 3` other edges (n = 2: one back edge) for
-- n = 2, 3, 4 (the n = 5 enumeration is too slow for the interpreter under the local memory guard: CI only, gap G20).
#eval show IO Unit from do
  let got := (List.range 3).map fun k => extremes (k + 2)
  let want := [(0, 0, 1), (1, 1, 3), (2, 3, 5)]
  if got != want then throw (IO.userError s!"Section 5 cross-check failed: {got} vs {want}")

end SmcIrred
