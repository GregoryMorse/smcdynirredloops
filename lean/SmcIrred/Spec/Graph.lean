module

public section

namespace SmcIrred

/-- A finite directed graph on the vertices `0 … n-1`; `succ v` lists the out-neighbours of `v` in a fixed
order (the order a depth-first search follows). -/
structure Digraph where
  n : Nat
  succ : Nat → List Nat

/-- `a → b` is an edge: both ends are vertices and `b` is listed among the successors of `a`. -/
@[expose] def Digraph.edge (g : Digraph) (a b : Nat) : Prop := a < g.n ∧ b < g.n ∧ b ∈ g.succ a

/-- Reachability along edges (reflexive-transitive closure). -/
inductive Digraph.Reach (g : Digraph) : Nat → Nat → Prop
  | refl (a : Nat) : Digraph.Reach g a a
  | step {a b c : Nat} : g.edge a b → Digraph.Reach g b c → Digraph.Reach g a c

/-- A control-flow graph with root `h`: every vertex is reachable from `h`. -/
@[expose] def Digraph.IsCFG (g : Digraph) (h : Nat) : Prop := h < g.n ∧ ∀ v, v < g.n → g.Reach h v

/-- Two vertices lie in the same strongly connected component. -/
@[expose] def Digraph.SameSCC (g : Digraph) (a b : Nat) : Prop := g.Reach a b ∧ g.Reach b a

/-- The number of distinct out-neighbours of `v` (a repeated entry in `succ v` is one edge). -/
@[expose] def Digraph.outDeg (g : Digraph) (v : Nat) : Nat :=
  ((List.range g.n).filter fun w => (g.succ v).contains w).length

/-- Vertex kinds of the paper's Section 2 by number of out-edges: none (exit or return vertex), one (sequence),
two (Boolean conditional), more (n-way conditional). -/
inductive VKind
  | exit | seq | cond | nway
  deriving DecidableEq, Repr

@[expose] def Digraph.kind (g : Digraph) (v : Nat) : VKind :=
  match g.outDeg v with
  | 0 => .exit
  | 1 => .seq
  | 2 => .cond
  | _ => .nway

end SmcIrred
