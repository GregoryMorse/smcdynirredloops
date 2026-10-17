module

public import SmcIrred.Spec.Graph

public section

namespace SmcIrred

/-- Preorder and postorder timestamps of the vertices of a graph (a candidate DFS "jungle": the depth-first
spanning tree is determined by the timestamps, see `Jungle.IsParent`). -/
structure Jungle where
  pre : Nat → Nat
  post : Nat → Nat

/-- `a` is an ancestor of `b` (or `b` itself): the interval of `b` lies inside the interval of `a`. -/
@[expose] def Jungle.Anc (J : Jungle) (a b : Nat) : Prop := J.pre a ≤ J.pre b ∧ J.post b ≤ J.post a

/-- `u` is the parent of `v` in the tree: its innermost proper ancestor. -/
@[expose] def Jungle.IsParent (g : Digraph) (J : Jungle) (u v : Nat) : Prop :=
  u < g.n ∧ u ≠ v ∧ J.Anc u v ∧ ∀ w, w < g.n → w ≠ v → J.Anc w v → J.Anc w u

/-- `J` is the timestamping of a depth-first search of `g` from `r` (in some order of the successors): intervals
are well formed, distinct and nested or disjoint; the root encloses everything; every other vertex has an
innermost proper ancestor which has an edge to it (the tree edge); and no edge leads to a vertex discovered after
the tail finished (the DFS invariant: edges are tree, forward, back, or cross edges to the left). -/
structure Jungle.Valid (g : Digraph) (r : Nat) (J : Jungle) : Prop where
  interval : ∀ v, v < g.n → J.pre v < J.post v
  pre_inj : ∀ a b, a < g.n → b < g.n → J.pre a = J.pre b → a = b
  post_inj : ∀ a b, a < g.n → b < g.n → J.post a = J.post b → a = b
  events : ∀ a b, a < g.n → b < g.n → J.pre a ≠ J.post b
  laminar : ∀ a b, a < g.n → b < g.n → J.Anc a b ∨ J.Anc b a ∨ J.post a < J.pre b ∨ J.post b < J.pre a
  root : ∀ v, v < g.n → J.Anc r v
  parent : ∀ v, v < g.n → v ≠ r → ∃ u, J.IsParent g u v ∧ g.edge u v
  no_rightward : ∀ a b, g.edge a b → ¬ J.post a < J.pre b

/-- The four classes of an edge relative to a jungle, by the timestamp characterization. -/
inductive EdgeClass
  | tree | forward | back | cross
  deriving DecidableEq, Repr

/-- Class of the edge `a → b`: tree (parent edge), forward (to a proper descendant, not the parent edge), back (to an
ancestor, including a self-loop), cross (to a vertex that finished earlier). -/
@[expose] noncomputable def Jungle.cls (g : Digraph) (J : Jungle) (a b : Nat) : EdgeClass :=
  open Classical in
  if J.IsParent g a b then .tree
  else if J.pre a < J.pre b ∧ J.post b < J.post a then .forward
  else if J.pre b ≤ J.pre a ∧ J.post a ≤ J.post b then .back
  else .cross

end SmcIrred
