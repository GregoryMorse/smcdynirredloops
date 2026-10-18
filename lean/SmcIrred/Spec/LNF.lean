module

public import SmcIrred.Spec.DFS

public section

namespace SmcIrred

/-- A path from `a` to `b` all of whose vertices (ends included) are vertices of the graph satisfying `S`. -/
inductive PathIn (g : Digraph) (S : Nat → Prop) : Nat → Nat → Prop
  | refl {a : Nat} : a < g.n → S a → PathIn g S a a
  | step {a b c : Nat} : S a → g.edge a b → PathIn g S b c → PathIn g S a c

/-- `t → w` is a back edge of the jungle `J`: its target is an ancestor of its source (a self-loop is a back edge). -/
@[expose] def Digraph.BackEdge (g : Digraph) (J : Jungle) (t w : Nat) : Prop := g.edge t w ∧ J.Anc w t

/-- `w` is a loop header: some back edge leads to it. -/
@[expose] def Digraph.IsHeader (g : Digraph) (J : Jungle) (w : Nat) : Prop := ∃ t, g.BackEdge J t w

/-- The Havlak loop body of the header `w`: `w` itself and every proper descendant of `w` that reaches the source of a
back edge to `w` (other than a self-loop) inside the subtree of `w` without passing through `w`. Nested loops are
contained in it. -/
@[expose] def Digraph.Body (g : Digraph) (J : Jungle) (w x : Nat) : Prop :=
  g.IsHeader J w ∧ (x = w ∨ ∃ t, t ≠ w ∧ g.BackEdge J t w ∧ PathIn g (fun z => J.Anc w z ∧ z ≠ w) x t)

/-- The loop of `w` is irreducible: a vertex of its body other than `w` has a predecessor that is not a descendant of
`w` (a second entry). -/
@[expose] def Digraph.Irreducible (g : Digraph) (J : Jungle) (w : Nat) : Prop :=
  g.IsHeader J w ∧ ∃ x y, g.Body J w x ∧ x ≠ w ∧ g.edge y x ∧ ¬ J.Anc w y

/-- `h` is the parent of `x` in the loop nesting forest: the innermost loop other than the loop of `x` itself whose
body contains `x`. -/
@[expose] def Digraph.LnfParent (g : Digraph) (J : Jungle) (h x : Nat) : Prop :=
  g.IsHeader J h ∧ h ≠ x ∧ g.Body J h x ∧ ∀ h', g.IsHeader J h' → h' ≠ x → g.Body J h' x → g.Body J h' h

/-- A multiple-entry edge: it enters the body of a loop, at a vertex other than the header, from outside the subtree of
the header. -/
@[expose] def Digraph.IsMEE (g : Digraph) (J : Jungle) (x y : Nat) : Prop :=
  g.edge x y ∧ ∃ w, g.Body J w y ∧ y ≠ w ∧ ¬ J.Anc w x

/-- `w` dominates `x` (with respect to the entry `r`): `x` is reachable from `r` and every path from `r` to `x` passes through
`w`. -/
@[expose] def Digraph.Dom (g : Digraph) (r w x : Nat) : Prop :=
  PathIn g (fun _ => True) r x ∧ ¬ PathIn g (fun u => u ≠ w) r x

/-- A path of one or more edges, each leaving a vertex reachable from `r` and not entering a vertex that dominates the
vertex it leaves (that is, no edge of the path is a back edge in the sense of dominance). -/
inductive Digraph.NonDomPath (g : Digraph) (r : Nat) : Nat → Nat → Prop
  | single {a b : Nat} : g.edge a b → PathIn g (fun _ => True) r a → ¬ g.Dom r b a → Digraph.NonDomPath g r a b
  | step {a b c : Nat} : g.edge a b → PathIn g (fun _ => True) r a → ¬ g.Dom r b a → Digraph.NonDomPath g r b c →
      Digraph.NonDomPath g r a c

/-- The flow graph is reducible (Hecht–Ullman): the edges that do not enter a vertex dominating their source contain no
cycle. -/
@[expose] def Digraph.Reducible (g : Digraph) (r : Nat) : Prop := ∀ v, ¬ g.NonDomPath r v v

end SmcIrred
