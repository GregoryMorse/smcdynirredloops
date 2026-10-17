module

public import SmcIrred.Spec.Graph

public section

namespace SmcIrred

/-- A literal: a variable (numbered from `0`) or its negation. -/
structure Lit where
  var : Nat
  pos : Bool
  deriving DecidableEq

@[expose] def Lit.neg (l : Lit) : Lit := ⟨l.var, !l.pos⟩

/-- The vertex of the implication graph of a literal: `2x` for `x`, `2x + 1` for `¬x`. -/
@[expose] def Lit.node (l : Lit) : Nat := 2 * l.var + (if l.pos then 0 else 1)

/-- The literal of a vertex of the implication graph. -/
@[expose] def Lit.ofNode (u : Nat) : Lit := ⟨u / 2, decide (u % 2 = 0)⟩

/-- A 2-SAT formula: `n` variables and `m` clauses of at most two literals each (`Wf`); the empty clause is allowed and
is unsatisfiable. -/
structure TwoSat where
  n : Nat
  clauses : List (List Lit)

@[expose] def TwoSat.Wf (f : TwoSat) : Prop := ∀ c ∈ f.clauses, c.length ≤ 2 ∧ ∀ l ∈ c, l.var < f.n

/-- The literal is true under the assignment `a`. -/
@[expose] def Lit.Holds (a : Nat → Bool) (l : Lit) : Prop := a l.var = l.pos

/-- A clause is satisfied when one of its literals holds (the empty clause is never satisfied). -/
@[expose] def ClauseSat (a : Nat → Bool) (c : List Lit) : Prop := ∃ l ∈ c, l.Holds a

@[expose] def TwoSat.Sat (f : TwoSat) (a : Nat → Bool) : Prop := ∀ c ∈ f.clauses, ClauseSat a c

/-- The implications of a clause: `(p ∨ q)` gives `¬p → q` and `¬q → p`; a unit clause `(p)` gives `¬p → p`; the empty
clause gives none. -/
@[expose] def clauseImps : List Lit → List (Lit × Lit)
  | [a, b] => [(a.neg, b), (b.neg, a)]
  | [a] => [(a.neg, a)]
  | _ => []

@[expose] def TwoSat.imps (f : TwoSat) : List (Lit × Lit) := f.clauses.flatMap clauseImps

/-- The implication graph on the `2n` literal vertices (successor order: clause order). -/
@[expose] def TwoSat.graph (f : TwoSat) : Digraph where
  n := 2 * f.n
  succ u := (f.imps.filter fun e => e.1.node == u).map fun e => e.2.node

/-- The variant that drops unit clauses from the implication graph. -/
@[expose] def clauseImpsNoUnit : List Lit → List (Lit × Lit)
  | [a, b] => [(a.neg, b), (b.neg, a)]
  | _ => []

@[expose] def TwoSat.graphNoUnit (f : TwoSat) : Digraph where
  n := 2 * f.n
  succ u := ((f.clauses.flatMap clauseImpsNoUnit).filter fun e => e.1.node == u).map fun e => e.2.node

/-- The variant that encodes a unit clause `(p)` as the self-loop `p → p`. -/
@[expose] def clauseImpsSelfLoop : List Lit → List (Lit × Lit)
  | [a, b] => [(a.neg, b), (b.neg, a)]
  | [a] => [(a, a)]
  | _ => []

@[expose] def TwoSat.graphSelfLoop (f : TwoSat) : Digraph where
  n := 2 * f.n
  succ u := ((f.clauses.flatMap clauseImpsSelfLoop).filter fun e => e.1.node == u).map fun e => e.2.node

end SmcIrred
