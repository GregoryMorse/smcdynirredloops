module

public import SmcIrred.Spec.TwoSat

public section

namespace SmcIrred

/-- A path of implications: `a ⇒* b` along the listed implications `(p, q)` ("`p` implies `q`"). -/
inductive ImpPath (imps : List (Lit × Lit)) : Lit → Lit → Prop
  | refl (l : Lit) : ImpPath imps l l
  | step {a b c : Lit} : (a, b) ∈ imps → ImpPath imps b c → ImpPath imps a c

/-- The 2-SAT formula of a list of implications: `p ⇒ q` is the clause `(¬p ∨ q)`; its contrapositive `¬q ⇒ ¬p` is the
same clause, so the implication graph of the formula is closed under contraposition. -/
@[expose] def impFormula (n : Nat) (imps : List (Lit × Lit)) : TwoSat :=
  ⟨n, imps.map fun e => [e.1.neg, e.2]⟩

/-- An implication that the desired assignment `σ` respects: it does not lead from a true to a false literal. -/
@[expose] def Respecting (σ : Nat → Bool) (e : Lit × Lit) : Prop := ¬ (e.1.Holds σ ∧ ¬ e.2.Holds σ)

/-- The planted generator (Section 3.1) with the desired assignment `σ` on the required variables `req` (the other
variables below `n` are free and `σ` is extended arbitrarily): a forest of implications that respects `σ` and gives
every required variable `x` a forcing path from its `σ`-false literal to its `σ`-true literal. -/
structure Planted (n : Nat) (σ : Nat → Bool) (req : Nat → Prop) (forest : List (Lit × Lit)) : Prop where
  wf : ∀ e ∈ forest, e.1.var < n ∧ e.2.var < n
  respect : ∀ e ∈ forest, Respecting σ e
  forcing : ∀ x, x < n → req x → ImpPath forest ⟨x, !σ x⟩ ⟨x, σ x⟩

/-! The generator as an algorithm (`native/protected.c`): the forest is built by giving every required variable `x` a forcing
chain `(x, ¬σ x) ⇒ (m₁, σ m₁) ⇒ … ⇒ (x, σ x)` through intermediate variables `mᵢ` (chosen by a pseudo-random generator, a black
box here: they are parameters), and the random implications that respect `σ` are kept. -/

/-- The chain from the literal `cur` through the variables `ms` (each reached at its `σ`-true literal) to `(x, σ x)`. -/
@[expose] def chainFrom (σ : Nat → Bool) : Lit → List Nat → Nat → List (Lit × Lit)
  | cur, [], x => [(cur, ⟨x, σ x⟩)]
  | cur, m :: ms, x => (cur, ⟨m, σ m⟩) :: chainFrom σ ⟨m, σ m⟩ ms x

/-- The forcing chain of the required variable `x`. -/
@[expose] def chain (σ : Nat → Bool) (x : Nat) (ms : List Nat) : List (Lit × Lit) := chainFrom σ ⟨x, !σ x⟩ ms x

/-- The forest of the chains of the specification `(x, intermediate variables)`. -/
@[expose] def genForest (σ : Nat → Bool) (specs : List (Nat × List Nat)) : List (Lit × Lit) :=
  specs.flatMap fun s => chain σ s.1 s.2

/-- The random implications kept by the generator: those that respect `σ` and stay among the `n` variables. -/
@[expose] def genExtra (n : Nat) (σ : Nat → Bool) (cands : List (Lit × Lit)) : List (Lit × Lit) :=
  cands.filter fun e => !(σ e.1.var == e.1.pos && σ e.2.var != e.2.pos) && decide (e.1.var < n) && decide (e.2.var < n)

end SmcIrred
