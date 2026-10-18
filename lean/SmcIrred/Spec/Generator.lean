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

end SmcIrred
