module

public import SmcIrred.Spec.TwoSat

public section

namespace SmcIrred

/-- A term (conjunction of literals) is satisfied by an assignment. -/
@[expose] def TermSat (t : List Lit) (a : Nat → Bool) : Prop := ∀ l ∈ t, a l.var = l.pos

/-- A DNF (disjunction of terms) is satisfied by an assignment. -/
@[expose] def DnfSat (D : List (List Lit)) (a : Nat → Bool) : Prop := ∃ t ∈ D, TermSat t a

/-- The parity (XOR) of the first `n` variables. -/
@[expose] def parity : Nat → (Nat → Bool) → Bool
  | 0, _ => false
  | n + 1, a => xor (a 0) (parity n (fun j => a (j + 1)))

end SmcIrred
