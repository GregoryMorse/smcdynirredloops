module

public import SmcIrred.Spec.TwoSat
public import SmcIrred.Spec.Tarjan

public section

namespace SmcIrred

/-- The index of the first component of the list containing `v` (`0` for an empty list). -/
@[expose] def compIdx : List (List Nat) → Nat → Nat
  | [], _ => 0
  | C :: cs, v => if v ∈ C then 0 else compIdx cs v + 1

/-- The Aspvall–Plass–Tarjan rule on a list of components in emission order, with the component index as label: `none`
when a variable shares its component with its negation. -/
@[expose] def twoSatSolveOf (comps : List (List Nat)) (f : TwoSat) : Option (Nat → Bool) :=
  let lab := compIdx comps
  if (List.range f.n).any (fun x => lab (Lit.node ⟨x, true⟩) == lab (Lit.node ⟨x, false⟩)) then none
  else some (aptAssign lab)

/-- The reference 2-SAT solver: Tarjan's components of the implication graph in emission order, then the
Aspvall–Plass–Tarjan rule. -/
@[expose] def twoSatSolve (f : TwoSat) : Option (Nat → Bool) := twoSatSolveOf (tarjanSccs f.graph) f

end SmcIrred
