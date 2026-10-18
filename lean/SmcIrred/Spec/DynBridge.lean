module

public import SmcIrred.Spec.Circuit
public import SmcIrred.Spec.Dynamic

public section

namespace SmcIrred

open Dyn

/-! The dynamic scheme of Section 5 over the Boolean-CFG evaluator of Section 4: a call-free circuit `c` with a start-token
input `inp` is the circuit `toD c inp` whose vertex function is the evaluator's `baseVal` read through the values of the
predecessors the vertex reads. -/

/-- The circuit has no calls (every vertex is `flow`, `any`, `add`, `addneg` or `tbl`). -/
@[expose] def Circ.Flat (c : Circ) : Prop := ∀ v, v < c.n → ∀ sid ins outs reps, c.kind v ≠ .call sid ins outs reps

/-- Every vertex reads only smaller vertices. -/
@[expose] def Circ.TopoR (c : Circ) : Prop := ∀ v, v < c.n → ∀ u ∈ c.reads v, u < v

/-- The value of vertex `u` from the list `l` of the values of the vertices `reads` (`false` if `u` is not read). -/
@[expose] def lookupAcc (reads : List Nat) (l : List Bool) (u : Nat) : Bool :=
  match (reads.zip l).find? (fun p => p.1 == u) with
  | some p => p.2
  | none => false

/-- The dynamic-scheme circuit of a call-free circuit: vertex `v` reads `c.reads v` and applies the evaluator's `baseVal`. -/
@[expose] def Circ.toD (c : Circ) (inp : Nat → Bool) : DCirc Bool where
  n := c.n
  ps := c.reads
  f v l := baseVal c inp (lookupAcc (c.reads v) l) v

end SmcIrred
