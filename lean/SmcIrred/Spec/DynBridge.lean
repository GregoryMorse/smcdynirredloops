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

/-! ### Circuits with calls

An output vertex `v` of a call `u` has the value written by the call: it depends on the predecessors of `u` (the activation
count) and on the call's input vertices (the first run of the subgraph). The dynamic-scheme vertex `v` therefore reads, besides
`c.reads v`, the predecessors and inputs of each call among its predecessors. -/

/-- What the call vertices among the predecessors of `v` read. -/
@[expose] def Circ.callReads (c : Circ) (v : Nat) : List Nat :=
  (c.pred v).flatMap fun u => match c.kind u with
    | .call _ ins _ _ => c.pred u ++ ins
    | _ => []

/-- The vertices the dynamic-scheme vertex `v` reads. -/
@[expose] def Circ.reads2 (c : Circ) (v : Nat) : List Nat := c.reads v ++ c.callReads v

/-- The dynamic-scheme circuit of an arbitrary circuit over the evaluator `V` of its subgraphs. -/
@[expose] def Circ.toDV (lib : Lib) (V : Circ → (Nat → Bool) → Nat → Nat → Bool) (c : Circ) (inp : Nat → Bool) :
    DCirc Bool where
  n := c.n
  ps := c.reads2
  f v l :=
    let acc := lookupAcc (c.reads2 v) l
    baseVal c inp acc v || (c.pred v).any fun u => writtenBy lib V acc c u v

/-- Every vertex, and everything its predecessor calls read, is smaller than the vertex. -/
@[expose] def Circ.TopoR2 (c : Circ) : Prop := ∀ v, v < c.n → ∀ u ∈ c.reads2 v, u < v

end SmcIrred
