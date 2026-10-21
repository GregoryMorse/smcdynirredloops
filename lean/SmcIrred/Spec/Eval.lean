module

public import SmcIrred.Spec.Virt

public section

namespace SmcIrred

/-- The local rule of a vertex of kind `k` with predecessor values `vs` and an active input `t`: `flow` needs all active and
some present, `any` some active, `add` an odd number, `addneg` an even number of active predecessors. -/
@[expose] def nodeVal (k : Kind) (vs : List Bool) (t : Bool) : Bool :=
  let a := (vs.filter id).length + (if t then 1 else 0)
  let l := vs.length + (if t then 1 else 0)
  match k with
  | .flow => decide (l ≠ 0 ∧ a = l)
  | .any => decide (l ≠ 0 ∧ a ≠ 0)
  | .add => decide (a % 2 = 1)
  | .addneg => decide (a % 2 = 0)
  | _ => false

/-- Append the value of the next vertex to the values computed so far. -/
@[expose] def stepE (inp : Nat → Bool) (vs : List Bool) (nd : Kind × List Nat) : List Bool :=
  vs ++ [nodeVal nd.1 (nd.2.map fun u => vs.getD u false) (inp vs.length)]

/-- The values of all vertices of a generator state, in the order the vertices were added. -/
@[expose] def evalNodes (inp : Nat → Bool) (nodes : List (Kind × List Nat)) : List Bool :=
  nodes.foldl (stepE inp) []

/-- The value of a wire. -/
@[expose] def Wire.ev (vs : List Bool) : Wire → Bool
  | .cst b => b
  | .nd i => vs.getD i false

/-- The value of a wire in the state `gb` under the active inputs `inp`. -/
@[expose] def wev (gb : GB) (inp : Nat → Bool) (w : Wire) : Bool := w.ev (evalNodes inp gb.nodes)

end SmcIrred
