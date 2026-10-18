module

public import SmcIrred.Spec.Graph

public section

namespace SmcIrred

/-!
# The Boolean-CFG virtual machine (Section 4, `python/virt.py` `do_run_virtual`, `BITSZ = 1`)

A circuit is a DAG on the vertices `0 … n-1`; a vertex is *accepting* when the control flow reaches it. The value of a
vertex is determined by the predecessors that are accepting: `flow` (AND), `any` (OR), `add` (XOR: an odd number),
`addneg` (XNOR: an even number), `tbl` (a constant selection table), `call` (a reusable subgraph with an activation edge,
an input map, an output map and a repetition count). The output vertices of a call are ordinary `flow` vertices whose only
predecessor is the call; the call writes them when it finishes. The start token is a virtual predecessor of every active
input vertex.

The evaluator is defined by the depth of the nesting of calls (a call at depth `0` writes nothing) and by a fuel that is the
number of vertices. All counts are of vertices and examined predecessor edges, as the Python statistics (`stats`).
-/

inductive Kind
  | flow | any | add | addneg
  | tbl (sel : List Nat) (tab : List Bool)
  | call (sid : Nat) (ins outs : List Nat) (reps : Nat)

structure Circ where
  n : Nat
  kind : Nat → Kind
  pred : Nat → List Nat

/-- A reusable subgraph: input vertices, output vertices, the feedback map (input `j` of the next run is fed from output
`fb[j]` of the previous run) and whether the last output is a gate bit (the repetition stops when it is not accepting). -/
structure Sub where
  c : Circ
  ins : List Nat
  outs : List Nat
  fb : List Nat
  gated : Bool

/-- The subgraph table. -/
abbrev Lib := Nat → Sub

/-- Number of vertices of `l` accepted by `acc`. -/
@[expose] def cnt (acc : Nat → Bool) (l : List Nat) : Nat := (l.filter acc).length

/-- The predecessors read by the vertex `x`: its predecessors, the selectors of a table, the inputs of a call. -/
@[expose] def Circ.reads (c : Circ) (x : Nat) : List Nat :=
  c.pred x ++ (match c.kind x with
    | .tbl sel _ => sel
    | .call _ ins _ _ => ins
    | _ => [])

/-- The executed runs of a call, as pairs (input predicate, accepting set), in order: the first run, then up to `reps`
feedback runs, each executed only if the gate allows it. -/
@[expose] def callRunsAux (run : (Nat → Bool) → (Nat → Bool)) (gate : (Nat → Bool) → Bool)
    (fbIn : (Nat → Bool) → (Nat → Bool)) : Nat → (Nat → Bool) → List ((Nat → Bool) × (Nat → Bool))
  | 0, _ => []
  | k + 1, z => if gate z then [] else (fbIn z, run (fbIn z)) :: callRunsAux run gate fbIn k (run (fbIn z))

@[expose] def callRuns (run : (Nat → Bool) → (Nat → Bool)) (gate : (Nat → Bool) → Bool)
    (fbIn : (Nat → Bool) → (Nat → Bool)) (reps : Nat) (inb0 : Nat → Bool) : List ((Nat → Bool) × (Nat → Bool)) :=
  (inb0, run inb0) :: callRunsAux run gate fbIn reps (run inb0)

/-- The accepting set after the last executed run. -/
@[expose] def finalZ (rs : List ((Nat → Bool) × (Nat → Bool))) : Nat → Bool :=
  match rs.getLast? with
  | some p => p.2
  | none => fun _ => false

/-- One level of the evaluator: values `V` and costs `K` (vertices, examined edges) of circuits one nesting level lower. -/
structure Level where
  val : Circ → (Nat → Bool) → Nat → Nat → Bool
  cost : Circ → (Nat → Bool) → Nat × Nat

/-- The runs of the call `u` of the caller `c` (given the final values `acc` of the caller) on the subgraph library. -/
@[expose] def callOf (lib : Lib) (V : Circ → (Nat → Bool) → Nat → Nat → Bool) (acc : Nat → Bool) (sid : Nat)
    (ins : List Nat) (reps : Nat) : List ((Nat → Bool) × (Nat → Bool)) :=
  let s := lib sid
  callRuns (fun inb u => V s.c inb s.c.n u)
    (fun z => s.gated && !(match s.outs.getLast? with | some o => z o | none => false))
    (fun z u => (s.ins.zip s.fb).any fun p => p.1 == u && z (s.outs.getD p.2 0))
    reps (fun u => (s.ins.zip ins).any fun p => p.1 == u && acc p.2)

/-- The vertices written by the call `u`: the caller outputs `outs[j]` whose subgraph output `j` is accepting at the end. -/
@[expose] def writtenBy (lib : Lib) (V : Circ → (Nat → Bool) → Nat → Nat → Bool) (acc : Nat → Bool) (c : Circ) (u v : Nat) :
    Bool :=
  match c.kind u with
  | .call sid ins outs reps =>
    (cnt acc (c.pred u) == 1) && ((outs.zip (lib sid).outs).any fun p => p.1 == v && finalZ (callOf lib V acc sid ins reps) p.2)
  | _ => false

/-- The value of a vertex from the accepting set `acc` of its predecessors (the start token counts for an active input). -/
@[expose] def baseVal (c : Circ) (inp : Nat → Bool) (acc : Nat → Bool) (v : Nat) : Bool :=
  let ps := c.pred v
  let tokn := if inp v then 1 else 0
  let a := cnt acc ps + tokn
  let l := ps.length + tokn
  match c.kind v with
  | .flow => decide (l ≠ 0 ∧ a = l)
  | .any => decide (l ≠ 0 ∧ a ≠ 0)
  | .add => decide (a % 2 = 1)
  | .addneg => decide (a % 2 = 0)
  | .tbl sel tab => decide (a = l) && (sel.zip tab).any fun p => acc p.1 && p.2
  | .call .. => false

/-- Value of a vertex with fuel `f` at one nesting level (`V` evaluates the subgraphs). -/
@[expose] def valAt (lib : Lib) (V : Circ → (Nat → Bool) → Nat → Nat → Bool) (c : Circ) (inp : Nat → Bool) :
    Nat → Nat → Bool
  | 0, _ => false
  | f + 1, v =>
    let acc := valAt lib V c inp f
    baseVal c inp acc v || (c.pred v).any fun u => writtenBy lib V acc c u v

/-- Examined predecessor edges of the vertex `v`. (The Python statistic `edgecount` also counts the start token of every
active input as a predecessor; that term is the number of active inputs and is data dependent.) -/
@[expose] def edgesOf (c : Circ) (v : Nat) : Nat := (c.pred v).length

/-- The cost of the call `u` (zero unless it is activated): the costs `K` of all executed subgraph runs. -/
@[expose] def callCost (lib : Lib) (V : Circ → (Nat → Bool) → Nat → Nat → Bool) (K : Circ → (Nat → Bool) → Nat × Nat)
    (c : Circ) (acc : Nat → Bool) (u : Nat) : Nat × Nat :=
  match c.kind u with
  | .call sid ins _ reps =>
    if cnt acc (c.pred u) == 1 then
      (((callOf lib V acc sid ins reps).map fun p => (K (lib sid).c p.1).1).sum,
       ((callOf lib V acc sid ins reps).map fun p => (K (lib sid).c p.1).2).sum)
    else (0, 0)
  | _ => (0, 0)

/-- The cost of a run at one level: own vertices and edges plus the costs `K` of all executed subgraph runs. -/
@[expose] def costAt (lib : Lib) (V : Circ → (Nat → Bool) → Nat → Nat → Bool) (K : Circ → (Nat → Bool) → Nat × Nat)
    (c : Circ) (inp : Nat → Bool) : Nat × Nat :=
  let acc := valAt lib V c inp c.n
  (c.n + ((List.range c.n).map fun u => (callCost lib V K c acc u).1).sum,
   ((List.range c.n).map (edgesOf c)).sum + ((List.range c.n).map fun u => (callCost lib V K c acc u).2).sum)

/-- The evaluator by nesting depth. -/
@[expose] def level (lib : Lib) : Nat → Level
  | 0 => ⟨fun c inp f v => valAt lib (fun _ _ _ _ => false) c inp f v,
          fun c inp => costAt lib (fun _ _ _ _ => false) (fun _ _ => (0, 0)) c inp⟩
  | d + 1 => ⟨valAt lib (level lib d).val, costAt lib (level lib d).val (level lib d).cost⟩

/-- Value of the vertex `v` of `c` at nesting depth `d`. -/
@[expose] def Circ.val (lib : Lib) (d : Nat) (c : Circ) (inp : Nat → Bool) (v : Nat) : Bool :=
  (level lib d).val c inp c.n v

/-- The cost (vertices, examined edges) of a run at nesting depth `d`. -/
@[expose] def Circ.cost (lib : Lib) (d : Nat) (c : Circ) (inp : Nat → Bool) : Nat × Nat := (level lib d).cost c inp

end SmcIrred
