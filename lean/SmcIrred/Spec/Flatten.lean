module

public import SmcIrred.Spec.Graph

public section

namespace SmcIrred.Struct

/-! The state-machine program of a CFG: `state = entry; while (state != EXIT) switch (state) { case v: block_v; state = ...; }`
with one variable `state` taking the `|V| + 1` values `0 … |V|-1` and `EXIT = |V|`. The CFG executes block `lab v` at
each vertex `v` and moves to the successor selected by the condition outputs `ch` (the `k`-th selection picks the
`ch k`-th successor, modulo the number of successors; a vertex without successors ends the run). -/

/-- The successor chosen at the `k`-th selection from the vertex `v` (the exit state if there is none). -/
@[expose] def nextState (g : Digraph) (ch : Nat → Nat) (v k : Nat) : Nat :=
  match g.succ v with
  | [] => g.n
  | l => l.getD (ch k % l.length) g.n

/-- The CFG semantics: the blocks executed (labels `lab v`) along the run from `v` at selection index `k`. -/
inductive Walk (g : Digraph) (lab : Nat → List Nat) (ch : Nat → Nat) : Nat → Nat → List Nat → Prop
  | stop {v k : Nat} : g.succ v = [] → Walk g lab ch v k (lab v)
  | go {v k : Nat} {t : List Nat} : g.succ v ≠ [] →
      Walk g lab ch (nextState g ch v k) (k + 1) t → Walk g lab ch v k (lab v ++ t)

/-- The flat program: the loop runs while `state ≠ EXIT` and dispatches on `state` (`case v`: the block of `v`, then
the assignment to `state`). `FRun g lab ch state k t`: the loop halts with the trace `t`. -/
inductive FRun (g : Digraph) (lab : Nat → List Nat) (ch : Nat → Nat) : Nat → Nat → List Nat → Prop
  | exit {k : Nat} : FRun g lab ch g.n k []
  | step {s k : Nat} {t : List Nat} : s ≠ g.n →
      FRun g lab ch (nextState g ch s k) (k + 1) t → FRun g lab ch s k (lab s ++ t)

/-- Well-formed graph: all successors are vertices. -/
@[expose] def WFg (g : Digraph) : Prop := ∀ v, v < g.n → ∀ w, w ∈ g.succ v → w < g.n

end SmcIrred.Struct
