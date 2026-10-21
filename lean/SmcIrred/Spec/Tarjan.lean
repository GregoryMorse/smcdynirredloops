module

public import SmcIrred.Spec.Graph

public section

namespace SmcIrred

/-- The state of Tarjan's algorithm: the index counter, the discovery index (`0` = not yet visited) and the lowlink of
every vertex, the component stack (head = top), the emitted components in emission order, and a step counter
(vertex entries, examined edges, popped vertices). -/
structure TState where
  cnt : Nat
  num : Nat → Nat
  low : Nat → Nat
  stk : List Nat
  out : List (List Nat)
  ticks : Nat

@[expose] def TState.init : TState := ⟨0, fun _ => 0, fun _ => 0, [], [], 0⟩

@[expose] def tupd (f : Nat → Nat) (k x : Nat) : Nat → Nat := fun j => if j = k then x else f j

/-- The in-range successors of `v` (the vertices of the graph; the 2-SAT implication graph has no others). -/
@[expose] def tsuccs (g : Digraph) (v : Nat) : List Nat := (g.succ v).filter fun w => decide (w < g.n)

/-- Pop the stack down to and including `v`: the popped component and the remaining stack. -/
@[expose] def popTo (v : Nat) : List Nat → List Nat × List Nat
  | [] => ([], [])
  | x :: xs => if x = v then ([x], xs) else ((x :: (popTo v xs).1), (popTo v xs).2)

/-- One iteration of the successor loop of `v` for the successor `w`: an unvisited `w` is visited recursively (the
call updates the lowlink of `v` on return); a visited `w` still on the stack lowers the lowlink of `v` to its index. -/
@[expose] def tEdge (vis : Nat → Nat → TState → TState) (v w : Nat) (s : TState) : TState :=
  let s0 : TState := { s with ticks := s.ticks + 1 }
  if s.num w = 0 then vis w v s0
  else if w ∈ s.stk then { s0 with low := tupd s0.low v (min (s0.low v) (s0.num w)) }
  else s0

@[expose] def tScan (vis : Nat → Nat → TState → TState) (v : Nat) : List Nat → TState → TState
  | [], s => s
  | w :: ws, s => tScan vis v ws (tEdge vis v w s)

/-- The end of `strongconnect` for `v` after its successor loop: emit the component if `v` is a root, then return the
lowlink to the parent `par`. -/
@[expose] def tFinish (v : Nat) (par : Option Nat) (s2 : TState) : TState :=
  let s3 : TState :=
    if s2.low v = s2.num v then
      { s2 with stk := (popTo v s2.stk).2, out := s2.out ++ [(popTo v s2.stk).1],
                ticks := s2.ticks + (popTo v s2.stk).1.length }
    else s2
  match par with
  | none => s3
  | some p => { s3 with low := tupd s3.low p (min (s3.low p) (s3.low v)) }

/-- `strongconnect` with a fuel bound: enter `v`, loop over its successors, then finish. -/
@[expose] def tVisit (g : Digraph) : Nat → Nat → Option Nat → TState → TState
  | 0, _, _, s => s
  | f + 1, v, par, s =>
    let c := s.cnt + 1
    let s1 : TState := { s with cnt := c, num := tupd s.num v c, low := tupd s.low v c, stk := v :: s.stk,
                                ticks := s.ticks + 1 }
    tFinish v par (tScan (fun w p t => tVisit g f w (some p) t) v (tsuccs g v) s1)

/-- The outer loop over the vertices, **skipping visited ones** (the corrected loop, L01). -/
@[expose] def tRun (g : Digraph) : List Nat → TState → TState
  | [], s => s
  | v :: vs, s => tRun g vs (if s.num v = 0 then tVisit g g.n v none s else s)

/-- Tarjan's strongly connected component algorithm on the vertices `0 … n-1`. -/
@[expose] def tarjan (g : Digraph) : TState := tRun g (List.range g.n) TState.init

/-- The components in emission order. -/
@[expose] def tarjanSccs (g : Digraph) : List (List Nat) := (tarjan g).out

/-- The number of in-range edges of the vertices `0 … k-1`. -/
@[expose] def tEdges (g : Digraph) : Nat → Nat
  | 0 => 0
  | k + 1 => tEdges g k + (tsuccs g k).length

end SmcIrred
