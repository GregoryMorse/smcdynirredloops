module

public import SmcIrred.Spec.TarjanCode
public import SmcIrred.Spec.TwoSat

public section

namespace SmcIrred

/-!
# Level 2 of the SMC 2-SAT solver (plan D3): an abstract self-modifying machine

This is the pseudo-language of `selfmodvmtwosathl` (`native/selfmodgraph.cpp`) and the node blueprint of
`selfmodmodel.asm`, read as a program over a machine with code cells that are rewritten while it runs.

**Modelling choices** (processors, compilers and timers stay black boxes, plan D2):
* Each implication-graph node `x` owns one code cell. Its fields are the immediates and instructions the blueprint
  patches: `ent x` (`none`: the original code is still there; `some k`: the first instruction was replaced by
  `return k`, where `k` is the node's index while the node is on the SCC stack and `n` once its component was popped),
  `low x` (lowlink immediate), `chk x` (the instruction at `checksccloc`: `true` once a `jmp` over the component
  extraction was patched in), `pk x` (the `pop` of the return address at `peekretloc` was patched into a `peek`),
  `dep x` (the stack depth recorded in `onstackloc`/`topopstackloc`), `set x` (`nodeaddrsetloc`: the component) .
* The machine has a stack of cells. A call pushes a cell naming the caller (`some x`: the return address inside the
  code of `x`, which is also how the node is recognised when it is popped) or `none` for the outer loop; a node
  entry pops that cell, or only peeks it when `pk` was patched; a visited node's stub returns and pops it.
* The successor loop of the blueprint counts `counterloc` down from `succ[x].size()` and calls `succ[x][counter-1]`:
  successors are visited **from last to first**. The counter immediate is a loop variable of a single execution and is
  modelled by the list recursion.
* The topological chain (`starttopo`/`nexttopoloc`) is the list `chain` in the order the components were popped; the
  solution phase walks it (`sSolFold`).
* The index and the finished marker are numbers; `n` (the number of nodes, `succ.size()`) is larger than every index.
* Calls to C++ callbacks (`getsuccnodeaddr`, `addsolution`, `sat`, `unsat`) are modelled by their contracts: the
  successor list, inserting the literal into the solution set, finishing, clearing the set.
-/

/-- The machine state. -/
structure SState where
  idx : Nat
  ent : Nat → Option Nat
  low : Nat → Nat
  pk : Nat → Bool
  dep : Nat → Nat
  chk : Nat → Bool
  set : Nat → Nat
  stk : List (Option Nat)
  chain : List Nat

/-- The freshly stamped image of a graph with `n` nodes. -/
@[expose] def SState.init (n : Nat) : SState :=
  ⟨0, fun _ => none, fun _ => 0, fun _ => false, fun _ => 0, fun _ => false, fun _ => n, [], []⟩

@[expose] def fupd {α : Type} (f : Nat → α) (k : Nat) (x : α) : Nat → α := fun j => if j = k then x else f j

/-- The graph with every successor list reversed (the order in which the blueprint visits them). -/
@[expose] def revG (g : Digraph) : Digraph := ⟨g.n, fun v => (g.succ v).reverse⟩

/-- The component extraction at a root `w`: pop cells until `w` is popped; each popped node `u` is appended to the
chain, assigned to the component `w` and marked finished (`return n`). -/
@[expose] def sExtract (n w : Nat) : Nat → SState → SState
  | 0, s => s
  | k + 1, s =>
    match s.stk with
    | [] => s
    | none :: rest => { s with stk := rest }
    | some u :: rest =>
      let s' : SState := { s with stk := rest, chain := s.chain ++ [u], set := fupd s.set u w, ent := fupd s.ent u (some n) }
      if u = w then s' else sExtract n w k s'

/-- After a call returned the value `r`: lower the lowlink of the caller `x` (and patch its check). -/
@[expose] def sStep (x : Nat) (rs : Nat × SState) : SState :=
  if rs.1 < rs.2.low x then { rs.2 with low := fupd rs.2.low x rs.1, chk := fupd rs.2.chk x true } else rs.2

/-- The successor loop of node `x` (successors in the given order). -/
@[expose] def sLoop (call : Nat → Nat → SState → Nat × SState) (x : Nat) : List Nat → SState → SState
  | [], s => s
  | w :: ws, s => sLoop call x ws (sStep x (call x w s))

/-- The start of the code of an unvisited node `w`, entered with the return cell on top of the stack: record the
index, pop or peek the return cell, record the depth, become a `return` stub. -/
@[expose] def sEnter (w : Nat) (s1 : SState) : SState :=
  let k := s1.idx
  let s2 : SState := { s1 with idx := k + 1, ent := fupd s1.ent w (some k), low := fupd s1.low w k,
                               chk := fupd s1.chk w false, stk := if s1.pk w then s1.stk else s1.stk.tail }
  { s2 with dep := fupd s2.dep w s2.stk.length }

/-- The end of the code of `w`: push the own return cell when nothing was pushed since the entry, extract the component
when no lowlink was lowered. -/
@[expose] def sLeave (n w : Nat) (s4 : SState) : SState :=
  let s5 : SState := if s4.stk.length = s4.dep w then { s4 with stk := some w :: s4.stk } else s4
  if s5.chk w then s5 else sExtract n w s5.stk.length s5

/-- The code of an unvisited node `w`: start, loop over the successors, end, return the lowlink. -/
@[expose] def sBody (g : Digraph) (call : Nat → Nat → SState → Nat × SState) (w : Nat) (s1 : SState) : Nat × SState :=
  let s6 := sLeave g.n w (sLoop call w (tsuccs (revG g) w) (sEnter w s1))
  (s6.low w, s6)

/-- The start of the call of `w` from `x`: patch `w` to peek when nothing was pushed since the entry of `x`, then push
the return cell (the return address inside the code of `x`). -/
@[expose] def sPre (x w : Nat) (s : SState) : SState :=
  let s0 : SState := if s.stk.length = s.dep x then { s with pk := fupd s.pk w true } else s
  { s0 with stk := some x :: s0.stk }

/-- The call of `w` from `x`: a visited `w` returns its marker and pops the cell (no fuel needed), an unvisited one runs
its code (`fuel` bounds the call depth; it is never exhausted on a graph with enough fuel). -/
@[expose] def sCall (g : Digraph) : Nat → Nat → Nat → SState → Nat × SState
  | f, x, w, s =>
    match (sPre x w s).ent w, f with
    | some k, _ => (k, { sPre x w s with stk := (sPre x w s).stk.tail })
    | none, 0 => (0, sPre x w s)
    | none, f + 1 => sBody g (sCall g f) w (sPre x w s)

/-- The outer loop: call every node that is still unvisited (`callblueprint`). The call pushes a `none` cell. -/
@[expose] def sRun (g : Digraph) (fuel : Nat) : List Nat → SState → SState
  | [], s => s
  | v :: vs, s =>
    sRun g fuel vs (match s.ent v with
      | some _ => s
      | none => (sBody g (sCall g fuel) v { s with stk := none :: s.stk }).2)

/-- The solution phase: walk the topological chain; a node in the same component as its negation ends the run with
`unsat` (the set is cleared); otherwise the node is added to the solution unless its negation is in it. -/
@[expose] def sSolFold (set : Nat → Nat) : List Nat → List Nat → Option (List Nat)
  | [], sol => some sol
  | x :: xs, sol =>
    if set x = set (nneg x) then none else sSolFold set xs (if nneg x ∈ sol then sol else x :: sol)

/-- The whole SMC solver on the implication graph of `f`: `none` is unsatisfiable, `some sol` lists the true literal
nodes (`2x` for the variable `x`). -/
@[expose] def smcSolve (f : TwoSat) : Option (List Nat) :=
  let g := f.graph
  let s := sRun g (g.n - 1) (List.range g.n) (SState.init g.n)
  sSolFold s.set s.chain []

/-- Restamping (Fig. 2b "Reuse"): the declared patch cells and registers are reset to the stamped image; the stack is
not touched (a finished run leaves it empty). -/
@[expose] def restamp (n : Nat) (s : SState) : SState :=
  { s with idx := 0, ent := fun _ => none, low := fun _ => 0, pk := fun _ => false, dep := fun _ => 0,
           chk := fun _ => false, set := fun _ => n, chain := [] }

/-- One query of the stamped image: run, read the answer off the chain, restamp. -/
@[expose] def smcRound (f : TwoSat) (s : SState) : Option (List Nat) × SState :=
  let g := f.graph
  let s' := sRun g (g.n - 1) (List.range g.n) s
  (sSolFold s'.set s'.chain [], restamp g.n s')

/-- The answers of `k` successive queries of the same image, restamping between runs. -/
@[expose] def smcRounds (f : TwoSat) : Nat → SState → List (Option (List Nat))
  | 0, _ => []
  | k + 1, s => (smcRound f s).1 :: smcRounds f k (smcRound f s).2

end SmcIrred
