module

public import SmcIrred.Spec.Tarjan

public section

namespace SmcIrred

/-- The state of the C++ function `tarjan_scc` (`native/selfmodgraph.cpp`): the index counter, the `index` and `lowlink`
fields of the `nodes` map (`0` = key absent; the Lean model counts from `1`), the `onstack` flag of each node, the
stack `s` (head = top) and the vector `sccs`. The stack and the flags are separate, as in the code. -/
structure CState where
  cnt : Nat
  num : Nat → Nat
  low : Nat → Nat
  on : Nat → Bool
  stk : List Nat
  out : List (List Nat)

@[expose] def CState.init : CState := ⟨0, fun _ => 0, fun _ => 0, fun _ => false, [], []⟩

@[expose] def tupdB (f : Nat → Bool) (k : Nat) (x : Bool) : Nat → Bool := fun j => if j = k then x else f j

/-- `nodes.insert({index, index++, true}); s.push(v)`: the map insertion does **not** overwrite an existing entry, but
`index++` and the push happen every time. -/
@[expose] def cEnter (v : Nat) (s : CState) : CState :=
  if s.num v = 0 then
    { s with cnt := s.cnt + 1, num := tupd s.num v (s.cnt + 1), low := tupd s.low v (s.cnt + 1),
             on := tupdB s.on v true, stk := v :: s.stk }
  else { s with cnt := s.cnt + 1, stk := v :: s.stk }

/-- The lambda of the successor loop: an unknown `w` is visited recursively and then the lowlink of `v` is lowered to
that of `w`; a known `w` on the stack lowers the lowlink of `v` to the index of `w`. -/
@[expose] def cEdge (vis : Nat → Nat → CState → CState) (v w : Nat) (s : CState) : CState :=
  if s.num w = 0 then vis w v s
  else if s.on w = true then { s with low := tupd s.low v (min (s.low v) (s.num w)) }
  else s

@[expose] def cScan (vis : Nat → Nat → CState → CState) (v : Nat) : List Nat → CState → CState
  | [], s => s
  | w :: ws, s => cScan vis v ws (cEdge vis v w s)

/-- `if (lowlink == index) { do { w = s.top(); s.pop(); onstack = false; vec.push_back(w); } while (w != v);
sccs.push_back(vec); }`, followed by the parent's lowlink update performed after the call returns. -/
@[expose] def cFinish (v : Nat) (par : Option Nat) (s2 : CState) : CState :=
  let s3 : CState :=
    if s2.low v = s2.num v then
      { s2 with stk := (popTo v s2.stk).2, on := fun w => if w ∈ (popTo v s2.stk).1 then false else s2.on w,
                out := s2.out ++ [(popTo v s2.stk).1] }
    else s2
  match par with
  | none => s3
  | some p => { s3 with low := tupd s3.low p (min (s3.low p) (s3.low v)) }

@[expose] def cVisit (g : Digraph) : Nat → Nat → Option Nat → CState → CState
  | 0, _, _, s => s
  | f + 1, v, par, s =>
    cFinish v par (cScan (fun w p t => cVisit g f w (some p) t) v (tsuccs g v) (cEnter v s))

/-- The outer loop of the **legacy** code: `strongconnect(p.first)` for every key, visited or not. -/
@[expose] def cRun (g : Digraph) : List Nat → CState → CState
  | [], s => s
  | v :: vs, s => cRun g vs (cVisit g g.n v none s)

@[expose] def ctarjan (g : Digraph) : CState := cRun g (List.range g.n) CState.init

/-- The vector `sccs` of the legacy code. -/
@[expose] def ctarjanSccs (g : Digraph) : List (List Nat) := (ctarjan g).out

/-- `out` is `comps` with extra singleton components `[r]` inserted, each after a component containing `r`. -/
inductive DupOf : List (List Nat) → List (List Nat) → Prop
  | nil : DupOf [] []
  | keep {l l' : List (List Nat)} (C : List Nat) : DupOf l l' → DupOf (l ++ [C]) (l' ++ [C])
  | dup {l l' : List (List Nat)} (r : Nat) (C : List Nat) : DupOf l l' → C ∈ l → r ∈ C → DupOf l (l' ++ [[r]])

/-- The negation of a literal node (`2x ↔ 2x+1`, the integer `-v` of the code). -/
@[expose] def nneg (v : Nat) : Nat := if v % 2 = 0 then v + 1 else v - 1

/-- One component of `twosat`: a fresh set `u`; for each `v`, `unsat` if `-v ∈ u`, else insert `v` into `u` and into
`sol` unless `-v ∈ sol`. The state is `(unsat, sol)`, `sol` a list read as a set. -/
@[expose] def tsComp : List Nat → List Nat → Bool × List Nat → Bool × List Nat
  | [], _, st => st
  | v :: vs, u, st =>
    if st.1 then st
    else if nneg v ∈ u then (true, st.2)
    else tsComp vs (v :: u) (st.1, if nneg v ∈ st.2 then st.2 else v :: st.2)

/-- The loop of `twosat` over the components, in order. -/
@[expose] def tsFold (comps : List (List Nat)) : Bool × List Nat :=
  comps.foldl (fun st C => tsComp C [] st) (false, [])

end SmcIrred
