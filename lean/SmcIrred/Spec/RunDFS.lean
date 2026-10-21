module

public import SmcIrred.Spec.DFS

public section

namespace SmcIrred

/-- State of a depth-first search: the clock and the preorder/postorder times assigned so far (0 = not yet assigned;
the clock starts at 1 or more). -/
structure DfsState where
  clock : Nat
  pre : Nat → Nat
  post : Nat → Nat

/-- Discover `v`: stamp its preorder time. -/
@[expose] def DfsState.opening (s : DfsState) (v : Nat) : DfsState :=
  { s with clock := s.clock + 1, pre := fun x => if x = v then s.clock else s.pre x }

/-- Finish `v`: stamp its postorder time. -/
@[expose] def DfsState.closing (s : DfsState) (v : Nat) : DfsState :=
  { s with clock := s.clock + 1, post := fun x => if x = v then s.clock else s.post x }

/-- Visit `v` (fuel-bounded recursion): stamp the preorder time, visit every not yet discovered successor in list
order, stamp the postorder time. -/
@[expose] def dfsVisit (g : Digraph) : Nat → Nat → DfsState → DfsState
  | 0, _, s => s
  | fuel + 1, v, s =>
    ((g.succ v).foldl (fun s w => if w < g.n ∧ s.pre w = 0 then dfsVisit g fuel w s else s) (s.opening v)).closing v

/-- The timestamps of the depth-first search from `r` whose clock starts at `c ≥ 1` (undiscovered vertices get 0). -/
@[expose] def dfsRun (g : Digraph) (r c : Nat) : Jungle :=
  let s := dfsVisit g (g.n + 1) r ⟨c, fun _ => 0, fun _ => 0⟩
  ⟨s.pre, s.post⟩

end SmcIrred
