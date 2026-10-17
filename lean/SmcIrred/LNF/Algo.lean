module

public import SmcIrred.LNF.NonUnique

public section

namespace SmcIrred

/-- State of Havlak's algorithm: union-find parent pointers, the loop header of each vertex, the irreducible flag of
each loop and the recorded second entries of each loop. -/
structure HavlakState where
  uf : Nat → Nat
  hdr : Nat → Option Nat
  irr : Nat → Bool
  extra : Nat → List Nat

/-- Union-find `find` (fuel-bounded path following). -/
@[expose] def ufFind (uf : Nat → Nat) : Nat → Nat → Nat
  | 0, v => v
  | f + 1, v => if uf v = v then v else ufFind uf f (uf v)

@[expose] def preds (g : Digraph) (v : Nat) : List Nat := (List.range g.n).filter fun u => v ∈ g.succ u

@[expose] def dedup (l : List Nat) : List Nat := l.foldl (fun acc a => if acc.contains a then acc else acc ++ [a]) []

/-- Scan predecessors `ys` of a vertex of the loop of `w`: those inside the subtree of `w` join the loop, the others are
second entries (the loop is irreducible). State: worklist, loop members, recorded entries, irreducible flag. -/
@[expose] def havlakScan (J : Jungle) (w : Nat) (fd : Nat → Nat) (ys : List Nat)
    (st : List Nat × List Nat × List Nat × Bool) : List Nat × List Nat × List Nat × Bool :=
  ys.foldl (fun (st : List Nat × List Nat × List Nat × Bool) y =>
    let y' := fd y
    if J.Anc w y' then
      if y' ≠ w ∧ !st.2.1.contains y' then (st.1 ++ [y'], st.2.1 ++ [y'], st.2.2.1, st.2.2.2)
      else st
    else (st.1, st.2.1, st.2.2.1 ++ [y'], true)) st

@[expose] def havlakDrain (g : Digraph) (J : Jungle) (w : Nat) (hs : HavlakState) (fd : Nat → Nat) :
    Nat → List Nat × List Nat × List Nat × Bool → List Nat × List Nat × Bool
  | 0, st => (st.2.1, st.2.2.1, st.2.2.2)
  | f + 1, st =>
    match st.1 with
    | [] => (st.2.1, st.2.2.1, st.2.2.2)
    | x :: wl =>
      havlakDrain g J w hs fd f
        (havlakScan J w fd (((preds g x).filter fun y => !decide (J.Anc x y)) ++ hs.extra x) (wl, st.2))

/-- Process the vertex `w` (Havlak's loop `w`). -/
@[expose] def havlakStep (g : Digraph) (J : Jungle) (hs : HavlakState) (w : Nat) : HavlakState :=
  let fd := ufFind hs.uf g.n
  let P0 := dedup (((preds g w).filter fun v => decide (J.Anc w v ∧ v ≠ w)).map fd)
  let res := havlakDrain g J w hs fd (g.n + 1) (P0, P0, [], false)
  { uf := fun x => if res.1.contains x then w else hs.uf x
    hdr := fun x => if res.1.contains x then some w else hs.hdr x
    irr := fun x => if x = w then res.2.2 || hs.irr x else hs.irr x
    extra := fun x => if x = w then hs.extra w ++ res.2.1 else hs.extra x }

@[expose] def insDesc (key : Nat → Nat) (a : Nat) : List Nat → List Nat
  | [] => [a]
  | b :: l => if key b ≤ key a then a :: b :: l else b :: insDesc key a l

/-- The vertices by decreasing preorder number. -/
@[expose] def byPreDesc (J : Jungle) (n : Nat) : List Nat := (List.range n).foldr (insDesc J.pre) []

/-- Havlak's algorithm for the jungle `J`: process the vertices in reverse preorder. -/
@[expose] def havlak (g : Digraph) (J : Jungle) : HavlakState :=
  (byPreDesc J g.n).foldl (havlakStep g J) ⟨fun v => v, fun _ => none, fun _ => false, fun _ => []⟩

/-- Fidelity evidence (mechanical, two depth-first orders of Figure 4): the headers computed by Havlak's algorithm are
the parents of the declarative loop nesting forest and its irreducible flags are the declarative irreducible loops. -/
theorem havlak_fig4 :
    (∀ x, x < 6 → ∀ h, h < 6 → ((havlak fig4 fig4Jungle).hdr x = some h ↔ fig4.LnfParent fig4Jungle h x)) ∧
    (∀ x, x < 6 → ((havlak fig4 fig4Jungle).hdr x = none ↔ ∀ h, h < 6 → ¬ fig4.LnfParent fig4Jungle h x)) ∧
    (∀ w, w < 6 → ((havlak fig4 fig4Jungle).irr w = true ↔ fig4.Irreducible fig4Jungle w)) := by
  refine ⟨?_, ?_, ?_⟩ <;> set_option synthInstance.maxSize 2048 in decide

theorem havlak_fig4Swap :
    (∀ x, x < 6 → ∀ h, h < 6 → ((havlak fig4 fig4SwapJungle).hdr x = some h ↔ fig4.LnfParent fig4SwapJungle h x)) ∧
    (∀ x, x < 6 → ((havlak fig4 fig4SwapJungle).hdr x = none ↔ ∀ h, h < 6 → ¬ fig4.LnfParent fig4SwapJungle h x)) ∧
    (∀ w, w < 6 → ((havlak fig4 fig4SwapJungle).irr w = true ↔ fig4.Irreducible fig4SwapJungle w)) := by
  refine ⟨?_, ?_, ?_⟩ <;> set_option synthInstance.maxSize 2048 in decide

end SmcIrred
