module

public import SmcIrred.Graph.Classify
public import SmcIrred.Graph.Decide
public import SmcIrred.Graph.RunDFS

public section

namespace SmcIrred

/-- Figure 4(a) (`native/IrredLoop.cpp`): vertices 0 = entry, 1 = u, 2 = v, 3 = w, 4 = x, 5 = exit (the paper's
labels 1..6), successors in the order of the code. -/
@[expose] def fig4 : Digraph where
  n := 6
  succ
    | 0 => [1, 2]
    | 1 => [3]
    | 2 => [4]
    | 3 => [1, 4, 5]
    | 4 => [2, 3, 5]
    | _ => []

/-- Figure 4(b): the published timestamps `[pre, post]` of the paper's vertices 1..6 (0..5 here). -/
@[expose] def fig4Jungle : Jungle where
  pre := fun v => [2, 3, 6, 4, 5, 8].getD v 0
  post := fun v => [13, 12, 7, 11, 10, 9].getD v 0

/-- The depth-first search of Figure 4(a) in the order of the code, with the clock starting at 2, gives exactly the
published timestamps. -/
theorem fig4_dfs_eq : ∀ v, v < 6 → (dfsRun fig4 0 2).pre v = fig4Jungle.pre v ∧ (dfsRun fig4 0 2).post v = fig4Jungle.post v := by
  decide

/-- The published timestamps form a valid depth-first jungle of the Figure 4 CFG rooted at the entry vertex. -/
theorem fig4Jungle_valid : fig4Jungle.Valid fig4 0 where
  interval := by decide
  pre_inj := by
    have key : ∀ a, a < 6 → ∀ b, b < 6 → fig4Jungle.pre a = fig4Jungle.pre b → a = b := by decide
    exact fun a b ha hb => key a ha b hb
  post_inj := by
    have key : ∀ a, a < 6 → ∀ b, b < 6 → fig4Jungle.post a = fig4Jungle.post b → a = b := by decide
    exact fun a b ha hb => key a ha b hb
  events := by
    have key : ∀ a, a < 6 → ∀ b, b < 6 → fig4Jungle.pre a ≠ fig4Jungle.post b := by decide
    exact fun a b ha hb => key a ha b hb
  laminar := by
    have key : ∀ a, a < 6 → ∀ b, b < 6 → fig4Jungle.Anc a b ∨ fig4Jungle.Anc b a ∨
        fig4Jungle.post a < fig4Jungle.pre b ∨ fig4Jungle.post b < fig4Jungle.pre a := by decide
    exact fun a b ha hb => key a ha b hb
  root := by decide
  parent := by
    have key : ∀ v, v < 6 → v ≠ 0 → ∃ u, u < 6 ∧ (fig4Jungle.IsParent fig4 u v ∧ fig4.edge u v) := by decide
    intro v hv hne
    obtain ⟨u, -, hu⟩ := key v hv hne
    exact ⟨u, hu⟩
  no_rightward := by
    have key : ∀ a, a < 6 → ∀ b, b < 6 → fig4.edge a b → ¬ fig4Jungle.post a < fig4Jungle.pre b := by decide
    exact fun a b he => key a he.1 b he.2.1 he

/-- Edge classes of Figure 4(b): tree 1→2, 2→4, 4→5, 5→3, 5→6; forward 1→3, 4→6; back 3→5, 4→2, 5→4 (paper labels). -/
theorem fig4_classes :
    fig4Jungle.cls fig4 0 1 = .tree ∧ fig4Jungle.cls fig4 1 3 = .tree ∧ fig4Jungle.cls fig4 3 4 = .tree ∧
    fig4Jungle.cls fig4 4 2 = .tree ∧ fig4Jungle.cls fig4 4 5 = .tree ∧
    fig4Jungle.cls fig4 0 2 = .forward ∧ fig4Jungle.cls fig4 3 5 = .forward ∧
    fig4Jungle.cls fig4 2 4 = .back ∧ fig4Jungle.cls fig4 3 1 = .back ∧ fig4Jungle.cls fig4 4 3 = .back := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [Jungle.cls, fig4Jungle] <;> decide

/-- Figure 4(a) is a CFG rooted at the entry vertex. -/
theorem fig4_isCFG : fig4.IsCFG 0 := by
  refine ⟨by decide, ?_⟩
  intro v hv
  change v < 6 at hv
  obtain (rfl | rfl | rfl | rfl | rfl | rfl) : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 ∨ v = 5 := by omega
  · exact .refl 0
  · exact .step (by decide) (.refl 1)
  · exact .step (by decide) (.refl 2)
  · exact .step (by decide : fig4.edge 0 1) (.step (by decide : fig4.edge 1 3) (.refl 3))
  · exact .step (by decide : fig4.edge 0 2) (.step (by decide : fig4.edge 2 4) (.refl 4))
  · exact .step (by decide : fig4.edge 0 1) (.step (by decide : fig4.edge 1 3)
      (.step (by decide : fig4.edge 3 5) (.refl 5)))

/-- P03 evidence: the exit vertex of Figure 4 has no out-edge, so the published "otherwise: more than two out-edges"
leaves it unclassified, whereas `Digraph.kind` gives `exit`; the other vertices have 2, 1, 1, 3, 3 out-edges. -/
theorem fig4_kinds :
    fig4.kind 5 = .exit ∧ fig4.kind 0 = .cond ∧ fig4.kind 1 = .seq ∧ fig4.kind 2 = .seq ∧
    fig4.kind 3 = .nway ∧ fig4.kind 4 = .nway := by
  decide

end SmcIrred
