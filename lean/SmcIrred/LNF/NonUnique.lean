module

public import SmcIrred.LNF.Fig4
public import SmcIrred.Graph.DfsValid

public section

namespace SmcIrred

/-- Figure 4(a) with the entry's successors listed in the other order (v before u): the same edges, another DFS. -/
@[expose] def fig4Swap : Digraph where
  n := 6
  succ
    | 0 => [2, 1]
    | 1 => [3]
    | 2 => [4]
    | 3 => [1, 4, 5]
    | 4 => [2, 3, 5]
    | _ => []

theorem fig4Swap_edge : ∀ a, a < 6 → ∀ b, b < 6 → (fig4.edge a b ↔ fig4Swap.edge a b) := by decide

theorem Jungle.Valid.of_edges {g g' : Digraph} {r : Nat} {J : Jungle} (hn : g.n = g'.n)
    (he : ∀ a b, g.edge a b ↔ g'.edge a b) (h : J.Valid g r) : J.Valid g' r where
  interval := fun v hv => h.interval v (hn ▸ hv)
  pre_inj := fun a b ha hb => h.pre_inj a b (hn ▸ ha) (hn ▸ hb)
  post_inj := fun a b ha hb => h.post_inj a b (hn ▸ ha) (hn ▸ hb)
  events := fun a b ha hb => h.events a b (hn ▸ ha) (hn ▸ hb)
  laminar := fun a b ha hb => h.laminar a b (hn ▸ ha) (hn ▸ hb)
  root := fun v hv => h.root v (hn ▸ hv)
  parent := fun v hv hne => by
    obtain ⟨u, hp, hedge⟩ := h.parent v (hn ▸ hv) hne
    exact ⟨u, ⟨hn ▸ hp.1, hp.2.1, hp.2.2.1, fun w hw => hp.2.2.2 w (hn ▸ hw)⟩, (he u v).1 hedge⟩
  no_rightward := fun a b hab => h.no_rightward a b ((he a b).2 hab)

theorem fig4Swap_isCFG : fig4Swap.IsCFG 0 := by
  refine ⟨by decide, ?_⟩
  intro v hv
  change v < 6 at hv
  obtain (rfl | rfl | rfl | rfl | rfl | rfl) : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 ∨ v = 5 := by omega
  · exact .refl 0
  · exact .step (by decide) (.refl 1)
  · exact .step (by decide) (.refl 2)
  · exact .step (by decide : fig4Swap.edge 0 1) (.step (by decide : fig4Swap.edge 1 3) (.refl 3))
  · exact .step (by decide : fig4Swap.edge 0 2) (.step (by decide : fig4Swap.edge 2 4) (.refl 4))
  · exact .step (by decide : fig4Swap.edge 0 1) (.step (by decide : fig4Swap.edge 1 3)
      (.step (by decide : fig4Swap.edge 3 5) (.refl 5)))

/-- The jungle of the depth-first search of Figure 4 that visits v before u. -/
@[expose] def fig4SwapJungle : Jungle := dfsRun fig4Swap 0 2

theorem fig4SwapJungle_valid : fig4SwapJungle.Valid fig4 0 :=
  Jungle.Valid.of_edges (by decide) (fun a b => by
      by_cases h : a < 6 ∧ b < 6
      · exact (fig4Swap_edge a h.1 b h.2).symm
      · constructor <;> intro e <;> exact absurd (⟨e.1, e.2.1⟩ : a < 6 ∧ b < 6) h)
    (dfsRun_valid fig4Swap_isCFG (by omega))

/-- C28: the loop nesting forest depends on the depth-first search. Visiting u first (the published Figure 4(b)) gives
the headers u, w, x; visiting v first gives v, w, x. Both are valid jungles of the same graph. -/
theorem lnf_not_unique : ∃ J₁ J₂ : Jungle, J₁.Valid fig4 0 ∧ J₂.Valid fig4 0 ∧
    fig4.IsHeader J₁ 1 ∧ ¬ fig4.IsHeader J₂ 1 ∧ fig4.IsHeader J₂ 2 ∧ ¬ fig4.IsHeader J₁ 2 :=
  ⟨fig4Jungle, fig4SwapJungle, fig4Jungle_valid, fig4SwapJungle_valid, by decide, by decide, by decide, by decide⟩

/-- The set of irreducible loops differs too (the headers of the irreducible loops are the headers of the loops here). -/
theorem irreducible_not_unique : ∃ J₁ J₂ : Jungle, J₁.Valid fig4 0 ∧ J₂.Valid fig4 0 ∧
    fig4.Irreducible J₁ 1 ∧ ¬ fig4.Irreducible J₂ 1 :=
  ⟨fig4Jungle, fig4SwapJungle, fig4Jungle_valid, fig4SwapJungle_valid, by decide, by decide⟩

end SmcIrred
