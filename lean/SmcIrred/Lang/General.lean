module

public import SmcIrred.Lang.NWay
public import SmcIrred.LNF.Reducible

public section

namespace SmcIrred.Lang

/-! # General n for C73 and C76 (G32 b)

`path_one_edge_reducible` and `nway_one_edge` were checked for at most 6 vertices or branches. Here they are proved for every
size: in a reducible flow graph no loop is irreducible (for every valid depth-first jungle); a path with one added edge is
reducible; an `n`-way conditional is reducible, and with the join-to-first-branch edge every valid jungle has an irreducible
loop. -/

variable {g : Digraph} {r : Nat} {J : Jungle}

/-- In a reducible flow graph no loop is irreducible, whatever the depth-first search. -/
theorem reducible_no_irreducible (hv : J.Valid g r) (hred : g.Reducible r) (w : Nat) : ¬ g.Irreducible J w := by
  rintro ⟨_, x, y, hbody, hxw, hyx, hna⟩
  obtain ⟨_, hx⟩ := (body_dom hv hred w x).1 hbody
  rcases hx with e | ⟨t, _, _, hdt, hp⟩
  · exact hxw e
  · have hdx : g.Dom r w x := ⟨reach hv hyx.2.1, fun hq => hdt.2 (hq.trans hp)⟩
    have hdy : g.Dom r w y := ⟨reach hv hyx.1, fun hq => hdx.2 (hq.snoc hxw hyx)⟩
    exact hna (dom_anc hv hdy)

/-- A path of non-dominating edges increases a numbering that every non-dominating edge increases. -/
theorem nondom_lt (hk : ∀ a b, g.edge a b → ¬ g.Dom r b a → a < b) : ∀ a b, g.NonDomPath r a b → a < b := by
  intro a b h
  induction h with
  | single he _ hnd => exact hk _ _ he hnd
  | step he _ hnd _ ih => exact Nat.lt_trans (hk _ _ he hnd) ih

theorem reducible_of_lt (hk : ∀ a b, g.edge a b → ¬ g.Dom r b a → a < b) : g.Reducible r := by
  intro v h
  exact Nat.lt_irrefl _ (nondom_lt hk v v h)

/-! ### A path with one added edge -/

theorem edge_pathAdd {n x y a b : Nat} :
    (addEdge (pathG n) x y).edge a b ↔ a < n ∧ b < n ∧ ((a + 1 < n ∧ b = a + 1) ∨ (a = x ∧ b = y)) := by
  unfold Digraph.edge addEdge pathG
  simp only
  constructor
  · rintro ⟨ha, hb, hm⟩
    refine ⟨ha, hb, ?_⟩
    by_cases hax : a = x
    · simp only [hax, ↓reduceIte, List.mem_append, List.mem_singleton] at hm
      subst hax
      by_cases h1 : a + 1 < n
      · simp only [h1, ↓reduceIte, List.mem_singleton] at hm
        rcases hm with h | h
        · exact Or.inl ⟨h1, h⟩
        · exact Or.inr ⟨rfl, h⟩
      · simp only [h1, ↓reduceIte, List.not_mem_nil, false_or] at hm
        exact Or.inr ⟨rfl, hm⟩
    · simp only [hax, ↓reduceIte] at hm
      by_cases h1 : a + 1 < n
      · simp only [h1, ↓reduceIte, List.mem_singleton] at hm
        exact Or.inl ⟨h1, hm⟩
      · simp [h1] at hm
  · rintro ⟨ha, hb, h | ⟨rfl, rfl⟩⟩
    · refine ⟨ha, hb, ?_⟩
      obtain ⟨h1, rfl⟩ := h
      by_cases hax : a = x
      · subst hax; simp [h1]
      · simp [hax, h1]
    · refine ⟨ha, hb, ?_⟩
      simp

/-- A vertex below the added edge's target cannot be left except upward. -/
theorem pathAdd_stay {n x y : Nat} (hyx : y ≤ x) :
    ∀ a c, PathIn (addEdge (pathG n) x y) (fun z => z ≠ y) a c → a < y → c < y := by
  intro a c hp
  induction hp with
  | refl _ _ => intro h; exact h
  | @step a b c hs he hp ih =>
    intro ha
    have hb := hp.source.2
    obtain ⟨_, _, h⟩ := edge_pathAdd.1 he
    rcases h with ⟨_, rfl⟩ | ⟨rfl, rfl⟩
    · exact ih (by omega)
    · omega

theorem reach_trans {a b c : Nat} (h1 : g.Reach a b) (h2 : g.Reach b c) : g.Reach a c := by
  induction h1 with
  | refl _ => exact h2
  | step he _ ih => exact .step he (ih h2)

theorem pathAdd_reach {n x y : Nat} : ∀ v, v < n → (addEdge (pathG n) x y).Reach 0 v := by
  intro v
  induction v with
  | zero => intro _; exact .refl 0
  | succ v ih =>
    intro hv
    have he : (addEdge (pathG n) x y).edge v (v + 1) := edge_pathAdd.2 ⟨by omega, hv, Or.inl ⟨hv, rfl⟩⟩
    exact reach_trans (ih (by omega)) (.step he (.refl _))

theorem pathAdd_pathIn {n x y : Nat} (hn : x < n) :
    ∀ v, v < n → PathIn (addEdge (pathG n) x y) (fun _ => True) 0 v := by
  intro v hv
  have hr := pathAdd_reach (x := x) (y := y) v hv
  have : ∀ a b, (addEdge (pathG n) x y).Reach a b → a < n → PathIn (addEdge (pathG n) x y) (fun _ => True) a b := by
    intro a b h
    induction h with
    | refl a => intro ha; exact .refl ha trivial
    | step he _ ih => intro ha; exact .step trivial he (ih he.2.1)
  exact this 0 v hr (by omega)

theorem pathAdd_reducible {n x y : Nat} (hx : x < n) (hy : y < n) : (addEdge (pathG n) x y).Reducible 0 := by
  apply reducible_of_lt
  intro a b he hnd
  by_cases hlt : a < b
  · exact hlt
  exfalso
  have hba : b ≤ a := by omega
  obtain ⟨ha, hb, h⟩ := edge_pathAdd.1 he
  rcases h with ⟨_, e⟩ | ⟨rfl, rfl⟩
  · omega
  · apply hnd
    refine ⟨pathAdd_pathIn hx a ha, fun hq => ?_⟩
    have h0 : 0 ≠ b := hq.source.2
    have := pathAdd_stay hba 0 a hq (by omega)
    omega

theorem pathAdd_cfg {n x y : Nat} (hx : x < n) : (addEdge (pathG n) x y).IsCFG 0 :=
  ⟨by simp only [addEdge, pathG]; omega, fun v hv => pathAdd_reach v hv⟩

/-- C73 for every size: one added edge (forward, backward or a self-loop) never makes an irreducible loop in a path of
`n` vertices, for any depth-first order of the successors (in particular the code order of `NoIrr`). -/
theorem path_one_edge_reducible_all (n : Nat) : ∀ x, x < n → ∀ y, y < n → NoIrr (addEdge (pathG n) x y) := by
  intro x hx y hy w _
  exact reducible_no_irreducible (dfsRun_valid (pathAdd_cfg hx) (by omega)) (pathAdd_reducible hx hy) w

/-! ### The `n`-way conditional -/

theorem edge_nway {k a b : Nat} :
    (nwayG k).edge a b ↔ a < k + 2 ∧ b < k + 2 ∧
      ((a = 0 ∧ 1 ≤ b ∧ b ≤ k) ∨ (1 ≤ a ∧ a ≤ k ∧ b = k + 1)) := by
  unfold Digraph.edge nwayG
  simp only
  constructor
  · rintro ⟨ha, hb, hm⟩
    refine ⟨ha, hb, ?_⟩
    by_cases h0 : a = 0
    · simp only [h0, ↓reduceIte, List.mem_map, List.mem_range] at hm
      obtain ⟨c, hc, rfl⟩ := hm
      exact Or.inl ⟨h0, by omega, by omega⟩
    · by_cases hk : a ≤ k
      · simp only [h0, hk, ↓reduceIte, List.mem_singleton] at hm
        exact Or.inr ⟨by omega, hk, hm⟩
      · simp [h0, hk] at hm
  · rintro ⟨ha, hb, h | h⟩
    · refine ⟨ha, hb, ?_⟩
      simp only [h.1, ↓reduceIte, List.mem_map, List.mem_range]
      exact ⟨b - 1, by omega, by omega⟩
    · refine ⟨ha, hb, ?_⟩
      have h0 : a ≠ 0 := by omega
      simp [h0, h.2.1, h.2.2]

theorem nway_n (k : Nat) : (nwayG k).n = k + 2 := rfl

theorem nway_cfg {k : Nat} (hk : 1 ≤ k) : (nwayG k).IsCFG 0 := by
  refine ⟨by rw [nway_n]; omega, fun v hv => ?_⟩
  rw [nway_n] at hv
  by_cases h0 : v = 0
  · subst h0; exact .refl 0
  · by_cases hvk : v ≤ k
    · exact .step (edge_nway.2 ⟨by omega, by omega, Or.inl ⟨rfl, by omega, hvk⟩⟩) (.refl v)
    · have hv' : v = k + 1 := by omega
      subst hv'
      exact .step (edge_nway.2 ⟨by omega, by omega, Or.inl ⟨rfl, Nat.le_refl 1, hk⟩⟩)
        (.step (edge_nway.2 ⟨by omega, by omega, Or.inr ⟨Nat.le_refl 1, hk, rfl⟩⟩) (.refl _))

theorem nway_reducible {k : Nat} : (nwayG k).Reducible 0 := by
  apply reducible_of_lt
  intro a b he _
  rcases edge_nway.1 he with ⟨_, _, ⟨rfl, h1, _⟩ | ⟨h1, h2, rfl⟩⟩
  · omega
  · omega

@[expose] def nwayE (k : Nat) : Digraph := addEdge (nwayG k) (k + 1) 1

theorem edge_nwayE {k a b : Nat} : (nwayE k).edge a b ↔ (nwayG k).edge a b ∨ (a = k + 1 ∧ b = 1) := by
  unfold Digraph.edge nwayE addEdge
  simp only [nwayG]
  by_cases ha : a = k + 1
  · subst ha
    have h1 : ¬ (k + 1 = 0) := by omega
    have h2 : ¬ (k + 1 ≤ k) := by omega
    simp only [↓reduceIte, h1, h2, List.append_nil, List.mem_append, List.mem_singleton, List.not_mem_nil, false_or]
    constructor
    · rintro ⟨h, hb, rfl⟩
      exact Or.inr ⟨trivial, rfl⟩
    · rintro (⟨h, hb, hm⟩ | ⟨_, rfl⟩)
      · simp at hm
      · exact ⟨by omega, by omega, rfl⟩
  · simp only [ha, ↓reduceIte, false_and, or_false]

/-- C76 for every number of branches `k ≥ 2`: with the edge from the join back into the first branch every valid depth-first
jungle (in particular the one of `dfsRun`) has an irreducible loop. -/
theorem nway_irreducible_every_jungle {k : Nat} (hk : 2 ≤ k) {J : Jungle} (hv : J.Valid (nwayE k) 0) :
    ∃ w, w < k + 2 ∧ (nwayE k).Irreducible J w := by
  have hn : (nwayE k).n = k + 2 := rfl
  have e1j : (nwayE k).edge 1 (k + 1) :=
    edge_nwayE.2 (Or.inl (edge_nway.2 ⟨by omega, by omega, Or.inr ⟨Nat.le_refl 1, by omega, rfl⟩⟩))
  have ej1 : (nwayE k).edge (k + 1) 1 := edge_nwayE.2 (Or.inr ⟨rfl, rfl⟩)
  have e01 : (nwayE k).edge 0 1 :=
    edge_nwayE.2 (Or.inl (edge_nway.2 ⟨by omega, by omega, Or.inl ⟨rfl, Nat.le_refl 1, by omega⟩⟩))
  have e2j : (nwayE k).edge 2 (k + 1) :=
    edge_nwayE.2 (Or.inl (edge_nway.2 ⟨by omega, by omega, Or.inr ⟨by omega, hk, rfl⟩⟩))
  have hlam := hv.laminar 1 (k + 1) (by rw [hn]; omega) (by rw [hn]; omega)
  have n1 := hv.no_rightward _ _ e1j
  have n2 := hv.no_rightward _ _ ej1
  have hcases : J.Anc 1 (k + 1) ∨ J.Anc (k + 1) 1 := by
    rcases hlam with h | h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h n1
    · exact absurd h n2
  rcases hcases with hA | hB
  · -- the loop headed by 1 contains the join, which vertex 2 enters from outside
    refine ⟨1, by omega, ⟨k + 1, ej1, hA⟩, k + 1, 2, ⟨⟨k + 1, ej1, hA⟩, Or.inr ⟨k + 1, by omega, ⟨ej1, hA⟩, ?_⟩⟩, by omega, e2j, ?_⟩
    · exact .refl (by rw [hn]; omega) ⟨hA, by omega⟩
    · intro h2
      have hp := hv.tree_path (u := 1) (by rw [hn]; omega) (J.pre 2 - J.pre 1) 2 (Nat.le_refl _) (by rw [hn]; omega) h2
      have stay : ∀ a c, PathIn (nwayE k) (fun z => J.Anc 1 z) a c → (a = 1 ∨ a = k + 1) → (c = 1 ∨ c = k + 1) := by
        intro a c hq
        induction hq with
        | refl _ _ => intro h; exact h
        | @step a b c _ he _ ih =>
          intro ha
          apply ih
          rcases edge_nwayE.1 he with he' | ⟨_, rfl⟩
          · rcases edge_nway.1 he' with ⟨_, _, ⟨h0, _⟩ | ⟨_, h2, hb⟩⟩
            · omega
            · right; exact hb
          · left; rfl
      have := stay 1 2 hp (Or.inl rfl)
      omega
  · -- the loop headed by the join contains vertex 1, which vertex 0 enters from outside
    refine ⟨k + 1, by omega, ⟨1, e1j, hB⟩, 1, 0, ⟨⟨1, e1j, hB⟩, Or.inr ⟨1, by omega, ⟨e1j, hB⟩, ?_⟩⟩, by omega, e01, ?_⟩
    · exact .refl (by rw [hn]; omega) ⟨hB, by omega⟩
    · intro h0
      have := hv.anc_antisymm (a := k + 1) (b := 0) (by rw [hn]; omega) (by rw [hn]; omega) h0 (hv.root _ (by rw [hn]; omega))
      omega

theorem nway_one_edge_all (k : Nat) (hk : 2 ≤ k) :
    NoIrr (nwayG k) ∧ ∃ w, w < k + 2 ∧ (nwayE k).Irreducible (dfsRun (nwayE k) 0 2) w := by
  refine ⟨fun w _ => reducible_no_irreducible (dfsRun_valid (nway_cfg (by omega)) (by omega)) nway_reducible w, ?_⟩
  have mono : ∀ a b, (nwayG k).Reach a b → (nwayE k).Reach a b := by
    intro a b hc
    induction hc with
    | refl a => exact .refl a
    | step he _ ih =>
      refine .step ?_ ih
      obtain ⟨h1, h2, h3⟩ := he
      refine ⟨h1, h2, ?_⟩
      simp only [nwayE, addEdge]
      split <;> simp [h3]
  have hcfg : (nwayE k).IsCFG 0 :=
    ⟨by show 0 < k + 2; omega, fun v hv => mono 0 v ((nway_cfg (k := k) (by omega)).2 v hv)⟩
  exact nway_irreducible_every_jungle hk (dfsRun_valid hcfg (by omega))

end SmcIrred.Lang
