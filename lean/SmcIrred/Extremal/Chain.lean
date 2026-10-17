module

public import SmcIrred.Extremal.Count
public import SmcIrred.LNF.Facts

public section

namespace SmcIrred

/-- Graphs on `0 … n-1` with the tree path `0 → 1 → … → n-1`, back edges from the last vertex to every `i ≥ lo`, all
forward edges that skip a vertex, no self-loop, and no other back edge below `lo` (`lo ≤ 1`). `K_n`, `M_n` (`lo = 0`)
and `M_n` without `v_n → v_1` (`lo = 1`) are of this form. -/
structure ChainGraph (g : Digraph) (lo : Nat) : Prop where
  lo_le : lo ≤ 1
  tree : ∀ i, i + 1 < g.n → g.edge i (i + 1)
  back : ∀ i, lo ≤ i → i + 1 < g.n → g.edge (g.n - 1) i
  backTarget : ∀ t w, g.edge t w → w < t → lo ≤ w
  noloop : ∀ i, ¬ g.edge i i
  fwd : ∀ a b, a + 2 ≤ b → b < g.n → g.edge a b

theorem chainJungle_anc {n a b : Nat} : (chainJungle n).Anc a b ↔ a ≤ b := by
  unfold Jungle.Anc chainJungle; simp only; omega

variable {g : Digraph} {lo : Nat}

theorem ChainGraph.valid (h : ChainGraph g lo) (hn : 1 ≤ g.n) : (chainJungle g.n).Valid g 0 where
  interval := fun v hv => by unfold chainJungle; simp only; omega
  pre_inj := fun a b ha hb e => by unfold chainJungle at e; simp only at e; omega
  post_inj := fun a b ha hb e => by unfold chainJungle at e; simp only at e; omega
  events := fun a b ha hb e => by unfold chainJungle at e; simp only at e; omega
  laminar := fun a b ha hb => by
    simp only [chainJungle_anc]; unfold chainJungle; simp only; omega
  root := fun v hv => chainJungle_anc.2 (by omega)
  parent := fun v hv hne => by
    refine ⟨v - 1, ⟨by omega, by omega, chainJungle_anc.2 (by omega), fun w hw hwv hwa => ?_⟩, ?_⟩
    · rw [chainJungle_anc] at hwa ⊢; omega
    · have := h.tree (v - 1) (by omega)
      have e : v - 1 + 1 = v := by omega
      rwa [e] at this
  no_rightward := fun a b he hlt => by
    have := he.1; have := he.2.1
    unfold chainJungle at hlt; simp only at hlt; omega

theorem ChainGraph.header_iff (h : ChainGraph g lo) (w : Nat) :
    g.IsHeader (chainJungle g.n) w ↔ lo ≤ w ∧ w + 1 < g.n := by
  constructor
  · rintro ⟨t, he, hanc⟩
    rw [chainJungle_anc] at hanc
    have hne : t ≠ w := fun e => h.noloop w (e ▸ he)
    have hlt : w < t := by omega
    exact ⟨h.backTarget t w he hlt, by have := he.1; omega⟩
  · rintro ⟨h1, h2⟩
    exact ⟨g.n - 1, h.back w h1 h2, chainJungle_anc.2 (by omega)⟩

theorem ChainGraph.chain_path (h : ChainGraph g lo) (w : Nat) :
    ∀ k x, x + k + 1 = g.n → w < x → PathIn g (fun z => (chainJungle g.n).Anc w z ∧ z ≠ w) x (g.n - 1) := by
  intro k
  induction k with
  | zero =>
    intro x hx hw
    have e : x = g.n - 1 := by omega
    rw [← e]
    exact .refl (by omega) ⟨chainJungle_anc.2 (by omega), by omega⟩
  | succ k ih =>
    intro x hx hw
    exact .step ⟨chainJungle_anc.2 (by omega), by omega⟩ (h.tree x (by omega)) (ih (x + 1) (by omega) (by omega))

theorem ChainGraph.body_iff (h : ChainGraph g lo) (w x : Nat) :
    g.Body (chainJungle g.n) w x ↔ lo ≤ w ∧ w + 1 < g.n ∧ w ≤ x ∧ x < g.n := by
  constructor
  · intro hb
    obtain ⟨h1, h2⟩ := (h.header_iff w).1 hb.1
    exact ⟨h1, h2, chainJungle_anc.1 (Digraph.Body.anc hb), Digraph.Body.lt hb⟩
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨(h.header_iff w).2 ⟨h1, h2⟩, ?_⟩
    by_cases e : x = w
    · exact Or.inl e
    · refine Or.inr ⟨g.n - 1, by omega, ⟨h.back w h1 h2, chainJungle_anc.2 (by omega)⟩, ?_⟩
      exact h.chain_path w (g.n - 1 - x) x (by omega) (by omega)

theorem ChainGraph.irreducible_iff (h : ChainGraph g lo) (w : Nat) :
    g.Irreducible (chainJungle g.n) w ↔ 1 ≤ w ∧ w + 1 < g.n := by
  have hl := h.lo_le
  constructor
  · rintro ⟨hh, x, y, hb, hx, he, hn⟩
    obtain ⟨h1, h2⟩ := (h.header_iff w).1 hh
    rw [chainJungle_anc] at hn
    exact ⟨by omega, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨(h.header_iff w).2 ⟨by omega, h2⟩, g.n - 1, 0, (h.body_iff w _).2 ⟨by omega, h2, by omega, by omega⟩, by omega,
      h.fwd 0 (g.n - 1) (by omega) (by omega), ?_⟩
    rw [chainJungle_anc]; omega

theorem ChainGraph.mee_iff (h : ChainGraph g lo) (x y : Nat) :
    g.IsMEE (chainJungle g.n) x y ↔ g.edge x y ∧ x + 2 ≤ y := by
  have hl := h.lo_le
  constructor
  · rintro ⟨he, w, hb, hy, hn⟩
    obtain ⟨h1, h2, h3, h4⟩ := (h.body_iff w y).1 hb
    rw [chainJungle_anc] at hn
    exact ⟨he, by omega⟩
  · rintro ⟨he, hxy⟩
    have hy := he.2.1
    refine ⟨he, x + 1, (h.body_iff _ _).2 ⟨by omega, by omega, by omega, hy⟩, by omega, ?_⟩
    rw [chainJungle_anc]; omega

theorem ChainGraph.irrCount (h : ChainGraph g lo) (hn : 2 ≤ g.n) : g.irrCount (chainJungle g.n) = g.n - 2 := by
  unfold Digraph.irrCount
  refine Eq.trans (congrArg List.length (List.filter_congr (q := fun w => decide (1 ≤ w ∧ w < g.n - 1)) ?_)) ?_
  · intro w _
    simp only [decide_eq_decide, h.irreducible_iff]
    omega
  · rw [count_interval]
    omega

theorem ChainGraph.meeCount (h : ChainGraph g lo) :
    2 * g.meeCount (chainJungle g.n) = (g.n - 1) * (g.n - 2) := by
  unfold Digraph.meeCount
  refine Eq.trans (congrArg (fun l => 2 * List.sum l) (List.map_congr_left (g := fun y => y - 1) ?_)) (sum_pred g.n)
  intro y hy
  have hy := List.mem_range.1 hy
  refine Eq.trans (congrArg List.length (List.filter_congr (q := fun x => decide (0 ≤ x ∧ x < y - 1)) ?_)) ?_
  · intro x _
    simp only [decide_eq_decide, h.mee_iff]
    constructor
    · rintro ⟨-, h2⟩; omega
    · intro h2
      exact ⟨h.fwd x y (by omega) hy, by omega⟩
  · rw [count_interval]
    omega

end SmcIrred
