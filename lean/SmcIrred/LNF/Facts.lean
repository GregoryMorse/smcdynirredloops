module

public import SmcIrred.LNF.Decide
public import SmcIrred.Graph.Classify

public section

namespace SmcIrred

variable {g : Digraph} {r : Nat} {J : Jungle}

theorem Jungle.Anc.trans {a b c : Nat} (h1 : J.Anc a b) (h2 : J.Anc b c) : J.Anc a c := by
  unfold Jungle.Anc at *; omega

theorem Jungle.Anc.refl (a : Nat) : J.Anc a a := by unfold Jungle.Anc; omega

theorem PathIn.mono {S S' : Nat → Prop} (hS : ∀ z, S z → S' z) {a b : Nat} (h : PathIn g S a b) : PathIn g S' a b := by
  induction h with
  | refl hn hs => exact .refl hn (hS _ hs)
  | step hs he _ ih => exact .step (hS _ hs) he ih

theorem PathIn.trans {S : Nat → Prop} {a b c : Nat} (h1 : PathIn g S a b) (h2 : PathIn g S b c) : PathIn g S a c := by
  induction h1 with
  | refl _ _ => exact h2
  | step hs he _ ih => exact .step hs he (ih h2)

theorem PathIn.source {S : Nat → Prop} {a b : Nat} (h : PathIn g S a b) : a < g.n ∧ S a := by
  cases h with
  | refl hn hs => exact ⟨hn, hs⟩
  | step hs he _ => exact ⟨he.1, hs⟩

/-- Every descendant is reached from its ancestor along the subtree. -/
theorem Jungle.Valid.tree_path (h : J.Valid g r) {u : Nat} (hu : u < g.n) :
    ∀ k v, J.pre v - J.pre u ≤ k → v < g.n → J.Anc u v → PathIn g (fun z => J.Anc u z) u v := by
  intro k
  induction k with
  | zero =>
    intro v hk hv hanc
    have : v = u := h.pre_inj v u hv hu (by unfold Jungle.Anc at hanc; omega)
    subst this
    exact .refl hu (Jungle.Anc.refl _)
  | succ k ih =>
    intro v hk hv hanc
    by_cases hvu : v = u
    · subst hvu; exact .refl hu (Jungle.Anc.refl _)
    · have hvr : v ≠ r := by
        intro e
        subst e
        exact hvu (h.anc_antisymm hv hu (h.root u hu) hanc)
      obtain ⟨p, hp, hedge⟩ := h.parent v hv hvr
      have hpn : p < g.n := hp.1
      have hup : J.Anc u p := hp.2.2.2 u hu (Ne.symm hvu) hanc
      have hnest := h.parent_nested hpn hv hp
      have hpath := ih p (by unfold Jungle.Anc at hup; omega) hpn hup
      exact hpath.trans (.step hup hedge (.refl hv hanc))

/-- The loop of the root is never irreducible (all vertices are descendants of the root). -/
theorem Jungle.Valid.root_not_irreducible (h : J.Valid g r) : ¬ g.Irreducible J r := by
  rintro ⟨-, x, y, -, -, he, hn⟩
  exact hn (h.root y he.1)

theorem Digraph.Body.anc {w x : Nat} (h : g.Body J w x) : J.Anc w x := by
  rcases h.2 with rfl | ⟨t, -, -, hp⟩
  · exact Jungle.Anc.refl _
  · exact hp.source.2.1

theorem Digraph.Body.lt {w x : Nat} (h : g.Body J w x) : x < g.n := by
  rcases h.2 with rfl | ⟨t, -, -, hp⟩
  · exact h.1.lt g J
  · exact hp.source.1

/-- A loop whose header is a proper descendant of another header and which shares a vertex with that loop is nested in it. -/
theorem Jungle.Valid.body_sub (h : J.Valid g r) {w1 w2 x : Nat} (hanc : J.Anc w1 w2) (hne : w1 ≠ w2)
    (h1 : g.Body J w1 x) (h2 : g.Body J w2 x) : ∀ z, g.Body J w2 z → g.Body J w1 z := by
  have hw1 := h1.1
  have hn1 := hw1.lt g J
  have hn2 := h2.1.lt g J
  have hS : ∀ z, (J.Anc w2 z ∧ z ≠ w2) → (J.Anc w1 z ∧ z ≠ w1) := by
    intro z ⟨hz, hzn⟩
    refine ⟨hanc.trans hz, ?_⟩
    rintro rfl
    exact hne (h.anc_antisymm hn1 hn2 hanc hz)
  have hS' : ∀ z, J.Anc w2 z → (J.Anc w1 z ∧ z ≠ w1) := by
    intro z hz
    refine ⟨hanc.trans hz, ?_⟩
    rintro rfl
    exact hne (h.anc_antisymm hn1 hn2 hanc hz)
  have hw2t1 : ∃ t, t ≠ w1 ∧ g.BackEdge J t w1 ∧ PathIn g (fun z => J.Anc w1 z ∧ z ≠ w1) w2 t := by
    rcases h1.2 with hx1 | ⟨t, ht, hb, hp⟩
    · subst hx1
      exact absurd (h.anc_antisymm hn1 hn2 hanc h2.anc) hne
    · rcases h2.2 with hx2 | _
      · subst hx2
        exact ⟨t, ht, hb, hp⟩
      · have hpath := h.tree_path hn2 (J.pre x) x (by omega) h2.lt h2.anc
        exact ⟨t, ht, hb, (hpath.mono hS').trans hp⟩
  obtain ⟨t1, ht1, hb1, hp1⟩ := hw2t1
  intro z hz
  refine ⟨hw1, ?_⟩
  rcases hz.2 with rfl | ⟨t2, ht2, hb2, hp2⟩
  · exact Or.inr ⟨t1, ht1, hb1, hp1⟩
  · have hp2' := hp2.mono hS
    have hts := hS _ hp2.target.2
    exact Or.inr ⟨t1, ht1, hb1, hp2'.trans (.step hts hb2.1 hp1)⟩

/-- Loop bodies are nested or disjoint (C28/C67 support). -/
theorem Jungle.Valid.body_nested_or_disjoint (h : J.Valid g r) {w1 w2 x : Nat} (h1 : g.Body J w1 x)
    (h2 : g.Body J w2 x) : (∀ z, g.Body J w2 z → g.Body J w1 z) ∨ (∀ z, g.Body J w1 z → g.Body J w2 z) := by
  have hn1 := h1.1.lt g J
  have hn2 := h2.1.lt g J
  have hxn := h1.lt
  have hint := h.interval x hxn
  have a1 := h1.anc
  have a2 := h2.anc
  unfold Jungle.Anc at a1 a2
  rcases h.laminar w1 w2 hn1 hn2 with hc | hc | hc | hc
  · by_cases e : w1 = w2
    · subst e; exact Or.inl fun _ hz => hz
    · exact Or.inl (h.body_sub hc e h1 h2)
  · by_cases e : w2 = w1
    · subst e; exact Or.inl fun _ hz => hz
    · exact Or.inr (h.body_sub hc e h2 h1)
  · exfalso; omega
  · exfalso; omega

/-- Every multiple-entry edge is a forward or cross edge (never a tree or back edge). -/
theorem Jungle.mee_forward_or_cross {x y : Nat} (hm : g.IsMEE J x y) :
    J.cls g x y = .forward ∨ J.cls g x y = .cross := by
  obtain ⟨he, w, hb, hy, hn⟩ := hm
  have hwn := hb.1.lt g J
  have hwy := hb.anc
  have hnp : ¬ J.IsParent g x y := fun hp => hn (hp.2.2.2 w hwn (Ne.symm hy) hwy)
  have hnb : ¬ (J.pre y ≤ J.pre x ∧ J.post x ≤ J.post y) := fun hback => hn (hwy.trans hback)
  by_cases hf : J.pre x < J.pre y ∧ J.post y < J.post x
  · exact Or.inl (by simp [Jungle.cls, hnp, hf])
  · exact Or.inr (by simp [Jungle.cls, hnp, hf, hnb])

end SmcIrred
