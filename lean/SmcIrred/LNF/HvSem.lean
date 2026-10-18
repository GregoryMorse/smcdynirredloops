module

public import SmcIrred.LNF.Facts
public import SmcIrred.LNF.HvUF

public section

namespace SmcIrred

variable {g : Digraph} {r : Nat} {J : Jungle}

/-- `h` is a header that has already been processed (`Pr` is the set of processed vertices). -/
@[expose] def ProcHdr (g : Digraph) (J : Jungle) (Pr : Nat → Prop) (h : Nat) : Prop := Pr h ∧ g.IsHeader J h

/-- `h` is a processed header whose loop contains `x`. -/
@[expose] def ContainsP (g : Digraph) (J : Jungle) (Pr : Nat → Prop) (x h : Nat) : Prop :=
  ProcHdr g J Pr h ∧ g.Body J h x

/-- `h` is the representative of `x`: the outermost processed loop containing `x`, or `x` itself if there is none. -/
@[expose] def Outer (g : Digraph) (J : Jungle) (Pr : Nat → Prop) (x h : Nat) : Prop :=
  (ContainsP g J Pr x h ∧ ∀ h', ContainsP g J Pr x h' → J.pre h ≤ J.pre h') ∨ (h = x ∧ ∀ h', ¬ ContainsP g J Pr x h')

/-- `h` is the parent of `x` among the processed loops. -/
@[expose] def ParentP (g : Digraph) (J : Jungle) (Pr : Nat → Prop) (h x : Nat) : Prop :=
  ProcHdr g J Pr h ∧ h ≠ x ∧ g.Body J h x ∧ ∀ h', ProcHdr g J Pr h' → h' ≠ x → g.Body J h' x → g.Body J h' h

theorem body_self {w : Nat} (h : g.IsHeader J w) : g.Body J w w := ⟨h, Or.inl rfl⟩

/-- Predecessors inside the subtree of a loop's header, reaching a body vertex, belong to the body. -/
theorem body_closure {w z y : Nat} (hb : g.Body J w z) (he : g.edge y z) (ha : J.Anc w y) : g.Body J w y := by
  by_cases hyw : y = w
  · subst hyw; exact body_self hb.1
  · rcases hb.2 with rfl | ⟨t, ht, hbk, hp⟩
    · exact ⟨hb.1, Or.inr ⟨y, hyw, ⟨he, ha⟩, .refl he.1 ⟨ha, hyw⟩⟩⟩
    · exact ⟨hb.1, Or.inr ⟨t, ht, hbk, .step ⟨ha, hyw⟩ he hp⟩⟩

theorem outer_anc {Pr : Nat → Prop} {x h : Nat} (ho : Outer g J Pr x h) : J.Anc h x := by
  rcases ho with ⟨⟨_, hb⟩, _⟩ | ⟨rfl, _⟩
  · exact hb.anc
  · exact Jungle.Anc.refl _

theorem containsP_anc {Pr : Nat → Prop} {x h : Nat} (hc : ContainsP g J Pr x h) : J.Anc h x := hc.2.anc

theorem outer_unique (hv : J.Valid g r) {Pr : Nat → Prop} {x h h' : Nat} (hlt : x < g.n)
    (h1 : Outer g J Pr x h) (h2 : Outer g J Pr x h') : h = h' := by
  have hlt' : ∀ k, ContainsP g J Pr x k → k < g.n := fun k hk => hk.1.2.lt g J
  rcases h1 with ⟨c1, m1⟩ | ⟨e1, n1⟩ <;> rcases h2 with ⟨c2, m2⟩ | ⟨e2, n2⟩
  · exact hv.pre_inj h h' (hlt' h c1) (hlt' h' c2) (Nat.le_antisymm (m1 h' c2) (m2 h c1))
  · exact absurd c1 (n2 h)
  · exact absurd c2 (n1 h')
  · rw [e1, e2]

/-- Representatives are idempotent. -/
theorem outer_idem (hv : J.Valid g r) {Pr : Nat → Prop} {x h : Nat} (hlt : x < g.n)
    (ho : Outer g J Pr x h) : Outer g J Pr h h := by
  rcases ho with ⟨⟨hp, hb⟩, hm⟩ | ⟨rfl, hn⟩
  · left
    refine ⟨⟨hp, body_self hp.2⟩, fun h' hc' => ?_⟩
    have hn1 := hp.2.lt g J
    have hn2 := hc'.1.2.lt g J
    rcases hv.body_nested_or_disjoint (body_self hp.2) hc'.2 with hh | hh
    · -- body of h' inside body of h? first alternative: `∀ z, Body h' z → Body h z`
      have := hh h' (body_self hc'.1.2)
      exact this.anc |> fun a => by unfold Jungle.Anc at a; omega
    · exact hm h' ⟨hc'.1, hh x hb⟩
  · right
    exact ⟨rfl, hn⟩

/-- The situation while the vertex `w` is processed: `Pr` is the set of processed vertices, all with larger preorder
numbers; it contains all proper descendants of `w` and not `w`. -/
structure SH (g : Digraph) (J : Jungle) (Pr : Nat → Prop) (w : Nat) : Prop where
  wn : w < g.n
  pr : ∀ u, Pr u → u < g.n ∧ J.pre w < J.pre u
  desc : ∀ u, u < g.n → J.Anc w u → u ≠ w → Pr u
  nw : ¬ Pr w

theorem outer_lt {Pr : Nat → Prop} {x h : Nat} (hx : x < g.n) (ho : Outer g J Pr x h) : h < g.n := by
  rcases ho with ⟨⟨hp, _⟩, _⟩ | ⟨rfl, _⟩
  · exact hp.2.lt g J
  · exact hx

/-- An ancestor of a vertex of the subtree of `w` that is a representative is again in the subtree of `w`. -/
theorem outer_anc_w (hv : J.Valid g r) {Pr : Nat → Prop} {w : Nat} (sh : SH g J Pr w) {y h : Nat} (hy : y < g.n)
    (ho : Outer g J Pr y h) (hw : J.Anc w y) : J.Anc w h := by
  rcases ho with ⟨⟨hp, hb⟩, _⟩ | ⟨rfl, _⟩
  · have hhn := hp.2.lt g J
    have hpre := (sh.pr h hp.1).2
    have a1 := hb.anc
    have int := hv.interval y hy
    unfold Jungle.Anc at hw a1 ⊢
    rcases hv.laminar w h sh.wn hhn with hc | hc | hc | hc
    · exact hc
    · unfold Jungle.Anc at hc; omega
    · omega
    · omega
  · exact hw

theorem outer_ne_w {Pr : Nat → Prop} {w : Nat} (sh : SH g J Pr w) {y h : Nat} (ho : Outer g J Pr y h) (hy : y ≠ w) :
    h ≠ w := by
  rcases ho with ⟨⟨hp, _⟩, _⟩ | ⟨rfl, _⟩
  · intro e; subst e; exact sh.nw hp.1
  · exact hy

theorem outer_w (hv : J.Valid g r) {Pr : Nat → Prop} {w : Nat} (sh : SH g J Pr w) {h : Nat}
    (ho : Outer g J Pr w h) : h = w := by
  rcases ho with ⟨⟨hp, hb⟩, _⟩ | ⟨rfl, _⟩
  · exfalso
    have a := hb.anc
    have := (sh.pr h hp.1).2
    unfold Jungle.Anc at a
    omega
  · rfl

/-- The representatives of the vertices of a loop body. -/
theorem outer_R (hv : J.Valid g r) {Pr : Nat → Prop} {w : Nat} (sh : SH g J Pr w) {z x : Nat}
    (hz : g.Body J w z) (hzw : z ≠ w) (ho : Outer g J Pr z x) :
    g.Body J w x ∧ x ≠ w ∧ J.Anc w x ∧ ∀ u, Outer g J Pr u x → g.Body J w u ∧ u ≠ w := by
  have hzn := hz.lt
  have hzanc := hz.anc
  have hxw := outer_ne_w sh ho hzw
  have hxa := outer_anc_w hv sh hzn ho hzanc
  have hxn := outer_lt hzn ho
  have hsub : ProcHdr g J Pr x → ∀ u, g.Body J x u → g.Body J w u := by
    intro hp
    have hcont : ∀ z', g.Body J x z' → True := fun _ _ => trivial
    intro u hu
    have hbs : g.Body J x z := by
      rcases ho with ⟨⟨_, hb⟩, _⟩ | ⟨rfl, hn⟩
      · exact hb
      · exact absurd ⟨hp, body_self hp.2⟩ (hn x)
    exact hv.body_sub hxa (Ne.symm hxw) hz hbs u hu
  rcases ho with ⟨⟨hp, hb⟩, hm⟩ | ⟨rfl, hn⟩
  · have hsub' := hsub hp
    refine ⟨hsub' x (body_self hp.2), hxw, hxa, fun u hu => ?_⟩
    rcases hu with ⟨⟨_, hbu⟩, _⟩ | ⟨hux, hn'⟩
    · refine ⟨hsub' u hbu, ?_⟩
      intro e
      subst e
      have a := hbu.anc
      have := (sh.pr x hp.1).2
      unfold Jungle.Anc at a
      omega
    · exact absurd (by rw [← hux]; exact ⟨hp, body_self hp.2⟩ : ContainsP g J Pr u x) (hn' x)
  · refine ⟨hz, hzw, hzanc, fun u hu => ?_⟩
    rcases hu with ⟨⟨hp, hbu⟩, _⟩ | ⟨rfl, _⟩
    · exact absurd ⟨hp, body_self hp.2⟩ (hn x)
    · exact ⟨hz, hzw⟩

/-- For a processed header that represents itself, its representatives are exactly its body. -/
theorem outer_hdr_iff (hv : J.Valid g r) {Pr : Nat → Prop} {x : Nat} (hx : ProcHdr g J Pr x)
    (hroot : Outer g J Pr x x) (y : Nat) : Outer g J Pr y x ↔ g.Body J x y := by
  constructor
  · rintro (⟨⟨_, hb⟩, _⟩ | ⟨rfl, hn⟩)
    · exact hb
    · exact absurd ⟨hx, body_self hx.2⟩ (hn x)
  · intro hb
    left
    refine ⟨⟨hx, hb⟩, fun h' hc' => ?_⟩
    rcases hv.body_nested_or_disjoint hb hc'.2 with hh | hh
    · have a := (hh h' (body_self hc'.1.2)).anc
      unfold Jungle.Anc at a
      omega
    · have hc2 : ContainsP g J Pr x h' := ⟨hc'.1, hh x (body_self hx.2)⟩
      rcases hroot with ⟨_, hm⟩ | ⟨_, hn⟩
      · exact hm h' hc2
      · exact absurd hc2 (hn h')

end SmcIrred
