module

public import SmcIrred.LNF.HvRes

public section

namespace SmcIrred

variable {g : Digraph} {r : Nat} {J : Jungle}

/-- The invariant of Havlak's algorithm after the vertices of `Pr` were processed. -/
structure HInv (g : Digraph) (J : Jungle) (r : Nat) (Pr : Nat → Prop) (hs : HavlakState) : Prop where
  hv : J.Valid g r
  chain : UfChain J g.n hs.uf
  ufPr : ∀ x, hs.uf x ≠ x → Pr x
  fdO : ∀ x, x < g.n → Outer g J Pr x (ufFind hs.uf g.n x)
  hdr : ∀ x, x < g.n → ∀ h, hs.hdr x = some h ↔ ParentP g J Pr h x
  irr : ∀ w', hs.irr w' = true ↔ (Pr w' ∧ g.Irreducible J w')
  es : ∀ h, ∀ e ∈ hs.extra h, e < g.n ∧ ProcHdr g J Pr h ∧ ∃ y z, g.Body J h z ∧ z ≠ h ∧ g.edge y z ∧
    ¬ J.Anc h y ∧ ufFind hs.uf g.n e = ufFind hs.uf g.n y
  ec : ∀ h, ProcHdr g J Pr h → ∀ z, g.Body J h z → z ≠ h → ∀ y, g.edge y z → ¬ J.Anc h y →
    ∃ e ∈ hs.extra h, ufFind hs.uf g.n e = ufFind hs.uf g.n y

theorem HInv.env {Pr : Nat → Prop} {hs : HavlakState} {w : Nat} (hi : HInv g J r Pr hs) (sh : SH g J Pr w) :
    DEnv g J r Pr w (ufFind hs.uf g.n) hs.extra := ⟨hi.hv, sh, hi.fdO, hi.es, hi.ec⟩

theorem HInv.init (hv : J.Valid g r) : HInv g J r (fun _ => False)
    ⟨fun v => v, fun _ => none, fun _ => false, fun _ => []⟩ where
  hv := hv
  chain := by intro x h; exact absurd rfl h
  ufPr := by intro x h; exact absurd rfl h
  fdO := by
    intro x hx
    right
    refine ⟨?_, fun h' hc => hc.1.1⟩
    exact find_of_root (fun v => v) x rfl g.n
  hdr := by
    intro x hx h
    simp only [reduceCtorEq, false_iff]
    intro hp; exact hp.1.1
  irr := by intro w'; simp
  es := by intro h e he; simp at he
  ec := by intro h hp; exact absurd hp.1 (by simp)

/-- Facts about a vertex in the new loop of `w`. -/
theorem mem_facts {Pr : Nat → Prop} {hs : HavlakState} {w : Nat} (hi : HInv g J r Pr hs) (sh : SH g J Pr w) {x : Nat}
    (hx : RepZ g J w (ufFind hs.uf g.n) x) :
    x < g.n ∧ g.Body J w x ∧ x ≠ w ∧ J.Anc w x ∧ hs.uf x = x ∧ J.pre w < J.pre x ∧ Outer g J Pr x x ∧ Pr x := by
  obtain ⟨z, hz, hzw, hfz⟩ := hx
  have hzn := hz.lt
  have ho := hi.fdO z hzn
  rw [hfz] at ho
  obtain ⟨hbx, hxw, hxa, -⟩ := outer_R hi.hv sh hz hzw ho
  have hxn : x < g.n := outer_lt hzn ho
  have hroot := (find_root_n hi.chain hzn).1
  rw [hfz] at hroot
  have hpre : J.pre w < J.pre x := by
    have h1 : J.pre w ≤ J.pre x := hxa.1
    have h2 : J.pre w ≠ J.pre x := fun e => hxw (hi.hv.pre_inj x w hxn sh.wn e.symm)
    omega
  exact ⟨hxn, hbx, hxw, hxa, hroot, hpre, outer_idem hi.hv hzn ho, sh.desc x hxn hxa hxw⟩

theorem old_not_contain_w {Pr : Nat → Prop} {w : Nat} (sh : SH g J Pr w) {h' : Nat} (hp : Pr h')
    (hb : g.Body J h' w) : False := by
  have a := hb.anc
  have := (sh.pr h' hp).2
  unfold Jungle.Anc at a
  omega

/-- The representatives after the loop of `w` was added. -/
theorem fdO_step {Pr : Nat → Prop} {hs : HavlakState} {w : Nat} (hi : HInv g J r Pr hs) (sh : SH g J Pr w)
    (m : Nat → Bool) (hm : ∀ x, m x = true ↔ (RepZ g J w (ufFind hs.uf g.n) x ∧ x < g.n)) (fd' : Nat → Nat)
    (hf' : ∀ x, x < g.n → fd' x = if m (ufFind hs.uf g.n x) = true then w else ufFind hs.uf g.n x) :
    ∀ x, x < g.n → Outer g J (fun u => Pr u ∨ u = w) x (fd' x) := by
  intro x hx
  rw [hf' x hx]
  by_cases hmx : m (ufFind hs.uf g.n x) = true
  · simp only [hmx, ↓reduceIte]
    obtain ⟨⟨z, hz, hzw, hfz⟩, hlt⟩ := (hm _).1 hmx
    have hoz : Outer g J Pr z (ufFind hs.uf g.n x) := hfz ▸ hi.fdO z hz.lt
    obtain ⟨-, -, -, hall⟩ := outer_R hi.hv sh hz hzw hoz
    have hbx : g.Body J w x := (hall x (hi.fdO x hx)).1
    left
    refine ⟨⟨⟨Or.inr rfl, hz.1⟩, hbx⟩, ?_⟩
    rintro h' ⟨⟨hp | rfl, _⟩, _⟩
    · exact Nat.le_of_lt (sh.pr h' hp).2
    · exact Nat.le_refl _
  · have hmx' : m (ufFind hs.uf g.n x) = false := by simpa using hmx
    simp only [hmx', Bool.false_eq_true, ↓reduceIte]
    by_cases hxw : x = w
    · subst hxw
      have hfw : ufFind hs.uf g.n x = x := outer_w hi.hv sh (hi.fdO x hx)
      rw [hfw]
      by_cases hh : g.IsHeader J x
      · left
        refine ⟨⟨⟨Or.inr rfl, hh⟩, body_self hh⟩, ?_⟩
        rintro h' ⟨⟨hp | rfl, _⟩, hb⟩
        · exact absurd (old_not_contain_w sh hp hb) id
        · exact Nat.le_refl _
      · right
        refine ⟨rfl, ?_⟩
        rintro h' ⟨⟨hp | rfl, hh'⟩, hb⟩
        · exact old_not_contain_w sh hp hb
        · exact hh hh'
    · have hnb : ¬ g.Body J w x := by
        intro hb
        apply hmx
        exact (hm _).2 ⟨⟨x, hb, hxw, rfl⟩, outer_lt hx (hi.fdO x hx)⟩
      rcases hi.fdO x hx with ⟨⟨hp, hb⟩, hmin⟩ | ⟨he, hn⟩
      · left
        refine ⟨⟨⟨Or.inl hp.1, hp.2⟩, hb⟩, ?_⟩
        rintro h' ⟨⟨hp' | rfl, hh'⟩, hb'⟩
        · exact hmin h' ⟨⟨hp', hh'⟩, hb'⟩
        · exact absurd hb' hnb
      · right
        refine ⟨he, ?_⟩
        rintro h' ⟨⟨hp' | rfl, hh'⟩, hb'⟩
        · exact hn h' ⟨⟨hp', hh'⟩, hb'⟩
        · exact hnb hb'

theorem noparent (hv : J.Valid g r) {Pr : Nat → Prop} {x h' : Nat} (hroot : Outer g J Pr x x)
    (hp : ProcHdr g J Pr h') (hb : g.Body J h' x) (hne : h' ≠ x) : False := by
  rcases hroot with ⟨_, hmin⟩ | ⟨_, hn⟩
  · have h1 := hmin h' ⟨hp, hb⟩
    have a := hb.anc
    unfold Jungle.Anc at a
    exact hne (hv.pre_inj h' x (hp.2.lt g J) hb.lt (by omega))
  · exact hn h' ⟨hp, hb⟩

theorem anc_of_common (hv : J.Valid g r) {w h x : Nat} (hw : w < g.n) (hh : h < g.n) (hx : x < g.n)
    (a1 : J.Anc w x) (a2 : J.Anc h x) (hpre : J.pre w < J.pre h) : J.Anc w h := by
  have int := hv.interval x hx
  unfold Jungle.Anc at a1 a2 ⊢
  rcases hv.laminar w h hw hh with hc | hc | hc | hc
  · exact hc
  · unfold Jungle.Anc at hc; omega
  · omega
  · omega

theorem hdr_step {Pr : Nat → Prop} {hs : HavlakState} {w : Nat} (hi : HInv g J r Pr hs) (sh : SH g J Pr w)
    (m : Nat → Bool) (hm : ∀ x, m x = true ↔ (RepZ g J w (ufFind hs.uf g.n) x ∧ x < g.n)) (hdr' : Nat → Option Nat)
    (hh' : ∀ x, hdr' x = if m x = true then some w else hs.hdr x) :
    ∀ x, x < g.n → ∀ h, hdr' x = some h ↔ ParentP g J (fun u => Pr u ∨ u = w) h x := by
  intro x hx h
  rw [hh' x]
  by_cases hmx : m x = true
  · simp only [hmx, ↓reduceIte, Option.some.injEq]
    obtain ⟨hxn, hbx, hxw, hxa, -, -, hroot, -⟩ := mem_facts hi sh ((hm x).1 hmx).1
    constructor
    · intro e
      subst e
      refine ⟨⟨Or.inr rfl, hbx.1⟩, fun e => hxw e.symm, hbx, ?_⟩
      rintro h' ⟨hp | rfl, hh2⟩ hne hb
      · exact absurd (noparent hi.hv hroot ⟨hp, hh2⟩ hb hne) id
      · exact body_self hh2
    · intro hp
      apply Classical.byContradiction
      intro hne
      obtain ⟨⟨hp1 | e, hh2⟩, hne2, hb2, -⟩ := hp
      · exact noparent hi.hv hroot ⟨hp1, hh2⟩ hb2 hne2
      · exact hne e.symm
  · have hmx' : m x = false := by simpa using hmx
    simp only [hmx', Bool.false_eq_true, ↓reduceIte]
    rw [hi.hdr x hx h]
    have hwnp : ¬ ParentP g J (fun u => Pr u ∨ u = w) w x := by
      rintro ⟨_, hwx, hbwx, hall⟩
      have hxw : x ≠ w := fun e => hwx e.symm
      have hrep : m (ufFind hs.uf g.n x) = true :=
        (hm _).2 ⟨⟨x, hbwx, hxw, rfl⟩, outer_lt hx (hi.fdO x hx)⟩
      rcases hi.fdO x hx with ⟨⟨hp, hb⟩, _⟩ | ⟨he, _⟩
      · have hne : ufFind hs.uf g.n x ≠ x := by
          intro e
          rw [e] at hrep
          rw [hrep] at hmx'
          exact Bool.noConfusion hmx'
        have := hall _ ⟨Or.inl hp.1, hp.2⟩ hne hb
        exact old_not_contain_w sh hp.1 this
      · rw [he] at hrep
        rw [hrep] at hmx'
        exact Bool.noConfusion hmx'
    constructor
    · rintro ⟨hph, hne, hb, hall⟩
      refine ⟨⟨Or.inl hph.1, hph.2⟩, hne, hb, ?_⟩
      rintro h' ⟨hp' | rfl, hh2⟩ hne' hb'
      · exact hall h' ⟨hp', hh2⟩ hne' hb'
      · have hhn := hph.2.lt g J
        have hxn := hb.lt
        have hanc := anc_of_common hi.hv sh.wn hhn hxn hb'.anc hb.anc (sh.pr h hph.1).2
        have hne2 : h' ≠ h := fun e => sh.nw (e ▸ hph.1)
        exact hi.hv.body_sub hanc hne2 hb' hb h (body_self hph.2)
    · rintro ⟨⟨hph | e, hh2⟩, hne, hb, hall⟩
      · refine ⟨⟨hph, hh2⟩, hne, hb, ?_⟩
        intro h' hp' hne' hb'
        exact hall h' ⟨Or.inl hp'.1, hp'.2⟩ hne' hb'
      · subst e
        exact absurd ⟨⟨Or.inr rfl, hh2⟩, hne, hb, hall⟩ hwnp

theorem irr_step {Pr : Nat → Prop} {hs : HavlakState} {w : Nat} (hi : HInv g J r Pr hs) (sh : SH g J Pr w)
    (irr : Bool) (hirr : irr = true ↔ ∃ y0, Entry g J w y0) (irr' : Nat → Bool)
    (hi' : ∀ w', irr' w' = if w' = w then (irr || hs.irr w) else hs.irr w') :
    ∀ w', irr' w' = true ↔ ((Pr w' ∨ w' = w) ∧ g.Irreducible J w') := by
  intro w'
  rw [hi' w']
  by_cases e : w' = w
  · subst e
    simp only [↓reduceIte]
    have hf : hs.irr w' = false := by
      cases h : hs.irr w'
      · rfl
      · exfalso; exact sh.nw ((hi.irr w').1 h).1
    rw [hf, Bool.or_false, hirr]
    simp only [or_true, true_and]
    constructor
    · rintro ⟨y0, z0, hb, hzw, he, hna⟩
      exact ⟨hb.1, z0, y0, hb, hzw, he, hna⟩
    · rintro ⟨hh, x, y, hb, hxw, he, hna⟩
      exact ⟨y, x, hb, hxw, he, hna⟩
  · simp only [e, ↓reduceIte, hi.irr w', or_false]

end SmcIrred
