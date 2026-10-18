module

public import SmcIrred.LNF.HvDrain

public section

namespace SmcIrred

variable {g : Digraph} {r : Nat} {J : Jungle}

/-- A predecessor inside the subtree of a representative `x` that has an edge to a vertex represented by `x` is
represented by `x`. -/
theorem cl_in {Pr : Nat → Prop} {w : Nat} {fd : Nat → Nat} {ex : Nat → List Nat} (env : DEnv g J r Pr w fd ex)
    {x b a : Nat} (hxa : J.Anc w x) (hxw : x ≠ w) (hb : Outer g J Pr b x) (he : g.edge a b) (ha : J.Anc x a) :
    Outer g J Pr a x := by
  have hbn : b < g.n := he.2.1
  have hxn : x < g.n := outer_lt hbn hb
  have hpx : ProcHdr g J Pr x := by
    rcases hb with ⟨⟨hp, _⟩, _⟩ | ⟨hxb, hn⟩
    · exact hp
    · subst hxb
      have hpr : Pr x := env.sh.desc x hxn hxa hxw
      have hh : g.IsHeader J x := ⟨a, he, ha⟩
      exact absurd ⟨⟨hpr, hh⟩, body_self hh⟩ (hn x)
  have hroot : Outer g J Pr x x := outer_idem env.hv hbn hb
  have hbx : g.Body J x b := by
    rcases hb with ⟨⟨_, hbb⟩, _⟩ | ⟨hxb, _⟩
    · exact hbb
    · subst hxb; exact body_self hpx.2
  exact (outer_hdr_iff env.hv hpx hroot a).2 (body_closure hbx he ha)

/-- A predecessor outside the subtree of a representative `x` with an edge to a vertex represented by `x` is examined
when `x` is scanned (directly, or through a recorded entry of its loop). -/
theorem cl_out {Pr : Nat → Prop} {w : Nat} {fd : Nat → Nat} {ex : Nat → List Nat} (env : DEnv g J r Pr w fd ex)
    {x b a : Nat} (hb : Outer g J Pr b x) (he : g.edge a b) (ha : ¬ J.Anc x a) :
    ∃ y ∈ ysOf g J ex x, fd y = fd a := by
  by_cases hbx : b = x
  · subst hbx
    refine ⟨a, ?_, rfl⟩
    unfold ysOf
    refine List.mem_append_left _ (List.mem_filter.2 ⟨mem_preds.2 ⟨he.1, he.2.2⟩, ?_⟩)
    simp [ha]
  · have hc : ContainsP g J Pr b x := by
      rcases hb with ⟨hc, _⟩ | ⟨hxb, _⟩
      · exact hc
      · exact absurd hxb.symm hbx
    obtain ⟨e, hee, hfe⟩ := env.ec x hc.1 b hc.2 hbx a he ha
    exact ⟨e, List.mem_append_right _ hee, hfe⟩

theorem path_mem {Pr : Nat → Prop} {w : Nat} {fd : Nat → Nat} {ex : Nat → List Nat} (env : DEnv g J r Pr w fd ex)
    {st : SC} (hS : ∀ x ∈ st.2.1, SDone J w fd (ysOf g J ex x) st) {a c : Nat}
    (hp : PathIn g (fun u => J.Anc w u ∧ u ≠ w) a c) :
    g.Body J w c → fd c ∈ st.2.1 → g.Body J w a ∧ fd a ∈ st.2.1 := by
  induction hp with
  | refl hn hs => intro h1 h2; exact ⟨h1, h2⟩
  | @step a b c hs he hp ih =>
    intro hc hfc
    obtain ⟨hbody, hfb⟩ := ih hc hfc
    have hbs := hp.source
    have hbw : b ≠ w := hbs.2.2
    have hbn : b < g.n := hbs.1
    have hou := env.fdO b hbn
    obtain ⟨_, hxw, hxa, _⟩ := outer_R env.hv env.sh hbody hbw hou
    refine ⟨body_closure hbody he hs.1, ?_⟩
    by_cases hax : J.Anc (fd b) a
    · have := cl_in env hxa hxw hou he hax
      have hfa : fd a = fd b := outer_unique env.hv he.1 (env.fdO a he.1) this
      rw [hfa]; exact hfb
    · obtain ⟨y, hy, hfy⟩ := cl_out env hou he hax
      have hh2 := hS (fd b) hfb y hy
      have han : J.Anc w (fd y) := by
        rw [hfy]; exact (anc_fd_iff env he.1).2 hs.1
      have hne : fd y ≠ w := by
        rw [hfy]; intro e; exact hs.2 ((fd_eq_w env he.1).1 e)
      rw [← hfy]
      rcases hh2.1 han with e | e
      · exact absurd e hne
      · exact e

theorem close_spec {Pr : Nat → Prop} {w : Nat} {fd : Nat → Nat} {ex : Nat → List Nat} (env : DEnv g J r Pr w fd ex)
    {st : SC}
    (hB : ∀ t, t ≠ w → g.edge t w → J.Anc w t → fd t ∈ st.2.1)
    (hS : ∀ x ∈ st.2.1, SDone J w fd (ysOf g J ex x) st) :
    (∀ z, g.Body J w z → z ≠ w → fd z ∈ st.2.1) ∧
    (∀ y z, g.Body J w z → z ≠ w → g.edge y z → ¬ J.Anc w y → fd y ∈ st.2.2.1 ∧ st.2.2.2 = true) := by
  have h1 : ∀ z, g.Body J w z → z ≠ w → fd z ∈ st.2.1 := by
    intro z hz hzw
    obtain ⟨hh, hz2⟩ := hz
    rcases hz2 with rfl | ⟨t, htw, hbk, hp⟩
    · exact absurd rfl hzw
    · have hbt : g.Body J w t := ⟨hh, Or.inr ⟨t, htw, hbk, .refl hbk.1.1 ⟨hbk.2, htw⟩⟩⟩
      exact (path_mem env hS hp hbt (hB t htw hbk.1 hbk.2)).2
  refine ⟨h1, ?_⟩
  intro y z hz hzw he hna
  have hzm := h1 z hz hzw
  have hzn := hz.lt
  have hou := env.fdO z hzn
  obtain ⟨_, hxw, hxa, _⟩ := outer_R env.hv env.sh hz hzw hou
  have hnx : ¬ J.Anc (fd z) y := fun h => hna (hxa.trans h)
  obtain ⟨y', hy', hfy'⟩ := cl_out env hou he hnx
  have hh2 := hS (fd z) hzm y' hy'
  have hnoanc : ¬ J.Anc w (fd y') := by
    rw [hfy']; intro h; exact hna ((anc_fd_iff env he.1).1 h)
  have := hh2.2 hnoanc
  rw [hfy'] at this
  exact this

end SmcIrred
