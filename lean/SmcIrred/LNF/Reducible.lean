module

public import SmcIrred.LNF.Facts

public section

namespace SmcIrred

variable {g : Digraph} {r : Nat} {J : Jungle}

theorem PathIn.snoc {S : Nat → Prop} {a u v : Nat} (h : PathIn g S a u) (hv : S v) (he : g.edge u v) :
    PathIn g S a v := by
  induction h with
  | refl hn hs => exact .step hs he (.refl he.2.1 hv)
  | step hs he' _ ih => exact .step hs he' (ih he)

theorem PathIn.last {S : Nat → Prop} {a b : Nat} (h : PathIn g S a b) : S b := h.target.2

/-- Every vertex is reachable from the root along tree edges, and the ancestors of `v` that are not `w` suffice when `w`
is not an ancestor. -/
theorem avoid_path (hv : J.Valid g r) {w : Nat} : ∀ n v, J.pre v ≤ n → v < g.n → ¬ J.Anc w v →
    PathIn g (fun u => u ≠ w) r v := by
  intro n
  induction n with
  | zero =>
    intro v hle hvn hna
    by_cases hr : v = r
    · subst hr
      exact .refl hvn (fun e => hna (e ▸ Jungle.Anc.refl _))
    · obtain ⟨u, hp, he⟩ := hv.parent v hvn hr
      have h1 := hp.2.2.1.1
      have h2 : J.pre u ≠ J.pre v := fun e => hp.2.1 (hv.pre_inj u v hp.1 hvn e)
      omega
  | succ n ih =>
    intro v hle hvn hna
    by_cases hr : v = r
    · subst hr
      exact .refl hvn (fun e => hna (e ▸ Jungle.Anc.refl _))
    · obtain ⟨u, hp, he⟩ := hv.parent v hvn hr
      have h1 := hp.2.2.1.1
      have h2 : J.pre u ≠ J.pre v := fun e => hp.2.1 (hv.pre_inj u v hp.1 hvn e)
      have hna' : ¬ J.Anc w u := fun h => hna (h.trans hp.2.2.1)
      have hwv : v ≠ w := fun e => hna (e ▸ Jungle.Anc.refl _)
      exact (ih u (by omega) hp.1 hna').snoc hwv he

theorem reach_all (hv : J.Valid g r) : ∀ n v, J.pre v ≤ n → v < g.n → PathIn g (fun _ => True) r v := by
  intro n
  induction n with
  | zero =>
    intro v hle hvn
    by_cases hr : v = r
    · subst hr; exact .refl hvn trivial
    · obtain ⟨u, hp, he⟩ := hv.parent v hvn hr
      have h1 := hp.2.2.1.1
      have h2 : J.pre u ≠ J.pre v := fun e => hp.2.1 (hv.pre_inj u v hp.1 hvn e)
      omega
  | succ n ih =>
    intro v hle hvn
    by_cases hr : v = r
    · subst hr; exact .refl hvn trivial
    · obtain ⟨u, hp, he⟩ := hv.parent v hvn hr
      have h1 := hp.2.2.1.1
      have h2 : J.pre u ≠ J.pre v := fun e => hp.2.1 (hv.pre_inj u v hp.1 hvn e)
      exact (ih u (by omega) hp.1).snoc trivial he

theorem reach (hv : J.Valid g r) {v : Nat} (hvn : v < g.n) : PathIn g (fun _ => True) r v :=
  reach_all hv (J.pre v) v (Nat.le_refl _) hvn

/-- A dominator is an ancestor in every depth-first tree. -/
theorem dom_anc (hv : J.Valid g r) {w y : Nat} (hd : g.Dom r w y) : J.Anc w y := by
  apply Classical.byContradiction
  intro hna
  exact hd.2 (avoid_path hv (J.pre y) y (Nat.le_refl _) hd.1.target.1 hna)

theorem dom_self {x : Nat} (h : PathIn g (fun _ => True) r x) : g.Dom r x x :=
  ⟨h, fun hp => hp.last rfl⟩

theorem Digraph.NonDomPath.snoc {a b c : Nat} (h : g.NonDomPath r a b) (he : g.edge b c) (hr : PathIn g (fun _ => True) r b)
    (hd : ¬ g.Dom r c b) : g.NonDomPath r a c := by
  induction h with
  | single e1 r1 d1 => exact .step e1 r1 d1 (.single he hr hd)
  | step e1 r1 d1 _ ih => exact .step e1 r1 d1 (ih he hr hd)

theorem tree_nondom (hv : J.Valid g r) {w : Nat} (hw : w < g.n) : ∀ n v, J.pre v ≤ n → v < g.n → J.Anc w v →
    w = v ∨ g.NonDomPath r w v := by
  intro n
  induction n with
  | zero =>
    intro v hle hvn hanc
    by_cases hvw : w = v
    · exact Or.inl hvw
    · by_cases hr : v = r
      · subst hr
        exact absurd (hv.anc_antisymm hw hvn hanc (hv.root w hw)) hvw
      · obtain ⟨u, hp, he⟩ := hv.parent v hvn hr
        have h1 := hp.2.2.1.1
        have h2 : J.pre u ≠ J.pre v := fun e => hp.2.1 (hv.pre_inj u v hp.1 hvn e)
        omega
  | succ n ih =>
    intro v hle hvn hanc
    by_cases hvw : w = v
    · exact Or.inl hvw
    · by_cases hr : v = r
      · subst hr
        exact absurd (hv.anc_antisymm hw hvn hanc (hv.root w hw)) hvw
      · obtain ⟨u, hp, he⟩ := hv.parent v hvn hr
        have h1 := hp.2.2.1.1
        have h2 : J.pre u ≠ J.pre v := fun e => hp.2.1 (hv.pre_inj u v hp.1 hvn e)
        have hwu : J.Anc w u := hp.2.2.2 w hw hvw hanc
        have hnd : ¬ g.Dom r v u := by
          intro hd
          exact hp.2.1 (hv.anc_antisymm hp.1 hvn hp.2.2.1 (dom_anc hv hd))
        right
        rcases ih u (by omega) hp.1 hwu with e | h
        · subst e; exact .single he (reach hv hp.1) hnd
        · exact h.snoc he (reach hv hp.1) hnd

/-- In a reducible flow graph, the back edges of every depth-first tree enter dominators. -/
theorem backedge_dom (hv : J.Valid g r) (hred : g.Reducible r) {t w : Nat} (he : g.edge t w) (ha : J.Anc w t) :
    g.Dom r w t := by
  apply Classical.byContradiction
  intro hnd
  have hT := tree_nondom hv he.2.1 (J.pre t) t (Nat.le_refl _) he.1 ha
  rcases hT with e | h
  · subst e; exact hnd (dom_self (reach hv he.1))
  · exact hred w (h.snoc he (reach hv he.1) hnd)

theorem header_dom (hv : J.Valid g r) (hred : g.Reducible r) (w : Nat) :
    g.IsHeader J w ↔ ∃ t, g.edge t w ∧ g.Dom r w t :=
  ⟨fun ⟨t, he, ha⟩ => ⟨t, he, backedge_dom hv hred he ha⟩, fun ⟨t, he, hd⟩ => ⟨t, he, dom_anc hv hd⟩⟩

theorem path_sub (hv : J.Valid g r) {w : Nat} : ∀ x c, PathIn g (fun z => z ≠ w) x c → g.Dom r w c →
    PathIn g (fun z => J.Anc w z ∧ z ≠ w) x c := by
  intro x c hp
  induction hp with
  | refl hn hs => intro hd; exact .refl hn ⟨dom_anc hv hd, hs⟩
  | @step a b c hs he hp ih =>
    intro hd
    have hpa : PathIn g (fun z => z ≠ w) a c := .step hs he hp
    have hda : g.Dom r w a := ⟨reach hv he.1, fun hr => hd.2 (hr.trans hpa)⟩
    exact .step ⟨dom_anc hv hda, hs⟩ he (ih hd)

/-- In a reducible flow graph, the loop body of a header is described by dominance alone (no depth-first tree). -/
theorem body_dom (hv : J.Valid g r) (hred : g.Reducible r) (w x : Nat) :
    g.Body J w x ↔ (∃ t, g.edge t w ∧ g.Dom r w t) ∧
      (x = w ∨ ∃ t, t ≠ w ∧ g.edge t w ∧ g.Dom r w t ∧ PathIn g (fun z => z ≠ w) x t) := by
  constructor
  · rintro ⟨hh, hx⟩
    refine ⟨(header_dom hv hred w).1 hh, ?_⟩
    rcases hx with e | ⟨t, htw, ⟨he, ha⟩, hp⟩
    · exact Or.inl e
    · exact Or.inr ⟨t, htw, he, backedge_dom hv hred he ha, hp.mono (fun z hz => hz.2)⟩
  · rintro ⟨hh, hx⟩
    refine ⟨(header_dom hv hred w).2 hh, ?_⟩
    rcases hx with e | ⟨t, htw, he, hd, hp⟩
    · exact Or.inl e
    · exact Or.inr ⟨t, htw, ⟨he, dom_anc hv hd⟩, path_sub hv x t hp hd⟩

/-- The loop bodies of a reducible flow graph do not depend on the depth-first search (C28, second half). -/
theorem body_dfs_independent {J' : Jungle} (hv : J.Valid g r) (hv' : J'.Valid g r) (hred : g.Reducible r) (w x : Nat) :
    g.Body J w x ↔ g.Body J' w x := by
  rw [body_dom hv hred, body_dom hv' hred]

theorem header_dfs_independent {J' : Jungle} (hv : J.Valid g r) (hv' : J'.Valid g r) (hred : g.Reducible r) (w : Nat) :
    g.IsHeader J w ↔ g.IsHeader J' w := by
  rw [header_dom hv hred, header_dom hv' hred]

/-- The loop nesting forest of a reducible flow graph does not depend on the depth-first search. -/
theorem lnfParent_dfs_independent {J' : Jungle} (hv : J.Valid g r) (hv' : J'.Valid g r) (hred : g.Reducible r)
    (h x : Nat) : g.LnfParent J h x ↔ g.LnfParent J' h x := by
  unfold Digraph.LnfParent
  simp only [header_dfs_independent hv hv' hred, body_dfs_independent hv hv' hred]

end SmcIrred
