module

public import SmcIrred.LNF.HvSem

public section

namespace SmcIrred

variable {g : Digraph} {r : Nat} {J : Jungle}

/-- State of the worklist loop: worklist, loop members, recorded entries, irreducible flag. -/
abbrev SC := List Nat × List Nat × List Nat × Bool

/-- The predecessors of the loop vertex `x` that are examined: those outside the subtree of `x`, and the recorded
entries of its loop. -/
@[expose] def ysOf (g : Digraph) (J : Jungle) (extra : Nat → List Nat) (x : Nat) : List Nat :=
  ((preds g x).filter fun y => !decide (J.Anc x y)) ++ extra x

/-- Facts about the state of the union-find structure and of the recorded entries while `w` is processed. -/
structure DEnv (g : Digraph) (J : Jungle) (r : Nat) (Pr : Nat → Prop) (w : Nat) (fd : Nat → Nat) (ex : Nat → List Nat) :
    Prop where
  hv : J.Valid g r
  sh : SH g J Pr w
  fdO : ∀ x, x < g.n → Outer g J Pr x (fd x)
  es : ∀ h, ∀ e ∈ ex h, e < g.n ∧ ProcHdr g J Pr h ∧ ∃ y z, g.Body J h z ∧ z ≠ h ∧ g.edge y z ∧ ¬ J.Anc h y ∧ fd e = fd y
  ec : ∀ h, ProcHdr g J Pr h → ∀ z, g.Body J h z → z ≠ h → ∀ y, g.edge y z → ¬ J.Anc h y →
    ∃ e ∈ ex h, fd e = fd y

/-- `x` is the representative of a vertex of the loop body of `w`. -/
@[expose] def RepZ (g : Digraph) (J : Jungle) (w : Nat) (fd : Nat → Nat) (x : Nat) : Prop :=
  ∃ z, g.Body J w z ∧ z ≠ w ∧ fd z = x

/-- `y` stands for a predecessor of a vertex of the loop body of `w`. -/
@[expose] def Leg (g : Digraph) (J : Jungle) (w : Nat) (fd : Nat → Nat) (y : Nat) : Prop :=
  ∃ y0 z0, g.Body J w z0 ∧ z0 ≠ w ∧ g.edge y0 z0 ∧ fd y = fd y0

@[expose] def Entry (g : Digraph) (J : Jungle) (w : Nat) (y0 : Nat) : Prop :=
  ∃ z0, g.Body J w z0 ∧ z0 ≠ w ∧ g.edge y0 z0 ∧ ¬ J.Anc w y0

structure Dinv (g : Digraph) (J : Jungle) (w : Nat) (fd : Nat → Nat) (st : SC) : Prop where
  nodup : st.2.1.Nodup
  mem : ∀ x ∈ st.2.1, x < g.n ∧ RepZ g J w fd x
  wl : ∀ x ∈ st.1, x ∈ st.2.1
  ext : ∀ e ∈ st.2.2.1, e < g.n ∧ ∃ y0, Entry g J w y0 ∧ fd e = fd y0
  irr : st.2.2.2 = true → ∃ y0, Entry g J w y0

/-- `y` has been dealt with in the state. -/
@[expose] def Hdone (J : Jungle) (w : Nat) (fd : Nat → Nat) (y : Nat) (st : SC) : Prop :=
  (J.Anc w (fd y) → fd y = w ∨ fd y ∈ st.2.1) ∧ (¬ J.Anc w (fd y) → fd y ∈ st.2.2.1 ∧ st.2.2.2 = true)

structure SCle (st st' : SC) : Prop where
  wl : ∀ x ∈ st.1, x ∈ st'.1
  mem : ∀ x ∈ st.2.1, x ∈ st'.2.1
  ext : ∀ x ∈ st.2.2.1, x ∈ st'.2.2.1
  irr : st.2.2.2 = true → st'.2.2.2 = true
  new : ∀ z ∈ st'.2.1, z ∈ st.2.1 ∨ z ∈ st'.1
  grow : st'.2.1.length + st.1.length = st.2.1.length + st'.1.length

theorem SCle.refl (st : SC) : SCle st st :=
  ⟨fun _ h => h, fun _ h => h, fun _ h => h, fun h => h, fun z h => Or.inl h, rfl⟩

theorem SCle.trans {a b c : SC} (h1 : SCle a b) (h2 : SCle b c) : SCle a c where
  wl x hx := h2.wl x (h1.wl x hx)
  mem x hx := h2.mem x (h1.mem x hx)
  ext x hx := h2.ext x (h1.ext x hx)
  irr h := h2.irr (h1.irr h)
  new z hz := by
    rcases h2.new z hz with h | h
    · rcases h1.new z h with h' | h'
      · exact Or.inl h'
      · exact Or.inr (h2.wl z h')
    · exact Or.inr h
  grow := by have := h1.grow; have := h2.grow; omega

theorem Hdone.mono {J : Jungle} {w : Nat} {fd : Nat → Nat} {y : Nat} {st st' : SC} (h : Hdone J w fd y st)
    (hle : SCle st st') : Hdone J w fd y st' :=
  ⟨fun ha => (h.1 ha).imp id (hle.mem _), fun ha => ⟨hle.ext _ (h.2 ha).1, hle.irr (h.2 ha).2⟩⟩

theorem scanOne_add (J : Jungle) (w : Nat) (fd : Nat → Nat) (st : SC) (y : Nat) (h1 : J.Anc w (fd y))
    (h2 : fd y ≠ w ∧ (!st.2.1.contains (fd y)) = true) :
    scanOne J w fd st y = (st.1 ++ [fd y], st.2.1 ++ [fd y], st.2.2.1, st.2.2.2) := by
  simp only [scanOne]
  rw [if_pos h1, if_pos h2]

theorem scanOne_skip (J : Jungle) (w : Nat) (fd : Nat → Nat) (st : SC) (y : Nat) (h1 : J.Anc w (fd y))
    (h2 : ¬ (fd y ≠ w ∧ (!st.2.1.contains (fd y)) = true)) : scanOne J w fd st y = st := by
  simp only [scanOne]
  rw [if_pos h1, if_neg h2]

theorem scanOne_rec (J : Jungle) (w : Nat) (fd : Nat → Nat) (st : SC) (y : Nat) (h1 : ¬ J.Anc w (fd y)) :
    scanOne J w fd st y = (st.1, st.2.1, st.2.2.1 ++ [fd y], true) := by
  simp only [scanOne]
  rw [if_neg h1]

theorem Hdone.mono2 {J : Jungle} {w : Nat} {fd : Nat → Nat} {y : Nat} {st st' : SC} (h : Hdone J w fd y st)
    (hm : ∀ x ∈ st.2.1, x ∈ st'.2.1) (he : ∀ x ∈ st.2.2.1, x ∈ st'.2.2.1) (hi : st.2.2.2 = true → st'.2.2.2 = true) :
    Hdone J w fd y st' :=
  ⟨fun ha => (h.1 ha).imp id (hm _), fun ha => ⟨he _ (h.2 ha).1, hi (h.2 ha).2⟩⟩

theorem hdone_scanOne (J : Jungle) (w : Nat) (fd : Nat → Nat) (st : SC) (y : Nat) :
    Hdone J w fd y (scanOne J w fd st y) := by
  by_cases ha : J.Anc w (fd y)
  · by_cases hc : fd y ≠ w ∧ (!st.2.1.contains (fd y)) = true
    · rw [scanOne_add J w fd st y ha hc]
      refine ⟨fun _ => Or.inr ?_, fun h => absurd ha h⟩
      simp
    · rw [scanOne_skip J w fd st y ha hc]
      refine ⟨fun _ => ?_, fun h => absurd ha h⟩
      by_cases e : fd y = w
      · exact Or.inl e
      · right
        have : ¬ (!st.2.1.contains (fd y)) = true := fun h => hc ⟨e, h⟩
        simpa using this
  · rw [scanOne_rec J w fd st y ha]
    refine ⟨fun h => absurd h ha, fun _ => ⟨?_, rfl⟩⟩
    simp

theorem scanOne_le (J : Jungle) (w : Nat) (fd : Nat → Nat) (st : SC) (y : Nat) : SCle st (scanOne J w fd st y) := by
  by_cases ha : J.Anc w (fd y)
  · by_cases hc : fd y ≠ w ∧ (!st.2.1.contains (fd y)) = true
    · rw [scanOne_add J w fd st y ha hc]
      refine ⟨fun x hx => List.mem_append_left _ hx, fun x hx => List.mem_append_left _ hx, fun x hx => hx,
        fun h => h, fun z hz => ?_, by simp; omega⟩
      rcases List.mem_append.1 hz with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_append_right _ h)
    · rw [scanOne_skip J w fd st y ha hc]; exact SCle.refl _
  · rw [scanOne_rec J w fd st y ha]
    exact ⟨fun x hx => hx, fun x hx => hx, fun x hx => List.mem_append_left _ hx, fun _ => rfl,
      fun z hz => Or.inl hz, rfl⟩

theorem fd_lt {Pr : Nat → Prop} {w : Nat} {fd : Nat → Nat} {ex : Nat → List Nat} (env : DEnv g J r Pr w fd ex)
    {x : Nat} (hx : x < g.n) : fd x < g.n := outer_lt hx (env.fdO x hx)

theorem fd_idem {Pr : Nat → Prop} {w : Nat} {fd : Nat → Nat} {ex : Nat → List Nat} (env : DEnv g J r Pr w fd ex)
    {x : Nat} (hx : x < g.n) : fd (fd x) = fd x :=
  outer_unique env.hv (fd_lt env hx) (env.fdO _ (fd_lt env hx)) (outer_idem env.hv hx (env.fdO x hx))

theorem anc_fd_iff {Pr : Nat → Prop} {w : Nat} {fd : Nat → Nat} {ex : Nat → List Nat} (env : DEnv g J r Pr w fd ex)
    {y : Nat} (hy : y < g.n) : J.Anc w (fd y) ↔ J.Anc w y :=
  ⟨fun h => h.trans (outer_anc (env.fdO y hy)), fun h => outer_anc_w env.hv env.sh hy (env.fdO y hy) h⟩

theorem fd_eq_w {Pr : Nat → Prop} {w : Nat} {fd : Nat → Nat} {ex : Nat → List Nat} (env : DEnv g J r Pr w fd ex)
    {y : Nat} (hy : y < g.n) : fd y = w ↔ y = w := by
  constructor
  · intro h
    by_cases e : y = w
    · exact e
    · exact absurd h (outer_ne_w env.sh (env.fdO y hy) e)
  · intro h
    subst h
    exact outer_w env.hv env.sh (env.fdO y hy)

theorem dinv_scanOne {Pr : Nat → Prop} {w : Nat} {fd : Nat → Nat} {ex : Nat → List Nat}
    (env : DEnv g J r Pr w fd ex) {st : SC} (hd : Dinv g J w fd st) {y : Nat}
    (hl : Leg g J w fd y) : Dinv g J w fd (scanOne J w fd st y) := by
  obtain ⟨y0, z0, hb, hzw, he, hfe⟩ := hl
  have hy0 : y0 < g.n := he.1
  have hfy : fd y0 < g.n := fd_lt env hy0
  have hanc0 : J.Anc (fd y0) y0 := outer_anc (env.fdO y0 hy0)
  rw [show scanOne J w fd st y = scanOne J w fd st y from rfl]
  have hfe' : fd y = fd y0 := hfe
  by_cases ha : J.Anc w (fd y)
  · by_cases hc : fd y ≠ w ∧ (!st.2.1.contains (fd y)) = true
    · rw [scanOne_add J w fd st y ha hc]
      have hnm : fd y ∉ st.2.1 := by
        have := hc.2
        simpa using this
      have ha0 : J.Anc w (fd y0) := hfe' ▸ ha
      have hay : J.Anc w y0 := ha0.trans hanc0
      have hy0w : y0 ≠ w := fun e => hc.1 (hfe' ▸ (fd_eq_w env hy0).2 e)
      have hby : g.Body J w y0 := body_closure hb he hay
      refine ⟨List.nodup_append.2 ⟨hd.nodup, List.nodup_cons.2 ⟨by simp, List.nodup_nil⟩, ?_⟩, ?_, ?_, hd.ext, hd.irr⟩
      · intro a ha' b hb' hab
        rw [List.mem_singleton] at hb'
        subst hb'; subst hab
        exact hnm ha'
      · intro x hx
        rcases List.mem_append.1 hx with hx | hx
        · exact hd.mem x hx
        · rw [List.mem_singleton] at hx
          subst hx
          exact ⟨hfe' ▸ hfy, y0, hby, hy0w, hfe'.symm⟩
      · intro x hx
        rcases List.mem_append.1 hx with hx | hx
        · exact List.mem_append_left _ (hd.wl x hx)
        · exact List.mem_append_right _ hx
    · rw [scanOne_skip J w fd st y ha hc]; exact hd
  · rw [scanOne_rec J w fd st y ha]
    have hay : ¬ J.Anc w y0 := fun h => ha (hfe' ▸ (anc_fd_iff env hy0).2 h)
    have hent : Entry g J w y0 := ⟨z0, hb, hzw, he, hay⟩
    refine ⟨hd.nodup, hd.mem, hd.wl, ?_, fun _ => ⟨y0, hent⟩⟩
    intro e he'
    rcases List.mem_append.1 he' with h | h
    · exact hd.ext e h
    · rw [List.mem_singleton] at h
      subst h
      exact ⟨hfe' ▸ hfy, y0, hent, by rw [hfe']; exact fd_idem env hy0⟩

theorem scan_fold {Pr : Nat → Prop} {w : Nat} {fd : Nat → Nat} {ex : Nat → List Nat}
    (env : DEnv g J r Pr w fd ex) : ∀ (ys : List Nat) (st : SC), (∀ y ∈ ys, Leg g J w fd y) →
    Dinv g J w fd st →
    Dinv g J w fd (ys.foldl (scanOne J w fd) st) ∧ SCle st (ys.foldl (scanOne J w fd) st) ∧
    ∀ y ∈ ys, Hdone J w fd y (ys.foldl (scanOne J w fd) st) := by
  intro ys
  induction ys with
  | nil => intro st _ hd; exact ⟨hd, SCle.refl _, by simp⟩
  | cons y ys ih =>
    intro st hl hd
    have h1 := dinv_scanOne env hd (hl y List.mem_cons_self)
    obtain ⟨h2, h3, h4⟩ := ih (scanOne J w fd st y) (fun y' hy' => hl y' (List.mem_cons_of_mem _ hy')) h1
    refine ⟨h2, (scanOne_le J w fd st y).trans h3, ?_⟩
    intro y' hy'
    rcases List.mem_cons.1 hy' with rfl | hy'
    · exact (hdone_scanOne J w fd st y').mono h3
    · exact h4 y' hy'

end SmcIrred
