module

public import SmcIrred.LNF.HvScan

public section

namespace SmcIrred

variable {g : Digraph} {r : Nat} {J : Jungle}

theorem mem_preds {x y : Nat} : y ∈ preds g x ↔ y < g.n ∧ x ∈ g.succ y := by simp [preds]

/-- All the predecessors examined for a representative of the loop body stand for entries of the body. -/
theorem leg_ysOf {Pr : Nat → Prop} {w : Nat} {fd : Nat → Nat} {ex : Nat → List Nat} (env : DEnv g J r Pr w fd ex)
    {x : Nat} (hx : x < g.n) (hR : RepZ g J w fd x) : ∀ y ∈ ysOf g J ex x, Leg g J w fd y := by
  obtain ⟨z, hz, hzw, hfz⟩ := hR
  have hzn := hz.lt
  have ho := env.fdO z hzn
  rw [hfz] at ho
  obtain ⟨hbx, hxw, hxa, hall⟩ := outer_R env.hv env.sh hz hzw ho
  intro y hy
  rcases List.mem_append.1 hy with hy | hy
  · have hy' := (List.mem_filter.1 hy).1
    have hp := mem_preds.1 hy'
    exact ⟨y, x, hbx, hxw, ⟨hp.1, hx, hp.2⟩, rfl⟩
  · obtain ⟨_, hp, y0, z0, hbz, hzx, he, _, hfy⟩ := env.es x y hy
    have hroot : Outer g J Pr x x := outer_idem env.hv hzn ho
    have hou : Outer g J Pr z0 x := (outer_hdr_iff env.hv hp hroot z0).2 hbz
    obtain ⟨hb0, hz0w⟩ := hall z0 hou
    exact ⟨y0, z0, hb0, hz0w, he, hfy⟩

/-- Every popped loop vertex has examined all its predecessors. -/
@[expose] def SDone (J : Jungle) (w : Nat) (fd : Nat → Nat) (ys : List Nat) (st : SC) : Prop :=
  ∀ y ∈ ys, Hdone J w fd y st

theorem havlakDrain_nil (g : Digraph) (J : Jungle) (w : Nat) (hs : HavlakState) (fd : Nat → Nat) (f : Nat) (st : SC)
    (h : st.1 = []) : havlakDrain g J w hs fd f st = (st.2.1, st.2.2.1, st.2.2.2) := by
  cases f with
  | zero => rfl
  | succ f => simp [havlakDrain, h]

theorem drain_spec {Pr : Nat → Prop} {w : Nat} {fd : Nat → Nat} {hs : HavlakState}
    (env : DEnv g J r Pr w fd hs.extra) : ∀ (f : Nat) (st : SC), Dinv g J w fd st →
    (∀ x ∈ st.2.1, x ∈ st.1 ∨ SDone J w fd (ysOf g J hs.extra x) st) → (g.n - st.2.1.length) + st.1.length ≤ f →
    ∃ st' : SC, havlakDrain g J w hs fd f st = (st'.2.1, st'.2.2.1, st'.2.2.2) ∧ Dinv g J w fd st' ∧ st'.1 = [] ∧
      (∀ x ∈ st.2.1, x ∈ st'.2.1) ∧ (∀ x ∈ st'.2.1, SDone J w fd (ysOf g J hs.extra x) st') := by
  intro f
  induction f with
  | zero =>
    intro st hd hsd hf
    have hwl : st.1 = [] := by
      cases h : st.1 with
      | nil => rfl
      | cons a l => rw [h] at hf; simp at hf
    refine ⟨st, havlakDrain_nil g J w hs fd 0 st hwl, hd, hwl, fun x hx => hx, fun x hx => ?_⟩
    rcases hsd x hx with h | h
    · rw [hwl] at h; simp at h
    · exact h
  | succ f ih =>
    intro st hd hsd hf
    obtain ⟨wl0, mem, ext, irr⟩ := st
    cases wl0 with
    | nil =>
      have hwl : ([] : List Nat) = [] := rfl
      refine ⟨([], mem, ext, irr), havlakDrain_nil g J w hs fd (f + 1) _ rfl, hd, rfl, fun x hx => hx, fun x hx => ?_⟩
      rcases hsd x hx with h | h
      · simp at h
      · exact h
    | cons x wl =>
      have hxm : x ∈ mem := hd.wl x List.mem_cons_self
      obtain ⟨hxn, hxR⟩ := hd.mem x hxm
      have hleg := leg_ysOf env hxn hxR
      have hd0 : Dinv g J w fd (wl, mem, ext, irr) :=
        ⟨hd.nodup, hd.mem, fun a ha => hd.wl a (List.mem_cons_of_mem _ ha), hd.ext, hd.irr⟩
      obtain ⟨hd1, hle, hH⟩ := scan_fold env (ysOf g J hs.extra x) (wl, mem, ext, irr) hleg hd0
      obtain ⟨st1, hst1⟩ : ∃ st1 : SC, st1 = (ysOf g J hs.extra x).foldl (scanOne J w fd) (wl, mem, ext, irr) :=
        ⟨_, rfl⟩
      rw [← hst1] at hd1 hle hH
      have hlen : st1.2.1.length ≤ g.n := by
        have hsub : st1.2.1 ⊆ List.range g.n := fun a ha => List.mem_range.2 (hd1.mem a ha).1
        have := List.Nodup.length_le_of_subset hd1.nodup hsub
        simpa using this
      have hgrow := hle.grow
      simp only at hgrow
      have hf1 : (g.n - st1.2.1.length) + st1.1.length ≤ f := by
        simp only [List.length_cons] at hf
        omega
      have hsd1 : ∀ a ∈ st1.2.1, a ∈ st1.1 ∨ SDone J w fd (ysOf g J hs.extra a) st1 := by
        intro a ha
        rcases hle.new a ha with h | h
        · rcases hsd a h with h' | h'
          · rcases List.mem_cons.1 h' with rfl | h''
            · right; exact hH
            · left; exact hle.wl a h''
          · right; exact fun y hy => (h' y hy).mono2 hle.mem hle.ext hle.irr
        · left; exact h
      obtain ⟨st', he, hd', hwl', hmem', hsd'⟩ := ih st1 hd1 hsd1 hf1
      refine ⟨st', ?_, hd', hwl', fun a ha => hmem' a (hle.mem a ha), hsd'⟩
      show havlakDrain g J w hs fd (f + 1) (x :: wl, mem, ext, irr) = _
      simp only [havlakDrain, havlakScan]
      rw [hst1] at he
      exact he

end SmcIrred
