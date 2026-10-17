module

public import SmcIrred.Graph.DfsRun

public section

namespace SmcIrred

variable {g : Digraph} {v : Nat} {s sk : DfsState}

/-- Closing `v` after the loop gives the summary of the whole visit. -/
theorem Done.of_loop (hs : s.Wf) (hvn : v < g.n) (h0 : s.pre v = 0)
    (hL : Loop g v (s.opening v) (g.succ v) sk) : Done g v s (sk.closing v) := by
  have hs0 : s.post v = 0 := by
    by_cases h : s.post v = 0
    · exact h
    · exact absurd h0 (hs.post_pre v h).1
  have hclk := hs.clock
  have c1 : (s.opening v).clock = s.clock + 1 := rfl
  have p1 : ∀ x, x ≠ v → (s.opening v).pre x = s.pre x := by intro x hx; simp [DfsState.opening, hx]
  have p2 : (s.opening v).pre v = s.clock := by simp [DfsState.opening]
  have p3 : ∀ x, (s.opening v).post x = s.post x := fun _ => rfl
  have e1 : ∀ x, (sk.closing v).pre x = sk.pre x := fun _ => rfl
  have e2 : ∀ x, x ≠ v → (sk.closing v).post x = sk.post x := by intro x hx; simp [DfsState.closing, hx]
  have e3 : (sk.closing v).post v = sk.clock := by simp [DfsState.closing]
  have e4 : (sk.closing v).clock = sk.clock + 1 := rfl
  have hv1 : sk.pre v = s.clock ∧ sk.post v = 0 := by
    have := hL.unchanged v (fun hn => by have := hn.1; omega)
    rw [p2, p3] at this
    exact ⟨this.1, by rw [this.2, hs0]⟩
  have hcl : s.clock + 1 ≤ sk.clock := by have := hL.clock; omega
  have hnew : ∀ x, s.New (sk.closing v) x ↔ x = v ∨ (s.opening v).New sk x := by
    intro x
    constructor
    · rintro ⟨h1, h2⟩
      rw [e1] at h2
      by_cases hx : x = v
      · exact Or.inl hx
      · exact Or.inr ⟨by rw [p1 x hx]; exact h1, h2⟩
    · rintro (hx | ⟨h1, h2⟩)
      · subst hx; exact ⟨h0, by rw [e1, hv1.1]; omega⟩
      · refine ⟨?_, by rw [e1]; exact h2⟩
        by_cases hx : x = v
        · subst hx; omega
        · rw [← p1 x hx]; exact h1
  have hlt := hL.wf.pre_lt
  have hpl := hL.wf.post_lt
  -- stamps of new vertices other than `v`
  have bnd : ∀ x, (s.opening v).New sk x → x ≠ v ∧ x < g.n ∧ s.clock + 1 ≤ sk.pre x ∧ sk.pre x < sk.post x ∧
      sk.post x < sk.clock := by
    intro x hx
    have ⟨a, b, c, d⟩ := hL.new x hx
    refine ⟨?_, a, by omega, c, d⟩
    intro hxv; subst hxv; have := hx.1; omega
  have same : ∀ x, x ≠ v → (sk.closing v).pre x = sk.pre x ∧ (sk.closing v).post x = sk.post x :=
    fun x hx => ⟨e1 x, e2 x hx⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · refine ⟨by omega, ?_, ?_, ?_⟩
    · intro x; rw [e1, e4]; have := hlt x; omega
    · intro x
      rw [e4]
      by_cases hx : x = v
      · subst hx; rw [e3]; omega
      · rw [e2 x hx]; have := hpl x; omega
    · intro x hx
      rw [e1]
      by_cases hxv : x = v
      · subst hxv; rw [e3] at hx ⊢; rw [hv1.1]; exact ⟨by omega, by omega⟩
      · rw [e2 x hxv] at hx ⊢; exact hL.wf.post_pre x hx
  · intro x hx
    have h1 : x ≠ v := by
      intro hxv; subst hxv; exact hx ((hnew x).2 (Or.inl rfl))
    have h2 : ¬ (s.opening v).New sk x := fun h => hx ((hnew x).2 (Or.inr h))
    have a := hL.unchanged x h2
    rw [e1, e2 x h1, a.1, a.2, p1 x h1, p3]
    exact ⟨rfl, rfl⟩
  · intro x hx
    rcases (hnew x).1 hx with hxv | hx
    · subst hxv
      rw [e1, e3, hv1.1]
      exact ⟨hvn, Nat.le_refl _, by omega, by omega⟩
    · have ⟨hne, a, b, c, d⟩ := bnd x hx
      rw [e1, e2 x hne]
      exact ⟨a, by omega, c, by omega⟩
  · rw [e1, e3, hv1.1]; exact ⟨rfl, rfl⟩
  · intro x hx
    rw [e1, e1, e3, hv1.1]
    rcases (hnew x).1 hx with hxv | hx
    · subst hxv; rw [e3]; omega
    · have ⟨hne, a, b, c, d⟩ := bnd x hx
      rw [e2 x hne]; omega
  · -- distinct
    intro x y hx hy
    rcases (hnew x).1 hx with hxv | hx <;> rcases (hnew y).1 hy with hyv | hy
    · refine ⟨fun _ => by rw [hxv, hyv], fun _ => by rw [hxv, hyv], ?_⟩
      rw [hxv, hyv]; simp only [e1, e3, hv1.1]; omega
    · have ⟨hne, _, _, c, d⟩ := bnd y hy
      rw [hxv]; simp only [e1, e3, hv1.1, e2 y hne]
      refine ⟨fun h => ?_, fun h => ?_, ?_⟩ <;> omega
    · have ⟨hne, _, _, c, d⟩ := bnd x hx
      rw [hyv]; simp only [e1, e3, hv1.1, e2 x hne]
      refine ⟨fun h => ?_, fun h => ?_, ?_⟩ <;> omega
    · have ⟨hnx, _⟩ := bnd x hx
      have ⟨hny, _⟩ := bnd y hy
      simp only [e1, e2 x hnx, e2 y hny]
      exact hL.distinct x y hx hy
  · -- laminar
    intro x y hx hy
    rcases (hnew x).1 hx with hxv | hx <;> rcases (hnew y).1 hy with hyv | hy
    · left; subst hxv; subst hyv; exact ⟨Nat.le_refl _, Nat.le_refl _⟩
    · have ⟨hne, _, _, c, d⟩ := bnd y hy
      left
      unfold DfsState.Anc
      rw [hxv]; simp only [e1, e3, hv1.1, e2 y hne]
      omega
    · have ⟨hne, _, _, c, d⟩ := bnd x hx
      right; left
      unfold DfsState.Anc
      rw [hyv]; simp only [e1, e3, hv1.1, e2 x hne]
      omega
    · have ⟨hnx, _⟩ := bnd x hx
      have ⟨hny, _⟩ := bnd y hy
      have l := hL.laminar x y hx hy
      unfold DfsState.Anc at l ⊢
      simp only [e1, e2 x hnx, e2 y hny]
      exact l
  · -- parent
    intro x hx hxv
    have hx1 : (s.opening v).New sk x := by
      rcases (hnew x).1 hx with h | h
      · exact absurd h hxv
      · exact h
    have ancS : ∀ a b, a ≠ v → b ≠ v → ((sk.closing v).Anc a b ↔ sk.Anc a b) := by
      intro a b ha hb
      unfold DfsState.Anc
      simp only [e1, e2 a ha, e2 b hb]
    have vAnc : ∀ y, (s.opening v).New sk y → (sk.closing v).Anc v y := by
      intro y hy
      have ⟨hne, _, _, c, d⟩ := bnd y hy
      unfold DfsState.Anc
      simp only [e1, e3, hv1.1, e2 y hne]
      omega
    rcases hL.parent x hx1 with ⟨u, hu, he, hne, hanc, hall⟩ | ⟨he, hall⟩
    · have ⟨hnu, _⟩ := bnd u hu
      have ⟨hnx, _⟩ := bnd x hx1
      refine ⟨u, (hnew u).2 (Or.inr hu), he, hne, (ancS u x hnu hnx).2 hanc, ?_⟩
      intro w hw hwx hwa
      rcases (hnew w).1 hw with hwv | hw
      · rw [hwv]; exact vAnc u hu
      · have ⟨hnw, _⟩ := bnd w hw
        exact (ancS w u hnw hnu).2 (hall w hw hwx ((ancS w x hnw hnx).1 hwa))
    · have ⟨hnx, _⟩ := bnd x hx1
      refine ⟨v, (hnew v).2 (Or.inl rfl), he, fun h => hxv h.symm, vAnc x hx1, ?_⟩
      intro w hw hwx hwa
      rcases (hnew w).1 hw with hwv | hw
      · rw [hwv]; exact ⟨Nat.le_refl _, Nat.le_refl _⟩
      · have ⟨hnw, _⟩ := bnd w hw
        exact absurd ((ancS w x hnw hnx).1 hwa) (hall w hw hwx)
  · -- closure
    intro x hx y he
    rcases (hnew x).1 hx with hxv | hx
    · subst hxv
      have hy : y < g.n := he.2.1
      have hm : y ∈ g.succ x := he.2.2
      have hp := hL.proc y hm hy
      simp only [e1, e3]
      exact ⟨hp, hlt y⟩
    · have ⟨hnx, _⟩ := bnd x hx
      obtain ⟨h1, h2⟩ := hL.closure x hx y he
      simp only [e1, e2 x hnx]
      exact ⟨h1, h2⟩

end SmcIrred
