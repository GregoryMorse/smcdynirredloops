module

public import SmcIrred.Lang.Blocks

public section

namespace SmcIrred.Lang

/-! # Goto-free programs have reducible flow graphs (G33 b3)

The block graph of the code of a structured statement has only back edges that come from the closing jump of a `while` or a
`do ... while`; the block at the head of the loop dominates the blocks of the loop (the loop is entered only at its head,
`Sub.entry`), so every edge that is not a forward edge enters a dominator of its source. -/

variable {g : Digraph} {r : Nat}

theorem nondom_lt' (hk : ∀ a b, g.edge a b → PathIn g (fun _ => True) r a → ¬ g.Dom r b a → a < b) :
    ∀ a b, g.NonDomPath r a b → a < b := by
  intro a b h
  induction h with
  | single he hr hnd => exact hk _ _ he hr hnd
  | step he hr hnd _ ih => exact Nat.lt_trans (hk _ _ he hr hnd) ih

theorem reducible_of_lt' (hk : ∀ a b, g.edge a b → PathIn g (fun _ => True) r a → ¬ g.Dom r b a → a < b) :
    g.Reducible r := by
  intro v h
  exact Nat.lt_irrefl _ (nondom_lt' hk v v h)

/-- A path avoiding `b` that ends in a region entered from outside only at `b` lies in the region. -/
theorem path_region {R : Nat → Prop} {b : Nat} (hentry : ∀ u u', g.edge u u' → R u' → ¬ R u → u' = b) {u v : Nat}
    (h : PathIn g (fun z => z ≠ b) u v) : R v → R u := by
  induction h with
  | refl _ _ => exact id
  | @step a' b' c' hS he hp ih =>
    intro hv
    by_cases hu : R a'
    · exact hu
    · exact absurd (hentry _ _ he (ih hv) hu) hp.source.2

/-- A step to an earlier or equal address of a structured statement is the closing jump of an occurrence of a loop. -/
theorem SStep.back {s : Stmt} {p a c : Nat} (h : SStep s p a c) (hc : c ≤ a) :
    ∃ (U : Stmt) (q : Nat), Sub U q s p ∧ c = q ∧ a + 1 = q + U.size := by
  induction h with
  | blk => omega
  | seqL _ ih =>
    obtain ⟨U, q, h1, h2, h3⟩ := ih hc
    exact ⟨U, q, .seqL h1, h2, h3⟩
  | seqR _ ih =>
    obtain ⟨U, q, h1, h2, h3⟩ := ih hc
    exact ⟨U, q, .seqR h1, h2, h3⟩
  | ite1_skip => omega
  | ite1_in => omega
  | ite1_body _ ih =>
    obtain ⟨U, q, h1, h2, h3⟩ := ih hc
    exact ⟨U, q, .ite1 h1, h2, h3⟩
  | ite_else => omega
  | ite_then => omega
  | ite_jmp => omega
  | ite_s _ ih =>
    obtain ⟨U, q, h1, h2, h3⟩ := ih hc
    exact ⟨U, q, .iteS h1, h2, h3⟩
  | ite_t _ ih =>
    obtain ⟨U, q, h1, h2, h3⟩ := ih hc
    exact ⟨U, q, .iteT h1, h2, h3⟩
  | while_exit => omega
  | while_in => omega
  | @while_back k s p => exact ⟨.while k s, p, .refl, rfl, by simp only [Stmt.size]; omega⟩
  | while_body _ ih =>
    obtain ⟨U, q, h1, h2, h3⟩ := ih hc
    exact ⟨U, q, .whl h1, h2, h3⟩
  | @do_back k s p => exact ⟨.doWhile s k, p, .refl, rfl, by simp only [Stmt.size]; omega⟩
  | do_exit => omega
  | do_body _ ih =>
    obtain ⟨U, q, h1, h2, h3⟩ := ih hc
    exact ⟨U, q, .dow h1, h2, h3⟩

theorem compile_length (s : Stmt) : (compile s).length = s.size + 1 := by
  simp [compile, comp_length]

theorem compile_halt (s : Stmt) {x : Nat} (hx : s.size ≤ x) : (compile s).getD x .halt = .halt := by
  unfold compile
  rw [List.getD_eq_getElem?_getD]
  by_cases h : x = s.size
  · subst h
    rw [List.getElem?_append_right (by rw [comp_length]; omega)]
    simp [comp_length]
  · rw [List.getElem?_eq_none (by simp [comp_length]; omega)]; rfl

theorem compile_at (s : Stmt) : AtAddr (compile s) 0 (comp (labelsOf 0 s) 0 s) := by
  have h : AtAddr (compile s) 0 (comp (labelsOf 0 s) 0 s ++ [.halt]) := fun j _ => by rw [Nat.zero_add]; rfl
  exact h.append_left

/-- The steps of the code of a structured statement are the steps of the statement; they start before `halt` and stay
inside the code. -/
theorem compile_step {s : Stmt} (hs : Structured s) {a c : Nat} (h : StepI (compile s) a c) : SStep s 0 a c := by
  have ha : a < s.size := by
    by_cases hh : a < s.size
    · exact hh
    · unfold StepI at h
      rw [compile_halt s (by omega)] at h
      exact h.elim
  exact (SStep_iff (labelsOf 0 s) (compile s) s 0 hs (compile_at s) a c (by omega) (by omega)).1 h

theorem structured_reducible {s : Stmt} (hs : Structured s) : (cfgOf (compile s)).Reducible 0 := by
  apply reducible_of_lt'
  intro a b he hr hnd
  by_cases hlt : a < b
  · exact hlt
  exfalso
  apply hnd
  refine ⟨hr, fun hpath => ?_⟩
  have hn := compile_length s
  have hga : (cfgOf (compile s)).n = (leaders (compile s)).length := rfl
  obtain ⟨ha, hb, hmem⟩ := he
  rw [hga] at ha hb
  have hsucc : b ∈ blockSucc (compile s) a := hmem
  obtain ⟨c, hstep, hbc⟩ := blockSucc_step (compile s) hsucc
  obtain ⟨hen, hbe, hnext⟩ := blockEnd_spec (compile s) ha
  generalize hE : blockEnd (compile s) a = e at hstep hen hbe hnext
  have hss := compile_step hs hstep
  have hrg := hss.range
  have hce : c ≤ e := by
    by_cases h : c ≤ e
    · exact h
    · exfalso
      have h1 : ldr (compile s) (e + 1) = true := hnext (by omega)
      have h2 := blockOf_strict (compile s) (x := e) (y := e + 1) (by omega) (by omega) h1
      have h3 := blockOf_mono (compile s) (x := e + 1) (y := c) (by omega) (by omega)
      omega
  obtain ⟨hlc, hle⟩ := back_leaders (compile s) hen hstep hce
  obtain ⟨U, q, hsub, hcq, hq⟩ := hss.back hce
  have hcq' : q = c := hcq.symm
  subst hcq'
  have hsr := hsub.range
  have hQ : q + U.size < (compile s).length := by omega
  -- the region of blocks `B1 ≤ u < B2`
  have hbl : blockOf (compile s) q = b := hbc
  have hB2 := blockOf_strict (compile s) (x := e) (y := e + 1) (by omega) (by omega) hle
  have hregion : ∀ u u', (cfgOf (compile s)).edge u u' → (blockOf (compile s) q ≤ u' ∧ u' < blockOf (compile s) (e + 1)) →
      ¬ (blockOf (compile s) q ≤ u ∧ u < blockOf (compile s) (e + 1)) → u' = b := by
    intro u u' he' hu' hnu
    obtain ⟨hu1, hu2, hmem'⟩ := he'
    rw [hga] at hu1 hu2
    obtain ⟨c', hstep', hbc'⟩ := blockSucc_step (compile s) hmem'
    obtain ⟨hen', hbe', _⟩ := blockEnd_spec (compile s) hu1
    generalize blockEnd (compile s) u = e' at hstep' hen' hbe'
    have hss' := compile_step hs hstep'
    have hrg' := hss'.range
    have hc1 : q ≤ c' := by
      by_cases h : q ≤ c'
      · exact h
      · exfalso
        have := blockOf_strict (compile s) (x := c') (y := q) (by omega) (by omega) hlc
        omega
    have hc2 : c' < q + U.size := by
      by_cases h : c' < q + U.size
      · exact h
      · exfalso
        have := blockOf_mono (compile s) (x := e + 1) (y := c') (by omega) (by omega)
        omega
    have he1 : ¬ (q ≤ e' ∧ e' < q + U.size) := by
      rintro ⟨h1, h2⟩
      apply hnu
      have h3 := blockOf_mono (compile s) (x := q) (y := e') h1 (by omega)
      have h4 := blockOf_strict (compile s) (x := e') (y := e + 1) (by omega) (by omega) hle
      omega
    by_cases hcq : q < c'
    · exact absurd (hsub.entry hss' hcq hc2) he1
    · have : c' = q := by omega
      subst this
      omega
  have hRa : blockOf (compile s) q ≤ a ∧ a < blockOf (compile s) (e + 1) := by
    have := blockOf_mono (compile s) (x := q) (y := e) hce (by omega)
    omega
  have h0 := path_region hregion hpath hRa
  have hsrc := hpath.source.2
  omega

end SmcIrred.Lang
