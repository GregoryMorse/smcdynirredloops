module

public import SmcIrred.Struct.Machine

public section

set_option linter.unusedSimpArgs false

namespace SmcIrred.Struct

variable (o : Nat → Nat) (us : Bool)

/-- Remaining call trace as the CFG semantics `G` says, for each instruction address of `codeGoto`. -/
@[expose] def meanGoto : Nat × Regs → List Evt → Prop
  | (0, g), t => if us then G o .u g.i t else G o .v g.i t
  | (1, g), t => G o .u g.i t
  | (2, g), t => G o .w g.i t
  | (3, g), t => G o .w g.i (.w :: t)
  | (4, g), t => G o .x g.i t
  | (5, g), t => G o .x g.i (.x :: t)
  | (6, g), t => G o .v g.i t
  | (7, g), t => G o .x g.i t
  | _, t => t = []

theorem goto_step (c c' : Nat × Regs) (h : step o us codeGoto c = some c') :
    ∃ d, c'.2.tr = c.2.tr ++ d ∧ ∀ t', meanGoto o us c' t' → meanGoto o us c (d ++ t') := by
  obtain ⟨pc, g⟩ := c
  match pc with
  | 0 =>
    cases hus : us <;> simp [step, codeGoto, Test.eval, hus] at h <;> subst h <;> exact ⟨[], by simp, by simp [meanGoto, hus]⟩
  | 1 =>
    simp [step, codeGoto] at h; subst h
    exact ⟨[.u], rfl, fun t' h' => by simp [meanGoto] at h' ⊢; exact .u h'⟩
  | 2 =>
    simp [step, codeGoto] at h; subst h
    exact ⟨[.w], rfl, fun t' h' => by simpa [meanGoto] using h'⟩
  | 3 =>
    simp only [step, codeGoto] at h
    by_cases h0 : o g.i = 0
    · simp [h0] at h; subst h
      exact ⟨[.wc], rfl, fun t' h' => by
        simp only [meanGoto] at h' ⊢; subst h'; exact .wExit h0⟩
    · by_cases h1 : o g.i = 1
      · simp [h1] at h; subst h
        exact ⟨[.wc], rfl, fun t' h' => by simp only [meanGoto] at h' ⊢; exact .wLoop h1 h'⟩
      · simp [h0, h1] at h; subst h
        exact ⟨[.wc], rfl, fun t' h' => by simp only [meanGoto] at h' ⊢; exact .wFwd h0 h1 h'⟩
  | 4 =>
    simp [step, codeGoto] at h; subst h
    exact ⟨[.x], rfl, fun t' h' => by simpa [meanGoto] using h'⟩
  | 5 =>
    simp only [step, codeGoto] at h
    by_cases h0 : o g.i = 0
    · simp [h0] at h; subst h
      exact ⟨[.xc], rfl, fun t' h' => by
        simp only [meanGoto] at h' ⊢; subst h'; exact .xExit h0⟩
    · by_cases h1 : o g.i = 1
      · simp [h1] at h; subst h
        exact ⟨[.xc], rfl, fun t' h' => by simp only [meanGoto] at h' ⊢; exact .xLoop h1 h'⟩
      · simp [h0, h1] at h; subst h
        exact ⟨[.xc], rfl, fun t' h' => by simp only [meanGoto] at h' ⊢; exact .xFwd h0 h1 h'⟩
  | 6 =>
    simp [step, codeGoto] at h; subst h
    exact ⟨[.v], rfl, fun t' h' => by simp only [meanGoto] at h' ⊢; exact .v h'⟩
  | 7 =>
    simp [step, codeGoto] at h; subst h
    exact ⟨[], by simp, fun t' h' => by simpa [meanGoto] using h'⟩
  | 8 => simp [step, codeGoto] at h
  | n + 9 => simp [step, codeGoto] at h

/-- Entry address of a node. -/
@[expose] def pcGoto : Node → Nat
  | .u => 1 | .w => 2 | .x => 4 | .v => 6

theorem goto_complete {n : Node} {i : Nat} {t : List Evt} (h : G o n i t) :
    ∀ g : Regs, g.i = i → ∃ c', Star o us codeGoto (pcGoto n, g) c' ∧ codeGoto.getD c'.1 .halt = .halt ∧
      c'.2.tr = g.tr ++ t := by
  induction h with
  | u _ ih =>
    intro g hg
    obtain ⟨c', h1, h2, h3⟩ := ih { g with tr := g.tr ++ [.u] } hg
    exact ⟨c', .cons (by simp [step, codeGoto, pcGoto]) h1, h2, by simpa using h3⟩
  | wExit h0 =>
    intro g hg
    subst hg
    refine ⟨(8, { g with i := g.i + 1, tr := g.tr ++ [.w] ++ [.wc] }), ?_, rfl, by simp⟩
    exact .cons (c' := (3, { g with tr := g.tr ++ [.w] })) (by simp [step, codeGoto, pcGoto]) (.one (by simp [step, codeGoto, h0]))
  | wLoop h1 _ ih =>
    intro g hg
    subst hg
    obtain ⟨c', k1, k2, k3⟩ := ih { g with i := g.i + 1, tr := g.tr ++ [.w] ++ [.wc] } rfl
    refine ⟨c', .cons (c' := (3, { g with tr := g.tr ++ [.w] })) (by simp [step, codeGoto, pcGoto]) (.cons (by simp [step, codeGoto, h1, pcGoto]) k1), k2, ?_⟩
    simpa using k3
  | wFwd h0 h1 _ ih =>
    intro g hg
    subst hg
    obtain ⟨c', k1, k2, k3⟩ := ih { g with i := g.i + 1, tr := g.tr ++ [.w] ++ [.wc] } rfl
    refine ⟨c', .cons (c' := (3, { g with tr := g.tr ++ [.w] })) (by simp [step, codeGoto, pcGoto]) (.cons (by simp [step, codeGoto, h0, h1, pcGoto]) k1), k2, ?_⟩
    simpa using k3
  | xExit h0 =>
    intro g hg
    subst hg
    refine ⟨(8, { g with i := g.i + 1, tr := g.tr ++ [.x] ++ [.xc] }), ?_, rfl, by simp⟩
    exact .cons (c' := (5, { g with tr := g.tr ++ [.x] })) (by simp [step, codeGoto, pcGoto]) (.one (by simp [step, codeGoto, h0]))
  | xLoop h1 _ ih =>
    intro g hg
    subst hg
    obtain ⟨c', k1, k2, k3⟩ := ih { g with i := g.i + 1, tr := g.tr ++ [.x] ++ [.xc] } rfl
    refine ⟨c', .cons (c' := (5, { g with tr := g.tr ++ [.x] })) (by simp [step, codeGoto, pcGoto]) (.cons (by simp [step, codeGoto, h1, pcGoto]) k1), k2, ?_⟩
    simpa using k3
  | xFwd h0 h1 _ ih =>
    intro g hg
    subst hg
    obtain ⟨c', k1, k2, k3⟩ := ih { g with i := g.i + 1, tr := g.tr ++ [.x] ++ [.xc] } rfl
    refine ⟨c', .cons (c' := (5, { g with tr := g.tr ++ [.x] })) (by simp [step, codeGoto, pcGoto]) (.cons (by simp [step, codeGoto, h0, h1, pcGoto]) k1), k2, ?_⟩
    simpa using k3
  | v _ ih =>
    intro g hg
    obtain ⟨c', k1, k2, k3⟩ := ih { g with tr := g.tr ++ [.v] } hg
    refine ⟨c', .cons (c' := (7, { g with tr := g.tr ++ [.v] })) (by simp [step, codeGoto, pcGoto]) (.cons (by simp [step, codeGoto, pcGoto]) k1), k2, ?_⟩
    simpa using k3

/-- `irreducible_loops_only_goto` halts with the call trace `t` exactly when the CFG semantics of Figure 4 does. -/
theorem goto_iff (t : List Evt) : Halts o us codeGoto t ↔ Cfg o us t := by
  constructor
  · rintro ⟨c, hs, hh, ht⟩
    obtain ⟨d, hd, hm⟩ := star_sound (o := o) (us := us) (code := codeGoto) (Inv := fun _ => True)
      (Mean := meanGoto o us) (fun _ _ _ _ => trivial) (fun c c' _ h => goto_step o us c c' h)
      (fun c _ hh => by
        obtain ⟨pc, g⟩ := c
        match pc with
        | 0 => simp [codeGoto] at hh
        | 1 => simp [codeGoto] at hh
        | 2 => simp [codeGoto] at hh
        | 3 => simp [codeGoto] at hh
        | 4 => simp [codeGoto] at hh
        | 5 => simp [codeGoto] at hh
        | 6 => simp [codeGoto] at hh
        | 7 => simp [codeGoto] at hh
        | 8 => rfl
        | n + 9 => rfl) (0, ⟨0, false, false, false, []⟩) c hs trivial hh
    have hdt : d = t := by rw [← ht, hd]; simp
    subst hdt
    exact hm
  · intro h
    unfold Cfg at h
    by_cases hus : us = true
    · simp [hus] at h
      obtain ⟨c', k1, k2, k3⟩ := goto_complete o us h ⟨0, false, false, false, []⟩ rfl
      exact ⟨c', .cons (by simp [step, codeGoto, Test.eval, hus, pcGoto]) k1, k2, by simpa using k3⟩
    · simp [hus] at h
      obtain ⟨c', k1, k2, k3⟩ := goto_complete o us h ⟨0, false, false, false, []⟩ rfl
      exact ⟨c', .cons (by simp [step, codeGoto, Test.eval, hus, pcGoto]) k1, k2, by simpa using k3⟩

end SmcIrred.Struct
