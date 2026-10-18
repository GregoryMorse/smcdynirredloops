module

public import SmcIrred.Struct.Machine

public section

set_option linter.unusedSimpArgs false

namespace SmcIrred.Struct

variable (o : Nat → Nat) (us : Bool)

/-- Remaining call trace as the CFG semantics `G` says, for each instruction address of `codeLoops`. -/
@[expose] def meanLoops : Nat × Regs → List Evt → Prop
  | (0, g), t => if us then G o .u g.i t else G o .v g.i t
  | (1, g), t => G o .u g.i t
  | (2, g), t => G o .w g.i t
  | (3, g), t => G o .w g.i (.w :: t)
  | (4, g), t => G o .w g.i (.w :: t)
  | (5, g), t => if g.loop then G o .u g.i t else G o .x g.i t
  | (6, g), t => G o .x g.i t
  | (7, g), t => G o .x g.i (.x :: t)
  | (8, g), t => G o .x g.i (.x :: t)
  | (9, g), t => if g.loop then G o .w g.i t else G o .v g.i t
  | (10, g), t => G o .v g.i t
  | (11, g), t => G o .x g.i t
  | (12, g), t => G o .w g.i t
  | (13, g), t => G o .u g.i t
  | _, t => t = []

/-- At the two `switch` statements the variable `loop` has just been cleared. -/
@[expose] def invLoops (c : Nat × Regs) : Prop := (c.1 = 4 ∨ c.1 = 8) → c.2.loop = false

theorem loops_inv (c c' : Nat × Regs) (hi : invLoops c) (h : step o us codeLoops c = some c') : invLoops c' := by
  obtain ⟨pc, g⟩ := c
  unfold invLoops at *
  match pc with
  | 0 => cases hus : us <;> simp [step, codeLoops, Test.eval, hus] at h <;> subst h <;> simp
  | 1 => simp [step, codeLoops, Test.eval, Regs.setVar] at h; subst h; simp
  | 2 => simp [step, codeLoops, Test.eval, Regs.setVar] at h; subst h; simp
  | 3 => simp [step, codeLoops, Test.eval, Regs.setVar] at h; subst h; simp
  | 4 =>
    simp only [step, codeLoops] at h
    by_cases h0 : o g.i = 0
    · simp [h0] at h; subst h; simp
    · by_cases h1 : o g.i = 1
      · simp [h0, h1] at h; subst h; simp
      · simp [h0, h1] at h; subst h; simp
  | 5 =>
    simp [step, codeLoops, Test.eval, Regs.setVar] at h
    cases hl : g.loop <;> simp [hl] at h <;> subst h <;> simp
  | 6 => simp [step, codeLoops, Test.eval, Regs.setVar] at h; subst h; simp
  | 7 => simp [step, codeLoops, Test.eval, Regs.setVar] at h; subst h; simp
  | 8 =>
    simp only [step, codeLoops] at h
    by_cases h0 : o g.i = 0
    · simp [h0] at h; subst h; simp
    · by_cases h1 : o g.i = 1
      · simp [h0, h1] at h; subst h; simp
      · simp [h0, h1] at h; subst h; simp
  | 9 =>
    simp [step, codeLoops, Test.eval, Regs.setVar] at h
    cases hl : g.loop <;> simp [hl] at h <;> subst h <;> simp
  | 10 => simp [step, codeLoops, Test.eval, Regs.setVar] at h; subst h; simp
  | 11 => simp [step, codeLoops, Test.eval, Regs.setVar] at h; subst h; simp
  | 12 => simp [step, codeLoops, Test.eval, Regs.setVar] at h; subst h; simp
  | 13 => simp [step, codeLoops, Test.eval, Regs.setVar] at h; subst h; simp
  | 14 => simp [step, codeLoops, Test.eval, Regs.setVar] at h
  | n + 15 => simp [step, codeLoops, Test.eval, Regs.setVar] at h

theorem loops_step (c c' : Nat × Regs) (hi : invLoops c) (h : step o us codeLoops c = some c') :
    ∃ d, c'.2.tr = c.2.tr ++ d ∧ ∀ t', meanLoops o us c' t' → meanLoops o us c (d ++ t') := by
  obtain ⟨pc, g⟩ := c
  unfold invLoops at hi
  simp only at hi
  match pc with
  | 0 =>
    cases hus : us <;> simp [step, codeLoops, Test.eval, Regs.setVar] at h <;> subst h <;> exact ⟨[], by simp, by simp [meanLoops, hus]⟩
  | 1 =>
    simp [step, codeLoops, Test.eval, Regs.setVar] at h; subst h
    exact ⟨[.u], rfl, fun t' h' => by simp [meanLoops] at h' ⊢; exact .u h'⟩
  | 2 =>
    simp [step, codeLoops, Test.eval, Regs.setVar] at h; subst h
    exact ⟨[.w], rfl, fun t' h' => by simpa [meanLoops] using h'⟩
  | 3 =>
    simp [step, codeLoops, Test.eval, Regs.setVar] at h; subst h
    exact ⟨[], by simp, fun t' h' => by simpa [meanLoops] using h'⟩
  | 4 =>
    have hl := hi (by simp)
    simp only [step, codeLoops] at h
    by_cases h0 : o g.i = 0
    · simp [h0] at h; subst h
      exact ⟨[.wc], rfl, fun t' h' => by simp only [meanLoops] at h' ⊢; subst h'; exact .wExit h0⟩
    · by_cases h1 : o g.i = 1
      · simp [h0, h1] at h; subst h
        exact ⟨[.wc], rfl, fun t' h' => by simp only [meanLoops] at h' ⊢; simp at h'; exact .wLoop h1 h'⟩
      · simp [h0, h1] at h; subst h
        exact ⟨[.wc], rfl, fun t' h' => by simp only [meanLoops] at h' ⊢; simp [hl] at h'; exact .wFwd h0 h1 h'⟩
  | 5 =>
    cases hl : g.loop <;> simp [step, codeLoops, Test.eval, Regs.setVar, hl] at h <;> subst h <;>
      exact ⟨[], by simp, fun t' h' => by simpa [meanLoops, hl] using h'⟩
  | 6 =>
    simp [step, codeLoops, Test.eval, Regs.setVar] at h; subst h
    exact ⟨[.x], rfl, fun t' h' => by simpa [meanLoops] using h'⟩
  | 7 =>
    simp [step, codeLoops, Test.eval, Regs.setVar] at h; subst h
    exact ⟨[], by simp, fun t' h' => by simpa [meanLoops] using h'⟩
  | 8 =>
    have hl := hi (by simp)
    simp only [step, codeLoops] at h
    by_cases h0 : o g.i = 0
    · simp [h0] at h; subst h
      exact ⟨[.xc], rfl, fun t' h' => by simp only [meanLoops] at h' ⊢; subst h'; exact .xExit h0⟩
    · by_cases h1 : o g.i = 1
      · simp [h0, h1] at h; subst h
        exact ⟨[.xc], rfl, fun t' h' => by simp only [meanLoops] at h' ⊢; simp at h'; exact .xLoop h1 h'⟩
      · simp [h0, h1] at h; subst h
        exact ⟨[.xc], rfl, fun t' h' => by simp only [meanLoops] at h' ⊢; simp [hl] at h'; exact .xFwd h0 h1 h'⟩
  | 9 =>
    cases hl : g.loop <;> simp [step, codeLoops, Test.eval, Regs.setVar, hl] at h <;> subst h <;>
      exact ⟨[], by simp, fun t' h' => by simpa [meanLoops, hl] using h'⟩
  | 10 =>
    simp [step, codeLoops, Test.eval, Regs.setVar] at h; subst h
    exact ⟨[.v], rfl, fun t' h' => by simp only [meanLoops] at h' ⊢; exact .v h'⟩
  | 11 =>
    simp [step, codeLoops, Test.eval, Regs.setVar] at h; subst h
    exact ⟨[], by simp, fun t' h' => by simpa [meanLoops] using h'⟩
  | 12 =>
    simp [step, codeLoops, Test.eval, Regs.setVar] at h; subst h
    exact ⟨[], by simp, fun t' h' => by simpa [meanLoops] using h'⟩
  | 13 =>
    simp [step, codeLoops, Test.eval, Regs.setVar] at h; subst h
    exact ⟨[], by simp, fun t' h' => by simpa [meanLoops] using h'⟩
  | 14 => simp [step, codeLoops, Test.eval, Regs.setVar] at h
  | n + 15 => simp [step, codeLoops, Test.eval, Regs.setVar] at h

/-- Entry address of a node. -/
@[expose] def pcLoops : Node → Nat
  | .u => 1 | .w => 2 | .x => 6 | .v => 10

theorem loops_complete {n : Node} {i : Nat} {t : List Evt} (h : G o n i t) :
    ∀ g : Regs, g.i = i → ∃ c', Star o us codeLoops (pcLoops n, g) c' ∧ codeLoops.getD c'.1 .halt = .halt ∧
      c'.2.tr = g.tr ++ t := by
  induction h with
  | u _ ih =>
    intro g hg
    obtain ⟨c', h1, h2, h3⟩ := ih { g with tr := g.tr ++ [.u] } hg
    exact ⟨c', .cons rfl h1, h2, by simpa using h3⟩
  | wExit h0 =>
    intro g hg
    subst hg
    refine ⟨(14, { g with i := g.i + 1, loop := false, tr := g.tr ++ [.w] ++ [.wc] }), ?_, rfl, by simp⟩
    exact .cons rfl (.cons rfl (.one (by simp [step, codeLoops, Test.eval, Regs.setVar, pcLoops, h0])))
  | wLoop h1 _ ih =>
    intro g hg
    subst hg
    obtain ⟨c', k1, k2, k3⟩ := ih { g with i := g.i + 1, loop := true, tr := g.tr ++ [.w] ++ [.wc] } rfl
    refine ⟨c', .cons rfl (.cons rfl (.cons (c' := (5, { g with i := g.i + 1, loop := true, tr := g.tr ++ [.w] ++ [.wc] }))
      (by simp [step, codeLoops, Test.eval, Regs.setVar, pcLoops, h1]) (.cons rfl (.cons rfl k1)))), k2, ?_⟩
    simpa using k3
  | wFwd h0 h1 _ ih =>
    intro g hg
    subst hg
    obtain ⟨c', k1, k2, k3⟩ := ih { g with i := g.i + 1, loop := false, tr := g.tr ++ [.w] ++ [.wc] } rfl
    refine ⟨c', .cons rfl (.cons rfl (.cons (c' := (5, { g with i := g.i + 1, loop := false, tr := g.tr ++ [.w] ++ [.wc] }))
      (by simp [step, codeLoops, Test.eval, Regs.setVar, pcLoops, h0, h1]) (.cons rfl k1))), k2, ?_⟩
    simpa using k3
  | xExit h0 =>
    intro g hg
    subst hg
    refine ⟨(14, { g with i := g.i + 1, loop := false, tr := g.tr ++ [.x] ++ [.xc] }), ?_, rfl, by simp⟩
    exact .cons rfl (.cons rfl (.one (by simp [step, codeLoops, Test.eval, Regs.setVar, pcLoops, h0])))
  | xLoop h1 _ ih =>
    intro g hg
    subst hg
    obtain ⟨c', k1, k2, k3⟩ := ih { g with i := g.i + 1, loop := true, tr := g.tr ++ [.x] ++ [.xc] } rfl
    refine ⟨c', .cons rfl (.cons rfl (.cons (c' := (9, { g with i := g.i + 1, loop := true, tr := g.tr ++ [.x] ++ [.xc] }))
      (by simp [step, codeLoops, Test.eval, Regs.setVar, pcLoops, h1]) (.cons rfl (.cons rfl k1)))), k2, ?_⟩
    simpa using k3
  | xFwd h0 h1 _ ih =>
    intro g hg
    subst hg
    obtain ⟨c', k1, k2, k3⟩ := ih { g with i := g.i + 1, loop := false, tr := g.tr ++ [.x] ++ [.xc] } rfl
    refine ⟨c', .cons rfl (.cons rfl (.cons (c' := (9, { g with i := g.i + 1, loop := false, tr := g.tr ++ [.x] ++ [.xc] }))
      (by simp [step, codeLoops, Test.eval, Regs.setVar, pcLoops, h0, h1]) (.cons rfl k1))), k2, ?_⟩
    simpa using k3
  | v _ ih =>
    intro g hg
    obtain ⟨c', k1, k2, k3⟩ := ih { g with tr := g.tr ++ [.v] } hg
    exact ⟨c', .cons rfl (.cons rfl k1), k2, by simpa using k3⟩

/-- `irreducible_loops` halts with the call trace `t` exactly when the CFG semantics of Figure 4 does. -/
theorem loops_iff (t : List Evt) : Halts o us codeLoops t ↔ Cfg o us t := by
  constructor
  · rintro ⟨c, hs, hh, ht⟩
    obtain ⟨d, hd, hm⟩ := star_sound (o := o) (us := us) (code := codeLoops) (Inv := invLoops)
      (Mean := meanLoops o us) (fun c c' hi h => loops_inv o us c c' hi h) (fun c c' hi h => loops_step o us c c' hi h)
      (fun c _ hh => by
        obtain ⟨pc, g⟩ := c
        match pc with
        | 0 => simp [codeLoops] at hh
        | 1 => simp [codeLoops] at hh
        | 2 => simp [codeLoops] at hh
        | 3 => simp [codeLoops] at hh
        | 4 => simp [codeLoops] at hh
        | 5 => simp [codeLoops] at hh
        | 6 => simp [codeLoops] at hh
        | 7 => simp [codeLoops] at hh
        | 8 => simp [codeLoops] at hh
        | 9 => simp [codeLoops] at hh
        | 10 => simp [codeLoops] at hh
        | 11 => simp [codeLoops] at hh
        | 12 => simp [codeLoops] at hh
        | 13 => simp [codeLoops] at hh
        | 14 => rfl
        | n + 15 => rfl) (0, ⟨0, false, false, false, []⟩) c hs (by simp [invLoops]) hh
    have hdt : d = t := by rw [← ht, hd]; simp
    subst hdt
    exact hm
  · intro h
    unfold Cfg at h
    by_cases hus : us = true
    · simp [hus] at h
      obtain ⟨c', k1, k2, k3⟩ := loops_complete o us h ⟨0, false, false, false, []⟩ rfl
      exact ⟨c', .cons (by simp [step, codeLoops, Test.eval, Regs.setVar, pcLoops, hus, pcLoops]) k1, k2, by simpa using k3⟩
    · simp [hus] at h
      obtain ⟨c', k1, k2, k3⟩ := loops_complete o us h ⟨0, false, false, false, []⟩ rfl
      exact ⟨c', .cons (by simp [step, codeLoops, Test.eval, Regs.setVar, pcLoops, hus, pcLoops]) k1, k2, by simpa using k3⟩

end SmcIrred.Struct
