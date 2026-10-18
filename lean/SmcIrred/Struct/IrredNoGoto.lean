module

public import SmcIrred.Struct.Machine

public section

set_option linter.unusedSimpArgs false

namespace SmcIrred.Struct

variable (o : Nat → Nat) (us : Bool)

/-- Remaining call trace as the CFG semantics `G` says, for each instruction address of `codeNoGoto`. -/
@[expose] def meanNG : Nat × Regs → List Evt → Prop
  | (0, g), t => if us then G o .u g.i t else G o .v g.i t
  | (1, g), t => if us then G o .u g.i t else G o .v g.i t
  | (2, g), t => if us then G o .u g.i t else G o .v g.i t
  | (3, g), t => if g.vFirst then (if g.vFirst then G o .v g.i t else G o .w g.i t) else G o .u g.i t
  | (4, g), t => G o .u g.i t
  | (5, g), t => if g.vFirst then G o .v g.i t else G o .w g.i t
  | (6, g), t => G o .w g.i t
  | (7, g), t => G o .w g.i (.w :: t)
  | (8, g), t => G o .w g.i (.w :: t)
  | (9, g), t => if g.loop then (if g.isEnd then t = [] else G o .u g.i t) else G o .x g.i t
  | (10, g), t => if g.vFirst then G o .v g.i t else G o .x g.i t
  | (11, g), t => G o .x g.i t
  | (12, g), t => G o .x g.i (.x :: t)
  | (13, g), t => G o .x g.i (.x :: t)
  | (14, g), t => if g.loop then (if g.isEnd then t = [] else G o .w g.i t) else G o .v g.i t
  | (15, g), t => G o .v g.i t
  | (16, g), t => G o .x g.i t
  | (17, g), t => G o .x g.i t
  | (18, g), t => if g.isEnd then t = [] else G o .w g.i t
  | (19, g), t => if g.isEnd then t = [] else G o .u g.i t
  | _, t => t = []

/-- The invariants of `codeNoGoto`: `is_end` is false except just after a `switch` with `EXIT`; `loop` has just been
cleared at the `switch`es; `v_first` is false after the first `v()`. -/
@[expose] def invNG (c : Nat × Regs) : Prop :=
  (c.1 ∈ [1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 12, 13, 15, 16, 17] → c.2.isEnd = false) ∧
  (c.1 ∈ [9, 14] → c.2.isEnd = true → c.2.loop = true) ∧
  (c.1 ∈ [8, 13] → c.2.loop = false) ∧
  (c.1 ∈ [4, 6, 7, 8, 9, 11, 12, 13, 14, 17, 18, 19] → c.2.vFirst = false) ∧
  (c.1 = 2 → c.2.vFirst = true)

theorem ng_inv (c c' : Nat × Regs) (hi : invNG c) (h : step o us codeNoGoto c = some c') : invNG c' := by
  obtain ⟨pc, g⟩ := c
  obtain ⟨i1, i2, i3, i4, i5⟩ := hi
  simp only at i1 i2 i3 i4 i5
  match pc with
  | 0 => simp [step, codeNoGoto, Regs.setVar] at h; subst h; simp [invNG]
  | 1 => simp [step, codeNoGoto, Regs.setVar] at h; subst h; simp_all [invNG]
  | 2 =>
    cases hus : us <;> simp [step, codeNoGoto, Regs.setVar, Test.eval, hus] at h <;> subst h <;> simp_all [invNG]
  | 3 =>
    cases hv : g.vFirst <;> simp [step, codeNoGoto, Test.eval, hv] at h <;> subst h <;> simp_all [invNG]
  | 4 => simp [step, codeNoGoto] at h; subst h; simp_all [invNG]
  | 5 =>
    cases hv : g.vFirst <;> simp [step, codeNoGoto, Test.eval, hv] at h <;> subst h <;> simp_all [invNG]
  | 6 => simp [step, codeNoGoto] at h; subst h; simp_all [invNG]
  | 7 => simp [step, codeNoGoto, Regs.setVar] at h; subst h; simp_all [invNG]
  | 8 =>
    simp only [step, codeNoGoto] at h
    by_cases h0 : o g.i = 0
    · simp [h0] at h; subst h; simp_all [invNG]
    · by_cases h1 : o g.i = 1
      · simp [h0, h1] at h; subst h; simp_all [invNG]
      · simp [h0, h1] at h; subst h; simp_all [invNG]
  | 9 =>
    cases hl : g.loop <;> simp [step, codeNoGoto, Test.eval, hl] at h <;> subst h <;> simp_all [invNG]
  | 10 =>
    cases hv : g.vFirst <;> simp [step, codeNoGoto, Test.eval, hv] at h <;> subst h <;> simp_all [invNG]
  | 11 => simp [step, codeNoGoto] at h; subst h; simp_all [invNG]
  | 12 => simp [step, codeNoGoto, Regs.setVar] at h; subst h; simp_all [invNG]
  | 13 =>
    simp only [step, codeNoGoto] at h
    by_cases h0 : o g.i = 0
    · simp [h0] at h; subst h; simp_all [invNG]
    · by_cases h1 : o g.i = 1
      · simp [h0, h1] at h; subst h; simp_all [invNG]
      · simp [h0, h1] at h; subst h; simp_all [invNG]
  | 14 =>
    cases hl : g.loop <;> simp [step, codeNoGoto, Test.eval, hl] at h <;> subst h <;> simp_all [invNG]
  | 15 => simp [step, codeNoGoto] at h; subst h; simp_all [invNG]
  | 16 => simp [step, codeNoGoto, Regs.setVar] at h; subst h; simp_all [invNG]
  | 17 => simp [step, codeNoGoto] at h; subst h; simp_all [invNG]
  | 18 =>
    cases he : g.isEnd <;> simp [step, codeNoGoto, Test.eval, he] at h <;> subst h <;> simp_all [invNG]
  | 19 =>
    cases he : g.isEnd <;> simp [step, codeNoGoto, Test.eval, he] at h <;> subst h <;> simp_all [invNG]
  | 20 => simp [step, codeNoGoto] at h
  | n + 21 => simp [step, codeNoGoto] at h

theorem ng_step (c c' : Nat × Regs) (hi : invNG c) (h : step o us codeNoGoto c = some c') :
    ∃ d, c'.2.tr = c.2.tr ++ d ∧ ∀ t', meanNG o us c' t' → meanNG o us c (d ++ t') := by
  obtain ⟨pc, g⟩ := c
  obtain ⟨i1, i2, i3, i4, i5⟩ := hi
  simp only at i1 i2 i3 i4 i5
  match pc with
  | 0 => simp [step, codeNoGoto, Regs.setVar] at h; subst h; exact ⟨[], by simp, fun t' h' => by simpa [meanNG] using h'⟩
  | 1 => simp [step, codeNoGoto, Regs.setVar] at h; subst h; exact ⟨[], by simp, fun t' h' => by simpa [meanNG] using h'⟩
  | 2 =>
    cases hus : us <;> simp [step, codeNoGoto, Regs.setVar, Test.eval, hus] at h <;> subst h <;>
      exact ⟨[], by simp, fun t' h' => by simp_all [meanNG]⟩
  | 3 =>
    cases hv : g.vFirst <;> simp [step, codeNoGoto, Test.eval, hv] at h <;> subst h <;>
      exact ⟨[], by simp, fun t' h' => by simp_all [meanNG]⟩
  | 4 =>
    simp [step, codeNoGoto] at h; subst h
    exact ⟨[.u], rfl, fun t' h' => by simp_all [meanNG]; exact .u h'⟩
  | 5 =>
    cases hv : g.vFirst <;> simp [step, codeNoGoto, Test.eval, hv] at h <;> subst h <;>
      exact ⟨[], by simp, fun t' h' => by simp_all [meanNG]⟩
  | 6 =>
    simp [step, codeNoGoto] at h; subst h
    exact ⟨[.w], rfl, fun t' h' => by simpa [meanNG] using h'⟩
  | 7 =>
    simp [step, codeNoGoto, Regs.setVar] at h; subst h
    exact ⟨[], by simp, fun t' h' => by simpa [meanNG] using h'⟩
  | 8 =>
    simp only [step, codeNoGoto] at h
    by_cases h0 : o g.i = 0
    · simp [h0] at h; subst h
      exact ⟨[.wc], rfl, fun t' h' => by simp [meanNG] at h' ⊢; subst h'; exact .wExit h0⟩
    · by_cases h1 : o g.i = 1
      · simp [h0, h1] at h; subst h
        exact ⟨[.wc], rfl, fun t' h' => by simp [meanNG, i1 (by simp)] at h' ⊢; exact .wLoop h1 h'⟩
      · simp [h0, h1] at h; subst h
        exact ⟨[.wc], rfl, fun t' h' => by simp [meanNG, i1 (by simp), i3 (by simp)] at h' ⊢; exact .wFwd h0 h1 h'⟩
  | 9 =>
    cases hl : g.loop <;> simp [step, codeNoGoto, Test.eval, hl] at h <;> subst h <;>
      exact ⟨[], by simp, fun t' h' => by simp_all [meanNG]⟩
  | 10 =>
    cases hv : g.vFirst <;> simp [step, codeNoGoto, Test.eval, hv] at h <;> subst h <;>
      exact ⟨[], by simp, fun t' h' => by simp_all [meanNG]⟩
  | 11 =>
    simp [step, codeNoGoto] at h; subst h
    exact ⟨[.x], rfl, fun t' h' => by simpa [meanNG] using h'⟩
  | 12 =>
    simp [step, codeNoGoto, Regs.setVar] at h; subst h
    exact ⟨[], by simp, fun t' h' => by simpa [meanNG] using h'⟩
  | 13 =>
    simp only [step, codeNoGoto] at h
    by_cases h0 : o g.i = 0
    · simp [h0] at h; subst h
      exact ⟨[.xc], rfl, fun t' h' => by simp [meanNG] at h' ⊢; subst h'; exact .xExit h0⟩
    · by_cases h1 : o g.i = 1
      · simp [h0, h1] at h; subst h
        exact ⟨[.xc], rfl, fun t' h' => by simp [meanNG, i1 (by simp)] at h' ⊢; exact .xLoop h1 h'⟩
      · simp [h0, h1] at h; subst h
        exact ⟨[.xc], rfl, fun t' h' => by simp [meanNG, i1 (by simp), i3 (by simp)] at h' ⊢; exact .xFwd h0 h1 h'⟩
  | 14 =>
    cases hl : g.loop <;> simp [step, codeNoGoto, Test.eval, hl] at h <;> subst h <;>
      exact ⟨[], by simp, fun t' h' => by simp_all [meanNG]⟩
  | 15 =>
    simp [step, codeNoGoto] at h; subst h
    exact ⟨[.v], rfl, fun t' h' => by simp only [meanNG] at h' ⊢; exact .v h'⟩
  | 16 =>
    simp [step, codeNoGoto, Regs.setVar] at h; subst h
    exact ⟨[], by simp, fun t' h' => by simpa [meanNG] using h'⟩
  | 17 =>
    simp [step, codeNoGoto] at h; subst h
    exact ⟨[], by simp, fun t' h' => by simp_all [meanNG]⟩
  | 18 =>
    cases he : g.isEnd <;> simp [step, codeNoGoto, Test.eval, he] at h <;> subst h <;>
      exact ⟨[], by simp, fun t' h' => by simp_all [meanNG]⟩
  | 19 =>
    cases he : g.isEnd <;> simp [step, codeNoGoto, Test.eval, he] at h <;> subst h <;>
      exact ⟨[], by simp, fun t' h' => by simp_all [meanNG]⟩
  | 20 => simp [step, codeNoGoto] at h
  | n + 21 => simp [step, codeNoGoto] at h

/-- Entry address of a node (`u` at the outer loop, `w` at the middle loop, `x` at the inner loop, `v` at its call). -/
@[expose] def pcNG : Node → Nat
  | .u => 3 | .w => 5 | .x => 10 | .v => 15

local macro "stp " c:term " ⟹ " "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| refine .cons (c' := $c) (by simp [step, codeNoGoto, Test.eval, Regs.setVar, pcNG, $hs,*]) ?_)

theorem ng_complete {n : Node} {i : Nat} {t : List Evt} (h : G o n i t) :
    ∀ g : Regs, g.i = i → g.isEnd = false → (n ≠ .v → g.vFirst = false) →
      ∃ c', Star o us codeNoGoto (pcNG n, g) c' ∧ codeNoGoto.getD c'.1 .halt = .halt ∧ c'.2.tr = g.tr ++ t := by
  induction h with
  | u _ ih =>
    intro g hg he hvf
    have hv := hvf (by simp)
    obtain ⟨c', k1, k2, k3⟩ := ih { g with tr := g.tr ++ [.u] } hg he (fun _ => hv)
    refine ⟨c', ?_, k2, by simpa using k3⟩
    stp (4, g) ⟹ [hv]
    exact .cons rfl k1
  | wExit h0 =>
    intro g hg he hvf
    subst hg
    have hv := hvf (by simp)
    refine ⟨(20, { g with i := g.i + 1, loop := true, isEnd := true, tr := g.tr ++ [.w] ++ [.wc] }), ?_, rfl, by simp⟩
    stp (6, g) ⟹ [hv]
    stp (7, { g with tr := g.tr ++ [.w] }) ⟹ []
    stp (8, { g with loop := false, tr := g.tr ++ [.w] }) ⟹ []
    stp (9, { g with i := g.i + 1, loop := true, isEnd := true, tr := g.tr ++ [.w] ++ [.wc] }) ⟹ [h0]
    stp (19, { g with i := g.i + 1, loop := true, isEnd := true, tr := g.tr ++ [.w] ++ [.wc] }) ⟹ []
    exact .one (by simp [step, codeNoGoto, Test.eval])
  | wLoop h1 _ ih =>
    intro g hg he hvf
    subst hg
    have hv := hvf (by simp)
    have h0 : o g.i ≠ 0 := by omega
    obtain ⟨c', k1, k2, k3⟩ := ih { g with i := g.i + 1, loop := true, tr := g.tr ++ [.w] ++ [.wc] } rfl he (fun _ => hv)
    refine ⟨c', ?_, k2, by simpa using k3⟩
    stp (6, g) ⟹ [hv]
    stp (7, { g with tr := g.tr ++ [.w] }) ⟹ []
    stp (8, { g with loop := false, tr := g.tr ++ [.w] }) ⟹ []
    stp (9, { g with i := g.i + 1, loop := true, tr := g.tr ++ [.w] ++ [.wc] }) ⟹ [h0, h1]
    stp (19, { g with i := g.i + 1, loop := true, tr := g.tr ++ [.w] ++ [.wc] }) ⟹ []
    stp (3, { g with i := g.i + 1, loop := true, tr := g.tr ++ [.w] ++ [.wc] }) ⟹ [he]
    exact k1
  | wFwd h0 h1 _ ih =>
    intro g hg he hvf
    subst hg
    have hv := hvf (by simp)
    obtain ⟨c', k1, k2, k3⟩ := ih { g with i := g.i + 1, loop := false, tr := g.tr ++ [.w] ++ [.wc] } rfl he (fun _ => hv)
    refine ⟨c', ?_, k2, by simpa using k3⟩
    stp (6, g) ⟹ [hv]
    stp (7, { g with tr := g.tr ++ [.w] }) ⟹ []
    stp (8, { g with loop := false, tr := g.tr ++ [.w] }) ⟹ []
    stp (9, { g with i := g.i + 1, loop := false, tr := g.tr ++ [.w] ++ [.wc] }) ⟹ [h0, h1]
    stp (10, { g with i := g.i + 1, loop := false, tr := g.tr ++ [.w] ++ [.wc] }) ⟹ []
    exact k1
  | xExit h0 =>
    intro g hg he hvf
    subst hg
    have hv := hvf (by simp)
    refine ⟨(20, { g with i := g.i + 1, loop := true, isEnd := true, tr := g.tr ++ [.x] ++ [.xc] }), ?_, rfl, by simp⟩
    stp (11, g) ⟹ [hv]
    stp (12, { g with tr := g.tr ++ [.x] }) ⟹ []
    stp (13, { g with loop := false, tr := g.tr ++ [.x] }) ⟹ []
    stp (14, { g with i := g.i + 1, loop := true, isEnd := true, tr := g.tr ++ [.x] ++ [.xc] }) ⟹ [h0]
    stp (18, { g with i := g.i + 1, loop := true, isEnd := true, tr := g.tr ++ [.x] ++ [.xc] }) ⟹ []
    stp (19, { g with i := g.i + 1, loop := true, isEnd := true, tr := g.tr ++ [.x] ++ [.xc] }) ⟹ []
    exact .one (by simp [step, codeNoGoto, Test.eval])
  | xLoop h1 _ ih =>
    intro g hg he hvf
    subst hg
    have hv := hvf (by simp)
    have h0 : o g.i ≠ 0 := by omega
    obtain ⟨c', k1, k2, k3⟩ := ih { g with i := g.i + 1, loop := true, tr := g.tr ++ [.x] ++ [.xc] } rfl he (fun _ => hv)
    refine ⟨c', ?_, k2, by simpa using k3⟩
    stp (11, g) ⟹ [hv]
    stp (12, { g with tr := g.tr ++ [.x] }) ⟹ []
    stp (13, { g with loop := false, tr := g.tr ++ [.x] }) ⟹ []
    stp (14, { g with i := g.i + 1, loop := true, tr := g.tr ++ [.x] ++ [.xc] }) ⟹ [h0, h1]
    stp (18, { g with i := g.i + 1, loop := true, tr := g.tr ++ [.x] ++ [.xc] }) ⟹ []
    stp (5, { g with i := g.i + 1, loop := true, tr := g.tr ++ [.x] ++ [.xc] }) ⟹ [he]
    exact k1
  | xFwd h0 h1 _ ih =>
    intro g hg he hvf
    subst hg
    have hv := hvf (by simp)
    obtain ⟨c', k1, k2, k3⟩ := ih { g with i := g.i + 1, loop := false, tr := g.tr ++ [.x] ++ [.xc] } rfl he (fun h => absurd rfl h)
    refine ⟨c', ?_, k2, by simpa using k3⟩
    stp (11, g) ⟹ [hv]
    stp (12, { g with tr := g.tr ++ [.x] }) ⟹ []
    stp (13, { g with loop := false, tr := g.tr ++ [.x] }) ⟹ []
    stp (14, { g with i := g.i + 1, loop := false, tr := g.tr ++ [.x] ++ [.xc] }) ⟹ [h0, h1]
    stp (15, { g with i := g.i + 1, loop := false, tr := g.tr ++ [.x] ++ [.xc] }) ⟹ []
    exact k1
  | v _ ih =>
    intro g hg he _
    obtain ⟨c', k1, k2, k3⟩ := ih { g with vFirst := false, tr := g.tr ++ [.v] } hg he (fun _ => rfl)
    refine ⟨c', ?_, k2, by simpa using k3⟩
    stp (16, { g with tr := g.tr ++ [.v] }) ⟹ []
    stp (17, { g with vFirst := false, tr := g.tr ++ [.v] }) ⟹ []
    stp (10, { g with vFirst := false, tr := g.tr ++ [.v] }) ⟹ []
    exact k1

/-- `irreducible_loops_no_goto` halts with the call trace `t` exactly when the CFG semantics of Figure 4 does. -/
theorem ng_iff (t : List Evt) : Halts o us codeNoGoto t ↔ Cfg o us t := by
  constructor
  · rintro ⟨c, hs, hh, ht⟩
    obtain ⟨d, hd, hm⟩ := star_sound (o := o) (us := us) (code := codeNoGoto) (Inv := invNG)
      (Mean := meanNG o us) (fun c c' hi h => ng_inv o us c c' hi h) (fun c c' hi h => ng_step o us c c' hi h)
      (fun c _ hh => by
        obtain ⟨pc, g⟩ := c
        match pc with
        | 0 => simp [codeNoGoto] at hh
        | 1 => simp [codeNoGoto] at hh
        | 2 => simp [codeNoGoto] at hh
        | 3 => simp [codeNoGoto] at hh
        | 4 => simp [codeNoGoto] at hh
        | 5 => simp [codeNoGoto] at hh
        | 6 => simp [codeNoGoto] at hh
        | 7 => simp [codeNoGoto] at hh
        | 8 => simp [codeNoGoto] at hh
        | 9 => simp [codeNoGoto] at hh
        | 10 => simp [codeNoGoto] at hh
        | 11 => simp [codeNoGoto] at hh
        | 12 => simp [codeNoGoto] at hh
        | 13 => simp [codeNoGoto] at hh
        | 14 => simp [codeNoGoto] at hh
        | 15 => simp [codeNoGoto] at hh
        | 16 => simp [codeNoGoto] at hh
        | 17 => simp [codeNoGoto] at hh
        | 18 => simp [codeNoGoto] at hh
        | 19 => simp [codeNoGoto] at hh
        | 20 => rfl
        | n + 21 => rfl) (0, ⟨0, false, false, false, []⟩) c hs (by simp [invNG]) hh
    have hdt : d = t := by rw [← ht, hd]; simp
    subst hdt
    exact hm
  · intro h
    unfold Cfg at h
    by_cases hus : us = true
    · simp [hus] at h
      obtain ⟨c', k1, k2, k3⟩ := ng_complete o us h ⟨0, false, false, false, []⟩ rfl rfl (fun _ => rfl)
      refine ⟨c', ?_, k2, by simpa using k3⟩
      stp (1, ⟨0, false, false, false, []⟩) ⟹ []
      stp (2, ⟨0, false, false, true, []⟩) ⟹ []
      stp (3, ⟨0, false, false, false, []⟩) ⟹ [hus]
      exact k1
    · simp [hus] at h
      obtain ⟨c', k1, k2, k3⟩ := ng_complete o us h ⟨0, false, false, true, []⟩ rfl rfl (fun h => absurd rfl h)
      refine ⟨c', ?_, k2, by simpa using k3⟩
      stp (1, ⟨0, false, false, false, []⟩) ⟹ []
      stp (2, ⟨0, false, false, true, []⟩) ⟹ []
      stp (3, ⟨0, false, false, true, []⟩) ⟹ [hus]
      stp (5, ⟨0, false, false, true, []⟩) ⟹ []
      stp (10, ⟨0, false, false, true, []⟩) ⟹ []
      stp (15, ⟨0, false, false, true, []⟩) ⟹ []
      exact k1

end SmcIrred.Struct
