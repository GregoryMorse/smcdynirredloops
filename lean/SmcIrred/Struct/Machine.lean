module

public import SmcIrred.Spec.IrredLoop

public section

namespace SmcIrred.Struct

variable {o : Nat → Nat} {us : Bool} {code : List Ins}

theorem Star.trans {a b c : Nat × Regs} (h1 : Star o us code a b) (h2 : Star o us code b c) : Star o us code a c := by
  induction h1 with
  | refl => exact h2
  | cons hs _ ih => exact .cons hs (ih h2)

theorem Star.one {a b : Nat × Regs} (h : step o us code a = some b) : Star o us code a b := .cons h (.refl b)

/-- Soundness shape: if every step from a configuration satisfying `Inv` stays in `Inv`, and `Mean` is
pulled back along steps (with the emitted events), then a run to a halt gives `Mean`. -/
theorem star_sound {Inv : Nat × Regs → Prop} {Mean : Nat × Regs → List Evt → Prop}
    (hinv : ∀ c c', Inv c → step o us code c = some c' → Inv c')
    (hstep : ∀ c c', Inv c → step o us code c = some c' →
      ∃ d, c'.2.tr = c.2.tr ++ d ∧ ∀ t', Mean c' t' → Mean c (d ++ t'))
    (hhalt : ∀ c, Inv c → code.getD c.1 .halt = .halt → Mean c []) :
    ∀ c c', Star o us code c c' → Inv c → code.getD c'.1 .halt = .halt →
      ∃ d, c'.2.tr = c.2.tr ++ d ∧ Mean c d := by
  intro c c' h
  induction h with
  | refl c => intro hi hh; exact ⟨[], by simp, by simpa using hhalt c hi hh⟩
  | @cons a b z hs _ ih =>
    intro hi hh
    obtain ⟨d1, hd1, hm1⟩ := hstep a b hi hs
    obtain ⟨d2, hd2, hm2⟩ := ih (hinv a b hi hs) hh
    refine ⟨d1 ++ d2, ?_, hm1 d2 hm2⟩
    rw [hd2, hd1, List.append_assoc]

theorem step_halt {c : Nat × Regs} (h : code.getD c.1 .halt = .halt) : step o us code c = none := by
  obtain ⟨pc, g⟩ := c
  simp only at h
  simp only [step]
  rw [h]

/-- The machine is deterministic: two runs from the same configuration that stop at a `halt` end in the same
configuration. -/
theorem star_det {c a b : Nat × Regs} (h1 : Star o us code c a) (ha : code.getD a.1 .halt = .halt)
    (h2 : Star o us code c b) (hb : code.getD b.1 .halt = .halt) : a = b := by
  induction h1 generalizing b with
  | refl c =>
    cases h2 with
    | refl => rfl
    | cons hs _ => rw [step_halt ha] at hs; cases hs
  | cons hs _ ih =>
    cases h2 with
    | refl => rw [step_halt hb] at hs; cases hs
    | cons hs2 h2' =>
      rw [hs] at hs2
      cases hs2
      exact ih ha h2' hb

theorem halts_unique {t t' : List Evt} (h : Halts o us code t) (h' : Halts o us code t') : t = t' := by
  obtain ⟨c, s1, h1, e1⟩ := h
  obtain ⟨c', s2, h2, e2⟩ := h'
  have := star_det s1 h1 s2 h2
  subst this
  rw [← e1, ← e2]

end SmcIrred.Struct
