module

public import SmcIrred.Lang.Insert1

public section

namespace SmcIrred.Lang

/-! # Shifted windows of code (G32 a, Figures 5(c), 6(c))

A window `[a0, a0 + len)` of the original code `P` sits in `Q` shifted by `d`.  The original keeps the toggled variable at
`v0`, the other code at `v1` (the loop of `while (trueThenFalse)` runs the window with the variable toggled).  Conditions
in the window do not read the variable (`pure`).  If the continuations after the window agree (`hexit`), the two codes
halt with the same results from every address of the window. -/

structure Win (P Q : List Instr) (sol : Nat → Bool) (env : Bool) (a0 len d : Nat) (v0 v1 : Bool) : Prop where
  body : ∀ a, a0 ≤ a → a < a0 + len → Q.getD (a + d) .halt = shiftI d (P.getD a .halt)
  tgt : ∀ a t, a0 ≤ a → a < a0 + len → (P.getD a .halt).target = some t → a0 ≤ t ∧ t ≤ a0 + len
  pure : ∀ a k t, a0 ≤ a → a < a0 + len → P.getD a .halt = .jmpIf k t →
    ∃ b, k.eval sol env v0 = (b, v0) ∧ k.eval sol env v1 = (b, v1)
  nohalt : ∀ a, a0 ≤ a → a < a0 + len → P.getD a .halt ≠ .halt

variable {P Q : List Instr} {sol : Nat → Bool} {env : Bool} {a0 len d : Nat} {v0 v1 : Bool}

theorem Win.fwd (w : Win P Q sol env a0 len d v0 v1)
    (hexit : ∀ tr r, Halts P sol env (a0 + len) v0 tr r → Halts Q sol env (a0 + len + d) v1 tr r)
    {pc : Nat} {v : Bool} {tr : List Nat} {r : List Nat × Bool} (hp : Halts P sol env pc v tr r) :
    a0 ≤ pc → pc ≤ a0 + len → v = v0 → Halts Q sol env (pc + d) v1 tr r := by
  induction hp with
  | @halt pc v tr hi =>
    intro h1 h2 hv
    subst hv
    by_cases hpc : pc = a0 + len
    · subst hpc; exact hexit _ _ (.halt hi)
    · exact absurd hi (w.nohalt pc h1 (by omega))
  | @blk pc a v tr r hi hrest ih =>
    intro h1 h2 hv
    subst hv
    by_cases hpc : pc = a0 + len
    · subst hpc; exact hexit _ _ (.blk hi hrest)
    · have hq : Q.getD (pc + d) .halt = .blk a := by rw [w.body pc h1 (by omega), hi]; rfl
      exact .blk hq (by
        have := ih (by omega) (by omega) rfl
        rwa [show pc + 1 + d = pc + d + 1 by omega] at this)
  | @jmp pc t v tr r hi hrest ih =>
    intro h1 h2 hv
    subst hv
    by_cases hpc : pc = a0 + len
    · subst hpc; exact hexit _ _ (.jmp hi hrest)
    · have hq : Q.getD (pc + d) .halt = .jmp (t + d) := by rw [w.body pc h1 (by omega), hi]; rfl
      have ht := w.tgt pc t h1 (by omega) (by rw [hi]; rfl)
      exact .jmp hq (ih ht.1 ht.2 rfl)
  | @jmpIf pc t kk v tr r hi hrest ih =>
    intro h1 h2 hv
    subst hv
    by_cases hpc : pc = a0 + len
    · subst hpc; exact hexit _ _ (.jmpIf hi hrest)
    · have hq : Q.getD (pc + d) .halt = .jmpIf kk (t + d) := by rw [w.body pc h1 (by omega), hi]; rfl
      have ht := w.tgt pc t h1 (by omega) (by rw [hi]; rfl)
      obtain ⟨b, e0, e1⟩ := w.pure pc kk t h1 (by omega) hi
      refine .jmpIf hq ?_
      rw [e1]
      rw [e0] at ih hrest
      cases b
      · simp only [Bool.false_eq_true, ↓reduceIte] at ih hrest ⊢
        have := ih (by omega) (by omega) (by first | rfl | trivial)
        rwa [show pc + 1 + d = pc + d + 1 by omega] at this
      · simp only [↓reduceIte] at ih hrest ⊢
        exact ih ht.1 ht.2 (by first | rfl | trivial)

theorem Win.bwd (w : Win P Q sol env a0 len d v0 v1)
    (hexit : ∀ tr r, Halts Q sol env (a0 + len + d) v1 tr r → Halts P sol env (a0 + len) v0 tr r)
    {pcQ : Nat} {v : Bool} {tr : List Nat} {r : List Nat × Bool} (hq : Halts Q sol env pcQ v tr r) :
    ∀ pc, pcQ = pc + d → a0 ≤ pc → pc ≤ a0 + len → v = v1 → Halts P sol env pc v0 tr r := by
  induction hq with
  | @halt pcQ v tr hi =>
    intro pc hpc h1 h2 hv
    subst hv; subst hpc
    by_cases hp : pc = a0 + len
    · subst hp; exact hexit _ _ (.halt hi)
    · have hb := w.body pc h1 (by omega)
      rw [hi] at hb
      cases hp0 : P.getD pc .halt <;> rw [hp0] at hb <;> simp [shiftI] at hb
      exact absurd hp0 (w.nohalt pc h1 (by omega))
  | @blk pcQ a v tr r hi hrest ih =>
    intro pc hpc h1 h2 hv
    subst hv; subst hpc
    by_cases hp : pc = a0 + len
    · subst hp; exact hexit _ _ (.blk hi hrest)
    · have hb := w.body pc h1 (by omega)
      rw [hi] at hb
      cases hp0 : P.getD pc .halt <;> rw [hp0] at hb <;> simp [shiftI] at hb
      rename_i b'
      subst hb
      exact .blk hp0 (ih (pc + 1) (by omega) (by omega) (by omega) rfl)
  | @jmp pcQ t' v tr r hi hrest ih =>
    intro pc hpc h1 h2 hv
    subst hv; subst hpc
    by_cases hp : pc = a0 + len
    · subst hp; exact hexit _ _ (.jmp hi hrest)
    · have hb := w.body pc h1 (by omega)
      rw [hi] at hb
      cases hp0 : P.getD pc .halt <;> rw [hp0] at hb <;> simp [shiftI] at hb
      rename_i t
      have ht := w.tgt pc t h1 (by omega) (by rw [hp0]; rfl)
      subst hb
      exact .jmp hp0 (ih t rfl ht.1 ht.2 rfl)
  | @jmpIf pcQ t' kk v tr r hi hrest ih =>
    intro pc hpc h1 h2 hv
    subst hv; subst hpc
    by_cases hp : pc = a0 + len
    · subst hp; exact hexit _ _ (.jmpIf hi hrest)
    · have hb := w.body pc h1 (by omega)
      rw [hi] at hb
      cases hp0 : P.getD pc .halt <;> rw [hp0] at hb <;> simp [shiftI] at hb
      rename_i k0 t
      obtain ⟨hk, ht'⟩ := hb
      subst hk; subst ht'
      have ht := w.tgt pc t h1 (by omega) (by rw [hp0]; rfl)
      obtain ⟨b, e0, e1⟩ := w.pure pc kk t h1 (by omega) hp0
      refine .jmpIf hp0 ?_
      rw [e0]
      rw [e1] at ih hrest
      cases b
      · simp only [Bool.false_eq_true, ↓reduceIte] at ih hrest ⊢
        exact ih (pc + 1) (by omega) (by omega) (by omega) (by first | rfl | trivial)
      · simp only [↓reduceIte] at ih hrest ⊢
        exact ih t rfl ht.1 ht.2 (by first | rfl | trivial)

end SmcIrred.Lang
