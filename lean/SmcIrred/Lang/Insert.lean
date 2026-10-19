module

public import SmcIrred.Lang.Protect

public section

namespace SmcIrred.Lang

/-! # Protecting any region of any code (R19b, G33 b, C65)

A protection inserts into flat code two conditional jumps around a region `[lo, hi)`: at `lo` the jump `if (h) goto mid`
(to the start of the second half of the region), after the region the jump `if (k) goto lo` (back to the start). When the two
conditions are false they are never taken, so the code does what it did: `insert_equiv` proves it for **every** code, every
region and every position, so the protection of any number of regions (nested, in loops, in sequence) preserves the result,
by repeated application. Instruction addresses move (`gA`), jump targets are redirected (`rmT`: a jump to `lo` runs the
entry test, a jump to `hi` runs the closing test). -/

/-- Big-step halting of flat code: from `pc` with the toggled variable `v` and the trace `tr`, the code halts with `r`. -/
inductive Halts (code : List Instr) (sol : Nat → Bool) (env : Bool) : Nat → Bool → List Nat → List Nat × Bool → Prop
  | halt {pc : Nat} {v : Bool} {tr : List Nat} : code.getD pc .halt = .halt → Halts code sol env pc v tr (tr, v)
  | blk {pc a : Nat} {v : Bool} {tr : List Nat} {r : List Nat × Bool} :
      code.getD pc .halt = .blk a → Halts code sol env (pc + 1) v (tr ++ [a]) r → Halts code sol env pc v tr r
  | jmp {pc t : Nat} {v : Bool} {tr : List Nat} {r : List Nat × Bool} :
      code.getD pc .halt = .jmp t → Halts code sol env t v tr r → Halts code sol env pc v tr r
  | jmpIf {pc t : Nat} {k : Cond} {v : Bool} {tr : List Nat} {r : List Nat × Bool} :
      code.getD pc .halt = .jmpIf k t →
      Halts code sol env (if (k.eval sol env v).1 then t else pc + 1) (k.eval sol env v).2 tr r →
      Halts code sol env pc v tr r

theorem halts_of_exec {code : List Instr} {sol : Nat → Bool} {env : Bool} : ∀ (f pc : Nat) (v : Bool) (tr : List Nat)
    (r : List Nat × Bool), exec f code sol env pc v tr = some r → Halts code sol env pc v tr r := by
  intro f
  induction f with
  | zero => intro pc v tr r h; simp [exec] at h
  | succ f ih =>
    intro pc v tr r h
    cases hi : code.getD pc .halt with
    | blk a => rw [exec_blk hi] at h; exact .blk hi (ih _ _ _ _ h)
    | jmp t => rw [exec_jmp hi] at h; exact .jmp hi (ih _ _ _ _ h)
    | jmpIf k t => rw [exec_jmpIf hi] at h; exact .jmpIf hi (ih _ _ _ _ h)
    | halt =>
      rw [exec_halt hi] at h
      cases h
      exact .halt hi

theorem exec_of_halts {code : List Instr} {sol : Nat → Bool} {env : Bool} {pc : Nat} {v : Bool} {tr : List Nat}
    {r : List Nat × Bool} (h : Halts code sol env pc v tr r) : ∃ f, exec f code sol env pc v tr = some r := by
  induction h with
  | halt hi => exact ⟨1, exec_halt hi⟩
  | blk hi _ ih => obtain ⟨f, hf⟩ := ih; exact ⟨f + 1, by rw [exec_blk hi]; exact hf⟩
  | jmp hi _ ih => obtain ⟨f, hf⟩ := ih; exact ⟨f + 1, by rw [exec_jmp hi]; exact hf⟩
  | jmpIf hi _ ih => obtain ⟨f, hf⟩ := ih; exact ⟨f + 1, by rw [exec_jmpIf hi]; exact hf⟩

theorem halts_iff_exec {code : List Instr} {sol : Nat → Bool} {env : Bool} {pc : Nat} {v : Bool} {tr : List Nat}
    {r : List Nat × Bool} : Halts code sol env pc v tr r ↔ ∃ f, exec f code sol env pc v tr = some r :=
  ⟨exec_of_halts, fun ⟨f, h⟩ => halts_of_exec f pc v tr r h⟩

/-! ### The insertion -/

/-- Where a jump target goes: a jump to `lo` runs the entry test, a jump to `hi` the closing test. -/
@[expose] def rmT (lo hi t : Nat) : Nat := if t ≤ lo then t else if t ≤ hi then t + 1 else t + 2

/-- Where an instruction address goes. -/
@[expose] def gA (lo hi a : Nat) : Nat := if a < lo then a else if a < hi then a + 1 else a + 2

@[expose] def remapI (lo hi : Nat) : Instr → Instr
  | .blk a => .blk a
  | .jmp t => .jmp (rmT lo hi t)
  | .jmpIf k t => .jmpIf k (rmT lo hi t)
  | .halt => .halt

/-- `Q` is `P` with the entry jump `if (h) goto mid + 1` inserted at `lo` and the closing jump `if (k) goto lo + 1` inserted
after the region `[lo, hi)`, all targets of `P` redirected. -/
structure InsertSpec (P Q : List Instr) (lo mid hi : Nat) (h k : Cond) : Prop where
  body : ∀ a, Q.getD (gA lo hi a) .halt = remapI lo hi (P.getD a .halt)
  entry : Q.getD lo .halt = .jmpIf h (mid + 1)
  closing : Q.getD (hi + 1) .halt = .jmpIf k (lo + 1)

/-- The related states: the same place, the entry test of a region about to start, the closing test of a region just run. -/
@[expose] def InsRel (lo hi pcP pcQ : Nat) : Prop :=
  pcQ = gA lo hi pcP ∨ (pcP = lo ∧ pcQ = lo) ∨ (pcP = hi ∧ pcQ = hi + 1)

variable {P Q : List Instr} {lo mid hi : Nat} {h k : Cond} {sol : Nat → Bool} {env : Bool}

theorem insRel_target (hlh : lo < hi) (t : Nat) : InsRel lo hi t (rmT lo hi t) := by
  unfold InsRel rmT gA
  by_cases h1 : t < lo
  · left; simp [h1, show t ≤ lo by omega]
  · by_cases h2 : t = lo
    · right; left; simp [h2]
    · by_cases h3 : t < hi
      · left; simp [h1, h3, show ¬ t ≤ lo by omega, show t ≤ hi by omega]
      · by_cases h4 : t = hi
        · right; right; simp [h4, show ¬ hi ≤ lo by omega]
        · left; simp [h1, h3, show ¬ t ≤ lo by omega, show ¬ t ≤ hi by omega]

theorem insRel_succ (hlh : lo < hi) (a : Nat) : InsRel lo hi (a + 1) (gA lo hi a + 1) := by
  unfold InsRel gA
  by_cases h1 : a + 1 < lo
  · left; simp [h1, show a < lo by omega]
  · by_cases h2 : a + 1 = lo
    · right; left; simp [h2, show a < lo by omega]
    · by_cases h3 : a + 1 < hi
      · left; simp [h1, h3, show ¬ a < lo by omega, show a < hi by omega]
      · by_cases h4 : a + 1 = hi
        · right; right; simp [h4, show ¬ a < lo by omega, show a < hi by omega]
        · left; simp [h1, h3, show ¬ a < lo by omega, show ¬ a < hi by omega]

theorem gA_lo (hlh : lo < hi) : gA lo hi lo = lo + 1 := by simp [gA, hlh]

theorem gA_hi (hlh : lo < hi) : gA lo hi hi = hi + 2 := by simp [gA, show ¬ hi < lo by omega]

/-- From the state of the original code (shifted) the inserted tests lead to it. -/
theorem to_rel (hs : InsertSpec P Q lo mid hi h k) (hlh : lo < hi) (hh : ∀ v, h.eval sol env v = (false, v))
    (hk : ∀ v, k.eval sol env v = (false, v)) {p q : Nat} (hr : InsRel lo hi p q) {v : Bool} {tr : List Nat}
    {r : List Nat × Bool} (hq : Halts Q sol env (gA lo hi p) v tr r) : Halts Q sol env q v tr r := by
  rcases hr with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hq
  · refine .jmpIf hs.entry ?_
    rw [hh v]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [gA_lo hlh] at hq
    exact hq
  · refine .jmpIf hs.closing ?_
    rw [hk v]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [gA_hi hlh] at hq
    exact hq

theorem insert_fwd (hs : InsertSpec P Q lo mid hi h k) (hlh : lo < hi) (hh : ∀ v, h.eval sol env v = (false, v))
    (hk : ∀ v, k.eval sol env v = (false, v)) {pc : Nat} {v : Bool} {tr : List Nat} {r : List Nat × Bool}
    (hp : Halts P sol env pc v tr r) : Halts Q sol env (gA lo hi pc) v tr r := by
  induction hp with
  | @halt pc v tr hi' => exact .halt (by rw [hs.body, hi']; rfl)
  | @blk pc a v tr r hi' _ ih =>
    refine .blk (a := a) (by rw [hs.body, hi']; rfl) ?_
    exact to_rel hs hlh hh hk (insRel_succ hlh pc) ih
  | @jmp pc t v tr r hi' _ ih =>
    refine .jmp (t := rmT lo hi t) (by rw [hs.body, hi']; rfl) ?_
    exact to_rel hs hlh hh hk (insRel_target hlh t) ih
  | @jmpIf pc t kk v tr r hi' _ ih =>
    refine .jmpIf (k := kk) (t := rmT lo hi t) (by rw [hs.body, hi']; rfl) ?_
    by_cases hc : (kk.eval sol env v).1 = true
    · simp only [hc, ↓reduceIte] at ih ⊢
      exact to_rel hs hlh hh hk (insRel_target hlh t) ih
    · simp only [hc, ↓reduceIte] at ih ⊢
      exact to_rel hs hlh hh hk (insRel_succ hlh pc) ih

theorem remapI_eq_blk {i : Instr} {a : Nat} (h : remapI lo hi i = .blk a) : i = .blk a := by
  cases i <;> simp [remapI] at h <;> simp [h]

theorem remapI_eq_halt {i : Instr} (h : remapI lo hi i = .halt) : i = .halt := by
  cases i <;> simp [remapI] at h <;> rfl

theorem remapI_eq_jmp {i : Instr} {t' : Nat} (h : remapI lo hi i = .jmp t') : ∃ t, i = .jmp t ∧ rmT lo hi t = t' := by
  cases i <;> simp [remapI] at h
  rename_i t; exact ⟨t, rfl, h⟩

theorem remapI_eq_jmpIf {i : Instr} {kk : Cond} {t' : Nat} (h : remapI lo hi i = .jmpIf kk t') :
    ∃ t, i = .jmpIf kk t ∧ rmT lo hi t = t' := by
  cases i <;> simp [remapI] at h
  rename_i k0 t
  obtain ⟨rfl, h2⟩ := h
  exact ⟨t, rfl, h2⟩

theorem insert_bwd (hs : InsertSpec P Q lo mid hi h k) (hlh : lo < hi) (hh : ∀ v, h.eval sol env v = (false, v))
    (hk : ∀ v, k.eval sol env v = (false, v)) {pcQ : Nat} {v : Bool} {tr : List Nat} {r : List Nat × Bool}
    (hq : Halts Q sol env pcQ v tr r) : ∀ pcP, InsRel lo hi pcP pcQ → Halts P sol env pcP v tr r := by
  induction hq with
  | @halt pc v tr hi' =>
    intro pcP hr
    rcases hr with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [hs.body] at hi'
      exact .halt (remapI_eq_halt hi')
    · rw [hs.entry] at hi'; cases hi'
    · rw [hs.closing] at hi'; cases hi'
  | @blk pc a v tr r hi' _ ih =>
    intro pcP hr
    rcases hr with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [hs.body] at hi'
      exact .blk (remapI_eq_blk hi') (ih (pcP + 1) (insRel_succ hlh pcP))
    · rw [hs.entry] at hi'; cases hi'
    · rw [hs.closing] at hi'; cases hi'
  | @jmp pc t' v tr r hi' _ ih =>
    intro pcP hr
    rcases hr with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [hs.body] at hi'
      obtain ⟨t, hP, rfl⟩ := remapI_eq_jmp hi'
      exact .jmp hP (ih t (insRel_target hlh t))
    · rw [hs.entry] at hi'; cases hi'
    · rw [hs.closing] at hi'; cases hi'
  | @jmpIf pc t' kk v tr r hi' _ ih =>
    intro pcP hr
    rcases hr with hr | ⟨hP, hQe⟩ | ⟨hP, hQe⟩
    · subst hr
      rw [hs.body] at hi'
      obtain ⟨t, hP, rfl⟩ := remapI_eq_jmpIf hi'
      refine .jmpIf hP ?_
      by_cases hc : (kk.eval sol env v).1 = true
      · simp only [hc, ↓reduceIte] at ih ⊢
        exact ih t (insRel_target hlh t)
      · simp only [hc, ↓reduceIte] at ih ⊢
        exact ih (pcP + 1) (insRel_succ hlh pcP)
    · have hi2 : Q.getD lo .halt = .jmpIf kk t' := by rw [← hQe]; exact hi'
      rw [hs.entry] at hi2
      cases hi2
      rw [hQe, hh v] at ih
      simp only [Bool.false_eq_true, ↓reduceIte] at ih
      have := ih lo (Or.inl (gA_lo hlh).symm)
      rw [hP]
      simpa [hh v] using this
    · have hi2 : Q.getD (hi + 1) .halt = .jmpIf kk t' := by rw [← hQe]; exact hi'
      rw [hs.closing] at hi2
      cases hi2
      rw [hQe, hk v] at ih
      simp only [Bool.false_eq_true, ↓reduceIte] at ih
      have := ih hi (Or.inl (by rw [gA_hi hlh]))
      rw [hP]
      simpa [hk v] using this

/-- Inserting the entry and closing tests around any region of any code does not change what the code returns, when the
two conditions are false (and leave the toggled variable alone). -/
theorem insert_equiv (hs : InsertSpec P Q lo mid hi h k) (hlh : lo < hi) (hh : ∀ v, h.eval sol env v = (false, v))
    (hk : ∀ v, k.eval sol env v = (false, v)) (v : Bool) (r : List Nat × Bool) :
    (∃ f, exec f P sol env 0 v [] = some r) ↔ ∃ f, exec f Q sol env 0 v [] = some r := by
  constructor
  · rintro ⟨f, hf⟩
    have := insert_fwd hs hlh hh hk (halts_of_exec f 0 v [] r hf)
    refine exec_of_halts (to_rel hs hlh hh hk (p := 0) ?_ this)
    unfold InsRel gA
    by_cases h0 : 0 < lo
    · left; simp [h0]
    · right; left; omega
  · rintro ⟨f, hf⟩
    refine exec_of_halts (insert_bwd hs hlh hh hk (halts_of_exec f 0 v [] r hf) 0 ?_)
    unfold InsRel gA
    by_cases h0 : 0 < lo
    · left; simp [h0]
    · right; left; omega

end SmcIrred.Lang
