module

public import SmcIrred.Lang.Insert

public section

namespace SmcIrred.Lang

/-! # Closing-test insertion (Figure 6(b), R19b, G32 a)

The variant of `Insert` for protections whose entry test is already in the program (the `if` of Figure 6): only the closing
test `if (k) goto lo + 1` is inserted after the region `[lo, hi)`. A jump to `hi` runs the closing test. -/

@[expose] def rmT1 (hi t : Nat) : Nat := if t ≤ hi then t else t + 1
@[expose] def gA1 (hi a : Nat) : Nat := if a < hi then a else a + 1

@[expose] def remapI1 (hi : Nat) : Instr → Instr
  | .blk a => .blk a
  | .jmp t => .jmp (rmT1 hi t)
  | .jmpIf k t => .jmpIf k (rmT1 hi t)
  | .halt => .halt

structure InsertSpec1 (P Q : List Instr) (lo hi : Nat) (k : Cond) : Prop where
  body : ∀ a, Q.getD (gA1 hi a) .halt = remapI1 hi (P.getD a .halt)
  closing : Q.getD hi .halt = .jmpIf k (lo + 1)

@[expose] def InsRel1 (hi pcP pcQ : Nat) : Prop := pcQ = gA1 hi pcP ∨ (pcP = hi ∧ pcQ = hi)

variable {P Q : List Instr} {lo hi : Nat} {k : Cond} {sol : Nat → Bool} {env : Bool}

theorem insRel1_target (t : Nat) : InsRel1 hi t (rmT1 hi t) := by
  unfold InsRel1 rmT1 gA1
  by_cases h1 : t < hi
  · left; simp [h1, show t ≤ hi by omega]
  · by_cases h2 : t = hi
    · right; simp [h2]
    · left; simp [h1, show ¬ t ≤ hi by omega]

theorem insRel1_succ (a : Nat) : InsRel1 hi (a + 1) (gA1 hi a + 1) := by
  unfold InsRel1 gA1
  by_cases h1 : a + 1 < hi
  · left; simp [h1, show a < hi by omega]
  · by_cases h2 : a + 1 = hi
    · right; simp [h2, show a < hi by omega]
    · left; simp [h1, show ¬ a < hi by omega]

theorem to_rel1 (hs : InsertSpec1 P Q lo hi k) (hk : ∀ v, k.eval sol env v = (false, v)) {p q : Nat}
    (hr : InsRel1 hi p q) {v : Bool} {tr : List Nat} {r : List Nat × Bool}
    (hq : Halts Q sol env (gA1 hi p) v tr r) : Halts Q sol env q v tr r := by
  rcases hr with rfl | ⟨rfl, rfl⟩
  · exact hq
  · refine .jmpIf hs.closing ?_
    rw [hk v]
    simp only [Bool.false_eq_true, ↓reduceIte]
    simpa [gA1] using hq

theorem insert1_fwd (hs : InsertSpec1 P Q lo hi k) (hk : ∀ v, k.eval sol env v = (false, v)) {pc : Nat} {v : Bool}
    {tr : List Nat} {r : List Nat × Bool} (hp : Halts P sol env pc v tr r) : Halts Q sol env (gA1 hi pc) v tr r := by
  induction hp with
  | @halt pc v tr hi' => exact .halt (by rw [hs.body, hi']; rfl)
  | @blk pc a v tr r hi' _ ih =>
    refine .blk (a := a) (by rw [hs.body, hi']; rfl) ?_
    exact to_rel1 hs hk (insRel1_succ pc) ih
  | @jmp pc t v tr r hi' _ ih =>
    refine .jmp (t := rmT1 hi t) (by rw [hs.body, hi']; rfl) ?_
    exact to_rel1 hs hk (insRel1_target t) ih
  | @jmpIf pc t kk v tr r hi' _ ih =>
    refine .jmpIf (k := kk) (t := rmT1 hi t) (by rw [hs.body, hi']; rfl) ?_
    by_cases hc : (kk.eval sol env v).1 = true
    · simp only [hc, ↓reduceIte] at ih ⊢
      exact to_rel1 hs hk (insRel1_target t) ih
    · simp only [hc, ↓reduceIte] at ih ⊢
      exact to_rel1 hs hk (insRel1_succ pc) ih

theorem remapI1_eq_blk {i : Instr} {a : Nat} (h : remapI1 hi i = .blk a) : i = .blk a := by
  cases i <;> simp [remapI1] at h <;> simp [h]

theorem remapI1_eq_halt {i : Instr} (h : remapI1 hi i = .halt) : i = .halt := by
  cases i <;> simp [remapI1] at h <;> rfl

theorem remapI1_eq_jmp {i : Instr} {t' : Nat} (h : remapI1 hi i = .jmp t') : ∃ t, i = .jmp t ∧ rmT1 hi t = t' := by
  cases i <;> simp [remapI1] at h
  rename_i t; exact ⟨t, rfl, h⟩

theorem remapI1_eq_jmpIf {i : Instr} {kk : Cond} {t' : Nat} (h : remapI1 hi i = .jmpIf kk t') :
    ∃ t, i = .jmpIf kk t ∧ rmT1 hi t = t' := by
  cases i <;> simp [remapI1] at h
  rename_i k0 t
  obtain ⟨rfl, h2⟩ := h
  exact ⟨t, rfl, h2⟩

theorem insert1_bwd (hs : InsertSpec1 P Q lo hi k) (hk : ∀ v, k.eval sol env v = (false, v)) {pcQ : Nat} {v : Bool}
    {tr : List Nat} {r : List Nat × Bool} (hq : Halts Q sol env pcQ v tr r) :
    ∀ pcP, InsRel1 hi pcP pcQ → Halts P sol env pcP v tr r := by
  induction hq with
  | @halt pc v tr hi' =>
    intro pcP hr
    rcases hr with rfl | ⟨rfl, rfl⟩
    · rw [hs.body] at hi'
      exact .halt (remapI1_eq_halt hi')
    · rw [hs.closing] at hi'; cases hi'
  | @blk pc a v tr r hi' _ ih =>
    intro pcP hr
    rcases hr with rfl | ⟨rfl, rfl⟩
    · rw [hs.body] at hi'
      exact .blk (remapI1_eq_blk hi') (ih (pcP + 1) (insRel1_succ pcP))
    · rw [hs.closing] at hi'; cases hi'
  | @jmp pc t' v tr r hi' _ ih =>
    intro pcP hr
    rcases hr with rfl | ⟨rfl, rfl⟩
    · rw [hs.body] at hi'
      obtain ⟨t, hP, rfl⟩ := remapI1_eq_jmp hi'
      exact .jmp hP (ih t (insRel1_target t))
    · rw [hs.closing] at hi'; cases hi'
  | @jmpIf pc t' kk v tr r hi' _ ih =>
    intro pcP hr
    rcases hr with hr | ⟨hP, hQe⟩
    · subst hr
      rw [hs.body] at hi'
      obtain ⟨t, hP, rfl⟩ := remapI1_eq_jmpIf hi'
      refine .jmpIf hP ?_
      by_cases hc : (kk.eval sol env v).1 = true
      · simp only [hc, ↓reduceIte] at ih ⊢
        exact ih t (insRel1_target t)
      · simp only [hc, ↓reduceIte] at ih ⊢
        exact ih (pcP + 1) (insRel1_succ pcP)
    · have hi2 : Q.getD hi .halt = .jmpIf kk t' := by rw [← hQe]; exact hi'
      rw [hs.closing] at hi2
      cases hi2
      rw [hQe, hk v] at ih
      simp only [Bool.false_eq_true, ↓reduceIte] at ih
      have := ih hi (Or.inl (by simp [gA1]))
      rw [hP]
      simpa [hk v] using this

/-- Inserting the closing test after any region of any code does not change what the code returns, when the test is false. -/
theorem insert1_equiv (hs : InsertSpec1 P Q lo hi k) (hk : ∀ v, k.eval sol env v = (false, v)) (hpos : 0 < hi)
    (v : Bool) (r : List Nat × Bool) :
    (∃ f, exec f P sol env 0 v [] = some r) ↔ ∃ f, exec f Q sol env 0 v [] = some r := by
  have h0 : InsRel1 hi 0 0 := Or.inl (by simp [gA1, hpos])
  constructor
  · rintro ⟨f, hf⟩
    have := insert1_fwd hs hk (halts_of_exec f 0 v [] r hf)
    exact exec_of_halts (to_rel1 hs hk h0 this)
  · rintro ⟨f, hf⟩
    exact exec_of_halts (insert1_bwd hs hk (halts_of_exec f 0 v [] r hf) 0 h0)

end SmcIrred.Lang
