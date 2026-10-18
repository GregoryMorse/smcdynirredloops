module

public import SmcIrred.Arith.Ones

public section

namespace SmcIrred.Arith

/-! The Montgomery ladder (C58): correct, and the sequence of operations does not depend on the exponent bits. -/

theorem and_pow_zero_iff (e i : Nat) : (e &&& (1 <<< i) = 0) ↔ ¬ (e / 2 ^ i % 2 = 1) := by
  rw [Nat.one_shiftLeft]
  constructor
  · intro h h1
    have h2 := congrArg (fun x => Nat.testBit x i) h
    rw [Nat.testBit_and, Nat.testBit_two_pow] at h2
    have h3 : e.testBit i = true := by rw [Nat.testBit_eq_decide_div_mod_eq]; simp [h1]
    simp [h3] at h2
  · intro h
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_and, Nat.testBit_two_pow]
    by_cases hj : i = j
    · subst hj
      simp only [Nat.testBit_eq_decide_div_mod_eq]
      simp [h]
    · simp [hj]

section Lad
variable {α : Type} {N : Nat} (mulOp : α → α → α) (ρ : α → Nat) (P : α → Prop) (b : α) (e : Nat)

/-- State representing the exponent prefix `E`: `(b^E, b^(E+1))`. -/
@[expose] def LRep (E : Nat) (x : α × α) : Prop :=
  P x.1 ∧ P x.2 ∧ Cong N (ρ x.1) (ρ b ^ E) ∧ Cong N (ρ x.2) (ρ b ^ (E + 1))

theorem ladderStep_rep
    (hP1 : ∀ x y, P x → P y → P (mulOp x y))
    (hm : ∀ x y, P x → P y → Cong N (ρ (mulOp x y)) (ρ x * ρ y)) (j : Nat) (x : α × α)
    (h : LRep (N := N) ρ P b (e / 2 ^ (j + 1)) x) : LRep (N := N) ρ P b (e / 2 ^ j) (ladderStep mulOp e x j) := by
  obtain ⟨p1, p2, c1, c2⟩ := h
  have hsplit : e / 2 ^ j = 2 * (e / 2 ^ (j + 1)) + e / 2 ^ j % 2 := by
    have h1 : e / 2 ^ (j + 1) = (e / 2 ^ j) / 2 := by rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul]
    rw [h1]; omega
  unfold ladderStep
  by_cases hb : e &&& (1 <<< j) = 0
  · rw [if_pos hb]
    have hb' : e / 2 ^ j % 2 = 0 := by have := (and_pow_zero_iff e j).1 hb; omega
    rw [hb'] at hsplit
    refine ⟨hP1 _ _ p1 p1, hP1 _ _ p1 p2, ?_, ?_⟩
    · refine (hm _ _ p1 p1).trans ?_
      have := c1.mul c1
      rw [← Nat.pow_add] at this
      have e2 : e / 2 ^ (j + 1) + e / 2 ^ (j + 1) = e / 2 ^ j := by omega
      rwa [e2] at this
    · refine (hm _ _ p1 p2).trans ?_
      have := c1.mul c2
      rw [← Nat.pow_add] at this
      have e2 : e / 2 ^ (j + 1) + (e / 2 ^ (j + 1) + 1) = e / 2 ^ j + 1 := by omega
      rwa [e2] at this
  · rw [if_neg hb]
    have hb' : e / 2 ^ j % 2 = 1 :=
      Classical.byContradiction (fun hn => hb ((and_pow_zero_iff e j).2 hn))
    rw [hb'] at hsplit
    refine ⟨hP1 _ _ p1 p2, hP1 _ _ p2 p2, ?_, ?_⟩
    · refine (hm _ _ p1 p2).trans ?_
      have := c1.mul c2
      rw [← Nat.pow_add] at this
      have e2 : e / 2 ^ (j + 1) + (e / 2 ^ (j + 1) + 1) = e / 2 ^ j := by omega
      rwa [e2] at this
    · refine (hm _ _ p2 p2).trans ?_
      have := c2.mul c2
      rw [← Nat.pow_add] at this
      have e2 : e / 2 ^ (j + 1) + 1 + (e / 2 ^ (j + 1) + 1) = e / 2 ^ j + 1 := by omega
      rwa [e2] at this

theorem ladder_loop
    (hP1 : ∀ x y, P x → P y → P (mulOp x y))
    (hm : ∀ x y, P x → P y → Cong N (ρ (mulOp x y)) (ρ x * ρ y)) :
    ∀ (m : Nat) (x : α × α), LRep (N := N) ρ P b (e / 2 ^ (m + 1)) x →
      LRep (N := N) ρ P b e (((List.range (m + 1)).reverse).foldl (ladderStep mulOp e) x) := by
  intro m
  induction m with
  | zero =>
    intro x hx
    have := ladderStep_rep mulOp ρ P b e hP1 hm 0 x hx
    simpa [List.range_succ, ladderStep] using this
  | succ m ih =>
    intro x hx
    have hrev : (List.range (m + 1 + 1)).reverse = (m + 1) :: (List.range (m + 1)).reverse := by
      rw [List.range_succ, List.reverse_append]; rfl
    rw [hrev, List.foldl_cons]
    exact ih _ (ladderStep_rep mulOp ρ P b e hP1 hm (m + 1) x hx)

/-- The ladder computes `b^e` for every `e ≥ 1`. -/
theorem ladder_spec
    (hP1 : ∀ x y, P x → P y → P (mulOp x y))
    (hm : ∀ x y, P x → P y → Cong N (ρ (mulOp x y)) (ρ x * ρ y))
    (hb : P b) (he : 1 ≤ e) :
    P (ladder mulOp b e) ∧ Cong N (ρ (ladder mulOp b e)) (ρ b ^ e) := by
  have hspec := bitLen_spec (e := e) (by omega)
  have hn : 0 < bitLen e := by
    unfold bitLen; rw [if_neg (by omega)]; omega
  obtain ⟨n, hn'⟩ : ∃ n, bitLen e = n + 1 := ⟨bitLen e - 1, by omega⟩
  rw [hn'] at hspec
  simp only [Nat.add_sub_cancel] at hspec
  have htop : e / 2 ^ n = 1 := by
    have h2 : 2 ^ (n + 1) = 2 ^ n * 2 := by rw [Nat.pow_succ]
    have hpos := Nat.two_pow_pos n
    have h3 : 1 ≤ e / 2 ^ n := (Nat.le_div_iff_mul_le hpos).2 (by omega)
    have h4 : e / 2 ^ n < 2 := (Nat.div_lt_iff_lt_mul hpos).2 (by omega)
    omega
  have h0 : LRep (N := N) ρ P b (e / 2 ^ n) (b, mulOp b b) := by
    rw [htop]
    refine ⟨hb, hP1 _ _ hb hb, by simpa using Cong.refl N (ρ b), ?_⟩
    simpa [Nat.pow_two] using hm b b hb hb
  unfold ladder
  rw [hn']
  simp only [Nat.add_sub_cancel]
  cases n with
  | zero =>
    have : e = 1 := by simpa using htop
    subst this
    simp only [List.range_zero, List.reverse_nil, List.foldl_nil]
    exact ⟨hb, by simpa using Cong.refl N (ρ b)⟩
  | succ m =>
    have := ladder_loop mulOp ρ P b e hP1 hm m _ h0
    exact ⟨this.1, this.2.2.1⟩

/-- Every step does one product `x1 · x2` and one squaring, whichever bit is read: the operation sequence
depends only on the length of the exponent. -/
theorem ladderStep_shape (e : Nat) (x : α × α) (i : Nat) :
    ladderStep mulOp e x i = (mulOp x.1 x.1, mulOp x.1 x.2) ∨
    ladderStep mulOp e x i = (mulOp x.1 x.2, mulOp x.2 x.2) := by
  unfold ladderStep
  by_cases h : e &&& (1 <<< i) = 0
  · exact Or.inl (if_pos h)
  · exact Or.inr (if_neg h)

theorem ladder_steps (e : Nat) : ((List.range (bitLen e - 1)).reverse).length = bitLen e - 1 := by simp

end Lad

end SmcIrred.Arith
