module

public import SmcIrred.Prims.BvVal
public import SmcIrred.Spec.RsaProg
public import SmcIrred.Arith.Montgomery

public section

namespace SmcIrred

open RSA

/-! # The value of one Montgomery product (R15)

For every valuation that is the identity on constants, the expression `redcE B N Np T` denotes `Arith.redc B N Np` of the
number denoted by `T` (for constants `N`, `Np` below `2^B`), and `mulE` denotes the product. -/

theorem val_zeroE (v : Wire → Bool) : bv (zeroE.sem v) = 0 := rfl

theorem sem_litW (v : Wire → Bool) (hv : IsVal v) (n w : Nat) : (litW n w).sem v = natBits n w := by
  have hv' : ∀ b, v (.cst b) = b := hv
  simp [litW, BvExp.sem, natBits_range, hv', Function.comp_def]

theorem val_litW (v : Wire → Bool) (hv : IsVal v) (n w : Nat) (h : n < 2 ^ w) : bv ((litW n w).sem v) = n := by
  rw [sem_litW v hv]; exact bv_natBits w n h

theorem val_shiftE (v : Wire → Bool) (hv : IsVal v) (a : BvExp) (i : Nat) :
    bv ((shiftE a i).sem v) = 2 ^ i * bv (a.sem v) := by
  have hv' : ∀ b, v (.cst b) = b := hv
  rw [shiftE, val_cat]
  have : bv ((BvExp.inp (List.replicate i (Wire.cst false))).sem v) = 0 := by
    simp only [BvExp.sem, List.map_replicate, hv']
    exact bv_zeros i
  rw [this]
  simp [BvExp.width]

theorem testBit0_mod_two (x : Nat) : (x % 2 ^ 1).testBit 0 = decide (x % 2 = 1) := by
  rw [Nat.pow_one, Nat.testBit_zero, Nat.mod_mod]

theorem mod_two_pow_succ (x k : Nat) : x % 2 ^ (k + 1) = x % 2 ^ k + 2 ^ k * ((x / 2 ^ k) % 2) := by
  rw [Nat.pow_succ, Nat.mod_mul]

theorem val_mulE_aux (v : Wire → Bool) (hv : IsVal v) (a b : BvExp) : ∀ k : Nat,
    bv (((List.range k).foldl (fun acc i => BvExp.add acc (BvExp.ite (BvExp.slice b i 1) (shiftE a i) zeroE))
      zeroE).sem v) = bv (a.sem v) * (bv (b.sem v) % 2 ^ k) := by
  intro k
  induction k with
  | zero => simp [val_zeroE, Nat.mod_one]
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, val_add, ih, val_ite, val_slice,
      val_shiftE v hv, val_zeroE, testBit0_mod_two, mod_two_pow_succ]
    by_cases h : (bv (b.sem v) / 2 ^ k) % 2 = 1
    · simp [h, Nat.mul_add]
      rw [Nat.mul_comm (2 ^ k) (bv (a.sem v))]
    · simp [h]
      have h0 : (bv (b.sem v) / 2 ^ k) % 2 = 0 := by omega
      simp [h0]

/-- The schoolbook product denotes the product. -/
theorem val_mulE (v : Wire → Bool) (hv : IsVal v) (a b : BvExp) :
    bv ((mulE a b).sem v) = bv (a.sem v) * bv (b.sem v) := by
  unfold mulE
  rw [val_mulE_aux v hv a b b.width]
  have hl := bv_lt (b.sem v)
  rw [BvExp.sem_length] at hl
  rw [Nat.mod_eq_of_lt hl]


/-- The arithmetic of the conditional subtraction in one more bit. -/
theorem bound_arith (X Y m : Nat) (hX : X < 2 ^ m) (hY : Y < 2 ^ m) :
    (if (((X + 2 ^ (m + 1) - Y) % 2 ^ (m + 1) / 2 ^ m) % 2 ^ 1).testBit 0 = true then X
      else ((X + 2 ^ (m + 1) - Y) % 2 ^ (m + 1) / 2 ^ 0) % 2 ^ m) = Arith.bound X Y := by
  have hP : 0 < 2 ^ m := Nat.two_pow_pos m
  have e : 2 ^ (m + 1) = 2 ^ m * 2 := Nat.pow_succ ..
  rw [testBit0_mod_two, e, Nat.pow_zero, Nat.div_one]
  generalize 2 ^ m = P at *
  unfold Arith.bound
  by_cases h : Y ≤ X
  · have h1 : (X + P * 2 - Y) % (P * 2) = X - Y := by
      have : X + P * 2 - Y = (X - Y) + P * 2 := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [h1, if_pos h]
    have h2 : (X - Y) / P = 0 := Nat.div_eq_of_lt (by omega)
    rw [h2]
    simp
    exact Nat.mod_eq_of_lt (by omega)
  · have h1 : (X + P * 2 - Y) % (P * 2) = X + P * 2 - Y := Nat.mod_eq_of_lt (by omega)
    rw [h1, if_neg h]
    have h2 : (X + P * 2 - Y) / P = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
    rw [h2]
    simp

theorem val_boundE (v : Wire → Bool) (hv : IsVal v) (t N : BvExp) :
    bv ((boundE t N).sem v) = Arith.bound (bv (t.sem v)) (bv (N.sem v)) := by
  have hv' : ∀ b, v (.cst b) = b := hv
  have hX := bv_lt (t.sem v)
  have hY := bv_lt (N.sem v)
  rw [BvExp.sem_length] at hX hY
  have hz : bv [v (Wire.cst false)] = 0 := by simp [bv, hv']
  have ha : bv ((BvExp.cat t (.inp [.cst false])).sem v) = bv (t.sem v) := by
    rw [val_cat]; simp [BvExp.sem, hz]
  have hb : bv ((BvExp.cat N (.inp [.cst false])).sem v) = bv (N.sem v) := by
    rw [val_cat]; simp [BvExp.sem, hz]
  have hM : max (BvExp.cat t (.inp [.cst false])).width (BvExp.cat N (.inp [.cst false])).width =
      max t.width N.width + 1 := by
    simp only [BvExp.width, List.length_singleton]; omega
  have hsub : bv ((boundD t N).sem v) =
      (bv (t.sem v) + 2 ^ (max t.width N.width + 1) - bv (N.sem v)) % 2 ^ (max t.width N.width + 1) := by
    unfold boundD
    rw [val_sub, ha, hb, hM]
  unfold boundE
  rw [val_ite, val_slice, val_slice, hsub]
  exact bound_arith _ _ _ (Nat.lt_of_lt_of_le hX (Nat.pow_le_pow_right (by omega) (Nat.le_max_left _ _)))
    (Nat.lt_of_lt_of_le hY (Nat.pow_le_pow_right (by omega) (Nat.le_max_right _ _)))


theorem val_redcE (v : Wire → Bool) (hv : IsVal v) (B N Np : Nat) (hN : N < 2 ^ B) (hNp : Np < 2 ^ B) (T : BvExp) :
    bv ((redcE B N Np T).sem v) = Arith.redc B N Np (bv (T.sem v)) := by
  have h1 : bv ((BvExp.slice T 0 B).sem v) = bv (T.sem v) % 2 ^ B := by
    rw [val_slice, Nat.pow_zero, Nat.div_one]
  have h2 : bv ((mulE (BvExp.slice T 0 B) (litW Np B)).sem v) = (bv (T.sem v) % 2 ^ B) * Np := by
    rw [val_mulE v hv, h1, val_litW v hv _ _ hNp]
  have h3 : bv ((redcM B Np T).sem v) = ((bv (T.sem v) % 2 ^ B) * Np) % 2 ^ B := by
    unfold redcM
    rw [val_slice, h2, Nat.pow_zero, Nat.div_one]
  have h4 : bv ((redcS B N Np T).sem v) = bv (T.sem v) + (((bv (T.sem v) % 2 ^ B) * Np) % 2 ^ B) * N := by
    unfold redcS
    rw [val_add, val_mulE v hv, h3, val_litW v hv _ _ hN]
  have h5 : bv ((BvExp.slice (redcS B N Np T) B (redcS B N Np T).width).sem v) =
      (bv (T.sem v) + (((bv (T.sem v) % 2 ^ B) * Np) % 2 ^ B) * N) / 2 ^ B := by
    rw [val_slice, h4]
    have hl := bv_lt ((redcS B N Np T).sem v)
    rw [BvExp.sem_length, h4] at hl
    apply Nat.mod_eq_of_lt
    exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hl
  unfold redcE
  rw [val_boundE v hv, h5, val_litW v hv _ _ hN]
  unfold Arith.redc
  simp only [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

end SmcIrred
