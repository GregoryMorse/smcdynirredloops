module

public import SmcIrred.Spec.Arith

public section

namespace SmcIrred.Arith

/-! Montgomery reduction (C57). `R = 2^B`, `Np` with `N * Np ≡ -1 (mod R)`, `N` odd. -/

/-- Congruence modulo `n`. -/
@[expose] def Cong (n a b : Nat) : Prop := a % n = b % n

theorem Cong.refl (n a : Nat) : Cong n a a := rfl
theorem Cong.symm {n a b : Nat} (h : Cong n a b) : Cong n b a := Eq.symm h
theorem Cong.trans {n a b c : Nat} (h : Cong n a b) (h' : Cong n b c) : Cong n a c := Eq.trans h h'

theorem Cong.add {n a b c d : Nat} (h : Cong n a b) (h' : Cong n c d) : Cong n (a + c) (b + d) := by
  unfold Cong at *
  rw [Nat.add_mod, h, h', ← Nat.add_mod]

theorem Cong.mul {n a b c d : Nat} (h : Cong n a b) (h' : Cong n c d) : Cong n (a * c) (b * d) := by
  unfold Cong at *
  rw [Nat.mul_mod, h, h', ← Nat.mul_mod]

theorem Cong.mul_left {n a b : Nat} (c : Nat) (h : Cong n a b) : Cong n (c * a) (c * b) := (Cong.refl n c).mul h
theorem Cong.mul_right {n a b : Nat} (c : Nat) (h : Cong n a b) : Cong n (a * c) (b * c) := h.mul (Cong.refl n c)

theorem Cong.pow {n a b : Nat} (h : Cong n a b) (k : Nat) : Cong n (a ^ k) (b ^ k) := by
  induction k with
  | zero => exact Cong.refl n 1
  | succ k ih => rw [Nat.pow_succ, Nat.pow_succ]; exact ih.mul h

theorem Cong.of_mod (n a : Nat) : Cong n (a % n) a := Nat.mod_mod a n

theorem cong_add_mul (n a k : Nat) : Cong n (a + n * k) a := by
  unfold Cong; exact Nat.add_mul_mod_self_left a n k

/-- Two numbers below `n` that are congruent are equal. -/
theorem Cong.eq_of_lt {n a b : Nat} (h : Cong n a b) (ha : a < n) (hb : b < n) : a = b := by
  unfold Cong at h
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h

/-! ### The common ending: a value `x < 2N` with `x R = T + k N` -/

theorem bound_lt {x N : Nat} (hx : x < 2 * N) : bound x N < N := by
  unfold bound
  split <;> omega

theorem bound_spec {N R x T k : Nat} (hN : 0 < N) (hx : x * R = T + k * N) (hlt : x < 2 * N) :
    bound x N < N ∧ Cong N (bound x N * R) T := by
  refine ⟨bound_lt hlt, ?_⟩
  unfold bound
  by_cases h : N ≤ x
  · rw [if_pos h]
    have e : (x - N) * R + N * R = T + N * k := by
      have : x = (x - N) + N := by omega
      have h2 : ((x - N) + N) * R = (x - N) * R + N * R := Nat.add_mul _ _ _
      rw [← h2, ← this, hx, Nat.mul_comm k N]
    have h3 : Cong N ((x - N) * R + N * R) (T + N * k) := by rw [e]; exact Cong.refl _ _
    have h4 : Cong N ((x - N) * R + N * R) ((x - N) * R) := by
      unfold Cong; rw [Nat.mul_comm N R]; exact Nat.add_mul_mod_self_right _ _ _
    exact (h4.symm.trans h3).trans (cong_add_mul N T k)
  · rw [if_neg h]
    have e : x * R = T + N * k := by rw [hx, Nat.mul_comm k N]
    exact (by rw [e]; exact Cong.refl _ _ : Cong N (x * R) (T + N * k)).trans (cong_add_mul N T k)

/-! ### REDC -/

section Redc
variable {B N Np : Nat}

theorem mask_mod (x : Nat) : x &&& (2 ^ B - 1) = x % 2 ^ B := Nat.and_two_pow_sub_one_eq_mod x B

/-- The multiplier `m` of REDC, with the exact divisibility `R ∣ T + m N` (for any positive modulus `R`). -/
theorem redc_m_gen {R N Np : Nat} (hR : 0 < R) (hNp : (N * Np + 1) % R = 0) (T : Nat) :
    ((T % R) * Np) % R < R ∧ (T + (((T % R) * Np) % R) * N) % R = 0 := by
  refine ⟨Nat.mod_lt _ hR, ?_⟩
  have h1 : Cong R (((T % R) * Np) % R) (T * Np) := by
    have : Cong R ((T % R) * Np) (T * Np) := (Cong.of_mod R T).mul_right Np
    exact (Cong.of_mod R _).trans this
  have h2 : Cong R (T + (((T % R) * Np) % R) * N) (T + T * Np * N) := (Cong.refl R T).add (h1.mul_right N)
  have h3 : T + T * Np * N = T * (N * Np + 1) := by
    rw [Nat.mul_add, Nat.mul_one, Nat.mul_assoc, Nat.mul_comm Np N]
    rw [Nat.add_comm]
  have h4 : (T * (N * Np + 1)) % R = 0 := by
    rw [Nat.mul_mod, hNp, Nat.mul_zero, Nat.zero_mod]
  unfold Cong at h2
  rw [h2, h3, h4]

/-- The pre-bound value `t = (T + m N) / R` satisfies `t R = T + m N`, and `t < 2N` when `T < R N`. -/
theorem redc_t (hN : 0 < N) {T m : Nat} (hm : m < 2 ^ B) (hd : (T + m * N) % 2 ^ B = 0) (hT : T < 2 ^ B * N) :
    ((T + m * N) >>> B) * 2 ^ B = T + m * N ∧ ((T + m * N) >>> B) < 2 * N := by
  have hdvd : 2 ^ B ∣ T + m * N := Nat.dvd_of_mod_eq_zero hd
  have e : ((T + m * N) >>> B) * 2 ^ B = T + m * N := by
    rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_mul_cancel hdvd
  refine ⟨e, ?_⟩
  have hmN : m * N < 2 ^ B * N := Nat.mul_lt_mul_of_pos_right hm hN
  have : ((T + m * N) >>> B) * 2 ^ B < (2 * N) * 2 ^ B := by
    rw [e]
    have : (2 * N) * 2 ^ B = 2 ^ B * N + 2 ^ B * N := by
      rw [Nat.two_mul, Nat.add_mul, Nat.mul_comm N (2 ^ B)]
    omega
  exact Nat.lt_of_mul_lt_mul_right this

/-- REDC is correct: for `T < R N` the result is below `N` and `result * R ≡ T (mod N)`. -/
theorem redc_spec (hN : 0 < N) (hNp : (N * Np + 1) % 2 ^ B = 0) {T : Nat} (hT : T < 2 ^ B * N) :
    redc B N Np T < N ∧ Cong N (redc B N Np T * 2 ^ B) T := by
  obtain ⟨hm, hd⟩ := redc_m_gen (Nat.two_pow_pos B) hNp T
  unfold redc
  simp only [mask_mod]
  obtain ⟨e, hlt⟩ := redc_t hN hm hd hT
  exact bound_spec hN e hlt

/-- Without the bound `T < R N` one conditional subtraction no longer suffices (witness). -/
theorem redc_precondition_necessary : ¬ redc 2 3 1 24 < 3 := by decide

end Redc

/-! ### Inverse of `R` modulo an odd `N` -/

theorem two_inv (N : Nat) (hN : N % 2 = 1) : Cong N (2 * ((N + 1) / 2)) 1 := by
  have : 2 * ((N + 1) / 2) = 1 + N * 1 := by omega
  rw [this]; exact cong_add_mul N 1 1

/-- For odd `N` an inverse of `2^B` modulo `N` exists. -/
theorem R_inv_exists (B : Nat) {N : Nat} (hN : N % 2 = 1) : ∃ Ri, Cong N (2 ^ B * Ri) 1 := by
  refine ⟨((N + 1) / 2) ^ B, ?_⟩
  rw [← Nat.mul_pow]
  have := (two_inv N hN).pow B
  rwa [Nat.one_pow] at this

/-! ### Montgomery form -/

section Domain
variable {B N Np R2 Ri : Nat}

/-- `redc` computes `T R⁻¹ (mod N)`. -/
theorem redc_cong (hN : 0 < N) (hNp : (N * Np + 1) % 2 ^ B = 0) (hRi : Cong N (2 ^ B * Ri) 1)
    {T : Nat} (hT : T < 2 ^ B * N) : Cong N (redc B N Np T) (T * Ri) := by
  obtain ⟨_, h⟩ := redc_spec hN hNp hT
  have h1 : Cong N (redc B N Np T * (2 ^ B * Ri)) (redc B N Np T) := by
    have := hRi.mul_left (redc B N Np T)
    rwa [Nat.mul_one] at this
  have h2 : Cong N (redc B N Np T * 2 ^ B * Ri) (T * Ri) := h.mul_right Ri
  rw [Nat.mul_assoc] at h2
  exact h1.symm.trans h2

/-- Montgomery multiplication. -/
@[expose] def mmul (B N Np a b : Nat) : Nat := redc B N Np (a * b)

/-- Conversion into Montgomery form (`R2 = R² mod N`). -/
@[expose] def toM (B N Np R2 a : Nat) : Nat := redc B N Np (a * R2)

theorem mul_lt_RN {a b : Nat} (hNR : N ≤ 2 ^ B) (ha : a < N) (hb : b < N) : a * b < 2 ^ B * N := by
  have h1 : a * b < N * N := Nat.mul_lt_mul'' ha hb
  have h2 : N * N ≤ 2 ^ B * N := Nat.mul_le_mul_right N hNR
  omega

theorem mmul_spec (hN : 0 < N) (hNp : (N * Np + 1) % 2 ^ B = 0) (hRi : Cong N (2 ^ B * Ri) 1)
    (hNR : N ≤ 2 ^ B) {a b : Nat} (ha : a < N) (hb : b < N) :
    mmul B N Np a b < N ∧ Cong N (mmul B N Np a b) (a * b * Ri) :=
  ⟨(redc_spec hN hNp (mul_lt_RN hNR ha hb)).1, redc_cong hN hNp hRi (mul_lt_RN hNR ha hb)⟩

theorem toM_spec (hN : 0 < N) (hNp : (N * Np + 1) % 2 ^ B = 0) (hRi : Cong N (2 ^ B * Ri) 1)
    (hNR : N ≤ 2 ^ B) (hR2 : R2 = (2 ^ B * 2 ^ B) % N) {a : Nat} (ha : a < N) :
    toM B N Np R2 a < N ∧ Cong N (toM B N Np R2 a) (a * 2 ^ B) := by
  have hR2lt : R2 < N := by rw [hR2]; exact Nat.mod_lt _ hN
  have hlt := mul_lt_RN hNR ha hR2lt
  refine ⟨(redc_spec hN hNp hlt).1, ?_⟩
  have h1 := redc_cong hN hNp hRi hlt
  have h2 : Cong N R2 (2 ^ B * 2 ^ B) := by rw [hR2]; exact Cong.of_mod N _
  have h3 : Cong N (a * R2 * Ri) (a * (2 ^ B * 2 ^ B) * Ri) := (Cong.mul_left a h2).mul_right Ri
  have h4 : a * (2 ^ B * 2 ^ B) * Ri = a * 2 ^ B * (2 ^ B * Ri) := by ac_rfl
  have h5 : Cong N (a * 2 ^ B * (2 ^ B * Ri)) (a * 2 ^ B) := by
    have := hRi.mul_left (a * 2 ^ B)
    rwa [Nat.mul_one] at this
  rw [h4] at h3
  exact h1.trans (h3.trans h5)

/-- Leaving Montgomery form recovers the number. -/
theorem redc_toM (hN : 0 < N) (hNp : (N * Np + 1) % 2 ^ B = 0) (hRi : Cong N (2 ^ B * Ri) 1)
    (hNR : N ≤ 2 ^ B) (hR2 : R2 = (2 ^ B * 2 ^ B) % N) {a : Nat} (ha : a < N) :
    redc B N Np (toM B N Np R2 a) = a := by
  obtain ⟨hlt, hc⟩ := toM_spec hN hNp hRi hNR hR2 ha
  have hlt' : toM B N Np R2 a < 2 ^ B * N := by
    have : N ≤ 2 ^ B * N := Nat.le_mul_of_pos_left N (Nat.two_pow_pos B)
    omega
  obtain ⟨hr, _⟩ := redc_spec hN hNp hlt'
  have h1 := redc_cong hN hNp hRi hlt'
  have h2 : Cong N (toM B N Np R2 a * Ri) (a * 2 ^ B * Ri) := hc.mul_right Ri
  have h3 : Cong N (a * 2 ^ B * Ri) a := by
    rw [Nat.mul_assoc]
    have := hRi.mul_left a
    rwa [Nat.mul_one] at this
  exact (h1.trans (h2.trans h3)).eq_of_lt hr ha

/-- Montgomery multiplication of two numbers in Montgomery form is the Montgomery form of the product. -/
theorem mmul_toM (hN : 0 < N) (hNp : (N * Np + 1) % 2 ^ B = 0) (hRi : Cong N (2 ^ B * Ri) 1)
    (hNR : N ≤ 2 ^ B) (hR2 : R2 = (2 ^ B * 2 ^ B) % N) {a b : Nat} (ha : a < N) (hb : b < N) :
    mmul B N Np (toM B N Np R2 a) (toM B N Np R2 b) = toM B N Np R2 (a * b % N) := by
  obtain ⟨hA, hAc⟩ := toM_spec hN hNp hRi hNR hR2 ha
  obtain ⟨hB, hBc⟩ := toM_spec hN hNp hRi hNR hR2 hb
  have hab : a * b % N < N := Nat.mod_lt _ hN
  obtain ⟨hC, hCc⟩ := toM_spec hN hNp hRi hNR hR2 hab
  obtain ⟨hM, hMc⟩ := mmul_spec hN hNp hRi hNR hA hB
  refine (hMc.trans ?_).eq_of_lt hM hC
  have h1 : Cong N (toM B N Np R2 a * toM B N Np R2 b * Ri) (a * 2 ^ B * (b * 2 ^ B) * Ri) :=
    (hAc.mul hBc).mul_right Ri
  have h2 : a * 2 ^ B * (b * 2 ^ B) * Ri = a * b * 2 ^ B * (2 ^ B * Ri) := by
    ac_rfl
  have h3 : Cong N (a * b * 2 ^ B * (2 ^ B * Ri)) (a * b * 2 ^ B) := by
    have := hRi.mul_left (a * b * 2 ^ B)
    rwa [Nat.mul_one] at this
  have h4 : Cong N (a * b * 2 ^ B) (a * b % N * 2 ^ B) := ((Cong.of_mod N (a * b)).mul_right (2 ^ B)).symm
  rw [h2] at h1
  exact h1.trans (h3.trans (h4.trans hCc.symm))

end Domain

end SmcIrred.Arith
