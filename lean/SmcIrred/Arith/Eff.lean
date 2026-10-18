module

public import SmcIrred.Arith.Montgomery

public section

namespace SmcIrred.Arith

/-! Bit-serial Montgomery reduction `montgomeryREDC_eff` and the interleaved multiplication
`montgomeryREDC_mul_eff` (Dusse–Kaliski) (C57). Both need `N` odd. -/

section Eff
variable {N : Nat}

theorem effStep_two (hN : N % 2 = 1) (x : Nat) :
    effStep N x * 2 = x + (if x % 2 = 1 then N else 0) := by
  unfold effStep
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Nat.pow_one]
  have hc : (x % 2 ≠ 0) ↔ (x % 2 = 1) := by omega
  simp only [hc]
  by_cases h : x % 2 = 1
  · simp only [if_pos h]; omega
  · simp only [if_neg h]; omega

theorem effLoop (hN : N % 2 = 1) (T : Nat) :
    ∀ i, ∃ k, k < 2 ^ i ∧ ((List.range i).foldl (fun x _ => effStep N x) T) * 2 ^ i = T + k * N := by
  intro i
  induction i with
  | zero => exact ⟨0, by decide, by simp⟩
  | succ i ih =>
    obtain ⟨k, hk, hx⟩ := ih
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize (List.range i).foldl (fun x _ => effStep N x) T = x at hk hx ⊢
    have h2 := effStep_two hN x
    have e1 : effStep N x * 2 ^ (i + 1) = (effStep N x * 2) * 2 ^ i := by rw [Nat.pow_succ]; ac_rfl
    by_cases h : x % 2 = 1
    · refine ⟨k + 2 ^ i, by rw [Nat.pow_succ]; omega, ?_⟩
      rw [if_pos h] at h2
      rw [e1, h2, Nat.add_mul, hx, Nat.add_mul k]
      have : N * 2 ^ i = 2 ^ i * N := Nat.mul_comm _ _
      omega
    · refine ⟨k, by rw [Nat.pow_succ]; omega, ?_⟩
      rw [if_neg h] at h2
      rw [e1, h2, Nat.add_zero, hx]

theorem redcEff_spec (hN : 0 < N) (hodd : N % 2 = 1) {B T : Nat} (hT : T < 2 ^ B * N) :
    redcEff B N T < N ∧ Cong N (redcEff B N T * 2 ^ B) T := by
  obtain ⟨k, hk, hx⟩ := effLoop hodd T B
  unfold redcEff
  generalize (List.range B).foldl (fun x _ => effStep N x) T = x at hx
  have hlt : x < 2 * N := by
    have h1 : k * N < 2 ^ B * N := Nat.mul_lt_mul_of_pos_right hk hN
    have : x * 2 ^ B < (2 * N) * 2 ^ B := by
      have : (2 * N) * 2 ^ B = 2 ^ B * N + 2 ^ B * N := by
        rw [Nat.two_mul, Nat.add_mul, Nat.mul_comm N (2 ^ B)]
      omega
    exact Nat.lt_of_mul_lt_mul_right this
  exact bound_spec hN hx hlt

/-! ### Interleaved multiplication -/

/-- The loop body of `montgomeryREDC_mul_eff`. -/
@[expose] def mulStep (N T0 T1 x i : Nat) : Nat :=
  effStep N (x + (if (T0 >>> i) &&& 1 = 1 then T1 else 0))

theorem mix_eq {x A k P T1 N : Nat} (hx : x * P = A * T1 + k * N) (s c : Nat) (hs : s = 0 ∨ s = 1)
    (hc : c = 0 ∨ c = 1) :
    (x + s * T1 + c * N) * P = (A + P * s) * T1 + (k + P * c) * N := by
  rcases hs with rfl | rfl <;> rcases hc with rfl | rfl <;>
  · simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.mul_zero, Nat.zero_mul, Nat.one_mul, Nat.add_zero,
      Nat.zero_add]
    have c1 := Nat.mul_comm T1 P
    have c2 := Nat.mul_comm N P
    omega

theorem mulLoop (hN : 0 < N) (hodd : N % 2 = 1) (T0 : Nat) {T1 : Nat} (hT1 : T1 < N) :
    ∀ i, ∃ k, k < 2 ^ i ∧
      ((List.range i).foldl (mulStep N T0 T1) 0) * 2 ^ i = (T0 % 2 ^ i) * T1 + k * N ∧
      ((List.range i).foldl (mulStep N T0 T1) 0) < 2 * N := by
  intro i
  induction i with
  | zero => exact ⟨0, by decide, by simp [Nat.mod_one], by simp; omega⟩
  | succ i ih =>
    obtain ⟨k, hk, hx, hlt⟩ := ih
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize (List.range i).foldl (mulStep N T0 T1) 0 = x at hk hx hlt ⊢
    unfold mulStep
    have hbit : ((T0 >>> i) &&& 1 = 1) ↔ (T0 / 2 ^ i % 2 = 1) := by
      rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
    have hmod : T0 % 2 ^ (i + 1) = T0 % 2 ^ i + 2 ^ i * (T0 / 2 ^ i % 2) := Nat.mod_pow_succ
    obtain ⟨s, hs0, hsT, hsA⟩ : ∃ s, (s = 0 ∨ s = 1) ∧
        (if (T0 >>> i) &&& 1 = 1 then T1 else 0) = s * T1 ∧ T0 % 2 ^ (i + 1) = T0 % 2 ^ i + 2 ^ i * s := by
      by_cases hb : T0 / 2 ^ i % 2 = 1
      · exact ⟨1, Or.inr rfl, by rw [if_pos (hbit.2 hb)]; simp, by rw [hmod, hb]⟩
      · refine ⟨0, Or.inl rfl, by rw [if_neg (fun h => hb (hbit.1 h))]; simp, ?_⟩
        have : T0 / 2 ^ i % 2 = 0 := by omega
        rw [hmod, this]
    rw [hsT, hsA]
    have h2 := effStep_two hodd (x + s * T1)
    obtain ⟨c, hc0, hcN, hcodd⟩ : ∃ c, (c = 0 ∨ c = 1) ∧
        (if (x + s * T1) % 2 = 1 then N else 0) = c * N ∧ (c = 1 ↔ (x + s * T1) % 2 = 1) := by
      by_cases h : (x + s * T1) % 2 = 1
      · exact ⟨1, Or.inr rfl, by rw [if_pos h]; simp, ⟨fun _ => h, fun _ => rfl⟩⟩
      · exact ⟨0, Or.inl rfl, by rw [if_neg h]; simp, ⟨fun h' => by omega, fun h' => absurd h' h⟩⟩
    rw [hcN] at h2
    have hsT1 : s * T1 ≤ T1 := by rcases hs0 with rfl | rfl <;> simp
    refine ⟨k + 2 ^ i * c, ?_, ?_, ?_⟩
    · rw [Nat.pow_succ]
      have : 2 ^ i * c ≤ 2 ^ i := by rcases hc0 with rfl | rfl <;> simp
      omega
    · rw [Nat.pow_succ, show effStep N (x + s * T1) * (2 ^ i * 2) = (effStep N (x + s * T1) * 2) * 2 ^ i by ac_rfl,
        h2, mix_eq hx s c hs0 hc0]
    · rcases hc0 with rfl | rfl <;> simp at h2 <;> omega

/-- `montgomeryREDC_mul_eff`: for `T0 < R`, `T1 < N`, the result is below `N` and `result · R ≡ T0 · T1 (mod N)`. -/
theorem redcMulEff_spec (hN : 0 < N) (hodd : N % 2 = 1) {B T0 T1 : Nat} (h0 : T0 < 2 ^ B) (h1 : T1 < N) :
    redcMulEff B N T0 T1 < N ∧ Cong N (redcMulEff B N T0 T1 * 2 ^ B) (T0 * T1) := by
  obtain ⟨k, _, hx, hlt⟩ := mulLoop hN hodd T0 h1 B
  have key : redcMulEff B N T0 T1 = bound ((List.range B).foldl (mulStep N T0 T1) 0) N := rfl
  rw [key]
  generalize (List.range B).foldl (mulStep N T0 T1) 0 = x at hx hlt ⊢
  rw [Nat.mod_eq_of_lt h0] at hx
  exact bound_spec hN hx hlt

end Eff

end SmcIrred.Arith
