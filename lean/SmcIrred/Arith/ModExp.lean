module

public import SmcIrred.Arith.Eff

public section

namespace SmcIrred.Arith

/-! Square-and-multiply (C54) and Montgomery exponentiation (C57, C59). -/

/-- Number of one bits. -/
@[expose] def popc (e : Nat) : Nat := if h : e = 0 then 0 else e % 2 + popc (e / 2)
termination_by e
decreasing_by omega

theorem bitLen_step {e : Nat} (h : e ≠ 0) : bitLen e = bitLen (e / 2) + 1 := by
  unfold bitLen
  rw [if_neg h]
  by_cases h2 : 2 ≤ e
  · have h3 : e / 2 ≠ 0 := by omega
    rw [if_neg h3, Nat.log2_def e, if_pos h2]
  · have h3 : e / 2 = 0 := by omega
    have h4 : e = 1 := by omega
    subst h4
    rw [h3]; simp [Nat.log2_def]

theorem popc_step {e : Nat} (h : e ≠ 0) : popc e = e % 2 + popc (e / 2) := by
  rw [popc, dif_neg h]

theorem bitLen_spec {e : Nat} (h : e ≠ 0) : 2 ^ (bitLen e - 1) ≤ e ∧ e < 2 ^ bitLen e := by
  unfold bitLen
  rw [if_neg h, Nat.add_sub_cancel]
  exact ⟨Nat.log2_self_le h, Nat.lt_log2_self⟩

/-! ### The loop over an abstract multiplication -/

section Loop
variable {α : Type} {N : Nat} (mulOp : α → α → α) (sqOp : α → α) (ρ : α → Nat) (P : α → Prop)

theorem sqmulF_spec
    (hP1 : ∀ x y, P x → P y → P (mulOp x y)) (hP2 : ∀ x, P x → P (sqOp x))
    (hm : ∀ x y, P x → P y → Cong N (ρ (mulOp x y)) (ρ x * ρ y))
    (hs : ∀ x, P x → Cong N (ρ (sqOp x)) (ρ x * ρ x)) :
    ∀ (f e : Nat) (res b : α), e ≤ f → P res → P b →
      P (sqmulF mulOp sqOp f e res b).1 ∧
      Cong N (ρ (sqmulF mulOp sqOp f e res b).1) (ρ res * ρ b ^ e) := by
  intro f
  induction f with
  | zero =>
    intro e res b he hr hb
    have : e = 0 := by omega
    subst this
    refine ⟨hr, ?_⟩
    simp [sqmulF, Cong.refl]
  | succ f ih =>
    intro e res b he hr hb
    unfold sqmulF
    by_cases h0 : e = 0
    · subst h0
      refine ⟨hr, ?_⟩
      simp [Cong.refl]
    · rw [if_neg h0]
      have hodd : (e &&& 1 ≠ 0) ↔ e % 2 = 1 := by rw [Nat.and_one_is_mod]; omega
      have hsh : e >>> 1 = e / 2 := by rw [Nat.shiftRight_eq_div_pow]
      rw [hsh]
      have hbsq := hs b hb
      have hPb := hP2 b hb
      obtain ⟨q, hq⟩ : ∃ q, q = e / 2 := ⟨_, rfl⟩
      rw [← hq]
      have hsq : (ρ b * ρ b) ^ q = ρ b ^ (2 * q) := by rw [Nat.pow_mul, Nat.pow_two]
      by_cases h1 : e % 2 = 1
      · simp only [hodd, h1, if_true]
        obtain ⟨hp, hc⟩ := ih q (mulOp res b) (sqOp b) (by omega) (hP1 res b hr hb) hPb
        refine ⟨hp, ?_⟩
        have h3 : Cong N (ρ (mulOp res b) * ρ (sqOp b) ^ q) (ρ res * ρ b * (ρ b * ρ b) ^ q) :=
          (hm res b hr hb).mul (hbsq.pow q)
        have e_eq : e = 2 * q + 1 := by omega
        have h4 : ρ res * ρ b * (ρ b * ρ b) ^ q = ρ res * ρ b ^ e := by
          rw [hsq, e_eq, Nat.pow_succ]; ac_rfl
        rw [h4] at h3
        exact hc.trans h3
      · simp only [hodd, h1, if_false]
        obtain ⟨hp, hc⟩ := ih q res (sqOp b) (by omega) hr hPb
        refine ⟨hp, ?_⟩
        have h3 : Cong N (ρ res * ρ (sqOp b) ^ q) (ρ res * (ρ b * ρ b) ^ q) :=
          (Cong.refl N _).mul (hbsq.pow q)
        have e_eq : e = 2 * q := by omega
        have h4 : ρ res * (ρ b * ρ b) ^ q = ρ res * ρ b ^ e := by rw [hsq, e_eq]
        rw [h4] at h3
        exact hc.trans h3
end Loop

/-! ### Operation counts -/

/-- Counting instance: the first component counts squarings (carried by `b`), the second multiplications
(carried by the result). -/
@[expose] def mulC (x _y : Nat × Nat) : Nat × Nat := (x.1, x.2 + 1)
@[expose] def sqC (x : Nat × Nat) : Nat × Nat := (x.1 + 1, x.2)

theorem sqmulF_counts : ∀ (f e : Nat) (res b : Nat × Nat), e ≤ f →
    sqmulF mulC sqC f e res b = ((res.1, res.2 + popc e), (b.1 + bitLen e, b.2)) := by
  intro f
  induction f with
  | zero =>
    intro e res b he
    have : e = 0 := by omega
    subst this
    simp [sqmulF, popc, bitLen]
  | succ f ih =>
    intro e res b he
    unfold sqmulF
    by_cases h0 : e = 0
    · subst h0; simp [popc, bitLen]
    · rw [if_neg h0]
      have hodd : (e &&& 1 ≠ 0) ↔ e % 2 = 1 := by rw [Nat.and_one_is_mod]; omega
      have hsh : e >>> 1 = e / 2 := by rw [Nat.shiftRight_eq_div_pow]
      rw [hsh, bitLen_step h0, popc_step h0]
      by_cases h1 : e % 2 = 1
      · simp only [hodd, h1, if_true]
        rw [ih (e / 2) _ _ (by omega)]
        simp [mulC, sqC, h1]
        omega
      · simp only [hodd, h1, if_false]
        rw [ih (e / 2) _ _ (by omega)]
        have : e % 2 = 0 := by omega
        simp [sqC, this]
        omega

/-- The exponentiation loop with `e > 0` squares `bitLen e = ⌊log₂ e⌋ + 1` times and multiplies
`popcount e` times (the last squaring is not needed for the result). -/
theorem sqmul_counts (e : Nat) :
    sqmulF mulC sqC e e (0, 0) (0, 0) = ((0, popc e), (bitLen e, 0)) := by
  rw [sqmulF_counts e e _ _ (Nat.le_refl e)]
  simp

theorem popc_le_bitLen : ∀ (f e : Nat), e ≤ f → popc e ≤ bitLen e := by
  intro f
  induction f with
  | zero => intro e he; have : e = 0 := by omega
            subst this; simp [popc, bitLen]
  | succ f ih =>
    intro e he
    by_cases h0 : e = 0
    · subst h0; simp [popc, bitLen]
    · rw [bitLen_step h0, popc_step h0]
      have := ih (e / 2) (by omega)
      omega

/-! ### Correctness -/

theorem modexp_spec {m : Nat} (hm : 1 < m) (b e : Nat) : modexp m b e = b ^ e % m := by
  unfold modexp
  rw [if_neg (by omega)]
  have hf := sqmulF_spec (N := m) (fun x y : Nat => x * y % m) (fun x : Nat => x * x % m) (fun x => x)
    (fun x => x < m) (fun _ _ _ _ => Nat.mod_lt _ (by omega)) (fun _ _ => Nat.mod_lt _ (by omega))
    (fun x y _ _ => Cong.of_mod m _) (fun x _ => Cong.of_mod m _) e e 1 (b % m) (Nat.le_refl e) hm
    (Nat.mod_lt _ (by omega))
  obtain ⟨hlt0, hc⟩ := hf
  have hlt : sqmul (fun x y : Nat => x * y % m) (fun x : Nat => x * x % m) e 1 (b % m) < m := hlt0
  change Cong m (sqmul _ _ e 1 (b % m)) (1 * (b % m) ^ e) at hc
  have h2 : Cong m ((b % m) ^ e) (b ^ e) := (Cong.of_mod m b).pow e
  rw [Nat.one_mul] at hc
  have := hc.trans h2
  unfold Cong at this
  rw [Nat.mod_eq_of_lt hlt] at this
  exact this

section Mont
variable {B N Np R2 Ri : Nat}

theorem modexpMont_spec (hN : 0 < N) (hNp : (N * Np + 1) % 2 ^ B = 0) (hRi : Cong N (2 ^ B * Ri) 1)
    (hNR : N ≤ 2 ^ B) (hR2 : R2 = (2 ^ B * 2 ^ B) % N) (hN1 : N ≠ 1) {b : Nat} (hb : b < N) (e : Nat) :
    modexpMont B N Np R2 b e < N ∧ Cong N (modexpMont B N Np R2 b e * Ri) ((b * Ri) ^ e) := by
  have hR2lt : R2 < N := by rw [hR2]; exact Nat.mod_lt _ hN
  have hone : 1 * R2 < 2 ^ B * N := by
    have : N ≤ 2 ^ B * N := Nat.le_mul_of_pos_left N (Nat.two_pow_pos B)
    omega
  have h0lt : redc B N Np R2 < N := (redc_spec hN hNp (by omega : R2 < 2 ^ B * N)).1
  -- the value of the starting accumulator is the Montgomery form of one
  have hone_c : Cong N (redc B N Np R2 * Ri) 1 := by
    have h1 := redc_cong hN hNp hRi (by omega : R2 < 2 ^ B * N)
    have h2 : Cong N R2 (2 ^ B * 2 ^ B) := by rw [hR2]; exact Cong.of_mod N _
    have h3 : Cong N (redc B N Np R2 * Ri) ((2 ^ B * 2 ^ B) * Ri * Ri) := (h1.trans (h2.mul_right Ri)).mul_right Ri
    have h4 : (2 ^ B * 2 ^ B) * Ri * Ri = (2 ^ B * Ri) * (2 ^ B * Ri) := by ac_rfl
    rw [h4] at h3
    have h5 : Cong N ((2 ^ B * Ri) * (2 ^ B * Ri)) (1 * 1) := hRi.mul hRi
    exact h3.trans h5
  have hf := sqmulF_spec (N := N) (fun x y : Nat => redc B N Np (x * y)) (fun x : Nat => redc B N Np (x * x))
    (fun x => x * Ri) (fun x => x < N)
    (fun x y hx hy => (mmul_spec hN hNp hRi hNR hx hy).1)
    (fun x hx => (mmul_spec hN hNp hRi hNR hx hx).1)
    (fun x y hx hy => by
      have h := (mmul_spec hN hNp hRi hNR hx hy).2
      have h2 : Cong N (redc B N Np (x * y) * Ri) (x * y * Ri * Ri) := h.mul_right Ri
      have h3 : x * y * Ri * Ri = x * Ri * (y * Ri) := by ac_rfl
      rw [h3] at h2; exact h2)
    (fun x hx => by
      have h := (mmul_spec hN hNp hRi hNR hx hx).2
      have h2 : Cong N (redc B N Np (x * x) * Ri) (x * x * Ri * Ri) := h.mul_right Ri
      have h3 : x * x * Ri * Ri = x * Ri * (x * Ri) := by ac_rfl
      rw [h3] at h2; exact h2)
    e e (redc B N Np R2) b (Nat.le_refl e) h0lt hb
  obtain ⟨hlt, hc⟩ := hf
  unfold modexpMont
  rw [if_neg hN1]
  refine ⟨hlt, ?_⟩
  have := hc.trans (hone_c.mul_right ((b * Ri) ^ e))
  rwa [Nat.one_mul] at this

/-- Exponentiation in Montgomery form: starting from the Montgomery form of `a`, REDC of the result is
`a^e mod N`. -/
theorem modexpMont_correct (hN : 0 < N) (hodd : N % 2 = 1) (hNp : (N * Np + 1) % 2 ^ B = 0)
    (hRi : Cong N (2 ^ B * Ri) 1) (hNR : N ≤ 2 ^ B) (hR2 : R2 = (2 ^ B * 2 ^ B) % N) {a : Nat} (ha : a < N)
    (e : Nat) :
    redc B N Np (modexpMont B N Np R2 (toM B N Np R2 a) e) = a ^ e % N := by
  by_cases hN1 : N = 1
  · subst hN1
    simp [modexpMont, redc, bound, Nat.mod_one]
  · obtain ⟨hA, hAc⟩ := toM_spec hN hNp hRi hNR hR2 ha
    obtain ⟨hr, hrc⟩ := modexpMont_spec hN hNp hRi hNR hR2 hN1 hA e
    have hrR : modexpMont B N Np R2 (toM B N Np R2 a) e < 2 ^ B * N := by
      have : N ≤ 2 ^ B * N := Nat.le_mul_of_pos_left N (Nat.two_pow_pos B)
      omega
    have h1 := redc_cong hN hNp hRi hrR
    have h2 : Cong N (toM B N Np R2 a * Ri) a := by
      have h3 : Cong N (toM B N Np R2 a * Ri) (a * 2 ^ B * Ri) := hAc.mul_right Ri
      have h4 : Cong N (a * 2 ^ B * Ri) a := by
        rw [Nat.mul_assoc]
        have := hRi.mul_left a
        rwa [Nat.mul_one] at this
      exact h3.trans h4
    have h5 : Cong N ((toM B N Np R2 a * Ri) ^ e) (a ^ e) := h2.pow e
    have h6 := h1.trans (hrc.trans h5)
    unfold Cong at h6
    rw [Nat.mod_eq_of_lt (redc_spec hN hNp hrR).1] at h6
    exact h6

end Mont

end SmcIrred.Arith
