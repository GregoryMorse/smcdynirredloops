module

public import SmcIrred.Spec.WNaf
public import SmcIrred.Arith.NAF

public section

namespace SmcIrred.Arith

/-! # Windowed NAF (C58, G31 b)

The windowed form always exists (it is a function), has the value of its argument, uses only zero and odd digits of
absolute value below `2 (q + 1)`, and with `q + 1 = 2^j` every nonzero digit is followed by at least `j + 1` zero digits
(so the weight is at most one per `j + 2` positions). -/

theorem wnaf_zero (q : Nat) : wnaf q 0 = [] := by rw [wnaf]; simp

theorem wnaf_even (q : Nat) {k : Int} (h0 : k ≠ 0) (h : k % 2 = 0) : wnaf q k = 0 :: wnaf q (k / 2) := by
  rw [wnaf]; simp [h0, h]

theorem wnaf_odd (q : Nat) {k : Int} (h : k % 2 ≠ 0) : wnaf q k = wd q k :: wnaf q ((k - wd q k) / 2) := by
  have h0 : k ≠ 0 := by omega
  rw [wnaf]; simp [h0, h]

/-- The windowed form has the value of its argument. -/
theorem sval_wnaf (q : Nat) (k : Int) : sval (wnaf q k) = k := by
  by_cases h0 : k = 0
  · subst h0; simp [wnaf_zero, sval]
  by_cases h : k % 2 = 0
  · rw [wnaf_even q h0 h, sval_cons, sval_wnaf q (k / 2)]; omega
  · obtain ⟨N, u, _, hk2, _, _, ho⟩ := wd_core q k (by omega)
    rw [wnaf_odd q h, sval_cons, sval_wnaf q ((k - wd q k) / 2)]; omega
termination_by k.natAbs
decreasing_by
  · omega
  · exact wd_dec q k h0 h

/-- The digits: zero, or odd with absolute value below `2 (q + 1)`. -/
theorem wnaf_digits (q : Nat) (k : Int) :
    ∀ d ∈ wnaf q k, d = 0 ∨ (d % 2 = 1 ∧ -(2 * ((q : Int) + 1)) < d ∧ d < 2 * ((q : Int) + 1)) := by
  by_cases h0 : k = 0
  · subst h0; simp [wnaf_zero]
  by_cases h : k % 2 = 0
  · rw [wnaf_even q h0 h]
    have := wnaf_digits q (k / 2)
    intro d hd
    rcases List.mem_cons.1 hd with rfl | hd
    · exact Or.inl rfl
    · exact this d hd
  · obtain ⟨N, u, _, hk2, hl, hu, ho⟩ := wd_core q k (by omega)
    rw [wnaf_odd q h]
    have := wnaf_digits q ((k - wd q k) / 2)
    intro d hd
    rcases List.mem_cons.1 hd with rfl | hd
    · exact Or.inr ⟨ho, hl, hu⟩
    · exact this d hd
termination_by k.natAbs
decreasing_by
  · omega
  · exact wd_dec q k h0 h

/-- A value divisible by `2^i` starts with `i` zero digits. -/
theorem wnaf_take_zero (q : Nat) : ∀ (i : Nat) (k : Int) (c : Int), k = 2 ^ i * c → ∀ d ∈ (wnaf q k).take i, d = 0 := by
  intro i
  induction i with
  | zero => intro k c _ d hd; simp at hd
  | succ i ih =>
    intro k c hc d hd
    by_cases h0 : k = 0
    · subst h0; simp [wnaf_zero] at hd
    have e : (2 : Int) ^ (i + 1) * c = 2 * (2 ^ i * c) := by
      rw [Int.pow_succ, Int.mul_comm (2 ^ i) 2, Int.mul_assoc]
    have h2 : k % 2 = 0 := by rw [hc, e]; omega
    have h3 : k / 2 = 2 ^ i * c := by rw [hc, e]; omega
    rw [wnaf_even q h0 h2, List.take_succ_cons] at hd
    rcases List.mem_cons.1 hd with rfl | hd
    · rfl
    · exact ih (k / 2) c h3 d hd

/-- After a nonzero digit of the window form, the next `j + 1` digits are zero when `q + 1 = 2^j`. -/
theorem wnaf_odd_spaced (q j : Nat) (hq : (q : Int) + 1 = 2 ^ j) {k : Int} (h : k % 2 ≠ 0) :
    ∀ d ∈ ((wnaf q k).tail).take (j + 1), d = 0 := by
  obtain ⟨N, u, hN, hk2, hl, hu, ho⟩ := wd_core q k (by omega)
  rw [wnaf_odd q h]
  simp only [List.tail_cons]
  refine wnaf_take_zero q (j + 1) _ u ?_
  rw [hq] at hN
  have e : (2 : Int) ^ (j + 1) * u = 2 * (2 ^ j * u) := by
    rw [Int.pow_succ, Int.mul_comm (2 ^ j) 2, Int.mul_assoc]
  rw [e]
  omega

/-- The spacing property: every nonzero digit is followed by `j + 1` zero digits (or the list ends). -/
inductive WSpaced (j : Nat) : List Int → Prop
  | nil : WSpaced j []
  | zero {t : List Int} : WSpaced j t → WSpaced j (0 :: t)
  | nz {d : Int} {t : List Int} : d ≠ 0 → (∀ e ∈ t.take (j + 1), e = 0) → WSpaced j t → WSpaced j (d :: t)

theorem wnaf_spaced (q j : Nat) (hq : (q : Int) + 1 = 2 ^ j) (k : Int) : WSpaced j (wnaf q k) := by
  by_cases h0 : k = 0
  · subst h0; rw [wnaf_zero]; exact WSpaced.nil
  by_cases h : k % 2 = 0
  · rw [wnaf_even q h0 h]; exact WSpaced.zero (wnaf_spaced q j hq (k / 2))
  · obtain ⟨N, u, _, hk2, hl, hu, ho⟩ := wd_core q k (by omega)
    have hsp := wnaf_odd_spaced q j hq (k := k) h
    have hrec := wnaf_spaced q j hq ((k - wd q k) / 2)
    rw [wnaf_odd q h] at hsp ⊢
    exact WSpaced.nz (by omega) hsp hrec
termination_by k.natAbs
decreasing_by
  · omega
  · exact wd_dec q k h0 h

/-- With `q = 0` (window 2) the window form is the ordinary non-adjacent form. -/
theorem wnaf_zero_window (k : Int) : wnaf 0 k = naf k := by
  by_cases h0 : k = 0
  · subst h0; rw [wnaf_zero, naf_zero]
  by_cases h : k % 2 = 0
  · rw [wnaf_even 0 h0 h, naf_even h0 h, wnaf_zero_window (k / 2)]
  · have hd : wd 0 k = 2 - k % 4 := by
      unfold wd; push_cast; omega
    rw [wnaf_odd 0 h, naf_odd h, hd, wnaf_zero_window ((k - (2 - k % 4)) / 2)]
termination_by k.natAbs
decreasing_by
  · omega
  · have := wd_dec 0 k h0 h
    have hd : wd 0 k = 2 - k % 4 := by
      unfold wd; push_cast; omega
    rw [hd] at this; exact this

end SmcIrred.Arith
