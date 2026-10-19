module

public import SmcIrred.Spec.CarrySave

public section

namespace SmcIrred.Arith

/-! # Carry-save addition and Wallace trees (C56, G31 c)

The 3:2 compressor preserves the sum without carry propagation and does not widen the sum vector; a Wallace tree reduces
`m ≥ 2` operands to exactly two with exactly `m - 2` compressors in `r` levels, where `r` is least with `m ≤ dadda r`
(`2, 3, 4, 6, 9, 13, 19, 28, 42, 63, 94, ...`, about `log_{3/2}(m/2)` levels). -/

theorem csa_zero : csa 0 0 0 = (0, 0) := by rw [csa]; simp

theorem csa_succ {a b c : Nat} (h : a + b + c ≠ 0) :
    csa a b c = ((a % 2 + b % 2 + c % 2) % 2 + 2 * (csa (a / 2) (b / 2) (c / 2)).1,
      2 * ((a % 2 + b % 2 + c % 2) / 2) + 2 * (csa (a / 2) (b / 2) (c / 2)).2) := by
  rw [csa, dif_neg h]

/-- The compressor preserves the sum. -/
theorem csa_sum (a b c : Nat) : (csa a b c).1 + (csa a b c).2 = a + b + c := by
  by_cases h : a + b + c = 0
  · have ha : a = 0 := by omega
    have hb : b = 0 := by omega
    have hc : c = 0 := by omega
    subst ha hb hc; simp [csa_zero]
  · rw [csa_succ h]
    have := csa_sum (a / 2) (b / 2) (c / 2)
    simp only
    omega
termination_by a + b + c
decreasing_by omega

/-- Operands below `2^w` give a sum vector below `2^w` and a carry vector at most `2^(w+1) - 2`: no growth, no propagation. -/
theorem csa_bound (w : Nat) : ∀ a b c : Nat, a < 2 ^ w → b < 2 ^ w → c < 2 ^ w →
    (csa a b c).1 < 2 ^ w ∧ (csa a b c).2 + 2 ≤ 2 ^ (w + 1) := by
  induction w with
  | zero =>
    intro a b c ha hb hc
    have ha : a = 0 := by simpa using ha
    have hb : b = 0 := by simpa using hb
    have hc : c = 0 := by simpa using hc
    subst ha hb hc; simp [csa_zero]
  | succ w ih =>
    intro a b c ha hb hc
    by_cases h : a + b + c = 0
    · have ha : a = 0 := by omega
      have hb : b = 0 := by omega
      have hc : c = 0 := by omega
      subst ha hb hc
      simp [csa_zero, Nat.pow_succ]
      have := Nat.two_pow_pos w
      omega
    · rw [csa_succ h]
      have ih' := ih (a / 2) (b / 2) (c / 2) (by rw [Nat.pow_succ] at ha; omega) (by rw [Nat.pow_succ] at hb; omega)
        (by rw [Nat.pow_succ] at hc; omega)
      simp only
      rw [Nat.pow_succ] at ha hb hc ⊢
      rw [Nat.pow_succ] at ih'
      omega

/-! ### One Wallace level and the whole tree -/

theorem wround_sum : ∀ l : List Nat, (wround l).sum = l.sum := by
  intro l
  match l with
  | a :: b :: c :: t =>
    simp only [wround, List.sum_cons]
    rw [wround_sum t]
    have := csa_sum a b c
    omega
  | [] => rfl
  | [_] => simp [wround]
  | [_, _] => simp [wround]
termination_by l => l.length

theorem wreduce_sum (l : List Nat) : (wreduce l).sum = l.sum := by
  by_cases h : l.length ≤ 2
  · rw [wreduce]; simp [h]
  · rw [wreduce]; simp only [h, ↓reduceDIte]
    rw [wreduce_sum (wround l), wround_sum]
termination_by l.length
decreasing_by rw [wround_length]; unfold rnd; omega

theorem wreduce_length (l : List Nat) : (wreduce l).length ≤ 2 := by
  by_cases h : l.length ≤ 2
  · rw [wreduce]; simpa [h] using h
  · rw [wreduce]; simp only [h, ↓reduceDIte]
    exact wreduce_length (wround l)
termination_by l.length
decreasing_by rw [wround_length]; unfold rnd; omega

theorem wreduce_length_eq (l : List Nat) (h2 : 2 ≤ l.length) : (wreduce l).length = 2 := by
  by_cases h : l.length ≤ 2
  · rw [wreduce]; simp only [h, ↓reduceDIte]; omega
  · rw [wreduce]; simp only [h, ↓reduceDIte]
    refine wreduce_length_eq (wround l) ?_
    rw [wround_length]; unfold rnd; omega
termination_by l.length
decreasing_by rw [wround_length]; unfold rnd; omega

/-! ### Counting the levels and the compressors -/

theorem rnd_mono {m n : Nat} (h : m ≤ n) : rnd m ≤ rnd n := by unfold rnd; omega

theorem rnd_dadda (r : Nat) : rnd (dadda (r + 1)) = dadda r := by
  simp only [dadda]; unfold rnd; omega

theorem rnd_dadda_succ (r : Nat) : dadda r < rnd (dadda (r + 1) + 1) := by
  simp only [dadda]; unfold rnd; omega

theorem dadda_ge_two (r : Nat) : 2 ≤ dadda r := by
  induction r with
  | zero => simp [dadda]
  | succ r ih => simp only [dadda]; omega

theorem rounds_le_of : ∀ r m : Nat, m ≤ dadda r → rounds m ≤ r := by
  intro r
  induction r with
  | zero => intro m h; rw [rounds]; simp only [dadda] at h; simp [h]
  | succ r ih =>
    intro m h
    rw [rounds]
    by_cases h2 : m ≤ 2
    · simp [h2]
    · simp only [h2, ↓reduceDIte]
      have := ih (rnd m) (by have := rnd_mono h; rw [rnd_dadda] at this; exact this)
      omega

theorem lt_rounds_of : ∀ r m : Nat, dadda r < m → r < rounds m := by
  intro r
  induction r with
  | zero =>
    intro m h; rw [rounds]; simp only [dadda] at h
    simp only [show ¬ m ≤ 2 by omega, ↓reduceDIte]; omega
  | succ r ih =>
    intro m h
    rw [rounds]
    have h2 : ¬ m ≤ 2 := by have := dadda_ge_two (r + 1); omega
    simp only [h2, ↓reduceDIte]
    have := ih (rnd m) (by
      have := rnd_mono (show dadda (r + 1) + 1 ≤ m by omega)
      have h3 := rnd_dadda_succ r
      omega)
    omega

/-- `m` operands need exactly `r` levels when `dadda (r-1) < m ≤ dadda r`. -/
theorem rounds_eq (r m : Nat) (h1 : dadda r < m) (h2 : m ≤ dadda (r + 1)) : rounds m = r + 1 :=
  Nat.le_antisymm (rounds_le_of (r + 1) m h2) (lt_rounds_of r m h1)

theorem wlevels_eq (l : List Nat) : wlevels l = rounds l.length := by
  by_cases h : l.length ≤ 2
  · rw [wlevels, rounds]; simp [h]
  · rw [wlevels, rounds]; simp only [h, ↓reduceDIte]
    rw [wlevels_eq (wround l), wround_length]
termination_by l.length
decreasing_by rw [wround_length]; unfold rnd; omega

/-- Each compressor removes one operand: `m - 2` compressors reduce `m ≥ 2` operands to two. -/
theorem wcount_eq (m : Nat) (h : 2 ≤ m) : wcount m = m - 2 := by
  by_cases h2 : m ≤ 2
  · rw [wcount]; simp only [h2, ↓reduceDIte]; omega
  · rw [wcount]; simp only [h2, ↓reduceDIte]
    have := wcount_eq (rnd m) (by unfold rnd; omega)
    rw [this]; unfold rnd; omega
termination_by m
decreasing_by unfold rnd; omega

/-- Dadda numbers: 63 operands (a 64-bit multiplier minus one) need 9 levels, 64 need 10. -/
theorem rounds_examples : dadda 9 = 63 ∧ dadda 10 = 94 ∧ rounds 64 = 10 ∧ rounds 3 = 1 ∧ rounds 2 = 0 := by
  refine ⟨by decide, by decide, ?_, ?_, ?_⟩
  · exact rounds_eq 9 64 (by decide) (by decide)
  · exact rounds_eq 0 3 (by decide) (by decide)
  · rw [rounds]; simp

end SmcIrred.Arith
