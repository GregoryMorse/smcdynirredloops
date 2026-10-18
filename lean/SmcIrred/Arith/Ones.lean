module

public import SmcIrred.Arith.Mul

public section

namespace SmcIrred.Arith

/-! Runs of ones: `get_consec_ones` and `consec_ones_to_num` are inverse (the code tests `i < 1024`), and
multiplication by a constant is a sum of signed shifted copies, one or two per run of ones (C57). -/

theorem zerosLoop_spec : ∀ (f num i : Nat), 0 < num → num ≤ f →
    ∃ k, (zerosLoop f num i).1 % 2 = 1 ∧ num = (zerosLoop f num i).1 * 2 ^ k ∧ (zerosLoop f num i).2 = i + k := by
  intro f
  induction f with
  | zero => intro num i h1 h2; omega
  | succ f ih =>
    intro num i h1 h2
    unfold zerosLoop
    have hand : (num &&& 1 = 0) ↔ num % 2 = 0 := by rw [Nat.and_one_is_mod]
    by_cases h : num % 2 = 0
    · rw [if_pos (hand.2 h)]
      have hsh : num >>> 1 = num / 2 := by rw [Nat.shiftRight_eq_div_pow]
      rw [hsh]
      obtain ⟨k, hk1, hk2, hk3⟩ := ih (num / 2) (i + 1) (by omega) (by omega)
      refine ⟨k + 1, hk1, ?_, by omega⟩
      have e : (zerosLoop f (num / 2) (i + 1)).1 * 2 ^ (k + 1) =
          2 * ((zerosLoop f (num / 2) (i + 1)).1 * 2 ^ k) := by rw [Nat.pow_succ]; ac_rfl
      rw [e, ← hk2]
      omega
    · rw [if_neg (fun h' => h (hand.1 h'))]
      exact ⟨0, by omega, by simp, by simp⟩

theorem onesLoop_spec : ∀ (f num i j : Nat), num < f →
    ∃ t, (onesLoop f num i j).1 % 2 = 0 ∧ num = (onesLoop f num i j).1 * 2 ^ t + (2 ^ t - 1) ∧
      (onesLoop f num i j).2.1 = i + t ∧ (onesLoop f num i j).2.2 = j + t := by
  intro f
  induction f with
  | zero => intro num i j h; omega
  | succ f ih =>
    intro num i j h
    unfold onesLoop
    have hand : (num &&& 1 = 1) ↔ num % 2 = 1 := by rw [Nat.and_one_is_mod]
    by_cases h1 : num % 2 = 1
    · rw [if_pos (hand.2 h1)]
      have hsh : num >>> 1 = num / 2 := by rw [Nat.shiftRight_eq_div_pow]
      rw [hsh]
      obtain ⟨t, ht1, ht2, ht3, ht4⟩ := ih (num / 2) (i + 1) (j + 1) (by omega)
      refine ⟨t + 1, ht1, ?_, by omega, by omega⟩
      have hp : 1 ≤ 2 ^ t := Nat.two_pow_pos t
      rw [Nat.pow_succ, ← Nat.mul_assoc]
      have e1 : (onesLoop f (num / 2) (i + 1) (j + 1)).1 * 2 ^ t * 2 =
          2 * ((onesLoop f (num / 2) (i + 1) (j + 1)).1 * 2 ^ t) := Nat.mul_comm _ _
      omega
    · rw [if_neg (fun h' => h1 (hand.1 h'))]
      exact ⟨0, by omega, by simp, by simp, by simp⟩

theorem consecToNum_append (a b : List Int) : consecToNum (a ++ b) = consecToNum a + consecToNum b := by
  induction a with
  | nil => simp [consecToNum]
  | cons x t ih => simp [consecToNum, ih]; omega

theorem toNum_one (x : Nat) : consecToNum [(x : Int)] = (2 : Int) ^ (x - 1) := by
  simp [consecToNum]

theorem toNum_two (a b : Nat) :
    consecToNum [-(a : Int) - 1, (b : Int) + 1] = -(2 : Int) ^ a + (2 : Int) ^ b := by
  have h1 : ¬ (0 ≤ -(a : Int) - 1) := by omega
  have h2 : (-(-(a : Int) - 1)).toNat = a + 1 := by omega
  have h3 : 0 ≤ (b : Int) + 1 := by omega
  have h4 : ((b : Int) + 1).toNat = b + 1 := by omega
  simp only [consecToNum, if_neg h1, h2, Nat.add_sub_cancel, if_pos h3, h4]
  omega

theorem run_alg1 (O A B Z : Int) (hz : Z = O * 2 + 1) : A * B + O * (A * B * 2) = Z * B * A := by
  rw [hz, Int.add_mul, Int.add_mul, Int.one_mul]
  ac_rfl

theorem run_alg2 (O A B C Z : Int) (hz : Z + 1 = O * C + C) :
    -(A * B) + A * B * C + O * (A * B * C) = Z * B * A := by
  have h1 : (Z + 1) * B * A = (O * C + C) * B * A := by rw [hz]
  simp only [Int.add_mul, Int.one_mul] at h1
  have c1 : O * C * B * A = O * (A * B * C) := by ac_rfl
  have c2 : C * B * A = A * B * C := by ac_rfl
  have c3 : B * A = A * B := by ac_rfl
  rw [c1, c2, c3] at h1
  omega

theorem consecGo_spec : ∀ (f num i : Nat), num < f → consecToNum (consecGo f num i) = (num : Int) * 2 ^ i := by
  intro f
  induction f with
  | zero => intro num i h; omega
  | succ f ih =>
    intro num i h
    unfold consecGo
    by_cases h0 : num = 0
    · subst h0; simp [consecToNum]
    · rw [if_neg h0]
      dsimp only
      obtain ⟨k, hz1, hz2, hz3⟩ := zerosLoop_spec (num + 1) num i (by omega) (by omega)
      generalize zerosLoop (num + 1) num i = z at hz1 hz2 hz3 ⊢
      obtain ⟨t, ho1, ho2, ho3, ho4⟩ := onesLoop_spec (z.1 + 1) z.1 z.2 0 (by omega)
      generalize onesLoop (z.1 + 1) z.1 z.2 0 = o at ho1 ho2 ho3 ho4 ⊢
      have hp : 1 ≤ 2 ^ t := Nat.two_pow_pos t
      have ht1 : 1 ≤ t := by
        cases t with
        | zero => simp at ho2; omega
        | succ t => omega
      have h2t : 2 ≤ 2 ^ t := by
        calc 2 = 2 ^ 1 := rfl
          _ ≤ 2 ^ t := Nat.pow_le_pow_right (by decide) ht1
      have hlt : o.1 < f := by
        have : o.1 * 2 ≤ o.1 * 2 ^ t := Nat.mul_le_mul_left o.1 h2t
        have h4 : z.1 ≤ num := by
          have : z.1 * 1 ≤ z.1 * 2 ^ k := Nat.mul_le_mul_left z.1 (Nat.two_pow_pos k)
          omega
        omega
      have hrest := ih o.1 o.2.1 hlt
      rw [consecToNum_append, hrest]
      -- arithmetic of the run
      have hnum : (num : Int) = (z.1 : Int) * 2 ^ k := by
        have := congrArg (fun x : Nat => (x : Int)) hz2
        simpa [Int.natCast_mul, Int.natCast_pow] using this
      have hi2 : o.2.1 = i + k + t := by omega
      have hj : o.2.2 = t := by omega
      have hz1N : z.1 + 1 = o.1 * 2 ^ t + 2 ^ t := by omega
      have hz1' : (z.1 : Int) + 1 = (o.1 : Int) * 2 ^ t + 2 ^ t := by exact_mod_cast hz1N
      have e1 : (2 : Int) ^ (i + k) = 2 ^ i * 2 ^ k := Int.pow_add _ _ _
      have e2 : (2 : Int) ^ o.2.1 = 2 ^ i * 2 ^ k * 2 ^ t := by rw [hi2, Int.pow_add, Int.pow_add]
      by_cases ht : t = 1
      · subst ht
        have hj1 : o.2.2 = 1 := hj
        rw [if_pos hj1, toNum_one]
        have hi2' : o.2.1 - 1 = i + k := by omega
        have hz1'' : (z.1 : Int) = (o.1 : Int) * 2 + 1 := by
          have : z.1 = o.1 * 2 + 1 := by omega
          exact_mod_cast this
        rw [hi2', hnum, e1, e2]
        have := run_alg1 (o.1 : Int) (2 ^ i) (2 ^ k) (z.1 : Int) hz1''
        simp only [Int.pow_one] at *
        omega
      · have hj1 : ¬ o.2.2 = 1 := by omega
        rw [if_neg hj1]
        have hlt2 : (o.2.2 : Int) - (o.2.1 : Int) - 1 = -((i + k : Nat) : Int) - 1 := by omega
        rw [hlt2, toNum_two (i + k) o.2.1, hnum, e1, e2]
        exact run_alg2 (o.1 : Int) (2 ^ i) (2 ^ k) (2 ^ t) (z.1 : Int) hz1'

/-- `get_consec_ones` and `consec_ones_to_num` are inverse, for every number. -/
theorem consec_roundtrip (n : Nat) : consecToNum (getConsecOnes n) = (n : Int) := by
  unfold getConsecOnes
  have := consecGo_spec (n + 1) n 0 (by omega)
  simpa using this

theorem mulConsec_eq (num : Int) : ∀ l : List Int, mulConsec num l = num * consecToNum l := by
  intro l
  induction l with
  | nil => simp [mulConsec, consecToNum]
  | cons x t ih =>
    simp only [mulConsec, consecToNum, ih, Int.mul_add]
    by_cases h : 0 ≤ x
    · simp [h]
    · simp [h, Int.mul_neg]

/-- Multiplying by a constant as signed shifted copies, one per run of ones (two for runs longer than one),
gives the product. -/
theorem mul_by_runs (num : Int) (n : Nat) : mulConsec num (getConsecOnes n) = num * n := by
  rw [mulConsec_eq, consec_roundtrip]

end SmcIrred.Arith
