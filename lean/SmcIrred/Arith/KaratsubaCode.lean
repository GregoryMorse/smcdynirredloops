module

public import SmcIrred.Spec.KaratsubaCode
public import SmcIrred.Arith.Mul

public section

namespace SmcIrred.Arith

/-! # The thresholds and the extra carry bit of `mulKaratsuba` (C55, G31 e)

`mulK` computes the product whenever its sub-multiplier does, for every split point, in the equal-operand (squaring) branch
as well; the thresholds of `doBigMul` only choose between the native product and `mulK`, so `doBig` returns `a * b` for every
fuel and every declared size. The declared size `n1 - m2 + 1` of `low + high` is a valid bound (the carry bit), and the
declared sizes of the three sub-calls are strictly smaller than the sizes of the call when both exceed `4096` (the recursion
terminates). -/

theorem mulK_eq (rec : Nat → Nat → Nat → Nat → Nat) (hrec : ∀ x y p q, rec x y p q = x * y) (a b n1 n2 : Nat) :
    mulK rec a b n1 n2 = a * b := by
  unfold mulK
  simp only [hrec]
  by_cases h : a = b
  · subst h
    simp only [if_true]
    have := kSqStep_eq (fun x y => x * y) (fun _ _ => rfl) (min n1 n2 / 2) a
    unfold kSqStep at this
    simpa using this
  · simp only [h, if_false]
    have := kStep_eq (fun x y => x * y) (fun _ _ => rfl) (min n1 n2 / 2) a b
    unfold kStep at this
    simpa using this

/-- `doBigMul` returns the product for every fuel and every declared size. -/
theorem doBig_eq : ∀ (f a b n1 n2 : Nat), doBig f a b n1 n2 = a * b := by
  intro f
  induction f with
  | zero => intro a b n1 n2; rfl
  | succ f ih =>
    intro a b n1 n2
    unfold doBig
    split
    · rfl
    · split
      · rfl
      · exact mulK_eq (doBig f) ih a b n1 n2

/-- The extra carry bit: the sum of the low and high halves of a number below `2^n1` fits in `n1 - m2 + 1` bits when the split
point `m2` is at most half of `n1`. -/
theorem lowHigh_bits {a n1 m2 : Nat} (ha : a < 2 ^ n1) (hm : 2 * m2 ≤ n1) :
    a % 2 ^ m2 + a / 2 ^ m2 < 2 ^ (n1 - m2 + 1) := by
  have hP : 0 < 2 ^ m2 := Nat.two_pow_pos m2
  have hlow : a % 2 ^ m2 < 2 ^ m2 := Nat.mod_lt _ hP
  have hle : 2 ^ m2 ≤ 2 ^ (n1 - m2) := Nat.pow_le_pow_right (by omega) (by omega)
  have hhigh : a / 2 ^ m2 < 2 ^ (n1 - m2) := by
    rw [Nat.div_lt_iff_lt_mul hP]
    rw [← Nat.pow_add]
    have : n1 - m2 + m2 = n1 := by omega
    rw [this]; exact ha
  rw [Nat.pow_succ]
  omega

/-- The extra bit is needed: `low + high` can need `n1 - m2 + 1` bits. -/
theorem lowHigh_bits_tight : ∃ a n1 m2 : Nat, a < 2 ^ n1 ∧ 2 * m2 ≤ n1 ∧ 2 ^ (n1 - m2) ≤ a % 2 ^ m2 + a / 2 ^ m2 :=
  ⟨15, 4, 2, by decide, by decide, by decide⟩

/-- Termination: both sizes exceed `4096`, then every size passed to a sub-call is smaller than the size of its call, so the
sum of the two declared sizes decreases. -/
theorem karatsuba_sizes_decrease {n1 n2 : Nat} (h1 : 4096 < n1) (h2 : 4096 < n2) :
    let m2 := min n1 n2 / 2
    m2 + m2 < n1 + n2 ∧ (n1 - m2) + (n2 - m2) < n1 + n2 ∧ m2 + (n1 - m2) < n1 + n2 ∧
      (n1 - m2 + 1) + (n2 - m2 + 1) < n1 + n2 := by
  intro m2
  have : 2048 ≤ m2 := by omega
  omega

end SmcIrred.Arith
