module

public import SmcIrred.Arith.Window

public section

namespace SmcIrred.Arith

/-! Multiplication algorithms (C55, P08), squaring (C56) and machine words (C62, P09). -/

/-! ### Karatsuba -/

theorem expand_mul (P A0 A1 B0 B1 : Nat) :
    (P * A1 + A0) * (P * B1 + B0) = A1 * B1 * (P * P) + (A0 * B1 + A1 * B0) * P + A0 * B0 := by
  simp only [Nat.add_mul, Nat.mul_add]
  ac_rfl

theorem kStep_eq (mulS : Nat → Nat → Nat) (hS : ∀ x y, mulS x y = x * y) (m a b : Nat) :
    kStep mulS m a b = a * b := by
  unfold kStep
  simp only [hS]
  have hP : 0 < 2 ^ m := Nat.two_pow_pos m
  have ha := Nat.div_add_mod a (2 ^ m)
  have hb := Nat.div_add_mod b (2 ^ m)
  have ha0 : a % 2 ^ m < 2 ^ m := Nat.mod_lt _ hP
  have hb0 : b % 2 ^ m < 2 ^ m := Nat.mod_lt _ hP
  generalize a % 2 ^ m = A0 at *
  generalize b % 2 ^ m = B0 at *
  generalize a / 2 ^ m = A1 at *
  generalize b / 2 ^ m = B1 at *
  generalize hPdef : 2 ^ m = P at *
  have hz0 : A0 * B0 < 2 ^ (2 * m) := by
    have : A0 * B0 < P * P := Nat.mul_lt_mul'' ha0 hb0
    rw [Nat.two_mul, Nat.pow_add, hPdef]; exact this
  have hz1 : (A0 + A1) * (B0 + B1) = A0 * B0 + A1 * B1 + (A0 * B1 + A1 * B0) := by
    simp only [Nat.add_mul, Nat.mul_add]
    have c1 : A1 * B0 = B0 * A1 := Nat.mul_comm _ _
    omega
  rw [← Nat.shiftLeft_add_eq_or_of_lt hz0, hz1]
  have e1 : A0 * B0 + A1 * B1 + (A0 * B1 + A1 * B0) - A0 * B0 - A1 * B1 = A0 * B1 + A1 * B0 := by omega
  rw [e1, Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.two_mul, Nat.pow_add, hPdef]
  rw [← ha, ← hb, expand_mul]
  ac_rfl

theorem kSqStep_eq (mulS : Nat → Nat → Nat) (hS : ∀ x y, mulS x y = x * y) (m a : Nat) :
    kSqStep mulS m a = a * a := by
  unfold kSqStep
  simp only [hS]
  have hP : 0 < 2 ^ m := Nat.two_pow_pos m
  have ha := Nat.div_add_mod a (2 ^ m)
  have ha0 : a % 2 ^ m < 2 ^ m := Nat.mod_lt _ hP
  generalize a % 2 ^ m = A0 at *
  generalize a / 2 ^ m = A1 at *
  generalize hPdef : 2 ^ m = P at *
  have hz0 : A0 * A0 < 2 ^ (2 * m) := by
    have : A0 * A0 < P * P := Nat.mul_lt_mul'' ha0 ha0
    rw [Nat.two_mul, Nat.pow_add, hPdef]; exact this
  rw [← Nat.shiftLeft_add_eq_or_of_lt hz0]
  rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.two_mul, Nat.pow_add, Nat.pow_succ, hPdef]
  rw [← ha, expand_mul]
  have c1 : A1 * A0 = A0 * A1 := Nat.mul_comm _ _
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_two]
  ac_rfl

/-- Karatsuba recursion with any split points multiplies correctly. -/
theorem kmulS_eq : ∀ (ms : List Nat) (a b : Nat), kmulS ms a b = a * b := by
  intro ms
  induction ms with
  | nil => intro a b; rfl
  | cons m ms ih => intro a b; exact kStep_eq (kmulS ms) ih m a b

/-- Three sub-products per level: `3^k` base products for `k` levels. -/
theorem kProds_eq : ∀ (ms : List Nat), kProds ms = 3 ^ ms.length := by
  intro ms
  induction ms with
  | nil => rfl
  | cons m ms ih => simp [kProds, ih, Nat.pow_succ, Nat.mul_comm]

/-- For `n = 2^k` the Karatsuba recursion makes `3^k` products, fewer than the `4^k = n²` of the schoolbook
method (`k ≥ 1`). -/
theorem karatsuba_fewer (k : Nat) (hk : 1 ≤ k) : 3 ^ k < 4 ^ k :=
  Nat.pow_lt_pow_left (by decide) (by omega)

/-! ### Toom-Cook (P08) -/

theorem toomProds_eq (k : Nat) : ∀ j, toomProds k j = (2 * k - 1) ^ j := by
  intro j
  induction j with
  | zero => rfl
  | succ j ih => simp [toomProds, ih, Nat.pow_succ, Nat.mul_comm]

/-- For `n = k^j` (so `n^{log_k (2k-1)} = (2k-1)^j`) Toom-`k` makes `(2k-1)^j` products: more than `n`
(`k ≥ 2`, `j ≥ 1`), and fewer than the `n² = k^(2j)` of the schoolbook method. -/
theorem toom_between (k j : Nat) (hk : 2 ≤ k) (hj : 1 ≤ j) :
    k ^ j < toomProds k j ∧ toomProds k j < k ^ (2 * j) := by
  rw [toomProds_eq]
  refine ⟨Nat.pow_lt_pow_left (a := k) (b := 2 * k - 1) (n := j) (by omega) (by omega), ?_⟩
  rw [Nat.pow_mul]
  have hlt : 2 * k - 1 < k ^ 2 := by
    rw [Nat.pow_two]
    have h2 : k * 2 ≤ k * k := Nat.mul_le_mul_left k hk
    omega
  exact Nat.pow_lt_pow_left hlt (by omega)

/-- The published exponent `log_k(2k) - 1 = log_k 2` would give `n^{log_k 2} = 2^j` products, fewer than the
`n = k^j` inputs (witness: `k = 3`, `j = 2`: 4 products for 9 digits), so it cannot be the cost. -/
theorem toom_published_too_small (k j : Nat) (hk : 3 ≤ k) (hj : 1 ≤ j) : 2 ^ j < k ^ j :=
  Nat.pow_lt_pow_left (by omega) (by omega)

theorem toom_witness : 2 ^ 2 < 3 ^ 2 ∧ toomProds 3 2 = 25 := by decide

/-! ### Squaring (C56) -/

/-- `∑_{i<n} f i`. -/
@[expose] def sumTo (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sumTo f n + f n

theorem sumTo_mul_left (c : Nat) (f : Nat → Nat) : ∀ n, c * sumTo f n = sumTo (fun i => c * f i) n := by
  intro n
  induction n with
  | zero => simp [sumTo]
  | succ n ih => simp [sumTo, Nat.mul_add, ih]

theorem sumTo_add (f g : Nat → Nat) : ∀ n, sumTo f n + sumTo g n = sumTo (fun i => f i + g i) n := by
  intro n
  induction n with
  | zero => simp [sumTo]
  | succ n ih => simp only [sumTo]; omega

theorem sumTo_congr (f g : Nat → Nat) (h : ∀ i, f i = g i) : ∀ n, sumTo f n = sumTo g n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simp [sumTo, ih, h]

/-- The value of a digit sequence in base 2. -/
@[expose] def val (d : Nat → Nat) (n : Nat) : Nat := sumTo (fun i => d i * 2 ^ i) n

/-- Schoolbook squaring: the square is the diagonal terms plus twice the terms `d_i d_j` for `j < i`. -/
theorem square_expand (d : Nat → Nat) : ∀ n,
    val d n * val d n =
      sumTo (fun i => d i * d i * 2 ^ i * 2 ^ i) n +
        2 * sumTo (fun i => sumTo (fun j => d i * d j * 2 ^ i * 2 ^ j) i) n := by
  intro n
  induction n with
  | zero => simp [val, sumTo]
  | succ n ih =>
    have hv : val d (n + 1) = val d n + d n * 2 ^ n := rfl
    have hcross : val d n * (d n * 2 ^ n) = sumTo (fun j => d n * d j * 2 ^ n * 2 ^ j) n := by
      unfold val
      rw [Nat.mul_comm, sumTo_mul_left]
      apply sumTo_congr
      intro j
      ac_rfl
    simp only [hv, sumTo]
    have e : (val d n + d n * 2 ^ n) * (val d n + d n * 2 ^ n) =
        val d n * val d n + 2 * (val d n * (d n * 2 ^ n)) + d n * 2 ^ n * (d n * 2 ^ n) := by
      simp only [Nat.add_mul, Nat.mul_add, Nat.two_mul]
      have c1 : d n * 2 ^ n * val d n = val d n * (d n * 2 ^ n) := by ac_rfl
      omega
    rw [e, ih, hcross]
    have e2 : d n * 2 ^ n * (d n * 2 ^ n) = d n * d n * 2 ^ n * 2 ^ n := by ac_rfl
    rw [e2]
    omega

/-- Number of distinct partial products of schoolbook squaring: pairs `j ≤ i < n`. -/
@[expose] def sqPartials (n : Nat) : Nat := sumTo (fun i => i + 1) n

theorem sqPartials_two (n : Nat) : 2 * sqPartials n = n * n + n := by
  unfold sqPartials
  induction n with
  | zero => simp [sumTo]
  | succ n ih =>
    simp only [sumTo]
    rw [Nat.mul_add, ih]
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul]
    omega

/-- Squaring needs `n(n+1)/2` partial products against `n²` for general multiplication. -/
theorem sqPartials_bounds (n : Nat) : n * n ≤ 2 * sqPartials n ∧ 2 * sqPartials n ≤ n * n + n :=
  ⟨by rw [sqPartials_two]; omega, by rw [sqPartials_two]; omega⟩

/-! ### Machine words (P09) -/

/-- Number of `w`-bit words of an `n`-bit number. -/
@[expose] def words (n w : Nat) : Nat := (n + w - 1) / w

/-- With `w`-bit words schoolbook multiplication uses `⌈n/w⌉²` word products. For `n = q w` that is exactly
`n² / w²`: the gain is a factor `w²` (not `2^w`). -/
theorem words_exact {w : Nat} (hw : 1 ≤ w) (q : Nat) : words (q * w) w = q := by
  unfold words
  have : q * w + w - 1 = (w - 1) + q * w := by omega
  rw [this, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt (by omega)]
  simp

theorem word_products (w q : Nat) (hw : 1 ≤ w) : (q * w) * (q * w) = (words (q * w) w * words (q * w) w) * (w * w) := by
  rw [words_exact hw]; ac_rfl

theorem words_cover {w : Nat} (hw : 1 ≤ w) (n : Nat) : n ≤ words n w * w := nW_mul n w hw

/-- `w²` is far below the `2^w` of the published sentence for the machine word sizes. -/
theorem word_gain_not_exponential : 32 * 32 < 2 ^ 32 ∧ 64 * 64 < 2 ^ 64 := by decide

end SmcIrred.Arith
