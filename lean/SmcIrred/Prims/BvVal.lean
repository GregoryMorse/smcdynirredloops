module

public import SmcIrred.Prims.BvDsl

public section

namespace SmcIrred

/-! # Numeric value of the bit-vector language (R15)

`bv (e.sem v)` is the number denoted by an expression. The lemmas below give it for every constructor that the RSA program
uses: slices are divisions and remainders by powers of two, concatenation is a shifted sum, the selector picks one operand. -/

/-- A valuation that is the identity on constants. -/
@[expose] def IsVal (v : Wire → Bool) : Prop := ∀ b, v (.cst b) = b

theorem bv_zeros (k : Nat) : bv (List.replicate k false) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, bv, ih]

theorem bv_getD : ∀ (l : List Bool) (k : Nat), l.getD k false = (bv l).testBit k := by
  intro l
  induction l with
  | nil => intro k; simp [bv]
  | cons b t ih =>
    intro k
    cases k with
    | zero =>
      cases b <;> simp [bv, Nat.testBit_zero]
    | succ k =>
      have h : (bv (b :: t)) = (if b then 1 else 0) + 2 * bv t := rfl
      have e : (bv (b :: t)).testBit (k + 1) = (bv t).testBit k := by
        rw [Nat.testBit_succ]
        congr 1
        rw [h]
        cases b <;> simp <;> omega
      rw [e, ← ih k]
      rfl

theorem bv_drop : ∀ (l : List Bool) (i : Nat), bv (l.drop i) = bv l / 2 ^ i := by
  intro l
  induction l with
  | nil => intro i; simp [bv]
  | cons b t ih =>
    intro i
    cases i with
    | zero => simp
    | succ i =>
      have h : (bv (b :: t)) / 2 = bv t := by
        simp only [bv]
        cases b <;> simp <;> omega
      rw [List.drop_succ_cons, ih i, Nat.pow_succ', ← Nat.div_div_eq_div_mul, h]

theorem bv_take : ∀ (l : List Bool) (n : Nat), bv (l.take n) = bv l % 2 ^ n := by
  intro l
  induction l with
  | nil => intro n; simp [bv]
  | cons b t ih =>
    intro n
    cases n with
    | zero => simp [bv, Nat.mod_one]
    | succ n =>
      have hP : 0 < 2 ^ n := Nat.two_pow_pos n
      rw [List.take_succ_cons]
      simp only [bv, ih n]
      have hy := Nat.div_add_mod (bv t) (2 ^ n)
      generalize bv t = y at *
      have hr : y % 2 ^ n < 2 ^ n := Nat.mod_lt _ hP
      generalize y % 2 ^ n = r at *
      generalize y / 2 ^ n = q at *
      have e : (if b then 1 else 0) + 2 * y = ((if b then 1 else 0) + 2 * r) + 2 ^ (n + 1) * q := by
        have h2 : 2 ^ (n + 1) * q = 2 * (2 ^ n * q) := by
          rw [Nat.pow_succ, Nat.mul_comm (2 ^ n) 2, Nat.mul_assoc]
        rw [h2]
        generalize 2 ^ n * q = s at hy ⊢
        omega
      rw [e, Nat.add_mul_mod_self_left]
      have hb : (if b then 1 else 0) ≤ 1 := by cases b <;> simp
      rw [Nat.mod_eq_of_lt]
      rw [Nat.pow_succ]
      omega

theorem bv_slice (l : List Bool) (i n : Nat) : bv ((l.drop i).take n) = (bv l / 2 ^ i) % 2 ^ n := by
  rw [bv_take, bv_drop]

theorem bv_padB (m : Nat) (l : List Bool) : bv (padB m l) = bv l := bv_pad l _

theorem bv_cat (a b : List Bool) : bv (a ++ b) = bv a + 2 ^ a.length * bv b := bv_append a b

theorem val_slice (v : Wire → Bool) (e : BvExp) (i n : Nat) :
    bv ((BvExp.slice e i n).sem v) = (bv (e.sem v) / 2 ^ i) % 2 ^ n := by
  simp only [BvExp.sem]; exact bv_slice _ _ _

theorem val_cat (v : Wire → Bool) (a b : BvExp) :
    bv ((BvExp.cat a b).sem v) = bv (a.sem v) + 2 ^ a.width * bv (b.sem v) := by
  simp only [BvExp.sem]
  rw [bv_cat, BvExp.sem_length]

theorem val_ite (v : Wire → Bool) (c a b : BvExp) :
    bv ((BvExp.ite c a b).sem v) = if (bv (c.sem v)).testBit 0 then bv (a.sem v) else bv (b.sem v) := by
  simp only [BvExp.sem]
  rw [bv_getD]
  split <;> simp [bv_padB, *]

theorem val_inp (v : Wire → Bool) (ws : List Wire) : bv ((BvExp.inp ws).sem v) = bv (ws.map v) := rfl

theorem val_add (v : Wire → Bool) (a b : BvExp) :
    bv ((BvExp.add a b).sem v) = bv (a.sem v) + bv (b.sem v) := sem_add_val v a b

theorem val_sub (v : Wire → Bool) (a b : BvExp) :
    bv ((BvExp.sub a b).sem v) = (bv (a.sem v) + 2 ^ max a.width b.width - bv (b.sem v)) % 2 ^ max a.width b.width := by
  rw [sem_sub_val, BvExp.sem_length, BvExp.sem_length]

end SmcIrred
