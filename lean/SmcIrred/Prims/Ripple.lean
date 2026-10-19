module

public import SmcIrred.Prims.Adder

public section

namespace SmcIrred

/-! ### The arithmetic of the ripple equations (pure Boolean/Nat statements) -/

theorem cout_add_eq : ∀ a b c : Bool, cout a b c false = ((a && b) || (c && (a != b))) := by decide
theorem cout_sub_eq : ∀ a b c : Bool, cout a b c true = ((!a && b) || (c && !(a != b))) := by decide
/-- The combined carry/borrow equation of the paper: `(a ⊕ s) ∧ b ∨ c ∧ (a ⊕ b ⊕ s)`. -/
theorem cout_combined : ∀ a b c s : Bool, cout a b c s = (((a != s) && b) || (c && ((a != b) != s))) := by decide

@[expose] def b2n (b : Bool) : Nat := if b then 1 else 0

/-- With the published carry `c_{i+1}` in place of `c_i`, the one-bit sum `1+1+0` would be `1`, not `0`. -/
theorem published_add_fails : b2n ((true != true) != cout true true false false) ≠ (1 + 1) % 2 := by decide

theorem bit_add : ∀ a b c : Bool, b2n a + b2n b + b2n c = b2n ((a != b) != c) + 2 * b2n (cout a b c false) := by decide
theorem bit_sub : ∀ a b c : Bool, b2n a + 2 * b2n (cout a b c true) = b2n b + b2n c + b2n ((a != b) != c) := by decide

/-- The ripple equations on a list of bit pairs (little endian): the sum bits and the final carry. -/
@[expose] def ripple (f : Bool) : Bool → List (Bool × Bool) → List Bool × Bool
  | c, [] => ([], c)
  | c, p :: t =>
    let r := ripple f (cout p.1 p.2 c f) t
    (((p.1 != p.2) != c) :: r.1, r.2)

theorem ripple_length (f : Bool) : ∀ (ps : List (Bool × Bool)) (c : Bool), (ripple f c ps).1.length = ps.length := by
  intro ps
  induction ps with
  | nil => intro c; rfl
  | cons p t ih => intro c; simp [ripple, ih]

theorem ripple_add : ∀ (ps : List (Bool × Bool)) (c : Bool),
    bv (ripple false c ps).1 + 2 ^ ps.length * b2n (ripple false c ps).2 =
      bv (ps.map Prod.fst) + bv (ps.map Prod.snd) + b2n c := by
  intro ps
  induction ps with
  | nil => intro c; cases c <;> rfl
  | cons p t ih =>
    intro c
    have h := ih (cout p.1 p.2 c false)
    have hb := bit_add p.1 p.2 c
    simp only [ripple, List.map_cons, List.length_cons, bv, Nat.pow_succ]
    have e1 : ∀ x : Bool, (if x then 1 else 0) = b2n x := fun x => rfl
    simp only [e1]
    -- bv(s::r) = s + 2 * bv r ;  A = a + 2 * bv as ;  etc.
    have e2 : 2 ^ t.length * 2 * b2n (ripple false (cout p.1 p.2 c false) t).2 =
        2 * (2 ^ t.length * b2n (ripple false (cout p.1 p.2 c false) t).2) := by
      rw [Nat.mul_comm (2 ^ t.length) 2, Nat.mul_assoc]
    rw [e2]
    omega

theorem ripple_sub : ∀ (ps : List (Bool × Bool)) (c : Bool),
    bv (ps.map Prod.fst) + 2 ^ ps.length * b2n (ripple true c ps).2 =
      bv (ps.map Prod.snd) + b2n c + bv (ripple true c ps).1 := by
  intro ps
  induction ps with
  | nil => intro c; cases c <;> rfl
  | cons p t ih =>
    intro c
    have h := ih (cout p.1 p.2 c true)
    have hb := bit_sub p.1 p.2 c
    simp only [ripple, List.map_cons, List.length_cons, bv, Nat.pow_succ]
    have e1 : ∀ x : Bool, (if x then 1 else 0) = b2n x := fun x => rfl
    simp only [e1]
    have e2 : 2 ^ t.length * 2 * b2n (ripple true (cout p.1 p.2 c true) t).2 =
        2 * (2 ^ t.length * b2n (ripple true (cout p.1 p.2 c true) t).2) := by
      rw [Nat.mul_comm (2 ^ t.length) 2, Nat.mul_assoc]
    rw [e2]
    omega

end SmcIrred
