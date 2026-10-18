module

public import SmcIrred.AES.Check

public section

namespace SmcIrred.AES

/-- The affine part is affine over GF(2): `A(a ⊕ b) = A a ⊕ A b ⊕ A 0`. -/
theorem aff_c0 : (List.range' 0 64).all (fun a => (List.range 256).all ((fun a b => affine (a ^^^ b) == affine a ^^^ affine b ^^^ affine 0) a)) = true := by decide +kernel
theorem aff_c1 : (List.range' 64 64).all (fun a => (List.range 256).all ((fun a b => affine (a ^^^ b) == affine a ^^^ affine b ^^^ affine 0) a)) = true := by decide +kernel
theorem aff_c2 : (List.range' 128 64).all (fun a => (List.range 256).all ((fun a b => affine (a ^^^ b) == affine a ^^^ affine b ^^^ affine 0) a)) = true := by decide +kernel
theorem aff_c3 : (List.range' 192 64).all (fun a => (List.range 256).all ((fun a b => affine (a ^^^ b) == affine a ^^^ affine b ^^^ affine 0) a)) = true := by decide +kernel

theorem affine_is_affine : ∀ a < 256, ∀ b < 256, affine (a ^^^ b) = affine a ^^^ affine b ^^^ affine 0 := by
  intro a ha b hb
  have := forall_lt2_4 (fun a b => affine (a ^^^ b) == affine a ^^^ affine b ^^^ affine 0) aff_c0 aff_c1 aff_c2 aff_c3 a ha b hb
  simpa using this

end SmcIrred.AES
