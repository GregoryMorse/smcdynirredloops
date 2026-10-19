module

public import SmcIrred.AES.Check

public section

namespace SmcIrred.AES

/-- The affine part is affine over GF(2): `A(a ⊕ b) = A a ⊕ A b ⊕ A 0`; checked in sixteen row blocks of 16. -/
theorem aff_c0 : (List.range' 0 16).all (fun a => (List.range 256).all ((fun a b => affine (a ^^^ b) == affine a ^^^ affine b ^^^ affine 0) a)) = true := by decide +kernel
theorem aff_c1 : (List.range' 16 16).all (fun a => (List.range 256).all ((fun a b => affine (a ^^^ b) == affine a ^^^ affine b ^^^ affine 0) a)) = true := by decide +kernel
theorem aff_c2 : (List.range' 32 16).all (fun a => (List.range 256).all ((fun a b => affine (a ^^^ b) == affine a ^^^ affine b ^^^ affine 0) a)) = true := by decide +kernel
theorem aff_c3 : (List.range' 48 16).all (fun a => (List.range 256).all ((fun a b => affine (a ^^^ b) == affine a ^^^ affine b ^^^ affine 0) a)) = true := by decide +kernel
theorem aff_c4 : (List.range' 64 16).all (fun a => (List.range 256).all ((fun a b => affine (a ^^^ b) == affine a ^^^ affine b ^^^ affine 0) a)) = true := by decide +kernel
theorem aff_c5 : (List.range' 80 16).all (fun a => (List.range 256).all ((fun a b => affine (a ^^^ b) == affine a ^^^ affine b ^^^ affine 0) a)) = true := by decide +kernel
theorem aff_c6 : (List.range' 96 16).all (fun a => (List.range 256).all ((fun a b => affine (a ^^^ b) == affine a ^^^ affine b ^^^ affine 0) a)) = true := by decide +kernel
theorem aff_c7 : (List.range' 112 16).all (fun a => (List.range 256).all ((fun a b => affine (a ^^^ b) == affine a ^^^ affine b ^^^ affine 0) a)) = true := by decide +kernel
theorem aff_c8 : (List.range' 128 16).all (fun a => (List.range 256).all ((fun a b => affine (a ^^^ b) == affine a ^^^ affine b ^^^ affine 0) a)) = true := by decide +kernel
theorem aff_c9 : (List.range' 144 16).all (fun a => (List.range 256).all ((fun a b => affine (a ^^^ b) == affine a ^^^ affine b ^^^ affine 0) a)) = true := by decide +kernel
theorem aff_c10 : (List.range' 160 16).all (fun a => (List.range 256).all ((fun a b => affine (a ^^^ b) == affine a ^^^ affine b ^^^ affine 0) a)) = true := by decide +kernel
theorem aff_c11 : (List.range' 176 16).all (fun a => (List.range 256).all ((fun a b => affine (a ^^^ b) == affine a ^^^ affine b ^^^ affine 0) a)) = true := by decide +kernel
theorem aff_c12 : (List.range' 192 16).all (fun a => (List.range 256).all ((fun a b => affine (a ^^^ b) == affine a ^^^ affine b ^^^ affine 0) a)) = true := by decide +kernel
theorem aff_c13 : (List.range' 208 16).all (fun a => (List.range 256).all ((fun a b => affine (a ^^^ b) == affine a ^^^ affine b ^^^ affine 0) a)) = true := by decide +kernel
theorem aff_c14 : (List.range' 224 16).all (fun a => (List.range 256).all ((fun a b => affine (a ^^^ b) == affine a ^^^ affine b ^^^ affine 0) a)) = true := by decide +kernel
theorem aff_c15 : (List.range' 240 16).all (fun a => (List.range 256).all ((fun a b => affine (a ^^^ b) == affine a ^^^ affine b ^^^ affine 0) a)) = true := by decide +kernel

theorem affine_is_affine : ∀ a < 256, ∀ b < 256, affine (a ^^^ b) = affine a ^^^ affine b ^^^ affine 0 := by
  intro a ha b hb
  have key : ∀ k, k < 16 → (List.range' (16 * k) 16).all (fun a => (List.range 256).all ((fun a b => affine (a ^^^ b) == affine a ^^^ affine b ^^^ affine 0) a)) = true := by
    intro k hk
    match k, hk with
    | 0, _ => exact aff_c0
    | 1, _ => exact aff_c1
    | 2, _ => exact aff_c2
    | 3, _ => exact aff_c3
    | 4, _ => exact aff_c4
    | 5, _ => exact aff_c5
    | 6, _ => exact aff_c6
    | 7, _ => exact aff_c7
    | 8, _ => exact aff_c8
    | 9, _ => exact aff_c9
    | 10, _ => exact aff_c10
    | 11, _ => exact aff_c11
    | 12, _ => exact aff_c12
    | 13, _ => exact aff_c13
    | 14, _ => exact aff_c14
    | 15, _ => exact aff_c15
    | k + 16, h => omega
  have hr := forall_rows (16 * (a / 16)) 16 (fun a b => affine (a ^^^ b) == affine a ^^^ affine b ^^^ affine 0) (key (a / 16) (by omega)) a (by omega) (by omega) b hb
  simpa using hr

end SmcIrred.AES
