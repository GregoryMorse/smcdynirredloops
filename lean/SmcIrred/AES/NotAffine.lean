module

public import SmcIrred.AES.Check

public section

namespace SmcIrred.AES

/-- The S-box as a whole is not affine over GF(2) (witness: `1`, `2`). This is the non-linearity that the
multiplicative inverse supplies. -/
theorem sbox_not_affine : ¬ ∀ a < 256, ∀ b < 256, sbox (a ^^^ b) = sbox a ^^^ sbox b ^^^ sbox 0 := by
  intro h
  have := h 1 (by decide) 2 (by decide)
  revert this
  decide +kernel

end SmcIrred.AES
