module

public import SmcIrred.AES.Check

public section

namespace SmcIrred.AES

/-- The affine part is invertible (the inverse affine map undoes it, and conversely). -/
theorem invAffine_affine : ∀ b < 256, invAffine (affine b) = b := by
  intro x hx
  have := forall_lt 256 (fun x => invAffine (affine x) == x) (by decide +kernel) x hx
  simpa using this

theorem affine_invAffine : ∀ b < 256, affine (invAffine b) = b := by
  intro x hx
  have := forall_lt 256 (fun x => affine (invAffine x) == x) (by decide +kernel) x hx
  simpa using this

end SmcIrred.AES
