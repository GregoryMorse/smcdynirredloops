module

public import SmcIrred.AES.Check

public section

namespace SmcIrred.AES

/-- `ginv` is the multiplicative inverse of every non-zero byte, and `0 ↦ 0`. -/
theorem ginv_mul : ∀ x < 256, x ≠ 0 → gmul x (ginv x) = 1 := by
  intro x hx h0
  have := forall_lt 256 (fun x => x == 0 || gmul x (ginv x) == 1) (by decide +kernel) x hx
  simp at this
  rcases this with h | h
  · exact absurd h h0
  · exact h

theorem ginv_zero : ginv 0 = 0 := by decide +kernel

theorem ginv_lt : ∀ x < 256, ginv x < 256 := by
  intro x hx
  have := forall_lt 256 (fun x => decide (ginv x < 256)) (by decide +kernel) x hx
  simpa using this

end SmcIrred.AES
