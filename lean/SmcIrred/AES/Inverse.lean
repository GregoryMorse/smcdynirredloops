module

public import SmcIrred.AES.Check

public section

namespace SmcIrred.AES

theorem ginv_mul_c0 : (List.range' (16 * 0) 16).all (fun x => x == 0 || gmul x (ginv x) == 1) = true := by decide +kernel
theorem ginv_mul_c1 : (List.range' (16 * 1) 16).all (fun x => x == 0 || gmul x (ginv x) == 1) = true := by decide +kernel
theorem ginv_mul_c2 : (List.range' (16 * 2) 16).all (fun x => x == 0 || gmul x (ginv x) == 1) = true := by decide +kernel
theorem ginv_mul_c3 : (List.range' (16 * 3) 16).all (fun x => x == 0 || gmul x (ginv x) == 1) = true := by decide +kernel
theorem ginv_mul_c4 : (List.range' (16 * 4) 16).all (fun x => x == 0 || gmul x (ginv x) == 1) = true := by decide +kernel
theorem ginv_mul_c5 : (List.range' (16 * 5) 16).all (fun x => x == 0 || gmul x (ginv x) == 1) = true := by decide +kernel
theorem ginv_mul_c6 : (List.range' (16 * 6) 16).all (fun x => x == 0 || gmul x (ginv x) == 1) = true := by decide +kernel
theorem ginv_mul_c7 : (List.range' (16 * 7) 16).all (fun x => x == 0 || gmul x (ginv x) == 1) = true := by decide +kernel
theorem ginv_mul_c8 : (List.range' (16 * 8) 16).all (fun x => x == 0 || gmul x (ginv x) == 1) = true := by decide +kernel
theorem ginv_mul_c9 : (List.range' (16 * 9) 16).all (fun x => x == 0 || gmul x (ginv x) == 1) = true := by decide +kernel
theorem ginv_mul_c10 : (List.range' (16 * 10) 16).all (fun x => x == 0 || gmul x (ginv x) == 1) = true := by decide +kernel
theorem ginv_mul_c11 : (List.range' (16 * 11) 16).all (fun x => x == 0 || gmul x (ginv x) == 1) = true := by decide +kernel
theorem ginv_mul_c12 : (List.range' (16 * 12) 16).all (fun x => x == 0 || gmul x (ginv x) == 1) = true := by decide +kernel
theorem ginv_mul_c13 : (List.range' (16 * 13) 16).all (fun x => x == 0 || gmul x (ginv x) == 1) = true := by decide +kernel
theorem ginv_mul_c14 : (List.range' (16 * 14) 16).all (fun x => x == 0 || gmul x (ginv x) == 1) = true := by decide +kernel
theorem ginv_mul_c15 : (List.range' (16 * 15) 16).all (fun x => x == 0 || gmul x (ginv x) == 1) = true := by decide +kernel

/-- `ginv` is the multiplicative inverse of every non-zero byte, and `0 ↦ 0`. -/
theorem ginv_mul : ∀ x < 256, x ≠ 0 → gmul x (ginv x) = 1 := by
  intro x hx h0
  have key : ∀ j, j < 16 → (List.range' (16 * j) 16).all (fun x => x == 0 || gmul x (ginv x) == 1) = true := by
    intro j hj
    match j, hj with
    | 0, _ => exact ginv_mul_c0
    | 1, _ => exact ginv_mul_c1
    | 2, _ => exact ginv_mul_c2
    | 3, _ => exact ginv_mul_c3
    | 4, _ => exact ginv_mul_c4
    | 5, _ => exact ginv_mul_c5
    | 6, _ => exact ginv_mul_c6
    | 7, _ => exact ginv_mul_c7
    | 8, _ => exact ginv_mul_c8
    | 9, _ => exact ginv_mul_c9
    | 10, _ => exact ginv_mul_c10
    | 11, _ => exact ginv_mul_c11
    | 12, _ => exact ginv_mul_c12
    | 13, _ => exact ginv_mul_c13
    | 14, _ => exact ginv_mul_c14
    | 15, _ => exact ginv_mul_c15
    | k + 16, h => omega
  have := forall_chunks _ 16 16 key x (by omega)
  simp at this
  rcases this with h | h
  · exact absurd h h0
  · exact h

theorem ginv_zero : ginv 0 = 0 := by decide +kernel

theorem ginv_lt_c0 : (List.range' (16 * 0) 16).all (fun x => decide (ginv x < 256)) = true := by decide +kernel
theorem ginv_lt_c1 : (List.range' (16 * 1) 16).all (fun x => decide (ginv x < 256)) = true := by decide +kernel
theorem ginv_lt_c2 : (List.range' (16 * 2) 16).all (fun x => decide (ginv x < 256)) = true := by decide +kernel
theorem ginv_lt_c3 : (List.range' (16 * 3) 16).all (fun x => decide (ginv x < 256)) = true := by decide +kernel
theorem ginv_lt_c4 : (List.range' (16 * 4) 16).all (fun x => decide (ginv x < 256)) = true := by decide +kernel
theorem ginv_lt_c5 : (List.range' (16 * 5) 16).all (fun x => decide (ginv x < 256)) = true := by decide +kernel
theorem ginv_lt_c6 : (List.range' (16 * 6) 16).all (fun x => decide (ginv x < 256)) = true := by decide +kernel
theorem ginv_lt_c7 : (List.range' (16 * 7) 16).all (fun x => decide (ginv x < 256)) = true := by decide +kernel
theorem ginv_lt_c8 : (List.range' (16 * 8) 16).all (fun x => decide (ginv x < 256)) = true := by decide +kernel
theorem ginv_lt_c9 : (List.range' (16 * 9) 16).all (fun x => decide (ginv x < 256)) = true := by decide +kernel
theorem ginv_lt_c10 : (List.range' (16 * 10) 16).all (fun x => decide (ginv x < 256)) = true := by decide +kernel
theorem ginv_lt_c11 : (List.range' (16 * 11) 16).all (fun x => decide (ginv x < 256)) = true := by decide +kernel
theorem ginv_lt_c12 : (List.range' (16 * 12) 16).all (fun x => decide (ginv x < 256)) = true := by decide +kernel
theorem ginv_lt_c13 : (List.range' (16 * 13) 16).all (fun x => decide (ginv x < 256)) = true := by decide +kernel
theorem ginv_lt_c14 : (List.range' (16 * 14) 16).all (fun x => decide (ginv x < 256)) = true := by decide +kernel
theorem ginv_lt_c15 : (List.range' (16 * 15) 16).all (fun x => decide (ginv x < 256)) = true := by decide +kernel

theorem ginv_lt : ∀ x < 256, ginv x < 256 := by
  have key : ∀ j, j < 16 → (List.range' (16 * j) 16).all (fun x => decide (ginv x < 256)) = true := by
    intro j hj
    match j, hj with
    | 0, _ => exact ginv_lt_c0
    | 1, _ => exact ginv_lt_c1
    | 2, _ => exact ginv_lt_c2
    | 3, _ => exact ginv_lt_c3
    | 4, _ => exact ginv_lt_c4
    | 5, _ => exact ginv_lt_c5
    | 6, _ => exact ginv_lt_c6
    | 7, _ => exact ginv_lt_c7
    | 8, _ => exact ginv_lt_c8
    | 9, _ => exact ginv_lt_c9
    | 10, _ => exact ginv_lt_c10
    | 11, _ => exact ginv_lt_c11
    | 12, _ => exact ginv_lt_c12
    | 13, _ => exact ginv_lt_c13
    | 14, _ => exact ginv_lt_c14
    | 15, _ => exact ginv_lt_c15
    | k + 16, h => omega
  intro x hx
  have := forall_chunks _ 16 16 key x (by omega)
  simpa using this

end SmcIrred.AES
