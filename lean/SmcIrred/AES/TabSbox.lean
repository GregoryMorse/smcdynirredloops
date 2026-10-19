module

public import SmcIrred.AES.Check

public section

namespace SmcIrred.AES

/-! The check of the table against the specification is made in sixteen blocks of 16 (kernel memory). -/

theorem sbox_c0 : (List.range' (16 * 0) 16).all (fun x => sBoxTable.getD x 0 == sbox x) = true := by decide +kernel
theorem sbox_c1 : (List.range' (16 * 1) 16).all (fun x => sBoxTable.getD x 0 == sbox x) = true := by decide +kernel
theorem sbox_c2 : (List.range' (16 * 2) 16).all (fun x => sBoxTable.getD x 0 == sbox x) = true := by decide +kernel
theorem sbox_c3 : (List.range' (16 * 3) 16).all (fun x => sBoxTable.getD x 0 == sbox x) = true := by decide +kernel
theorem sbox_c4 : (List.range' (16 * 4) 16).all (fun x => sBoxTable.getD x 0 == sbox x) = true := by decide +kernel
theorem sbox_c5 : (List.range' (16 * 5) 16).all (fun x => sBoxTable.getD x 0 == sbox x) = true := by decide +kernel
theorem sbox_c6 : (List.range' (16 * 6) 16).all (fun x => sBoxTable.getD x 0 == sbox x) = true := by decide +kernel
theorem sbox_c7 : (List.range' (16 * 7) 16).all (fun x => sBoxTable.getD x 0 == sbox x) = true := by decide +kernel
theorem sbox_c8 : (List.range' (16 * 8) 16).all (fun x => sBoxTable.getD x 0 == sbox x) = true := by decide +kernel
theorem sbox_c9 : (List.range' (16 * 9) 16).all (fun x => sBoxTable.getD x 0 == sbox x) = true := by decide +kernel
theorem sbox_c10 : (List.range' (16 * 10) 16).all (fun x => sBoxTable.getD x 0 == sbox x) = true := by decide +kernel
theorem sbox_c11 : (List.range' (16 * 11) 16).all (fun x => sBoxTable.getD x 0 == sbox x) = true := by decide +kernel
theorem sbox_c12 : (List.range' (16 * 12) 16).all (fun x => sBoxTable.getD x 0 == sbox x) = true := by decide +kernel
theorem sbox_c13 : (List.range' (16 * 13) 16).all (fun x => sBoxTable.getD x 0 == sbox x) = true := by decide +kernel
theorem sbox_c14 : (List.range' (16 * 14) 16).all (fun x => sBoxTable.getD x 0 == sbox x) = true := by decide +kernel
theorem sbox_c15 : (List.range' (16 * 15) 16).all (fun x => sBoxTable.getD x 0 == sbox x) = true := by decide +kernel

/-- Every entry of the table equals the specification value. -/
theorem sbox_table : ∀ x < 256, sBoxTable.getD x 0 = sbox x := by
  have key : ∀ j, j < 16 → (List.range' (16 * j) 16).all (fun x => sBoxTable.getD x 0 == sbox x) = true := by
    intro j hj
    match j, hj with
    | 0, _ => exact sbox_c0
    | 1, _ => exact sbox_c1
    | 2, _ => exact sbox_c2
    | 3, _ => exact sbox_c3
    | 4, _ => exact sbox_c4
    | 5, _ => exact sbox_c5
    | 6, _ => exact sbox_c6
    | 7, _ => exact sbox_c7
    | 8, _ => exact sbox_c8
    | 9, _ => exact sbox_c9
    | 10, _ => exact sbox_c10
    | 11, _ => exact sbox_c11
    | 12, _ => exact sbox_c12
    | 13, _ => exact sbox_c13
    | 14, _ => exact sbox_c14
    | 15, _ => exact sbox_c15
    | k + 16, h => omega
  intro x hx
  have := forall_chunks _ 16 16 key x (by omega)
  simpa using this

theorem sBoxTable_length : sBoxTable.length = 256 := by decide +kernel

/-- The sBoxTable of `aes.py` is the list of the specification values. -/
theorem sbox_map : (List.range 256).map sbox = sBoxTable := by
  apply List.ext_getElem
  · simp [sBoxTable_length]
  · intro i h1 h2
    have := sbox_table i (by simpa using h1)
    simpa [List.getD_eq_getElem?_getD, h2] using this.symm

end SmcIrred.AES
