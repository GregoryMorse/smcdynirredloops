module

public import SmcIrred.AES.Check

public section

namespace SmcIrred.AES

/-- The sBoxTable of `aes.py` is the list of the specification values. -/
theorem sbox_map : (List.range 256).map sbox = sBoxTable := by decide +kernel

theorem sBoxTable_length : sBoxTable.length = 256 := by
  rw [← sbox_map]; simp

/-- Every entry of the table equals the specification value. -/
theorem sbox_table : ∀ x < 256, sBoxTable.getD x 0 = sbox x := by
  intro x hx
  rw [← sbox_map]
  simp [List.getD_eq_getElem?_getD, hx]

end SmcIrred.AES
