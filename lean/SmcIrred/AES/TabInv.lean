module

public import SmcIrred.AES.Check

public section

namespace SmcIrred.AES

/-- The invSBoxTable of `aes.py` is the list of the specification values. -/
theorem invSbox_map : (List.range 256).map invSbox = invSBoxTable := by decide +kernel

theorem invSBoxTable_length : invSBoxTable.length = 256 := by
  rw [← invSbox_map]; simp

/-- Every entry of the table equals the specification value. -/
theorem invSbox_table : ∀ x < 256, invSBoxTable.getD x 0 = invSbox x := by
  intro x hx
  rw [← invSbox_map]
  simp [List.getD_eq_getElem?_getD, hx]

end SmcIrred.AES
