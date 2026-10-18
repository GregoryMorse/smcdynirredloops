module

public import SmcIrred.AES.Check

public section

namespace SmcIrred.AES

/-- `xtime` is a selection on the top bit between the shifted byte and the shifted byte XOR `0x1B`. -/
theorem xtime_selection : ∀ a < 256, xtime a =
    (if a.testBit 7 then ((a <<< 1) &&& 0xFF) ^^^ 0x1B else (a <<< 1) &&& 0xFF) := by
  intro x hx
  have := forall_lt 256 (fun a => xtime a ==
    (if a.testBit 7 then ((a <<< 1) &&& 0xFF) ^^^ 0x1B else (a <<< 1) &&& 0xFF)) (by decide +kernel) x hx
  simpa using this

theorem xtime_lt : ∀ a < 256, xtime a < 256 := by
  intro x hx
  have := forall_lt 256 (fun a => decide (xtime a < 256)) (by decide +kernel) x hx
  simpa using this

/-- `xtime` is multiplication by `x` (= 2) in GF(2^8). -/
theorem xtime_gmul : ∀ a < 256, xtime a = gmul a 2 := by
  intro x hx
  have := forall_lt 256 (fun a => xtime a == gmul a 2) (by decide +kernel) x hx
  simpa using this

end SmcIrred.AES
