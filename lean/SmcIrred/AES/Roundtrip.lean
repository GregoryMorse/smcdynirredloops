module

public import SmcIrred.AES.Check

public section

namespace SmcIrred.AES

/-- Decryption inverts encryption on single bytes. -/
theorem rtA_c0 : (List.range' 0 64).all (fun x => invSbox (sbox x) == x) = true := by decide +kernel
theorem rtA_c1 : (List.range' 64 64).all (fun x => invSbox (sbox x) == x) = true := by decide +kernel
theorem rtA_c2 : (List.range' 128 64).all (fun x => invSbox (sbox x) == x) = true := by decide +kernel
theorem rtA_c3 : (List.range' 192 64).all (fun x => invSbox (sbox x) == x) = true := by decide +kernel

theorem invSbox_sbox : ∀ x < 256, invSbox (sbox x) = x := by
  intro x hx
  have := forall_lt_4 (fun x => invSbox (sbox x) == x) rtA_c0 rtA_c1 rtA_c2 rtA_c3 x hx
  simpa using this

theorem rtB_c0 : (List.range' 0 64).all (fun x => sbox (invSbox x) == x) = true := by decide +kernel
theorem rtB_c1 : (List.range' 64 64).all (fun x => sbox (invSbox x) == x) = true := by decide +kernel
theorem rtB_c2 : (List.range' 128 64).all (fun x => sbox (invSbox x) == x) = true := by decide +kernel
theorem rtB_c3 : (List.range' 192 64).all (fun x => sbox (invSbox x) == x) = true := by decide +kernel

theorem sbox_invSbox : ∀ x < 256, sbox (invSbox x) = x := by
  intro x hx
  have := forall_lt_4 (fun x => sbox (invSbox x) == x) rtB_c0 rtB_c1 rtB_c2 rtB_c3 x hx
  simpa using this

end SmcIrred.AES
