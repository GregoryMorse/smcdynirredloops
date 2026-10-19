module

public import SmcIrred.Spec.AES

public section

namespace SmcIrred.AES

/-! FIPS-197 Appendix C plaintext `00112233445566778899aabbccddeeff`; the vectors are split over several modules so each kernel run stays well below the Lean memory cap. -/

@[expose] def pt : Nat := 0x00112233445566778899aabbccddeeff

end SmcIrred.AES
