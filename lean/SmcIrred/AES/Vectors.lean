module

public import SmcIrred.Spec.AES

public section

namespace SmcIrred.AES

/-! FIPS-197 Appendix C example vectors (plaintext `00112233445566778899aabbccddeeff`, key `000102…`) and the
Appendix A.1 key-expansion check. -/

def pt : Nat := 0x00112233445566778899aabbccddeeff

theorem enc128 : encrypt 10 (aes128 0x000102030405060708090a0b0c0d0e0f) (beBytes pt 16) =
    beBytes 0x69c4e0d86a7b0430d8cdb78070b4c55a 16 := by decide +kernel

theorem dec128 : decrypt 10 (aes128 0x000102030405060708090a0b0c0d0e0f)
    (beBytes 0x69c4e0d86a7b0430d8cdb78070b4c55a 16) = beBytes pt 16 := by decide +kernel

theorem enc192 : encrypt 12 (aes192 0x000102030405060708090a0b0c0d0e0f1011121314151617) (beBytes pt 16) =
    beBytes 0xdda97ca4864cdfe06eaf70a0ec0d7191 16 := by decide +kernel

theorem dec192 : decrypt 12 (aes192 0x000102030405060708090a0b0c0d0e0f1011121314151617)
    (beBytes 0xdda97ca4864cdfe06eaf70a0ec0d7191 16) = beBytes pt 16 := by decide +kernel

theorem enc256 : encrypt 14 (aes256 0x000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f)
    (beBytes pt 16) = beBytes 0x8ea2b7ca516745bfeafc49904b496089 16 := by decide +kernel

theorem dec256 : decrypt 14 (aes256 0x000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f)
    (beBytes 0x8ea2b7ca516745bfeafc49904b496089 16) = beBytes pt 16 := by decide +kernel

/-- FIPS-197 A.1: the last word of the AES-128 expansion of `2b7e1516 28aed2a6 abf71588 09cf4f3c`. -/
theorem keyexp128_last : (aes128 0x2b7e151628aed2a6abf7158809cf4f3c).getD 43 [] = beBytes 0xb6630ca6 4 := by
  decide +kernel

/-- FIPS-197 A.2 (AES-192) last word `01002202`. -/
theorem keyexp192_last : (aes192 0x8e73b0f7da0e6452c810f32b809079e562f8ead2522c6b7b).getD 51 [] =
    beBytes 0x01002202 4 := by decide +kernel

/-- FIPS-197 A.3 (AES-256) last word `706c631e`. -/
theorem keyexp256_last : (aes256 0x603deb1015ca71be2b73aef0857d77811f352c073b6108d72d9810a30914dff4).getD 59 [] =
    beBytes 0x706c631e 4 := by decide +kernel

theorem keyexp_length128 : (aes128 0).length = 44 := by decide +kernel
theorem keyexp_length192 : (aes192 0).length = 52 := by decide +kernel
theorem keyexp_length256 : (aes256 0).length = 60 := by decide +kernel

end SmcIrred.AES
