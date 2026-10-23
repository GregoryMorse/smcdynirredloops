module

public import SmcIrred.Spec.Lang

public section

namespace SmcIrred.Lang

/-! # The control flow of `native/protected.c` as structured programs over abstract blocks (G11, P13)

The blocks stand for the straight-line statements of the C code; the loops' conditions are opaque conditions of the run.

AES-128 (`aes_plain`): block 0 key expansion, input copy and the initial AddRoundKey; rounds 1-9 in a loop with the blocks 1
(SubBytes), 2 (ShiftRows), 3 (MixColumns), 4 (AddRoundKey); then the last round SubBytes, ShiftRows (blocks 1, 2) and block 5
(final AddRoundKey and output copy). `aes_protected` protects the pairs (SubBytes, ShiftRows) and (MixColumns, AddRoundKey) in the
loop and (SubBytes, ShiftRows) of the last round.

Modular exponentiation (`modexp_plain`): block 0 initialisation, a loop over the 32 exponent bits whose body is
`if (bit) acc = acc * base % n; base = base * base % n` (blocks 1, 2), block 3 the result. `modexp_protected` protects that
`if`-statement together with the squaring (Figure 6(b)). -/

/-- AES-128 as a program over blocks: 0 setup, 1 SubBytes, 2 ShiftRows, 3 MixColumns, 4 AddRoundKey of a round, 5 the end. -/
@[expose] def aesPlain : Stmt :=
  .seq (.blk 0)
    (.seq (.while (.out 3 true) (.seq (.seq (.blk 1) (.blk 2)) (.seq (.blk 3) (.blk 4))))
      (.seq (.seq (.blk 1) (.blk 2)) (.blk 5)))

/-- Modular exponentiation: 0 setup, 1 multiplication into the accumulator, 2 squaring, 3 result; the multiplication is
conditional on the exponent bit (condition 4), the loop on the bit counter (condition 3). -/
@[expose] def modexpPlain : Stmt :=
  .seq (.blk 0) (.seq (.while (.out 3 true) (.seq (.ite1 (.out 4 true) (.blk 1)) (.blk 2))) (.blk 3))

end SmcIrred.Lang
