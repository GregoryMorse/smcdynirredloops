module

public import SmcIrred.Spec.BvDsl
public import SmcIrred.Spec.AES

public section

namespace SmcIrred.AES

/-! # The AES graph program (`python/aes.py: aes_virtual_encrypt_no_tab`, R13)

The generator of the legacy code is written as bit-vector expressions (`BvExp`) over the wires of the previous stage and
compiled stage by stage with `BvExp.comp`, so the wires of a stage are shared by everything that reads them. A state is
the 128 wires of 16 bytes, the byte `b` in the wires `8b .. 8b+7` (little-endian bits). The three stages are

* `arkE`: `AddRoundKey` with a constant round key (`xor_to_virtual` against `constant_to_virtual`),
* `subShiftE`: `SubBytes` with `ShiftRows` (the byte positions are permuted by the table lookups, no node is spent on the
  permutation): one `table_lookup_virtual` of the constant S-box per byte,
* `mixE`: `MixColumns` followed by `AddRoundKey`: XORs and `xtime` as a selection on the top bit
  (`selection_to_virtual`), as in `mix_single_column_virtual` (the `xtime` of the two columns that share it is built twice
  here; the Python code builds each once, which changes the node count and not the value).

The expanded key is a constant: `rk` is the list of the words of `Spec.AES.keyExp`. -/

open SmcIrred

/-- Concatenation of a list of expressions, the first one in the lowest bits. -/
@[expose] def catAll : List BvExp → BvExp
  | [] => .inp []
  | e :: es => .cat e (catAll es)

/-- Byte `b` of a state. -/
@[expose] def byteE (W : List Wire) (b : Nat) : BvExp := .slice (.inp W) (8 * b) 8

/-- The constant byte `n` as eight constant wires (`constant_to_virtual` after `zero_extend_virtual`). -/
@[expose] def lit8 (n : Nat) : BvExp := .inp ((List.range 8).map fun j => Wire.cst (n.testBit j))

/-- Shift left by one inside a byte. -/
@[expose] def shlE (x : BvExp) : BvExp := .cat (.inp [.cst false]) (.slice x 0 7)

/-- `xtime` as a selection on the top bit (`aes.py: xtime_virtual`). -/
@[expose] def xtimeE (x : BvExp) : BvExp := .ite (.slice x 7 1) (.bxor (shlE x) (lit8 0x1B)) (shlE x)

/-- The byte that `ShiftRows` moves to position `i`. -/
@[expose] def srcIdx (i : Nat) : Nat := 4 * (((i / 4) + (i % 4)) % 4) + i % 4

/-- The S-box lookup of the byte that `ShiftRows` moves to position `i`. -/
@[expose] def subByteE (W : List Wire) (i : Nat) : BvExp := .tbl (byteE W (srcIdx i)) sBoxTable

/-- `SubBytes` and `ShiftRows`. -/
@[expose] def subShiftE (W : List Wire) : BvExp := catAll ((List.range 16).map (subByteE W))

/-- Byte `i` of `AddRoundKey` with the constant bytes `key`. -/
@[expose] def arkByteE (W : List Wire) (key : List Nat) (i : Nat) : BvExp := .bxor (byteE W i) (lit8 (key.getD i 0))

/-- `AddRoundKey` with the constant bytes `key`. -/
@[expose] def arkE (W : List Wire) (key : List Nat) : BvExp := catAll ((List.range 16).map (arkByteE W key))

/-- Byte `i = 4c + r` of `MixColumns` followed by `AddRoundKey`: `a_r ^ t ^ xtime(a_r ^ a_{r+1}) ^ key` with the column
bytes `a_j` and `t = a_0 ^ a_1 ^ a_2 ^ a_3`. -/
@[expose] def mixByteE (W : List Wire) (key : List Nat) (i : Nat) : BvExp :=
  .bxor
    (.bxor
      (.bxor (byteE W (4 * (i / 4) + i % 4))
        (.bxor (.bxor (.bxor (byteE W (4 * (i / 4))) (byteE W (4 * (i / 4) + 1))) (byteE W (4 * (i / 4) + 2)))
          (byteE W (4 * (i / 4) + 3))))
      (xtimeE (.bxor (byteE W (4 * (i / 4) + i % 4)) (byteE W (4 * (i / 4) + (i % 4 + 1) % 4)))))
    (lit8 (key.getD i 0))

/-- `MixColumns` and `AddRoundKey`. -/
@[expose] def mixE (W : List Wire) (key : List Nat) : BvExp := catAll ((List.range 16).map (mixByteE W key))

/-- One inner round: `SubBytes`, `ShiftRows`, `MixColumns`, `AddRoundKey`; the wires of the first stage are shared. -/
@[expose] def aesRound (key : List Nat) (gb : GB) (W : List Wire) : List Wire × GB :=
  let a := (subShiftE W).comp gb
  (mixE a.1 key).comp a.2

/-- The compiled AES with `Nr` rounds and the constant expanded key `rk`, from the 128 wires `W` of the block. -/
@[expose] def aesCircuit (Nr : Nat) (rk : List (List Nat)) (gb : GB) (W : List Wire) : List Wire × GB :=
  let r0 := (arkE W (roundKey rk 0)).comp gb
  let rs := (List.range (Nr - 1)).foldl
    (fun (st : List Wire × GB) i => aesRound (roundKey rk (i + 1)) st.2 st.1) r0
  let a := (subShiftE rs.1).comp rs.2
  (arkE a.1 (roundKey rk Nr)).comp a.2

/-- The little-endian bits of a list of bytes. -/
@[expose] def bits8 (bs : List Nat) : List Bool := bs.flatMap fun x => natBits x 8

/-- The block read from the 128 input nodes. -/
@[expose] def blockBytes (inp : Nat → Bool) : List Nat :=
  (List.range 16).map fun b => bv ((List.range 8).map fun j => inp (8 * b + j))

/-- The graph of AES: 128 input nodes followed by the compiled stages. -/
@[expose] def aesGraph (Nr : Nat) (rk : List (List Nat)) : List Wire × GB :=
  let i := mkInputs ⟨[]⟩ 128
  aesCircuit Nr rk i.2 i.1

end SmcIrred.AES
