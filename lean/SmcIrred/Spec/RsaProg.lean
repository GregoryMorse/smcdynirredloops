module

public import SmcIrred.Spec.BvDsl
public import SmcIrred.Spec.Arith

public section

namespace SmcIrred.RSA

/-! # The RSA graph program (`python/virt.py: modexp_virtual`, `modexp_window_to_virtual`, R15)

The modular exponentiation by a constant exponent is written with bit-vector expressions (`BvExp`) over the wires of
the previous product and compiled product by product with `BvExp.comp`, so every intermediate value is shared by everything
that reads it (the Python code shares them as subgraphs). One *Montgomery product* is the schoolbook product of two vectors
(one conditional shifted copy per bit of the second operand, summed) followed by `montgomeryREDC`: the low `B` bits, the
product with the constant `Np`, the low `B` bits, the product with the constant `N`, the sum, the shift by `B` and the
conditional subtraction of `N` (`montgomeryBound`). The windowed schedule is that of `winExp`: the table of the powers
`0 .. 2^w - 1` of the base in Montgomery form, then one table product per window and `w` squarings between windows;
the conversion into and out of Montgomery form are products with the constants `R2` and `1`.

The multiplier of the Python code (Karatsuba above 18 words, the add/subtract sequence for constants with few runs of ones,
constant folding of the first product) is not transcribed; those variants are covered at the level of values by
`Arith.KaratsubaCode`, `Arith.Ones` and `Arith.Eff` and by the native regeneration (evidence). -/

open SmcIrred

/-- A constant of `w` bits, as constant wires. -/
@[expose] def litW (n w : Nat) : BvExp := .inp ((List.range w).map fun j => Wire.cst (n.testBit j))

/-- The constant wires of the same constant. -/
@[expose] def constWires (n w : Nat) : List Wire := (List.range w).map fun j => Wire.cst (n.testBit j)

@[expose] def zeroE : BvExp := .inp []

/-- Shift left by `i` positions (zero wires below). -/
@[expose] def shiftE (a : BvExp) (i : Nat) : BvExp := .cat (.inp (List.replicate i (.cst false))) a

/-- The schoolbook product: one conditional shifted copy of `a` per bit of `b`, summed. -/
@[expose] def mulE (a b : BvExp) : BvExp :=
  (List.range b.width).foldl (fun acc i => .add acc (.ite (.slice b i 1) (shiftE a i) zeroE)) zeroE

/-- The difference `t - N` computed in `max (width t) (width N) + 1` bits: the top bit is the borrow. -/
@[expose] def boundD (t N : BvExp) : BvExp := .sub (.cat t (.inp [.cst false])) (.cat N (.inp [.cst false]))

/-- `montgomeryBound(t, N)`: subtract `N` once when `t ≥ N`; the borrow of the subtraction in one more bit selects. -/
@[expose] def boundE (t N : BvExp) : BvExp :=
  .ite (.slice (boundD t N) (max t.width N.width) 1) t (.slice (boundD t N) 0 (max t.width N.width))

/-- `m = (T mod R) * Np mod R`. -/
@[expose] def redcM (B Np : Nat) (T : BvExp) : BvExp := .slice (mulE (.slice T 0 B) (litW Np B)) 0 B

/-- `T + m * N`. -/
@[expose] def redcS (B N Np : Nat) (T : BvExp) : BvExp := .add T (mulE (redcM B Np T) (litW N B))

/-- `montgomeryREDC(T, B, R, N, Np)` with `R = 2^B`. -/
@[expose] def redcE (B N Np : Nat) (T : BvExp) : BvExp :=
  boundE (.slice (redcS B N Np T) B (redcS B N Np T).width) (litW N B)

/-- One Montgomery product on wires (the wires of the product are new nodes). -/
@[expose] def mmulG (B N Np : Nat) (gb : GB) (x y : List Wire) : List Wire × GB :=
  (redcE B N Np (mulE (.inp x) (.inp y))).comp gb

/-- One table step of `winTbl`, with the state threaded. -/
@[expose] def tblStepG (B N Np : Nat) (one b : List Wire) (st : List (List Wire) × GB) (k : Nat) :
    List (List Wire) × GB :=
  let j := k + 2
  let r := if j % 2 = 0 then mmulG B N Np st.2 (st.1.getD (j / 2) one) (st.1.getD (j / 2) one)
    else mmulG B N Np st.2 (st.1.getD (j - 1) one) b
  (st.1 ++ [r.1], r.2)

@[expose] def winTblG (B N Np : Nat) (one b : List Wire) (w : Nat) (gb : GB) : List (List Wire) × GB :=
  (List.range (2 ^ w - 2)).foldl (tblStepG B N Np one b) ([one, b], gb)

/-- The `w` squarings between two windows. -/
@[expose] def sqLoopG (B N Np w : Nat) (st : List Wire × GB) : List Wire × GB :=
  (List.range w).foldl (fun (s : List Wire × GB) _ => mmulG B N Np s.2 s.1 s.1) st

/-- One window: the product with the table entry of the window digit, then the squarings (none after the last window). -/
@[expose] def winStepG (B N Np : Nat) (one : List Wire) (T : List (List Wire)) (w e : Nat) (st : List Wire × GB)
    (j : Nat) : List Wire × GB :=
  let r := mmulG B N Np st.2 (T.getD ((e >>> (j * w)) &&& (2 ^ w - 1)) one) st.1
  if j = 0 then r else sqLoopG B N Np w r

/-- The main loop of `winExp` with the state threaded. -/
@[expose] def winExpG (B N Np : Nat) (one b : List Wire) (w e : Nat) (gb : GB) : List Wire × GB :=
  let T := winTblG B N Np one b w gb
  ((List.range ((B + w - 1) / w)).reverse).foldl (winStepG B N Np one T.1 w e) (one, T.2)

/-- `modexp_virtual` for a constant odd modulus and a constant exponent: into Montgomery form, windowed exponentiation, out. -/
@[expose] def rsaCircuit (B N Np R2 w e : Nat) (gb : GB) (W : List Wire) : List Wire × GB :=
  let x := mmulG B N Np gb W (constWires R2 B)
  let r := winExpG B N Np (constWires (Arith.redc B N Np R2) B) x.1 w e x.2
  mmulG B N Np r.2 r.1 (constWires 1 B)

/-- The graph of RSA with a `B`-bit modulus: `B` input nodes followed by the compiled products. -/
@[expose] def rsaGraph (B N Np R2 w e : Nat) : List Wire × GB :=
  let i := mkInputs ⟨[]⟩ B
  rsaCircuit B N Np R2 w e i.2 i.1

end SmcIrred.RSA
