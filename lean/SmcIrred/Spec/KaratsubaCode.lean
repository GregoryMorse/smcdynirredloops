module

public import SmcIrred.Spec.Arith

public section

namespace SmcIrred.Arith

/-! # `doBigMul` / `mulKaratsuba` of `python/virt.py` with the bit-size arguments and the thresholds

The dispatch of `doBigMul`: word-size operands, or one operand of at most 32 bits, or a declared size of at most 4096 bits,
use the native product; otherwise `mulKaratsuba`. `mulKaratsuba` splits at `m2 = min(num1bits, num2bits) / 2` and passes the
declared sizes `m2`, `num1bits - m2`, and `num1bits - m2 + 1` (the extra carry bit of `low + high`) to its three sub-calls.
`fuel` bounds the recursion; at fuel `0` the native product is used (the recursion terminates, see `Arith.KaratsubaCode`). -/

/-- `mulKaratsuba(num1, num2, num1bits, num2bits)` with the sub-multiplier `rec` (`doBigMul`). -/
@[expose] def mulK (rec : Nat → Nat → Nat → Nat → Nat) (a b n1 n2 : Nat) : Nat :=
  let m2 := min n1 n2 / 2
  let low1 := a % 2 ^ m2
  let low2 := b % 2 ^ m2
  let high1 := a / 2 ^ m2
  let high2 := b / 2 ^ m2
  let z0 := rec low1 low2 m2 m2
  let z2 := rec high1 high2 (n1 - m2) (n2 - m2)
  if a = b then
    let z1 := rec low1 high1 m2 (n1 - m2)
    ((z2 <<< (2 * m2)) ||| z0) + (z1 <<< (m2 + 1))
  else
    let z1 := rec (low1 + high1) (low2 + high2) (n1 - m2 + 1) (n2 - m2 + 1)
    ((z2 <<< (2 * m2)) ||| z0) + ((z1 - z0 - z2) <<< m2)

/-- `doBigMul(num1, num2, num1bits, num2bits)` with recursion depth bound `fuel`. -/
@[expose] def doBig : Nat → Nat → Nat → Nat → Nat → Nat
  | 0, a, b, _, _ => a * b
  | f + 1, a, b, n1, n2 =>
    if a ≤ 0xFFFFFFFF ∧ b ≤ 0xFFFFFFFF then a * b
    else if a ≤ 0xFFFFFFFF ∨ b ≤ 0xFFFFFFFF ∨ n1 ≤ 4096 ∨ n2 ≤ 4096 then a * b
    else mulK (doBig f) a b n1 n2

end SmcIrred.Arith
