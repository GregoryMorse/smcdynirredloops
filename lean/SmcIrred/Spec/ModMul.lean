module

public section

namespace SmcIrred.Arith

/-! # The bit-serial `modmul` of `python/virt.py`

```python
def modmul(a, b, m):
  d, mp2 = 0, m >> 1
  if a >= m or a < 0: a %= m
  if b >= m or b < 0: b %= m
  bits = getBitSize(a)
  if bits == 0: return 0
  check = 1 << (bits - 1)
  for i in range(bits):
    d = (d << 1) - m if (d > mp2) else d << 1
    if (a & check) != 0: d += b
    if d >= m: d -= m
    a <<= 1
  return d
```
The loop scans the bits of `a` from the most significant one; `modmulStep` is one pass of its body. -/

/-- One pass of the loop body for the bit `x` of `a`. -/
@[expose] def modmulStep (m b d x : Nat) : Nat :=
  let d1 := if d > m / 2 then 2 * d - m else 2 * d
  let d2 := if x != 0 then d1 + b else d1
  if d2 ≥ m then d2 - m else d2

/-- The bits of `a`, most significant first (no leading zero). -/
@[expose] def msbBits (a : Nat) : List Nat :=
  if h : a = 0 then [] else msbBits (a / 2) ++ [a % 2]
termination_by a
decreasing_by omega

/-- `modmul(a, b, m)` for natural numbers. -/
@[expose] def modmulBit (a b m : Nat) : Nat :=
  (msbBits (a % m)).foldl (modmulStep m (b % m)) 0

/-- The value of bits (most significant first) read from the initial value `v`. -/
@[expose] def msbVal (v : Nat) (l : List Nat) : Nat := l.foldl (fun acc x => 2 * acc + x) v

end SmcIrred.Arith
