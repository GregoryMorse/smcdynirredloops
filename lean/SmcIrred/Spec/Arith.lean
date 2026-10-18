module

public section

namespace SmcIrred.Arith

/-! Literal models of the arithmetic of `python/virt.py` (C54–C57, C59) on natural numbers. -/

/-- `montgomeryBound(T, N)` for the non-subtraction case: one conditional subtraction. -/
@[expose] def bound (t N : Nat) : Nat := if N ≤ t then t - N else t

/-- `montgomeryREDC(T, B, R, N, Np)` with `R = 2^B`, bit-mask branch. -/
@[expose] def redc (B N Np T : Nat) : Nat :=
  let m := ((T &&& (2 ^ B - 1)) * Np) &&& (2 ^ B - 1)
  bound ((T + m * N) >>> B) N

/-- One halving step of `montgomeryREDC_eff`: `(x + (N if x odd)) >> 1`. -/
@[expose] def effStep (N x : Nat) : Nat := (x + (if x &&& 1 ≠ 0 then N else 0)) >>> 1

/-- `montgomeryREDC_eff`: bit-serial reduction. -/
@[expose] def redcEff (B N T : Nat) : Nat :=
  bound ((List.range B).foldl (fun x _ => effStep N x) T) N

/-- `montgomeryREDC_mul_eff` (Dusse–Kaliski): interleaved bit-serial multiplication and reduction. -/
@[expose] def redcMulEff (B N T0 T1 : Nat) : Nat :=
  bound ((List.range B).foldl
    (fun x i => effStep N (x + (if (T0 >>> i) &&& 1 = 1 then T1 else 0))) 0) N

/-- The loop of `modexp`/`modexpMontgomery`: while `e > 0`, multiply the result by `b` when `e` is odd,
halve `e`, square `b`. Returns the final result and the final `b`. The multiplication and squaring are
parameters, so that values and operation counts are both read off from the same loop. -/
@[expose] def sqmulF {α : Type} (mulOp : α → α → α) (sqOp : α → α) : Nat → Nat → α → α → α × α
  | 0, _, res, b => (res, b)
  | f + 1, e, res, b =>
    if e = 0 then (res, b)
    else sqmulF mulOp sqOp f (e >>> 1) (if e &&& 1 ≠ 0 then mulOp res b else res) (sqOp b)

@[expose] def sqmul {α : Type} (mulOp : α → α → α) (sqOp : α → α) (e : Nat) (res b : α) : α :=
  (sqmulF mulOp sqOp e e res b).1

/-- `modexp(b, e, m)` of the reference code, with `modmul` read as multiplication modulo `m`. -/
@[expose] def modexp (m b e : Nat) : Nat :=
  if m = 1 then 0 else sqmul (fun x y => x * y % m) (fun x => x * x % m) e 1 (b % m)

/-- `modexpMontgomery(b, e, m, B, R, Np, R2)` for odd `m`. -/
@[expose] def modexpMont (B N Np R2 b e : Nat) : Nat :=
  if N = 1 then 0
  else sqmul (fun x y => redc B N Np (x * y)) (fun x => redc B N Np (x * x)) e (redc B N Np R2) b

/-- One table-building step of `modexpMontgomeryWindow` (entry `j = k + 2`): the square of entry `j/2` for
even `j`, entry `j-1` times `b` for odd `j`. -/
@[expose] def tblStep {α : Type} (mulOp : α → α → α) (one b : α) (t : List α) (k : Nat) : List α :=
  let j := k + 2
  t ++ [if j % 2 = 0 then mulOp (t.getD (j / 2) one) (t.getD (j / 2) one)
        else mulOp (t.getD (j - 1) one) b]

/-- The power table: entries `0` and `1`, then `2 ≤ j < 2^w`. -/
@[expose] def winTbl {α : Type} (mulOp : α → α → α) (one b : α) (w : Nat) : List α :=
  (List.range (2 ^ w - 2)).foldl (tblStep mulOp one b) [one, b]

/-- The main loop of `modexpMontgomeryWindow`: windows from the top; one table product per window,
and `w` squarings between windows. -/
@[expose] def winExp {α : Type} (mulOp : α → α → α) (one b : α) (B w e : Nat) : α :=
  let tbl := winTbl mulOp one b w
  ((List.range ((B + w - 1) / w)).reverse).foldl
    (fun res j =>
      let res := mulOp (tbl.getD ((e >>> (j * w)) &&& (2 ^ w - 1)) one) res
      if j = 0 then res else (List.range w).foldl (fun r _ => mulOp r r) res) one

/-- `modexpMontgomeryWindow` for odd `N ≠ 1` with window size `w`. -/
@[expose] def modexpMontWin (B N Np R2 w b e : Nat) : Nat :=
  if N = 1 then 0
  else winExp (fun x y => redc B N Np (x * y)) (redc B N Np R2) b B w e

/-- Number of multiplications of the table: one per entry `2 ≤ j < 2^w` (the loop of `winTbl`). -/
@[expose] def tblMuls (w : Nat) : Nat := (List.range (2 ^ w - 2)).foldl (fun c _ => c + 1) 0

/-- Number of multiplications in the window loop: one product per window and `w` squarings after every
window but the last (the loop of `winExp`). -/
@[expose] def loopMuls (B w : Nat) : Nat :=
  ((List.range ((B + w - 1) / w)).reverse).foldl (fun c j => c + 1 + (if j = 0 then 0 else w)) 0

/-- The cost of a window size `w` for `B`-bit exponents (the expression minimized in the code). -/
@[expose] def wCost (B w : Nat) : Nat := (B + w - 1) / w + 2 ^ w - 2

/-- `min((cost, w) for w in range(1, B.bit_length()))[1]` of the code. -/
@[expose] def bestW (B : Nat) : Nat :=
  let cands := (List.range (B.log2 + 1 - 1)).map fun i => (wCost B (i + 1), i + 1)
  match cands with
  | [] => 0
  | c :: cs => (cs.foldl (fun a p => if p.1 < a.1 ∨ (p.1 = a.1 ∧ p.2 < a.2) then p else a) c).2

/-- One Karatsuba step on operands split at bit `m`; `mulS` multiplies the three sub-operands. -/
@[expose] def kStep (mulS : Nat → Nat → Nat) (m a b : Nat) : Nat :=
  let a0 := a % 2 ^ m
  let b0 := b % 2 ^ m
  let a1 := a / 2 ^ m
  let b1 := b / 2 ^ m
  let z0 := mulS a0 b0
  let z2 := mulS a1 b1
  let z1 := mulS (a0 + a1) (b0 + b1)
  ((z2 <<< (2 * m)) ||| z0) + ((z1 - z0 - z2) <<< m)

/-- The squaring variant of the step (`num1 == num2` branch of `mulKaratsuba`). -/
@[expose] def kSqStep (mulS : Nat → Nat → Nat) (m a : Nat) : Nat :=
  let a0 := a % 2 ^ m
  let a1 := a / 2 ^ m
  let z0 := mulS a0 a0
  let z2 := mulS a1 a1
  let z1 := mulS a0 a1
  ((z2 <<< (2 * m)) ||| z0) + (z1 <<< (m + 1))

/-- Karatsuba recursion with the split points `ms` of the successive levels. -/
@[expose] def kmulS : List Nat → Nat → Nat → Nat
  | [], a, b => a * b
  | m :: ms, a, b => kStep (kmulS ms) m a b

/-- Number of base products: three per level. -/
@[expose] def kProds : List Nat → Nat
  | [] => 1
  | _ :: ms => 3 * kProds ms

/-- Toom-`k` product count: `2k - 1` sub-products per level. -/
@[expose] def toomProds (k : Nat) : Nat → Nat
  | 0 => 1
  | j + 1 => (2 * k - 1) * toomProds k j
/-- Bit length of `e` (`0 ↦ 0`). -/
@[expose] def bitLen (e : Nat) : Nat := if e = 0 then 0 else e.log2 + 1

/-- One step of `modexp_montgomery_ladder` for exponent bit `i`: one product `x1 * x2` and one squaring, in both
branches. -/
@[expose] def ladderStep {α : Type} (mulOp : α → α → α) (e : Nat) (x : α × α) (i : Nat) : α × α :=
  if e &&& (1 <<< i) = 0 then (mulOp x.1 x.1, mulOp x.1 x.2) else (mulOp x.1 x.2, mulOp x.2 x.2)

/-- `modexp_montgomery_ladder(b, e, m)`: start from `(b, b*b)` and process the bits below the top one. -/
@[expose] def ladder {α : Type} (mulOp : α → α → α) (b : α) (e : Nat) : α :=
  (((List.range (bitLen e - 1)).reverse).foldl (ladderStep mulOp e) (b, mulOp b b)).1

/-! ### Runs of ones (`get_consec_ones`, `consec_ones_to_num`) -/

/-- `while (num & 1) == 0: i += 1; num >>= 1` with fuel. -/
@[expose] def zerosLoop : Nat → Nat → Nat → Nat × Nat
  | 0, num, i => (num, i)
  | f + 1, num, i => if num &&& 1 = 0 then zerosLoop f (num >>> 1) (i + 1) else (num, i)

/-- `while (num & 1) == 1: i += 1; j += 1; num >>= 1` with fuel. -/
@[expose] def onesLoop : Nat → Nat → Nat → Nat → Nat × Nat × Nat
  | 0, num, i, j => (num, i, j)
  | f + 1, num, i, j => if num &&& 1 = 1 then onesLoop f (num >>> 1) (i + 1) (j + 1) else (num, i, j)

/-- The outer loop of `get_consec_ones`: for each run of ones, either one position (run of length 1)
or the pair (negative position, positive position). -/
@[expose] def consecGo : Nat → Nat → Nat → List Int
  | 0, _, _ => []
  | f + 1, num, i =>
    if num = 0 then []
    else
      let z := zerosLoop (num + 1) num i
      let o := onesLoop (z.1 + 1) z.1 z.2 0
      (if o.2.2 = 1 then [(o.2.1 : Int)] else [(o.2.2 : Int) - (o.2.1 : Int) - 1, (o.2.1 : Int) + 1]) ++
        consecGo f o.1 o.2.1

@[expose] def getConsecOnes (num : Nat) : List Int := consecGo (num + 1) num 0

/-- `consec_ones_to_num`. -/
@[expose] def consecToNum : List Int → Int
  | [] => 0
  | i :: t => (if 0 ≤ i then (2 : Int) ^ (i.toNat - 1) else -((2 : Int) ^ ((-i).toNat - 1))) + consecToNum t

/-- The multiplication `mul_consec_ones_virtual` performs on numbers: add or subtract shifted copies. -/
@[expose] def mulConsec (num : Int) : List Int → Int
  | [] => 0
  | i :: t =>
    (if 0 ≤ i then num * (2 : Int) ^ (i.toNat - 1) else -(num * (2 : Int) ^ ((-i).toNat - 1))) + mulConsec num t

end SmcIrred.Arith
