module

public import SmcIrred.Spec.Circuit

public section

/-! The generator of the Boolean graph (`python/virt.py`), its bit-vector DSL, the AES specification and the evaluator, in one
module: Lean reuses the compiler's auxiliary pattern-matching definitions (`match_N`, `_sparseCasesOn_N`) only inside one
file, and the generated Challenge (`ChallengeAES.lean`) is one file, so these declarations must be elaborated in one module
for the Challenge to define exactly the constants of the development (Palomar's Comparator compares them). The former
modules `Virt`, `VirtSel`, `BvDsl`, `AES`, `AESProg` and `Eval` re-export this module. -/

namespace SmcIrred

/-!
# Literal transcription of the graph generators (`python/virt.py`, `BITSZ = 1`)

A wire is a constant or a graph node. The generator state `GB` is the list of nodes (kind and predecessors); the Python
dictionary of successor lists `g` is replaced by predecessor lists (the evaluator reads predecessors), and the vertex numbering
starts at `0` (the Python numbering starts at `1`, node `0` being the start vertex). Python sets are modelled by duplicate-free
lists (`eraseDups`; the order of a set is not significant for any statement made here). Constant folding is kept exactly as in
`and_to_virtual`, `or_to_virtual`, `xor_to_virtual`, `not_to_virtual`, `multi_to_virtual`, `cmp_zero_to_virtual`,
`decoder_shift_to_virtual`, `decoder_to_virtual`, `addition_bit_to_virtual`, `addition_to_virtual`.

`not_to_virtual` of a *constant* indexes `g[True]` in the Python code; the model folds the constant instead (see
`lean/CODE_FIXES.md`).
-/

inductive Wire
  | cst (b : Bool)
  | nd (i : Nat)

/-- Decidable equality, written out (a derived instance carries the name of its module in a private helper, which differs between
the development and the single-file Challenge). -/
@[expose] instance instDecidableEqWire : DecidableEq Wire := fun a b =>
  match a, b with
  | .cst x, .cst y => if h : x = y then isTrue (by subst h; rfl) else isFalse (by intro e; cases e; exact h rfl)
  | .nd i, .nd j => if h : i = j then isTrue (by subst h; rfl) else isFalse (by intro e; cases e; exact h rfl)
  | .cst _, .nd _ => isFalse (by intro e; cases e)
  | .nd _, .cst _ => isFalse (by intro e; cases e)

@[expose] def Wire.isc : Wire → Bool
  | .cst _ => true
  | .nd _ => false

@[expose] def Wire.idx : Wire → Nat
  | .cst _ => 0
  | .nd i => i

/-- The generator state: the nodes created so far (the node `i` is the `i`-th entry). -/
structure GB where
  nodes : List (Kind × List Nat)

@[expose] def GB.n (gb : GB) : Nat := gb.nodes.length

/-- The number of predecessor edges of the generated graph. -/
@[expose] def GB.e (gb : GB) : Nat := (gb.nodes.map fun x => x.2.length).sum

/-- A fresh node (kind and predecessors). -/
@[expose] def GB.add (gb : GB) (k : Kind) (ps : List Nat) : Wire × GB :=
  (.nd gb.n, ⟨gb.nodes ++ [(k, ps)]⟩)

/-- `make_input`: `k` input nodes (`FLOW`, no predecessors). -/
@[expose] def mkInputs (gb : GB) : Nat → List Wire × GB
  | 0 => ([], gb)
  | k + 1 =>
    let r := gb.add .flow []
    let t := mkInputs r.2 k
    (r.1 :: t.1, t.2)

/-- Thread the generator through a list. -/
@[expose] def mapG {α β : Type} (f : GB → α → β × GB) : GB → List α → List β × GB
  | gb, [] => ([], gb)
  | gb, a :: l =>
    let r := f gb a
    let t := mapG f r.2 l
    (r.1 :: t.1, t.2)

/-- `not_to_virtual`. -/
@[expose] def notV (gb : GB) (w : Wire) : Wire × GB :=
  match w with
  | .cst b => (.cst !b, gb)
  | .nd i => gb.add .addneg [i]

/-- The duplicate-free copy of a list (a Python `set`), keeping first occurrences. -/
@[expose] def dedupW (l : List Wire) : List Wire :=
  l.foldl (fun acc a => if acc.contains a then acc else acc ++ [a]) []

/-- `and_to_virtual`. -/
@[expose] def andV (gb : GB) (ws : List Wire) : Wire × GB :=
  if ws.all Wire.isc then (.cst (ws.all fun w => w == .cst true), gb)
  else if ws.any fun w => w == .cst false then (.cst false, gb)
  else
    match dedupW (ws.filter fun w => !w.isc) with
    | [w] => (w, gb)
    | nums => gb.add .flow (nums.map Wire.idx)

/-- `or_to_virtual`. -/
@[expose] def orV (gb : GB) (ws : List Wire) : Wire × GB :=
  if ws.all Wire.isc then (.cst (ws.any fun w => w == .cst true), gb)
  else if ws.any fun w => w == .cst true then (.cst true, gb)
  else
    match dedupW (ws.filter fun w => !w.isc) with
    | [w] => (w, gb)
    | nums => gb.add .any (nums.map Wire.idx)

/-- The duplicate-cancelling set of `xor_to_virtual`. -/
@[expose] def toggle (l : List Wire) : List Wire :=
  l.foldl (fun acc x => if acc.contains x then acc.erase x else acc ++ [x]) []

/-- `xor_to_virtual`. -/
@[expose] def xorV (gb : GB) (ws : List Wire) : Wire × GB :=
  let flip := ((ws.filter fun w => w == .cst true).length % 2 == 1)
  if ws.all Wire.isc then (.cst flip, gb)
  else
    match toggle (ws.filter fun w => !w.isc) with
    | [] => (.cst flip, gb)
    | [w] => if flip then notV gb w else (w, gb)
    | nums => gb.add (if flip then .addneg else .add) (nums.map Wire.idx)

/-- `zero_extend_virtual`: pad a number with constant zeros. -/
@[expose] def zeroExt (n : Nat) (ws : List Wire) : List Wire := ws ++ List.replicate (n - ws.length) (.cst false)

/-- `multi_to_virtual` for two numbers and a bitwise operation on a pair of wires. -/
@[expose] def multiV (f : GB → List Wire → Wire × GB) (gb : GB) (a b : List Wire) : List Wire × GB :=
  let m := max a.length b.length
  mapG (fun gb p => f gb [p.1, p.2]) gb ((zeroExt m a).zip (zeroExt m b))

/-- `bit_length` of a natural number. -/
@[expose] def bitLen : Nat → Nat
  | 0 => 0
  | n + 1 => bitLen ((n + 1) / 2) + 1
termination_by n => n
decreasing_by omega

/-- `constant_to_virtual`. -/
@[expose] def constBits (x : Nat) : List Wire := (List.range (bitLen x)).map fun j => .cst (x.testBit j)

/-- `cmp_zero_to_virtual(·, False)`: the output is accepting iff all the bits are zero. -/
@[expose] def cmpZeroV (gb : GB) (bits : List Wire) : Wire × GB :=
  if bits.length == 0 then (.cst true, gb)
  else
    let r := orV gb bits
    notV r.2 r.1

/-- `decoder_shift_to_virtual`: the loop body for one bit `s` of the argument. -/
@[expose] def decStep (gb : GB) (num : List Wire) (s : Wire) : List Wire × GB :=
  let r0 := notV gb s
  let r1 := mapG (fun gb w => andV gb [w, r0.1]) r0.2 num
  let r2 := mapG (fun gb w => andV gb [w, s]) r1.2 num
  (r1.1 ++ r2.1, r2.2)

@[expose] def decLoop : GB → List Wire → List Wire → List Wire × GB
  | gb, num, [] => (num, gb)
  | gb, num, s :: rest =>
    let r := decStep gb num s
    decLoop r.2 r.1 rest

@[expose] def decoderShift (gb : GB) (shift : List Wire) : List Wire × GB :=
  decLoop gb [.cst true] shift

/-- `decoder_to_virtual`: one output per value `i < 2^m`. -/
@[expose] def decoderOne (gb : GB) (shift : List Wire) (i : Nat) : Wire × GB :=
  let r := multiV xorV gb (constBits i) shift
  cmpZeroV r.2 r.1

@[expose] def decoder (gb : GB) (shift : List Wire) : List Wire × GB :=
  mapG (fun gb i => decoderOne gb shift i) gb (List.range (2 ^ shift.length))

/-- `addition_bit_to_virtual` with `need_carry = True`: the sum bit and the carry (borrow) out. -/
@[expose] def addBit (gb : GB) (n1 n2 carry issub : Wire) : (Wire × Wire) × GB :=
  let a := xorV gb [issub, n1]
  let num1sub := a.1
  if (!carry.isc) && ((n1.isc && num1sub == .cst true && !n2.isc) || (!n1.isc && n2.isc && n2 == .cst true)) then
    let res := xorV a.2 [n1, n2, carry]
    let t := andV res.2 [num1sub, n2]
    let c := orV t.2 [t.1, carry]
    ((res.1, c.1), c.2)
  else
    let s := xorV a.2 [n1, n2]
    let res := xorV s.2 [carry, s.1]
    if carry.isc && carry == .cst true then
      let c := orV res.2 [num1sub, n2]
      ((res.1, c.1), c.2)
    else
      let x := xorV res.2 [issub, s.1]
      let c0 := andV x.2 [carry, x.1]
      let t := andV c0.2 [num1sub, n2]
      let c := xorV t.2 [t.1, c0.1]
      ((res.1, c.1), c.2)

/-- `addition_bit_to_virtual` with `need_carry = False`. -/
@[expose] def addBitNoCarry (gb : GB) (n1 n2 carry : Wire) : Wire × GB := xorV gb [n1, n2, carry]

/-- `addition_to_virtual`: ripple loop over the bit pairs; the last pair appends the final carry (borrow). -/
@[expose] def addLoop (issub : Wire) (needCarry : Bool) : GB → Wire → List (Wire × Wire) → List Wire × GB
  | gb, _, [] => ([], gb)
  | gb, carry, [p] =>
    if needCarry then
      let r := addBit gb p.1 p.2 carry issub
      ([r.1.1, r.1.2], r.2)
    else
      let r := addBitNoCarry gb p.1 p.2 carry
      ([r.1], r.2)
  | gb, carry, p :: rest =>
    let r := addBit gb p.1 p.2 carry issub
    let t := addLoop issub needCarry r.2 r.1.2 rest
    (r.1.1 :: t.1, t.2)

@[expose] def addition (gb : GB) (a b : List Wire) (issub : Wire) (needCarry : Bool) : List Wire × GB :=
  let m := max a.length b.length
  addLoop issub needCarry gb (.cst false) ((zeroExt m a).zip (zeroExt m b))

/-- The number represented by a little-endian bit list. -/
@[expose] def bv : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * bv bs

/-- The one-hot vector of length `n` with the hot position `x`. -/
@[expose] def oneHot (n x : Nat) : List Bool := (List.range n).map fun p => p == x

/-- The circuit of a generator state. -/
@[expose] def GB.toCirc (gb : GB) : Circ where
  n := gb.nodes.length
  kind := fun v => (gb.nodes.getD v (.flow, [])).1
  pred := fun v => (gb.nodes.getD v (.flow, [])).2

end SmcIrred

namespace SmcIrred

/-! # Selection and table lookup of the legacy generator (`python/virt.py`, G30/R13)

`selV` is `multi_selection_to_virtual` for one bit (`BITSZ = 1`): the list of selector wires is scanned; a constant false
selector is skipped, a constant true one returns the number at its position at once, a constant number selects with the
selector alone, otherwise the selector and the number are `AND`ed; the surviving terms are `XOR`ed. `colsV` is
`multi_to_virtual` for several numbers (zero extension, one call per bit position), `iteV` is `selection_to_virtual` and
`tableLookupV` is `table_lookup_virtual` without the subgraph indirection (the decoder is built inline). -/

/-- The scan of `multi_selection_to_virtual`: the early return (`some`), the surviving terms and the state. -/
@[expose] def selLoop : GB → List Wire → List Wire → List Wire → Option Wire × List Wire × GB
  | gb, acc, s :: ss, n :: ns =>
    match s with
    | .cst false => selLoop gb acc ss ns
    | .cst true => (some n, acc, gb)
    | .nd i =>
      match n with
      | .cst true => selLoop gb (acc ++ [.nd i]) ss ns
      | .cst false => selLoop gb acc ss ns
      | .nd j =>
        let r := andV gb [.nd i, .nd j]
        selLoop r.2 (acc ++ [r.1]) ss ns
  | gb, acc, _, _ => (none, acc, gb)

/-- `multi_selection_to_virtual` for one-bit numbers. -/
@[expose] def selV (gb : GB) (sels nums : List Wire) : Wire × GB :=
  match selLoop gb [] sels nums with
  | (some w, _, gb') => (w, gb')
  | (none, [], gb') => (.cst false, gb')
  | (none, acc, gb') => xorV gb' acc

/-- `multi_to_virtual` for a list of numbers: zero extension to the longest, one call of `f` per bit position. -/
@[expose] def colsV (f : GB → List Wire → Wire × GB) (gb : GB) (nums : List (List Wire)) : List Wire × GB :=
  let m := (nums.map List.length).foldl max 0
  mapG (fun gb j => f gb ((nums.map (zeroExt m)).map fun x => x.getD j (.cst false))) gb (List.range m)

/-- `selection_to_virtual(selector, a, b)`: `a` where the selector wire is true, else `b`; the negation is rebuilt per bit. -/
@[expose] def iteV (gb : GB) (s : Wire) (a b : List Wire) : List Wire × GB :=
  colsV (fun gb col => let r0 := notV gb s; selV r0.2 [s, r0.1] col) gb [a, b]

/-- `table_lookup_virtual` (decoder inline): the entries of the table are constants. -/
@[expose] def tableLookupV (gb : GB) (idx : List Wire) (tab : List Nat) : List Wire × GB :=
  let d := decoderShift gb idx
  colsV (fun gb col => selV gb d.1 col) d.2 (tab.map constBits)

/-- The width of the entries of a table (`mlen` of `zero_extend_virtual`). -/
@[expose] def tblW (tab : List Nat) : Nat := ((tab.map bitLen).foldl max 0)

end SmcIrred

namespace SmcIrred

/-! # A bit-vector expression language and its compiler to the graph generator (C48, G30 b)

Bit vectors are little-endian lists of wires of the generator state (`Wire.nd i` is the node `i`, `Wire.cst b` a constant).
`BvExp.sem v e` is the meaning of an expression when the wires have the values `v`; `BvExp.comp gb e` emits the nodes of the
expression with the legacy primitives (`notV`, `andV`, `orV`, `xorV` through `multiV`/`mapG`, `addition`) and returns the
output wires and the extended state. `Prims.BvDsl` proves that the output wires evaluate to `sem`. -/

/-- The bits of a natural number in `m` positions, least significant first. -/
@[expose] def natBits : Nat → Nat → List Bool
  | _, 0 => []
  | i, m + 1 => decide (i % 2 = 1) :: natBits (i / 2) m

/-- Pad a bit list with zeros to `m` bits. -/
@[expose] def padB (m : Nat) (l : List Bool) : List Bool := l ++ List.replicate (m - l.length) false

/-- A bitwise operation on two bit vectors zero-extended to the longer length. -/
@[expose] def bitwiseB (f : Bool → Bool → Bool) (a b : List Bool) : List Bool :=
  ((padB (max a.length b.length) a).zip (padB (max a.length b.length) b)).map fun p => f p.1 p.2

inductive BvExp where
  | inp (ws : List Wire)
  | lit (n : Nat)
  | bnot (a : BvExp)
  | band (a b : BvExp)
  | bor (a b : BvExp)
  | bxor (a b : BvExp)
  | add (a b : BvExp)
  | sub (a b : BvExp)
  /-- `n` bits of `a` from position `i` (wires only, no nodes). -/
  | slice (a : BvExp) (i n : Nat)
  /-- Concatenation, the bits of `a` first. -/
  | cat (a b : BvExp)
  /-- `selection_to_virtual`: `a` if the lowest bit of `c` is set, else `b` (zero extended to the longer). -/
  | ite (c a b : BvExp)
  /-- `table_lookup_virtual`: the entry of the constant table selected by `idx`. -/
  | tbl (idx : BvExp) (tab : List Nat)

/-- The width of the result of an addition: the longer width plus the carry bit (an addition of two empty vectors is empty). -/
@[expose] def addWidth (m : Nat) : Nat := if m = 0 then 0 else m + 1

/-- The static width of the result. -/
@[expose] def BvExp.width : BvExp → Nat
  | .inp ws => ws.length
  | .lit n => bitLen n
  | .bnot a => a.width
  | .band a b => max a.width b.width
  | .bor a b => max a.width b.width
  | .bxor a b => max a.width b.width
  | .add a b => addWidth (max a.width b.width)
  | .sub a b => max a.width b.width
  | .slice a i n => min n (a.width - i)
  | .cat a b => a.width + b.width
  | .ite _ a b => max a.width b.width
  | .tbl _ tab => tblW tab

/-- Meaning of an expression when the wires have the values `v`. Addition is the sum with its carry bit, subtraction the
difference modulo `2^m` for the longer width `m`. -/
@[expose] def BvExp.sem (v : Wire → Bool) : BvExp → List Bool
  | .inp ws => ws.map v
  | .lit n => natBits n (bitLen n)
  | .bnot a => (a.sem v).map (fun b => !b)
  | .band a b => bitwiseB (fun x y => x && y) (a.sem v) (b.sem v)
  | .bor a b => bitwiseB (fun x y => x || y) (a.sem v) (b.sem v)
  | .bxor a b => bitwiseB (fun x y => x != y) (a.sem v) (b.sem v)
  | .add a b =>
    natBits (bv (a.sem v) + bv (b.sem v)) (addWidth (max (a.sem v).length (b.sem v).length))
  | .sub a b =>
    natBits ((bv (a.sem v) + 2 ^ max (a.sem v).length (b.sem v).length - bv (b.sem v)) %
      2 ^ max (a.sem v).length (b.sem v).length) (max (a.sem v).length (b.sem v).length)
  | .slice a i n => ((a.sem v).drop i).take n
  | .cat a b => a.sem v ++ b.sem v
  | .ite c a b =>
    if (c.sem v).getD 0 false then padB (max (a.sem v).length (b.sem v).length) (a.sem v)
    else padB (max (a.sem v).length (b.sem v).length) (b.sem v)
  | .tbl idx tab => natBits (tab.getD (bv (idx.sem v)) 0) (tblW tab)

/-- The compiler: nodes emitted left to right, the second operand in the state after the first. -/
@[expose] def BvExp.comp : GB → BvExp → List Wire × GB
  | gb, .inp ws => (ws, gb)
  | gb, .lit n => (constBits n, gb)
  | gb, .bnot a => mapG (fun g w => notV g w) (a.comp gb).2 (a.comp gb).1
  | gb, .band a b =>
    multiV andV (b.comp (a.comp gb).2).2 (a.comp gb).1 (b.comp (a.comp gb).2).1
  | gb, .bor a b =>
    multiV orV (b.comp (a.comp gb).2).2 (a.comp gb).1 (b.comp (a.comp gb).2).1
  | gb, .bxor a b =>
    multiV xorV (b.comp (a.comp gb).2).2 (a.comp gb).1 (b.comp (a.comp gb).2).1
  | gb, .add a b =>
    addition (b.comp (a.comp gb).2).2 (a.comp gb).1 (b.comp (a.comp gb).2).1 (.cst false) true
  | gb, .sub a b =>
    addition (b.comp (a.comp gb).2).2 (a.comp gb).1 (b.comp (a.comp gb).2).1 (.cst true) false
  | gb, .slice a i n => (((a.comp gb).1.drop i).take n, (a.comp gb).2)
  | gb, .cat a b => ((a.comp gb).1 ++ (b.comp (a.comp gb).2).1, (b.comp (a.comp gb).2).2)
  | gb, .ite c a b =>
    iteV (b.comp (a.comp (c.comp gb).2).2).2 ((c.comp gb).1.getD 0 (.cst false))
      (a.comp (c.comp gb).2).1 (b.comp (a.comp (c.comp gb).2).2).1
  | gb, .tbl idx tab => tableLookupV (idx.comp gb).2 (idx.comp gb).1 tab

/-- The wire exists in a state with `n` nodes. -/
@[expose] def Wire.inb (n : Nat) : Wire → Prop
  | .cst _ => True
  | .nd i => i < n

/-- All the wires read by the expression exist in the state with `n` nodes. -/
@[expose] def BvExp.ok (n : Nat) : BvExp → Prop
  | .inp ws => ∀ w ∈ ws, w.inb n
  | .lit _ => True
  | .bnot a => a.ok n
  | .band a b => a.ok n ∧ b.ok n
  | .bor a b => a.ok n ∧ b.ok n
  | .bxor a b => a.ok n ∧ b.ok n
  | .add a b => a.ok n ∧ b.ok n
  | .sub a b => a.ok n ∧ b.ok n
  | .slice a _ _ => a.ok n
  | .cat a b => a.ok n ∧ b.ok n
  | .ite c a b => c.ok n ∧ a.ok n ∧ b.ok n
  | .tbl idx tab => idx.ok n ∧ tab.length = 2 ^ idx.width

end SmcIrred

namespace SmcIrred.AES

/-! Specification of AES (FIPS-197) on bytes represented as `Nat` below 256. The state is a flat list of 16
bytes, column-major (index `4c + r`), as in `python/aes.py`. -/

/-- Multiplication by `x` in GF(2^8) modulo 0x11B (`aes.py: xtime`). -/
@[expose] def xtime (a : Nat) : Nat := if a &&& 0x80 ≠ 0 then ((a <<< 1) ^^^ 0x1B) &&& 0xFF else a <<< 1

@[expose] def gmulAux : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, acc => acc
  | n + 1, a, b, acc => gmulAux n (xtime a) (b >>> 1) (if b &&& 1 ≠ 0 then acc ^^^ a else acc)

/-- Multiplication in GF(2^8) modulo 0x11B (shift-and-add over eight bits). -/
@[expose] def gmul (a b : Nat) : Nat := gmulAux 8 a b 0

@[expose] def gpowAux : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, acc => acc
  | n + 1, b, e, acc => gpowAux n (gmul b b) (e >>> 1) (if e &&& 1 ≠ 0 then gmul acc b else acc)

/-- `a ^ e` in GF(2^8) by square-and-multiply, for exponents below 256. -/
@[expose] def gpow (a e : Nat) : Nat := gpowAux 8 a e 1

/-- Multiplicative inverse in GF(2^8) (`0 ↦ 0`), computed as `a^254`. -/
@[expose] def ginv (a : Nat) : Nat := gpow a 254

@[expose] def rotl8 (x k : Nat) : Nat := ((x <<< k) ||| (x >>> (8 - k))) &&& 0xFF

/-- The affine map of the S-box (FIPS-197 (5.2)). -/
@[expose] def affine (b : Nat) : Nat :=
  b ^^^ rotl8 b 1 ^^^ rotl8 b 2 ^^^ rotl8 b 3 ^^^ rotl8 b 4 ^^^ 0x63

/-- The inverse affine map (FIPS-197 (5.14)). -/
@[expose] def invAffine (b : Nat) : Nat := rotl8 b 1 ^^^ rotl8 b 3 ^^^ rotl8 b 6 ^^^ 0x05

/-- S-box: multiplicative inverse followed by the affine map. -/
@[expose] def sbox (x : Nat) : Nat := affine (ginv x)

/-- Inverse S-box: inverse affine map followed by the multiplicative inverse. -/
@[expose] def invSbox (x : Nat) : Nat := ginv (invAffine x)

/-- The S-box table of `aes.py` (`s_box`). -/
@[expose] def sBoxTable : List Nat :=
  [
    0x63, 0x7C, 0x77, 0x7B, 0xF2, 0x6B, 0x6F, 0xC5, 0x30, 0x01, 0x67, 0x2B, 0xFE, 0xD7, 0xAB, 0x76, 
    0xCA, 0x82, 0xC9, 0x7D, 0xFA, 0x59, 0x47, 0xF0, 0xAD, 0xD4, 0xA2, 0xAF, 0x9C, 0xA4, 0x72, 0xC0, 
    0xB7, 0xFD, 0x93, 0x26, 0x36, 0x3F, 0xF7, 0xCC, 0x34, 0xA5, 0xE5, 0xF1, 0x71, 0xD8, 0x31, 0x15, 
    0x04, 0xC7, 0x23, 0xC3, 0x18, 0x96, 0x05, 0x9A, 0x07, 0x12, 0x80, 0xE2, 0xEB, 0x27, 0xB2, 0x75, 
    0x09, 0x83, 0x2C, 0x1A, 0x1B, 0x6E, 0x5A, 0xA0, 0x52, 0x3B, 0xD6, 0xB3, 0x29, 0xE3, 0x2F, 0x84, 
    0x53, 0xD1, 0x00, 0xED, 0x20, 0xFC, 0xB1, 0x5B, 0x6A, 0xCB, 0xBE, 0x39, 0x4A, 0x4C, 0x58, 0xCF, 
    0xD0, 0xEF, 0xAA, 0xFB, 0x43, 0x4D, 0x33, 0x85, 0x45, 0xF9, 0x02, 0x7F, 0x50, 0x3C, 0x9F, 0xA8, 
    0x51, 0xA3, 0x40, 0x8F, 0x92, 0x9D, 0x38, 0xF5, 0xBC, 0xB6, 0xDA, 0x21, 0x10, 0xFF, 0xF3, 0xD2, 
    0xCD, 0x0C, 0x13, 0xEC, 0x5F, 0x97, 0x44, 0x17, 0xC4, 0xA7, 0x7E, 0x3D, 0x64, 0x5D, 0x19, 0x73, 
    0x60, 0x81, 0x4F, 0xDC, 0x22, 0x2A, 0x90, 0x88, 0x46, 0xEE, 0xB8, 0x14, 0xDE, 0x5E, 0x0B, 0xDB, 
    0xE0, 0x32, 0x3A, 0x0A, 0x49, 0x06, 0x24, 0x5C, 0xC2, 0xD3, 0xAC, 0x62, 0x91, 0x95, 0xE4, 0x79, 
    0xE7, 0xC8, 0x37, 0x6D, 0x8D, 0xD5, 0x4E, 0xA9, 0x6C, 0x56, 0xF4, 0xEA, 0x65, 0x7A, 0xAE, 0x08, 
    0xBA, 0x78, 0x25, 0x2E, 0x1C, 0xA6, 0xB4, 0xC6, 0xE8, 0xDD, 0x74, 0x1F, 0x4B, 0xBD, 0x8B, 0x8A, 
    0x70, 0x3E, 0xB5, 0x66, 0x48, 0x03, 0xF6, 0x0E, 0x61, 0x35, 0x57, 0xB9, 0x86, 0xC1, 0x1D, 0x9E, 
    0xE1, 0xF8, 0x98, 0x11, 0x69, 0xD9, 0x8E, 0x94, 0x9B, 0x1E, 0x87, 0xE9, 0xCE, 0x55, 0x28, 0xDF, 
    0x8C, 0xA1, 0x89, 0x0D, 0xBF, 0xE6, 0x42, 0x68, 0x41, 0x99, 0x2D, 0x0F, 0xB0, 0x54, 0xBB, 0x16]

/-- The inverse S-box table of `aes.py` (`inv_s_box`). -/
@[expose] def invSBoxTable : List Nat :=
  [
    0x52, 0x09, 0x6A, 0xD5, 0x30, 0x36, 0xA5, 0x38, 0xBF, 0x40, 0xA3, 0x9E, 0x81, 0xF3, 0xD7, 0xFB, 
    0x7C, 0xE3, 0x39, 0x82, 0x9B, 0x2F, 0xFF, 0x87, 0x34, 0x8E, 0x43, 0x44, 0xC4, 0xDE, 0xE9, 0xCB, 
    0x54, 0x7B, 0x94, 0x32, 0xA6, 0xC2, 0x23, 0x3D, 0xEE, 0x4C, 0x95, 0x0B, 0x42, 0xFA, 0xC3, 0x4E, 
    0x08, 0x2E, 0xA1, 0x66, 0x28, 0xD9, 0x24, 0xB2, 0x76, 0x5B, 0xA2, 0x49, 0x6D, 0x8B, 0xD1, 0x25, 
    0x72, 0xF8, 0xF6, 0x64, 0x86, 0x68, 0x98, 0x16, 0xD4, 0xA4, 0x5C, 0xCC, 0x5D, 0x65, 0xB6, 0x92, 
    0x6C, 0x70, 0x48, 0x50, 0xFD, 0xED, 0xB9, 0xDA, 0x5E, 0x15, 0x46, 0x57, 0xA7, 0x8D, 0x9D, 0x84, 
    0x90, 0xD8, 0xAB, 0x00, 0x8C, 0xBC, 0xD3, 0x0A, 0xF7, 0xE4, 0x58, 0x05, 0xB8, 0xB3, 0x45, 0x06, 
    0xD0, 0x2C, 0x1E, 0x8F, 0xCA, 0x3F, 0x0F, 0x02, 0xC1, 0xAF, 0xBD, 0x03, 0x01, 0x13, 0x8A, 0x6B, 
    0x3A, 0x91, 0x11, 0x41, 0x4F, 0x67, 0xDC, 0xEA, 0x97, 0xF2, 0xCF, 0xCE, 0xF0, 0xB4, 0xE6, 0x73, 
    0x96, 0xAC, 0x74, 0x22, 0xE7, 0xAD, 0x35, 0x85, 0xE2, 0xF9, 0x37, 0xE8, 0x1C, 0x75, 0xDF, 0x6E, 
    0x47, 0xF1, 0x1A, 0x71, 0x1D, 0x29, 0xC5, 0x89, 0x6F, 0xB7, 0x62, 0x0E, 0xAA, 0x18, 0xBE, 0x1B, 
    0xFC, 0x56, 0x3E, 0x4B, 0xC6, 0xD2, 0x79, 0x20, 0x9A, 0xDB, 0xC0, 0xFE, 0x78, 0xCD, 0x5A, 0xF4, 
    0x1F, 0xDD, 0xA8, 0x33, 0x88, 0x07, 0xC7, 0x31, 0xB1, 0x12, 0x10, 0x59, 0x27, 0x80, 0xEC, 0x5F, 
    0x60, 0x51, 0x7F, 0xA9, 0x19, 0xB5, 0x4A, 0x0D, 0x2D, 0xE5, 0x7A, 0x9F, 0x93, 0xC9, 0x9C, 0xEF, 
    0xA0, 0xE0, 0x3B, 0x4D, 0xAE, 0x2A, 0xF5, 0xB0, 0xC8, 0xEB, 0xBB, 0x3C, 0x83, 0x53, 0x99, 0x61, 
    0x17, 0x2B, 0x04, 0x7E, 0xBA, 0x77, 0xD6, 0x26, 0xE1, 0x69, 0x14, 0x63, 0x55, 0x21, 0x0C, 0x7D]

/-- The round constant table of `aes.py` (`r_con`). -/
@[expose] def rconTable : List Nat :=
  [
    0x00, 0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1B, 0x36, 0x6C, 0xD8, 0xAB, 0x4D, 0x9A, 
    0x2F, 0x5E, 0xBC, 0x63, 0xC6, 0x97, 0x35, 0x6A, 0xD4, 0xB3, 0x7D, 0xFA, 0xEF, 0xC5, 0x91, 0x39]

@[expose] def subBytes (s : List Nat) : List Nat := s.map sbox
@[expose] def invSubBytes (s : List Nat) : List Nat := s.map invSbox

@[expose] def shiftRows (s : List Nat) : List Nat :=
  (List.range 16).map fun i => s.getD (4 * (((i / 4) + (i % 4)) % 4) + i % 4) 0

@[expose] def invShiftRows (s : List Nat) : List Nat :=
  (List.range 16).map fun i => s.getD (4 * (((i / 4) + 4 - (i % 4)) % 4) + i % 4) 0

/-- One column, as `mix_single_column` of `aes.py`. -/
@[expose] def mixColumn : List Nat → List Nat
  | [a0, a1, a2, a3] =>
    let t := a0 ^^^ a1 ^^^ a2 ^^^ a3
    [a0 ^^^ t ^^^ xtime (a0 ^^^ a1), a1 ^^^ t ^^^ xtime (a1 ^^^ a2),
     a2 ^^^ t ^^^ xtime (a2 ^^^ a3), a3 ^^^ t ^^^ xtime (a3 ^^^ a0)]
  | s => s

/-- One column, as `inv_mix_columns` of `aes.py` (pre-processing followed by `mixColumn`). -/
@[expose] def invMixColumn : List Nat → List Nat
  | [a0, a1, a2, a3] =>
    let u := xtime (xtime (a0 ^^^ a2))
    let v := xtime (xtime (a1 ^^^ a3))
    mixColumn [a0 ^^^ u, a1 ^^^ v, a2 ^^^ u, a3 ^^^ v]
  | s => s

@[expose] def mapCols (f : List Nat → List Nat) (s : List Nat) : List Nat :=
  (List.range 4).flatMap fun c => f ((List.range 4).map fun r => s.getD (4 * c + r) 0)

@[expose] def mixColumns (s : List Nat) : List Nat := mapCols mixColumn s
@[expose] def invMixColumns (s : List Nat) : List Nat := mapCols invMixColumn s

@[expose] def addRoundKey (s k : List Nat) : List Nat := List.zipWith (· ^^^ ·) s k

/-! Key expansion, written once over an abstract byte algebra. Its operations are the only ones it may use:
XOR, S-box lookup and the round-constant byte; everything else moves words around. -/

structure Alg (α : Type) where
  zero : α
  xor : α → α → α
  sb : α → α
  rc : Nat → α

@[expose] def natAlg : Alg Nat := ⟨0, (· ^^^ ·), sbox, fun j => rconTable.getD j 0⟩

section KeyExp
variable {α : Type} (A : Alg α)

@[expose] def zW : List α := [A.zero, A.zero, A.zero, A.zero]
@[expose] def wxor (u v : List α) : List α := List.zipWith A.xor u v
@[expose] def rotW : List α → List α
  | [a, b, c, d] => [b, c, d, a]
  | w => w
@[expose] def subW (w : List α) : List α := w.map A.sb
@[expose] def rcW (j : Nat) : List α → List α
  | a :: t => A.xor a (A.rc j) :: t
  | [] => []

@[expose] def expandStep (Nk : Nat) (ws : List (List α)) : List (List α) :=
  let i := ws.length
  let prev := ws.getD (i - 1) (zW A)
  let back := ws.getD (i - Nk) (zW A)
  let temp :=
    if i % Nk = 0 then rcW A (i / Nk) (subW A (rotW prev))
    else if 6 < Nk ∧ i % Nk = 4 then subW A prev
    else prev
  ws ++ [wxor A back temp]

@[expose] def expandN (Nk : Nat) : Nat → List (List α) → List (List α)
  | 0, ws => ws
  | n + 1, ws => expandN Nk n (expandStep A Nk ws)

/-- The expanded key as `4 * (Nr + 1)` words, from a key of `4 * Nk` bytes. -/
@[expose] def keyExp (Nk Nr : Nat) (key : List α) : List (List α) :=
  expandN A Nk (4 * (Nr + 1) - Nk)
    ((List.range Nk).map fun j => (List.range 4).map fun r => key.getD (4 * j + r) A.zero)

end KeyExp

@[expose] def roundKey (rk : List (List Nat)) (r : Nat) : List Nat :=
  (List.range 4).flatMap fun c => rk.getD (4 * r + c) []

/-- AES encryption with `Nr` rounds and expanded key `rk` (FIPS-197 Cipher). -/
@[expose] def encrypt (Nr : Nat) (rk : List (List Nat)) (inp : List Nat) : List Nat :=
  let s0 := addRoundKey inp (roundKey rk 0)
  let s := (List.range (Nr - 1)).foldl
    (fun s i => addRoundKey (mixColumns (shiftRows (subBytes s))) (roundKey rk (i + 1))) s0
  addRoundKey (shiftRows (subBytes s)) (roundKey rk Nr)

/-- AES decryption (FIPS-197 InvCipher, in the order of `AES_decrypt_no_tab`). -/
@[expose] def decrypt (Nr : Nat) (rk : List (List Nat)) (inp : List Nat) : List Nat :=
  let s0 := invSubBytes (invShiftRows (addRoundKey inp (roundKey rk Nr)))
  let s := ((List.range (Nr - 1)).reverse.map (· + 1)).foldl
    (fun s i => invSubBytes (invShiftRows (invMixColumns (addRoundKey s (roundKey rk i))))) s0
  addRoundKey s (roundKey rk 0)

/-- Big-endian bytes of a number. -/
@[expose] def beBytes (n : Nat) : Nat → List Nat
  | 0 => []
  | k + 1 => (n >>> (8 * k)) % 256 :: beBytes n k

@[expose] def aes128 (key : Nat) : List (List Nat) := keyExp natAlg 4 10 (beBytes key 16)
@[expose] def aes192 (key : Nat) : List (List Nat) := keyExp natAlg 6 12 (beBytes key 24)
@[expose] def aes256 (key : Nat) : List (List Nat) := keyExp natAlg 8 14 (beBytes key 32)

end SmcIrred.AES

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

namespace SmcIrred

/-- The local rule of a vertex of kind `k` with predecessor values `vs` and an active input `t`: `flow` needs all active and
some present, `any` some active, `add` an odd number, `addneg` an even number of active predecessors. -/
@[expose] def nodeVal (k : Kind) (vs : List Bool) (t : Bool) : Bool :=
  let a := (vs.filter id).length + (if t then 1 else 0)
  let l := vs.length + (if t then 1 else 0)
  match k with
  | .flow => decide (l ≠ 0 ∧ a = l)
  | .any => decide (l ≠ 0 ∧ a ≠ 0)
  | .add => decide (a % 2 = 1)
  | .addneg => decide (a % 2 = 0)
  | _ => false

/-- Append the value of the next vertex to the values computed so far. -/
@[expose] def stepE (inp : Nat → Bool) (vs : List Bool) (nd : Kind × List Nat) : List Bool :=
  vs ++ [nodeVal nd.1 (nd.2.map fun u => vs.getD u false) (inp vs.length)]

/-- The values of all vertices of a generator state, in the order the vertices were added. -/
@[expose] def evalNodes (inp : Nat → Bool) (nodes : List (Kind × List Nat)) : List Bool :=
  nodes.foldl (stepE inp) []

/-- The value of a wire. -/
@[expose] def Wire.ev (vs : List Bool) : Wire → Bool
  | .cst b => b
  | .nd i => vs.getD i false

/-- The value of a wire in the state `gb` under the active inputs `inp`. -/
@[expose] def wev (gb : GB) (inp : Nat → Bool) (w : Wire) : Bool := w.ev (evalNodes inp gb.nodes)

end SmcIrred
