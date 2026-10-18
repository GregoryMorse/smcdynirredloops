module

public import SmcIrred.Spec.Circuit

public section

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
  deriving DecidableEq

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
