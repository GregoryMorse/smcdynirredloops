module

public import SmcIrred.Spec.Virt
public import SmcIrred.Spec.VirtSel

public section

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
