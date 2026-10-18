module

public section

namespace SmcIrred.Arith

/-! Literal model of `add_rbsd` of `python/virt.py` (carry-free addition of recoded binary signed-digit numbers, C58). A
number is a little-endian list of digits `-1`, `0`, `1`; `bsdVal` is its value. The Python dictionaries are transcribed
entry by entry; a lookup that raises `KeyError` in Python is `none`. -/

/-- The value of a little-endian signed-digit list. -/
@[expose] def bsdVal : List Int → Int
  | [] => 0
  | d :: t => d + 2 * bsdVal t

/-- The keys of the dictionaries of `add_rbsd`: `x1`, `(None, y1)`, `(x1, y1)` (a tag and two integers, so that equality of
keys is the equality of core pairs). -/
@[expose] def RKey : Type := Nat × Int × Int

namespace RKey
@[expose] def one (k : Int) : RKey := (0, k, 0)
@[expose] def nn (y : Int) : RKey := (1, 0, y)
@[expose] def two (a b : Int) : RKey := (2, a, b)
end RKey

instance : BEq RKey := inferInstanceAs (BEq (Nat × Int × Int))

/-- An entry of `table`: an integer or a dictionary. -/
inductive RCell where
  | const (a : Int)
  | dict (d : List (RKey × Int))

/-- `l[x1]`, else `l[(None, y1)]`, else `l[(x1, y1)]` (the lookup chain of the loop of `add_rbsd`). -/
@[expose] def rLookup (d : List (RKey × Int)) (x1 y1 : Int) : Option Int :=
  match d.lookup (RKey.one x1) with
  | some a => some a
  | none =>
    match d.lookup (RKey.nn y1) with
    | some a => some a
    | none => d.lookup (RKey.two x1 y1)

/-- `table[x+1][y+1]` of `add_rbsd`. -/
@[expose] def rTable (x y : Int) : Option RCell :=
  if x = -1 ∧ y = -1 then some (.dict [(.one 0, 0), (.two 1 0, 0), (.two 1 1, 1)])
  else if x = -1 ∧ y = 0 then some (.dict [(.one 0, -1), (.two 1 (-1), -1), (.two 1 0, -1), (.two 1 1, 0)])
  else if x = -1 ∧ y = 1 then some (.const 0)
  else if x = 0 ∧ y = -1 then some (.dict [(.nn 0, -1), (.two (-1) 1, -1), (.two 0 1, -1), (.two 1 1, 0)])
  else if x = 0 ∧ y = 0 then some (.dict [(.two (-1) (-1), -1), (.nn 0, 0), (.two (-1) 1, 0), (.one 0, 0), (.two 1 (-1), 0), (.two 1 1, 1)])
  else if x = 0 ∧ y = 1 then some (.dict [(.two (-1) (-1), 0), (.nn 0, 1), (.two 0 (-1), 1), (.two 1 (-1), 1)])
  else if x = 1 ∧ y = -1 then some (.const 0)
  else if x = 1 ∧ y = 0 then some (.dict [(.two (-1) (-1), 0), (.two (-1) 0, 1), (.two (-1) 1, 1), (.one 0, 1)])
  else if x = 1 ∧ y = 1 then some (.dict [(.two (-1) (-1), -1), (.two (-1) 0, 0), (.one 0, 0)])
  else none

/-- The digit produced at a position with digits `x`, `y` and the previous digits `x1`, `y1`. -/
@[expose] def rCell (x y x1 y1 : Int) : Option Int :=
  match rTable x y with
  | none => none
  | some (.const a) => some a
  | some (.dict d) => rLookup d x1 y1

/-- The loop of `add_rbsd`: `k` positions, the digits of the operands read as `0` past their end. -/
@[expose] def rAddGo : List Int → List Int → Int → Int → Nat → Option (List Int)
  | _, _, _, _, 0 => some []
  | a, b, x1, y1, k + 1 =>
    match rCell (a.headD 0) (b.headD 0) x1 y1 with
    | none => none
    | some r =>
      match rAddGo a.tail b.tail (a.headD 0) (b.headD 0) k with
      | none => none
      | some t => some (r :: t)

/-- `add_rbsd(num1, num2, issub)`. -/
@[expose] def rAdd (a b : List Int) (issub : Bool) : Option (List Int) :=
  rAddGo a (if issub then b.map (fun d => -d) else b) 0 0 (max a.length b.length + 1)

/-- `to_rbsd`: the recoding of a signed-digit number into the form the carry-free adder needs. The dictionaries `enc1`,
`enc2`, `enc3` of the Python code are functions of the digit two places below (`i2`) and, for `enc1`, `enc2`, with `i2 = 0`,
of the digit three places below (`i3`). -/
@[expose] def rEnc1 (i2 i3 : Int) : Option Int :=
  if i2 = -1 then some 0 else if i2 = 1 then some 1
  else if i3 = -1 then some 0 else if i3 = 0 then some 1 else if i3 = 1 then some 1 else none

@[expose] def rEnc2 (i2 i3 : Int) : Option Int :=
  if i2 = -1 then some (-1) else if i2 = 1 then some 0
  else if i3 = -1 then some (-1) else if i3 = 0 then some 0 else if i3 = 1 then some 0 else none

@[expose] def rEnc3 (i2 : Int) : Option Int :=
  if i2 = -1 then some 1 else if i2 = 0 then some (-1) else if i2 = 1 then some (-1) else none

/-- `recoding[i+1][i1+1]` followed by the lookup chain: `i` is the digit being recoded, `i1`, `i2`, `i3` the digits one,
two and three places below. -/
@[expose] def rToCell (i i1 i2 i3 : Int) : Option Int :=
  if i = 0 then
    (if i1 = -1 then rEnc2 i2 i3 else if i1 = 0 then some 0 else if i1 = 1 then rEnc1 i2 i3 else none)
  else if i = -1 ∨ i = 1 then
    (if i1 = -1 then rEnc1 i2 i3 else if i1 = 0 then rEnc3 i2 else if i1 = 1 then rEnc2 i2 i3 else none)
  else none

/-- The loop of `to_rbsd` over the digits followed by the final `0`. -/
@[expose] def rToGo : List Int → Int → Int → Int → Option (List Int)
  | [], _, _, _ => some []
  | i :: t, i1, i2, i3 =>
    match rToCell i i1 i2 i3 with
    | none => none
    | some r =>
      match rToGo t i i1 i2 with
      | none => none
      | some rest => some (r :: rest)

@[expose] def rToRbsd (bsd : List Int) : Option (List Int) := rToGo (bsd ++ [0]) 0 0 0

/-- `montgomeryBound(T, N, issub=True)`: one conditional addition of the modulus. -/
@[expose] def boundSub (t N : Int) : Int := if t < 0 then t + N else t

end SmcIrred.Arith
