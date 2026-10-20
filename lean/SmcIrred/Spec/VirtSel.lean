module

public import SmcIrred.Spec.Virt

public section

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
