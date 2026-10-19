module

public section

namespace SmcIrred.Arith

/-! # Carry-save addition and Wallace trees (paper §4.2: "carry-save/Wallace")

`csa a b c` is a 3:2 compressor on natural numbers, column by column: the sum bit of a column is the parity of its three
input bits and the carry bit is their majority (their sum divided by two) one column up. No carry travels further than one
column. -/

/-- The 3:2 compressor: `(sum vector, carry vector)`. -/
@[expose] def csa (a b c : Nat) : Nat × Nat :=
  if h : a + b + c = 0 then (0, 0) else
  let t := a % 2 + b % 2 + c % 2
  let r := csa (a / 2) (b / 2) (c / 2)
  (t % 2 + 2 * r.1, 2 * (t / 2) + 2 * r.2)
termination_by a + b + c
decreasing_by omega

/-- One Wallace level: each group of three operands becomes two. -/
@[expose] def wround : List Nat → List Nat
  | a :: b :: c :: t => (csa a b c).1 :: (csa a b c).2 :: wround t
  | l => l

/-- Number of operands after one level. -/
@[expose] def rnd (m : Nat) : Nat := 2 * (m / 3) + m % 3

/-- Number of levels needed to reduce `m` operands to at most two. -/
@[expose] def rounds (m : Nat) : Nat :=
  if h : m ≤ 2 then 0 else 1 + rounds (rnd m)
termination_by m
decreasing_by unfold rnd; omega

/-- The largest operand counts that `r` levels reduce to two: `2, 3, 4, 6, 9, 13, 19, 28, ...`. -/
@[expose] def dadda : Nat → Nat
  | 0 => 2
  | r + 1 => dadda r + dadda r / 2

theorem wround_length (l : List Nat) : (wround l).length = rnd l.length := by
  match l with
  | a :: b :: c :: t =>
    simp only [wround, List.length_cons]
    rw [wround_length t]
    unfold rnd; omega
  | [] => rfl
  | [_] => simp [wround, rnd]
  | [_, _] => simp [wround, rnd]
termination_by l.length

/-- The Wallace tree: levels until at most two operands are left. -/
@[expose] def wreduce (l : List Nat) : List Nat :=
  if _h : l.length ≤ 2 then l else wreduce (wround l)
termination_by l.length
decreasing_by rw [wround_length]; unfold rnd; omega

/-- The number of levels `wreduce` performs. -/
@[expose] def wlevels (l : List Nat) : Nat :=
  if _h : l.length ≤ 2 then 0 else 1 + wlevels (wround l)
termination_by l.length
decreasing_by rw [wround_length]; unfold rnd; omega

/-- The number of 3:2 compressors used to reduce `m` operands to two. -/
@[expose] def wcount (m : Nat) : Nat :=
  if _h : m ≤ 2 then 0 else m / 3 + wcount (rnd m)
termination_by m
decreasing_by unfold rnd; omega

end SmcIrred.Arith
