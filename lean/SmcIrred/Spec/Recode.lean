module

public section

namespace SmcIrred.Arith

/-! # Signed-digit recodings of the exponent (paper §4.2, "non-adjacent form (NAF) and mutual opposite form (MOF)")

Digit lists are least-significant first. `sval` is the value, `wt` the Hamming weight (number of nonzero digits). -/

/-- Value of a signed-digit list (least significant digit first). -/
@[expose] def sval : List Int → Int
  | [] => 0
  | d :: ds => d + 2 * sval ds

/-- Hamming weight: the number of nonzero digits. -/
@[expose] def wt (l : List Int) : Nat := l.countP (fun d => d != 0)

/-- Binary signed digits: every digit is `0`, `1` or `-1`. -/
@[expose] def Sd (l : List Int) : Prop := ∀ d ∈ l, d = 0 ∨ d = 1 ∨ d = -1

/-- Non-adjacent form: signed binary digits, no two adjacent nonzero digits. -/
inductive IsNaf : List Int → Prop
  | nil : IsNaf []
  | zero {t : List Int} : IsNaf t → IsNaf (0 :: t)
  | nz {a : Int} {t : List Int} : (a = 1 ∨ a = -1) → IsNaf t → (t = [] ∨ ∃ t', t = 0 :: t') → IsNaf (a :: t)

/-- The non-adjacent form of an integer: for odd `n` the digit is `2 - n mod 4 ∈ {1, -1}`, which makes the next value even. -/
@[expose] def naf (n : Int) : List Int :=
  if h : n = 0 then [] else
  if h2 : n % 2 = 0 then 0 :: naf (n / 2)
  else (2 - n % 4) :: naf ((n - (2 - n % 4)) / 2)
termination_by n.natAbs
decreasing_by all_goals omega

/-- Binary digits of a natural number, least significant first. -/
@[expose] def bin (n : Nat) : List Int :=
  if h : n = 0 then [] else ((n % 2 : Nat) : Int) :: bin (n / 2)
termination_by n
decreasing_by omega

/-- Digits `prev - b[0], b[0] - b[1], ..., b[last] - 0` after the previous bit `prev`. -/
@[expose] def mofGo : Int → List Int → List Int
  | prev, [] => [prev]
  | prev, x :: xs => (prev - x) :: mofGo x xs

/-- Mutual opposite form (Joye-Yen) of the binary digits `b` (least significant first): digit `i` is `b[i-1] - b[i]`, with
`b[-1] = 0` and `b[i] = 0` past the end, for `i = 0, ..., len`. -/
@[expose] def mof (b : List Int) : List Int := mofGo 0 b

/-- The nonzero digits alternate in sign, the next one being `s`. -/
inductive Alt : Int → List Int → Prop
  | nil {s : Int} : Alt s []
  | zero {s : Int} {t : List Int} : Alt s t → Alt s (0 :: t)
  | nz {s : Int} {t : List Int} : (s = 1 ∨ s = -1) → Alt (-s) t → Alt s (s :: t)

/-- All lists of `n` binary digits. -/
@[expose] def allBits : Nat → List (List Int)
  | 0 => [[]]
  | n + 1 => (allBits n).map (fun b => 0 :: b) ++ (allBits n).map (fun b => 1 :: b)

end SmcIrred.Arith
