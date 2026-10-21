import SmcIrred.Spec.TwoSatSolve

/-! Test vectors for the native 2-SAT solvers (plan R8 item 2): the four test formulas of `selfmodgraph.cpp` and 2000
pseudo-random formulas (fixed seed). Each line is `id|a,b;c,d;...|SAT or UNSAT|count`, where the verdict is the Lean
reference solver `twoSatSolve` (cross-checked by brute force when at most 14 variables occur) and `count` is the number of
satisfying assignments of the occurring variables (`?` if there are more than 14 of them). Mechanical evidence only. -/

open SmcIrred

def toLit (a : Int) : Lit := ⟨a.natAbs - 1, decide (0 < a)⟩

def toTwoSat (cs : List (Int × Int)) : TwoSat :=
  { n := (cs.foldl (fun m (p : Int × Int) => max m (max p.1.natAbs p.2.natAbs)) 0)
    clauses := cs.map fun (p : Int × Int) => if p.1 = p.2 then [toLit p.1] else [toLit p.1, toLit p.2] }

def occurring (cs : List (Int × Int)) : List Nat :=
  (cs.flatMap fun p => [p.1.natAbs - 1, p.2.natAbs - 1]).eraseDups

def evalLit (a : Nat → Bool) (z : Int) : Bool := a (z.natAbs - 1) == decide (0 < z)

def bruteCount (cs : List (Int × Int)) : Option Nat :=
  let vs := occurring cs
  if vs.length > 14 then none
  else
    some ((List.range (2 ^ vs.length)).filter fun mask =>
      let a : Nat → Bool := fun v => match vs.idxOf? v with
        | some i => (mask / 2 ^ i) % 2 == 1
        | none => false
      cs.all fun p => evalLit a p.1 || evalLit a p.2).length

def lcgNext (s : Nat) : Nat := (s * 6364136223846793005 + 1442695040888963407) % 18446744073709551616

def randFormula (s : Nat) : List (Int × Int) × Nat :=
  let s := lcgNext s
  let V := 2 + (s >>> 33) % 7
  let s := lcgNext s
  let m := 1 + (s >>> 33) % (3 * V)
  let rec go : Nat → Nat → List (Int × Int) → List (Int × Int) × Nat
    | 0, s, acc => (acc.reverse, s)
    | k + 1, s, acc =>
      let s := lcgNext s
      let a : Int := (1 + (s >>> 33) % V : Nat) * (if (s >>> 40) % 2 = 0 then 1 else -1)
      let s := lcgNext s
      let b : Int := (1 + (s >>> 33) % V : Nat) * (if (s >>> 40) % 2 = 0 then 1 else -1)
      go k s ((a, b) :: acc)
  go m s []

def fmt (cs : List (Int × Int)) : String :=
  ";".intercalate (cs.map fun p => s!"{p.1},{p.2}")

def line (id : Nat) (cs : List (Int × Int)) : String :=
  let sat := (twoSatSolve (toTwoSat cs)).isSome
  let bc := bruteCount cs
  let chk := match bc with
    | some c => if (c > 0) == sat then "" else "!BRUTE_MISMATCH"
    | none => ""
  let cnt := match bc with | some c => toString c | none => "?"
  s!"{id}|{fmt cs}|{if sat then "SAT" else "UNSAT"}{chk}|{cnt}"

def testFormulas : List (List (Int × Int)) :=
  [ [(1, 2), (-1, 2), (-2, 1), (-1, -2)],
    [(1, 2), (2, 3), (3, 4), (-1, -3), (-2, -4)],
    [(1, 4), (-2, 5), (3, 7), (2, -5), (-8, -2), (3, -1), (4, -3), (5, -4), (-3, -7), (6, 7), (1, 7), (-7, -1)],
    [(21, 34), (-49, -12), (7, 18), (-5, -1), (28, 17), (3, 55), (36, 33), (-6, -50), (44, -41), (-55, 3), (14, -54),
     (-30, 13), (-13, 60), (54, -16), (-48, 41), (3, 6), (49, -48), (34, -4), (14, -46), (58, -20), (52, 54), (-37, -25),
     (56, -1), (50, -9), (-58, 11), (-19, 58), (17, 8), (56, 51), (38, 49), (-13, 36), (24, 9), (18, -29), (6, 49),
     (-30, 4), (-13, -20), (31, -9), (54, -4), (37, 17), (-48, -8), (-7, -45), (-3, -42), (27, -22), (-50, -27), (47, 19),
     (-21, 20), (-20, -37), (-42, 12), (-35, 1), (-41, -19), (11, 30), (-17, -48), (21, -49), (16, -53), (57, 57),
     (15, 2), (-6, -7), (-23, -28), (-12, -17), (-59, -36), (38, -6), (-16, -6), (21, -14), (17, -7), (3, -49),
     (-55, -13), (22, -52), (24, -56), (22, -42), (13, -4), (-8, -16), (-55, -7), (-12, 48), (52, 18), (-47, 44),
     (-22, -23), (-29, -23), (-53, 57), (-38, 54), (43, -53), (49, -18), (-60, 58), (-5, -14), (16, 34), (-24, -43),
     (10, -21), (-52, -40), (-45, -22), (-5, -11), (-32, -11), (-15, 11), (-24, 44), (-17, -15), (10, -27), (8, -26),
     (-36, 24), (13, 1), (59, -34), (-40, -25), (11, -22)] ]

def main : IO Unit := do
  let mut out : Array String := #[]
  let mut id := 1
  for f in testFormulas do
    out := out.push (line id f)
    id := id + 1
  let mut s := 20221103
  for _ in [0:2000] do
    let (f, s') := randFormula s
    s := s'
    out := out.push (line id f)
    id := id + 1
  IO.FS.writeFile "../validation/data/twosat_vectors.txt" ("\n".intercalate out.toList ++ "\n")

#eval main
