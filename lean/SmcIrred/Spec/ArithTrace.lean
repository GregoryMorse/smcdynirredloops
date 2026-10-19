module

public import SmcIrred.Spec.Arith

public section

namespace SmcIrred.Arith

/-! # The windowed exponentiation with its multiplications logged

`winExpC` is `winExp` with every call of the multiplication recorded in a log of operand pairs (the instrumented run of the
algorithm; the log is not read by the algorithm). The theorems of `Arith.WindowTrace` show that the instrumented run returns
the same value and that the log has `tblMuls w + loopMuls B w` entries. -/

/-- A multiplication that appends its operands to the log. -/
@[expose] def mulLog {α : Type} (mulOp : α → α → α) (x y : α) (lg : List (α × α)) : α × List (α × α) :=
  (mulOp x y, lg ++ [(x, y)])

/-- `tblStep` with the multiplication logged. -/
@[expose] def tblStepC {α : Type} (mulOp : α → α → α) (one b : α) (st : List α × List (α × α)) (k : Nat) :
    List α × List (α × α) :=
  let j := k + 2
  if j % 2 = 0 then
    let p := mulLog mulOp (st.1.getD (j / 2) one) (st.1.getD (j / 2) one) st.2
    (st.1 ++ [p.1], p.2)
  else
    let p := mulLog mulOp (st.1.getD (j - 1) one) b st.2
    (st.1 ++ [p.1], p.2)

/-- The power table with its multiplications logged. -/
@[expose] def winTblC {α : Type} (mulOp : α → α → α) (one b : α) (w : Nat) : List α × List (α × α) :=
  (List.range (2 ^ w - 2)).foldl (tblStepC mulOp one b) ([one, b], [])

/-- `winExp` with every multiplication logged. -/
@[expose] def winExpC {α : Type} (mulOp : α → α → α) (one b : α) (B w e : Nat) : α × List (α × α) :=
  let t := winTblC mulOp one b w
  ((List.range ((B + w - 1) / w)).reverse).foldl
    (fun st j =>
      let p := mulLog mulOp (t.1.getD ((e >>> (j * w)) &&& (2 ^ w - 1)) one) st.1 st.2
      if j = 0 then p else (List.range w).foldl (fun s _ => mulLog mulOp s.1 s.1 s.2) p) (one, t.2)

end SmcIrred.Arith
