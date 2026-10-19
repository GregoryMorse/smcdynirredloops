module

public import SmcIrred.Spec.ArithTrace
public import SmcIrred.Arith.Window

public section

namespace SmcIrred.Arith

/-! # The instrumented windowed exponentiation (C59, G31 g)

The run of `winExpC` calls the multiplication exactly `tblMuls w + loopMuls B w` times and returns the value of `winExp`: the
operation count is that of a logged run of the algorithm, not only of its loop structure. -/

theorem tblStepC_fst {α : Type} (mulOp : α → α → α) (one b : α) (st : List α × List (α × α)) (k : Nat) :
    (tblStepC mulOp one b st k).1 = tblStep mulOp one b st.1 k := by
  have hk : (k + 2) % 2 = k % 2 := by omega
  unfold tblStepC tblStep mulLog
  simp only [hk]
  by_cases h : k % 2 = 0 <;> simp [h]

theorem tblStepC_len {α : Type} (mulOp : α → α → α) (one b : α) (st : List α × List (α × α)) (k : Nat) :
    (tblStepC mulOp one b st k).2.length = st.2.length + 1 := by
  have hk : (k + 2) % 2 = k % 2 := by omega
  unfold tblStepC mulLog
  simp only [hk]
  by_cases h : k % 2 = 0 <;> simp [h]

theorem winTblC_aux {α : Type} (mulOp : α → α → α) (one b : α) :
    ∀ (n : Nat) (t : List α) (lg : List (α × α)),
      ((List.range n).foldl (tblStepC mulOp one b) (t, lg)).1 = (List.range n).foldl (tblStep mulOp one b) t ∧
      ((List.range n).foldl (tblStepC mulOp one b) (t, lg)).2.length = lg.length + n := by
  intro n
  induction n with
  | zero => intro t lg; simp
  | succ n ih =>
    intro t lg
    rw [List.range_succ, List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_cons, List.foldl_nil,
      List.foldl_nil]
    obtain ⟨h1, h2⟩ := ih t lg
    refine ⟨?_, ?_⟩
    · rw [tblStepC_fst, h1]
    · rw [tblStepC_len, h2]; omega

/-- The logged table is the table, and building it logs `2^w - 2` multiplications. -/
theorem winTblC_spec {α : Type} (mulOp : α → α → α) (one b : α) (w : Nat) :
    (winTblC mulOp one b w).1 = winTbl mulOp one b w ∧ (winTblC mulOp one b w).2.length = 2 ^ w - 2 := by
  have := winTblC_aux mulOp one b (2 ^ w - 2) [one, b] []
  unfold winTblC winTbl
  simpa using this

theorem sqLoop_spec {α : Type} (mulOp : α → α → α) (w : Nat) :
    ∀ (r : α) (lg : List (α × α)),
      ((List.range w).foldl (fun s _ => mulLog mulOp s.1 s.1 s.2) (r, lg)).1 =
        (List.range w).foldl (fun r _ => mulOp r r) r ∧
      ((List.range w).foldl (fun s _ => mulLog mulOp s.1 s.1 s.2) (r, lg)).2.length = lg.length + w := by
  induction w with
  | zero => intro r lg; simp
  | succ w ih =>
    intro r lg
    rw [List.range_succ, List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_cons, List.foldl_nil,
      List.foldl_nil]
    obtain ⟨h1, h2⟩ := ih r lg
    refine ⟨?_, ?_⟩
    · show mulOp _ _ = mulOp _ _
      rw [h1]
    · show (_ ++ [_]).length = lg.length + (w + 1)
      simp only [List.length_append, List.length_singleton]
      omega

/-- One window of the loop, logged. -/
def winStepC {α : Type} (mulOp : α → α → α) (T : List α) (one : α) (w e : Nat) (st : α × List (α × α)) (j : Nat) :
    α × List (α × α) :=
  let p := mulLog mulOp (T.getD ((e >>> (j * w)) &&& (2 ^ w - 1)) one) st.1 st.2
  if j = 0 then p else (List.range w).foldl (fun s _ => mulLog mulOp s.1 s.1 s.2) p

theorem cnt_shift (w : Nat) (l : List Nat) (c0 : Nat) :
    l.foldl (fun c j => c + 1 + (if j = 0 then 0 else w)) c0 = c0 + l.foldl (fun c j => c + 1 + (if j = 0 then 0 else w)) 0 := by
  induction l generalizing c0 with
  | nil => simp
  | cons j t ih =>
    simp only [List.foldl_cons]
    rw [ih (c0 + 1 + _), ih (0 + 1 + _)]
    omega

/-- The value of one window. -/
def winStepV {α : Type} (mulOp : α → α → α) (T : List α) (one : α) (w e : Nat) (res : α) (j : Nat) : α :=
  let res := mulOp (T.getD ((e >>> (j * w)) &&& (2 ^ w - 1)) one) res
  if j = 0 then res else (List.range w).foldl (fun r _ => mulOp r r) res

theorem winStepC_spec {α : Type} (mulOp : α → α → α) (T : List α) (one : α) (w e : Nat) (st : α × List (α × α))
    (j : Nat) :
    (winStepC mulOp T one w e st j).1 = winStepV mulOp T one w e st.1 j ∧
      (winStepC mulOp T one w e st j).2.length = st.2.length + 1 + (if j = 0 then 0 else w) := by
  unfold winStepC winStepV
  by_cases hj : j = 0
  · simp only [hj, ↓reduceIte, mulLog, List.length_append, List.length_singleton]
    constructor <;> first | rfl | trivial | simp
  · simp only [hj, if_false]
    have hs := sqLoop_spec mulOp w (mulOp (T.getD ((e >>> (j * w)) &&& (2 ^ w - 1)) one) st.1)
      (st.2 ++ [(T.getD ((e >>> (j * w)) &&& (2 ^ w - 1)) one, st.1)])
    refine ⟨hs.1, ?_⟩
    have := hs.2
    simp only [mulLog] at this ⊢
    rw [this]
    simp only [List.length_append, List.length_singleton]

theorem winLoopC_spec {α : Type} (mulOp : α → α → α) (T : List α) (one : α) (w e : Nat) :
    ∀ (l : List Nat) (st : α × List (α × α)),
      (l.foldl (winStepC mulOp T one w e) st).1 = l.foldl (winStepV mulOp T one w e) st.1 ∧
      (l.foldl (winStepC mulOp T one w e) st).2.length =
        st.2.length + l.foldl (fun c j => c + 1 + (if j = 0 then 0 else w)) 0 := by
  intro l
  induction l with
  | nil => intro st; simp
  | cons j t ih =>
    intro st
    rw [List.foldl_cons, List.foldl_cons, List.foldl_cons]
    obtain ⟨h1, h2⟩ := winStepC_spec mulOp T one w e st j
    obtain ⟨i1, i2⟩ := ih (winStepC mulOp T one w e st j)
    rw [h1] at i1
    rw [cnt_shift w t (0 + 1 + (if j = 0 then 0 else w))]
    refine ⟨i1, ?_⟩
    rw [i2, h2]
    omega

/-- **The instrumented windowed exponentiation**: same value as `winExp`, and the log has `tblMuls w + loopMuls B w`
entries. -/
theorem winExpC_spec {α : Type} (mulOp : α → α → α) (one b : α) (B w e : Nat) :
    (winExpC mulOp one b B w e).1 = winExp mulOp one b B w e ∧
      (winExpC mulOp one b B w e).2.length = tblMuls w + loopMuls B w := by
  obtain ⟨ht1, ht2⟩ := winTblC_spec mulOp one b w
  have hloop := winLoopC_spec mulOp (winTbl mulOp one b w) one w e ((List.range ((B + w - 1) / w)).reverse)
    (one, (winTblC mulOp one b w).2)
  have e1 : winExpC mulOp one b B w e =
      ((List.range ((B + w - 1) / w)).reverse).foldl (winStepC mulOp (winTbl mulOp one b w) one w e)
        (one, (winTblC mulOp one b w).2) := by
    rw [← ht1]; rfl
  have e2 : winExp mulOp one b B w e =
      ((List.range ((B + w - 1) / w)).reverse).foldl (winStepV mulOp (winTbl mulOp one b w) one w e) one := rfl
  rw [e1, e2]
  refine ⟨hloop.1, ?_⟩
  rw [hloop.2, ht2]
  unfold tblMuls loopMuls
  rw [foldl_count]
  omega

end SmcIrred.Arith
