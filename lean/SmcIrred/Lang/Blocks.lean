module

public import SmcIrred.Lang.Struct
public import SmcIrred.LNF.Reducible

public section

namespace SmcIrred.Lang

/-! # Basic blocks of flat code

Facts about `leaders`, `blockOf`, `blockEnd` and `cfgOf` for arbitrary code whose jump targets lie inside the code:
the blocks are the intervals between consecutive leaders, block edges are exactly the instruction successors out of the
last instruction of a block, and the successor of an instruction stays in its block unless the next address is a leader. -/

/-- The elements of `range n` with property `p`. -/
@[expose] def fl (p : Nat → Bool) (n : Nat) : List Nat := (List.range n).filter p

/-- The number of elements below `a`. -/
@[expose] def pos (p : Nat → Bool) (a : Nat) : Nat := (fl p a).length

theorem fl_succ (p : Nat → Bool) (n : Nat) : fl p (n + 1) = fl p n ++ (if p n then [n] else []) := by
  unfold fl
  rw [List.range_succ, List.filter_append]
  by_cases h : p n <;> simp [h]

theorem pos_succ (p : Nat → Bool) (n : Nat) : pos p (n + 1) = pos p n + (if p n then 1 else 0) := by
  unfold pos
  rw [fl_succ]
  by_cases h : p n <;> simp [h]

theorem pos_mono (p : Nat → Bool) : ∀ a b, a ≤ b → pos p a ≤ pos p b := by
  intro a b h
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih => rw [pos_succ]; omega

theorem pos_le (p : Nat → Bool) (a : Nat) : pos p a ≤ a := by
  induction a with
  | zero => simp [pos, fl]
  | succ a ih => rw [pos_succ]; split <;> omega

theorem fl_length (p : Nat → Bool) (n : Nat) : (fl p n).length = pos p n := rfl

/-- The `pos p a`-th element is `a`, for `a` with `p a`. -/
theorem fl_getD_pos (p : Nat → Bool) : ∀ n a, a < n → p a = true → (fl p n).getD (pos p a) 0 = a := by
  intro n
  induction n with
  | zero => intro a h; omega
  | succ n ih =>
    intro a ha hp
    rw [fl_succ]
    by_cases han : a < n
    · have h1 := ih a han hp
      have h2 : pos p a < (fl p n).length := by
        have := pos_mono p (a + 1) n (by omega)
        rw [pos_succ] at this
        simp only [hp, ↓reduceIte] at this
        rw [fl_length]
        omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h2, ← List.getD_eq_getElem?_getD]
      exact h1
    · have han' : a = n := by omega
      subst han'
      have : pos p a = (fl p a).length := rfl
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
      simp [hp, this]

/-- Every element of `fl p n` is a number below `n` with `p`, and its position is its index. -/
theorem fl_getD_spec (p : Nat → Bool) : ∀ n K, K < (fl p n).length →
    p ((fl p n).getD K 0) = true ∧ (fl p n).getD K 0 < n ∧ pos p ((fl p n).getD K 0) = K := by
  intro n
  induction n with
  | zero => intro K h; simp [fl] at h
  | succ n ih =>
    intro K hK
    rw [fl_succ] at hK ⊢
    by_cases hKn : K < (fl p n).length
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hKn, ← List.getD_eq_getElem?_getD]
      obtain ⟨h1, h2, h3⟩ := ih K hKn
      exact ⟨h1, by omega, h3⟩
    · by_cases hp : p n = true
      · simp only [hp, ↓reduceIte, List.length_append, List.length_singleton] at hK
        have hK' : K = (fl p n).length := by omega
        subst hK'
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _)]
        simp [hp, fl_length]
      · simp [hp] at hK
        omega

/-! ### Blocks of code -/

variable {code : List Instr}

@[expose] def ldr (code : List Instr) : Nat → Bool := isLeader code

theorem leaders_eq (code : List Instr) : leaders code = fl (ldr code) code.length := rfl

theorem fl_filter_le (p : Nat → Bool) (i : Nat) : ∀ n,
    ((fl p n).filter (fun x => decide (x ≤ i))).length = pos p (min n (i + 1)) := by
  intro n
  induction n with
  | zero => simp [fl, pos]
  | succ n ih =>
    rw [fl_succ, List.filter_append, List.length_append, ih]
    by_cases hn : n ≤ i
    · have h1 : min (n + 1) (i + 1) = n + 1 := by omega
      have h2 : min n (i + 1) = n := by omega
      rw [h1, h2, pos_succ]
      by_cases hp : p n = true <;> simp [hp, hn]
    · have h1 : min (n + 1) (i + 1) = i + 1 := by omega
      have h2 : min n (i + 1) = i + 1 := by omega
      rw [h1, h2]
      by_cases hp : p n = true <;> simp [hp, hn]

theorem blockOf_eq (code : List Instr) {i : Nat} (hi : i < code.length) :
    blockOf code i = pos (ldr code) (i + 1) - 1 := by
  unfold blockOf
  rw [leaders_eq, fl_filter_le]
  have : min code.length (i + 1) = i + 1 := by omega
  rw [this]

end SmcIrred.Lang
