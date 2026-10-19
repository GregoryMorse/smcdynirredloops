module

public import SmcIrred.Lang.Struct
public import SmcIrred.LNF.Reducible
public import SmcIrred.Lang.General

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

theorem ldr_zero (code : List Instr) : ldr code 0 = true := by simp [ldr, isLeader]

theorem pos_one (code : List Instr) : pos (ldr code) 1 = 1 := by
  have := pos_succ (ldr code) 0
  have h0 : pos (ldr code) 0 = 0 := by simp [pos, fl]
  rw [h0, ldr_zero] at this
  simpa using this

theorem pos_pos (code : List Instr) {x : Nat} : 1 ≤ pos (ldr code) (x + 1) := by
  have := pos_mono (ldr code) 1 (x + 1) (by omega)
  rw [pos_one] at this
  exact this

theorem pos_lead_succ (code : List Instr) {y : Nat} (hy : ldr code y = true) :
    pos (ldr code) (y + 1) = pos (ldr code) y + 1 := by
  rw [pos_succ]; simp [hy]

theorem blockOf_mono (code : List Instr) {x y : Nat} (hxy : x ≤ y) (hy : y < code.length) :
    blockOf code x ≤ blockOf code y := by
  rw [blockOf_eq code (by omega), blockOf_eq code hy]
  have := pos_mono (ldr code) (x + 1) (y + 1) (by omega)
  omega

theorem blockOf_strict (code : List Instr) {x y : Nat} (hxy : x < y) (hy : y < code.length) (hl : ldr code y = true) :
    blockOf code x < blockOf code y := by
  rw [blockOf_eq code (by omega), blockOf_eq code hy]
  have h1 := pos_mono (ldr code) (x + 1) y (by omega)
  have h2 := pos_lead_succ code hl
  have h3 := @pos_pos code x
  omega

theorem blockOf_lead (code : List Instr) {y : Nat} (hy : y < code.length) (hl : ldr code y = true) :
    blockOf code y = pos (ldr code) y := by
  rw [blockOf_eq code hy, pos_lead_succ code hl]; omega

/-- The last address of a block lies in it, and the address after it starts a block. -/
theorem blockEnd_spec (code : List Instr) {B : Nat} (hB : B < (leaders code).length) :
    blockEnd code B < code.length ∧ blockOf code (blockEnd code B) = B ∧
      (blockEnd code B + 1 < code.length → ldr code (blockEnd code B + 1) = true) := by
  have hlen : (leaders code).length = pos (ldr code) code.length := rfl
  unfold blockEnd
  by_cases h : B + 1 < (leaders code).length
  · have hspec := fl_getD_spec (ldr code) code.length (B + 1) h
    rw [leaders_eq] at h ⊢
    obtain ⟨h1, h2, h3⟩ := hspec
    have hy0 : 1 ≤ (fl (ldr code) code.length).getD (B + 1) 0 := by
      by_cases h0 : (fl (ldr code) code.length).getD (B + 1) 0 = 0
      · rw [h0] at h3; simp [pos, fl] at h3
      · omega
    have e1 : (fl (ldr code) code.length).getD (B + 1) code.length =
        (fl (ldr code) code.length).getD (B + 1) 0 := by
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl
    rw [e1]
    generalize (fl (ldr code) code.length).getD (B + 1) 0 = y at h1 h2 h3 hy0 ⊢
    refine ⟨by omega, ?_, fun _ => ?_⟩
    · rw [blockOf_eq code (by omega)]
      have : y - 1 + 1 = y := by omega
      rw [this, h3]; omega
    · have : y - 1 + 1 = y := by omega
      rw [this]; exact h1
  · have e1 : (leaders code).getD (B + 1) code.length = code.length := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
    rw [e1]
    have hn : 0 < code.length := by
      by_cases h0 : code.length = 0
      · exfalso
        have : (leaders code).length = 0 := by simp [leaders, h0]
        omega
      · omega
    refine ⟨by omega, ?_, fun h' => by omega⟩
    rw [blockOf_eq code (by omega)]
    have : code.length - 1 + 1 = code.length := by omega
    rw [this, ← hlen]; omega

/-- A block edge is the successor step of the last instruction of the block. -/
theorem blockSucc_step (code : List Instr) {a b : Nat} (hb : b ∈ blockSucc code a) :
    ∃ c, StepI code (blockEnd code a) c ∧ blockOf code c = b := by
  unfold blockSucc at hb
  unfold StepI
  cases hi : code.getD (blockEnd code a) .halt <;> simp only [hi] at hb ⊢
  · by_cases h : blockEnd code a + 1 < code.length
    · simp only [h, ↓reduceIte, List.mem_singleton] at hb
      exact ⟨_, rfl, hb.symm⟩
    · simp [h] at hb
  · simp only [List.mem_singleton] at hb
    exact ⟨_, rfl, hb.symm⟩
  · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hb
    rcases hb with h | h
    · exact ⟨_, Or.inl rfl, h.symm⟩
    · exact ⟨_, Or.inr rfl, h.symm⟩
  · simp at hb

theorem ldr_target (code : List Instr) {e t : Nat} (he : e < code.length)
    (h : (code.getD e .halt).target = some t) : ldr code t = true := by
  simp only [ldr, isLeader, Bool.or_eq_true, List.any_eq_true]
  exact Or.inr ⟨e, List.mem_range.2 he, by rw [h]; simp⟩

theorem ldr_next (code : List Instr) {e : Nat} (he : e < code.length)
    (h : (code.getD e .halt).isTerm = true) : ldr code (e + 1) = true := by
  simp only [ldr, isLeader, Bool.or_eq_true, List.any_eq_true]
  exact Or.inr ⟨e, List.mem_range.2 he, by rw [h]; simp⟩

/-- A backward step leaves a jump and enters a leader; the address after it starts a block. -/
theorem back_leaders (code : List Instr) {e c : Nat} (he : e < code.length) (hs : StepI code e c) (hce : c ≤ e) :
    ldr code c = true ∧ ldr code (e + 1) = true := by
  unfold StepI at hs
  cases hi : code.getD e .halt <;> simp only [hi] at hs
  · omega
  · subst hs
    exact ⟨ldr_target code he (by rw [hi]; rfl), ldr_next code he (by rw [hi]; rfl)⟩
  · rcases hs with h | h
    · subst h
      exact ⟨ldr_target code he (by rw [hi]; rfl), ldr_next code he (by rw [hi]; rfl)⟩
    · omega

end SmcIrred.Lang
