module

public import SmcIrred.Spec.Lang

public section

namespace SmcIrred.Lang

/-! # Control flow of structured statements at the address level

`Structured` statements have no `goto`, `ifGoto` or label. `SStep s p a c` is the control-flow relation of the code of `s`
placed at address `p`, written from the statement (one constructor per instruction, plus the steps of the children);
`SStep_iff` proves that it is the successor relation of the flat code (`StepI`) at the addresses of `s`. -/

@[expose] def Structured : Stmt → Prop
  | .skip => True
  | .blk _ => True
  | .seq s t => Structured s ∧ Structured t
  | .ite1 _ s => Structured s
  | .ite _ s t => Structured s ∧ Structured t
  | .while _ s => Structured s
  | .doWhile s _ => Structured s
  | .goto _ => False
  | .ifGoto _ _ => False
  | .lab _ _ => False

/-- The successor relation of flat code at one address (the program counter after the instruction). -/
@[expose] def StepI (code : List Instr) (a c : Nat) : Prop :=
  match code.getD a .halt with
  | .blk _ => c = a + 1
  | .jmp t => c = t
  | .jmpIf _ t => c = t ∨ c = a + 1
  | .halt => False

inductive SStep : Stmt → Nat → Nat → Nat → Prop
  | blk {b p : Nat} : SStep (.blk b) p p (p + 1)
  | seqL {s t : Stmt} {p a c : Nat} : SStep s p a c → SStep (.seq s t) p a c
  | seqR {s t : Stmt} {p a c : Nat} : SStep t (p + s.size) a c → SStep (.seq s t) p a c
  | ite1_skip {k : Cond} {s : Stmt} {p : Nat} : SStep (.ite1 k s) p p (p + 1 + s.size)
  | ite1_in {k : Cond} {s : Stmt} {p : Nat} : SStep (.ite1 k s) p p (p + 1)
  | ite1_body {k : Cond} {s : Stmt} {p a c : Nat} : SStep s (p + 1) a c → SStep (.ite1 k s) p a c
  | ite_else {k : Cond} {s t : Stmt} {p : Nat} : SStep (.ite k s t) p p (p + 2 + s.size)
  | ite_then {k : Cond} {s t : Stmt} {p : Nat} : SStep (.ite k s t) p p (p + 1)
  | ite_jmp {k : Cond} {s t : Stmt} {p : Nat} : SStep (.ite k s t) p (p + 1 + s.size) (p + 2 + s.size + t.size)
  | ite_s {k : Cond} {s t : Stmt} {p a c : Nat} : SStep s (p + 1) a c → SStep (.ite k s t) p a c
  | ite_t {k : Cond} {s t : Stmt} {p a c : Nat} : SStep t (p + 2 + s.size) a c → SStep (.ite k s t) p a c
  | while_exit {k : Cond} {s : Stmt} {p : Nat} : SStep (.while k s) p p (p + 2 + s.size)
  | while_in {k : Cond} {s : Stmt} {p : Nat} : SStep (.while k s) p p (p + 1)
  | while_back {k : Cond} {s : Stmt} {p : Nat} : SStep (.while k s) p (p + 1 + s.size) p
  | while_body {k : Cond} {s : Stmt} {p a c : Nat} : SStep s (p + 1) a c → SStep (.while k s) p a c
  | do_back {k : Cond} {s : Stmt} {p : Nat} : SStep (.doWhile s k) p (p + s.size) p
  | do_exit {k : Cond} {s : Stmt} {p : Nat} : SStep (.doWhile s k) p (p + s.size) (p + s.size + 1)
  | do_body {k : Cond} {s : Stmt} {p a c : Nat} : SStep s p a c → SStep (.doWhile s k) p a c

theorem comp_length (labs : List (Nat × Nat)) : ∀ (s : Stmt) (p : Nat), (comp labs p s).length = s.size := by
  intro s
  induction s with
  | skip => intro p; rfl
  | blk _ => intro p; rfl
  | seq s t ihs iht => intro p; simp [comp, Stmt.size, ihs, iht]
  | ite1 k s ih => intro p; simp [comp, Stmt.size, ih]; omega
  | ite k s t ihs iht => intro p; simp [comp, Stmt.size, ihs, iht]; omega
  | «while» k s ih => intro p; simp [comp, Stmt.size, ih]; omega
  | doWhile s k ih => intro p; simp [comp, Stmt.size, ih]
  | goto _ => intro p; rfl
  | ifGoto _ _ => intro p; rfl
  | lab _ s ih => intro p; simp [comp, Stmt.size, ih]

/-- The code `l` sits at address `p` of `code`. -/
@[expose] def AtAddr (code : List Instr) (p : Nat) (l : List Instr) : Prop :=
  ∀ j, j < l.length → code.getD (p + j) .halt = l.getD j .halt

theorem AtAddr.append_left {code : List Instr} {p : Nat} {l m : List Instr} (h : AtAddr code p (l ++ m)) :
    AtAddr code p l := by
  intro j hj
  rw [h j (by simp; omega)]
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hj]

theorem AtAddr.append_right {code : List Instr} {p : Nat} {l m : List Instr} (h : AtAddr code p (l ++ m)) :
    AtAddr code (p + l.length) m := by
  intro j hj
  rw [Nat.add_assoc, h (l.length + j) (by simp; omega)]
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_add_right _ _)]

theorem AtAddr.cons {code : List Instr} {p : Nat} {i : Instr} {m : List Instr} (h : AtAddr code p (i :: m)) :
    code.getD p .halt = i ∧ AtAddr code (p + 1) m := by
  refine ⟨by simpa using h 0 (by simp), fun j hj => ?_⟩
  have := h (j + 1) (by simp; omega)
  rw [Nat.add_assoc, Nat.add_comm 1 j]
  simpa [← Nat.add_assoc] using this

theorem AtAddr.get {code : List Instr} {p : Nat} {l : List Instr} (h : AtAddr code p l) {j : Nat} (hj : j < l.length) :
    code.getD (p + j) .halt = l.getD j .halt := h j hj

theorem SStep.range {s : Stmt} {p a c : Nat} (h : SStep s p a c) : p ≤ a ∧ a < p + s.size ∧ p ≤ c ∧ c ≤ p + s.size := by
  induction h with
  | blk => simp only [Stmt.size]; omega
  | @seqL s t p a c _ ih => simp only [Stmt.size]; omega
  | @seqR s t p a c _ ih => simp only [Stmt.size]; omega
  | ite1_skip => simp only [Stmt.size]; omega
  | ite1_in => simp only [Stmt.size]; omega
  | @ite1_body k s p a c _ ih => simp only [Stmt.size]; omega
  | ite_else => simp only [Stmt.size]; omega
  | ite_then => simp only [Stmt.size]; omega
  | ite_jmp => simp only [Stmt.size]; omega
  | @ite_s k s t p a c _ ih => simp only [Stmt.size]; omega
  | @ite_t k s t p a c _ ih => simp only [Stmt.size]; omega
  | while_exit => simp only [Stmt.size]; omega
  | while_in => simp only [Stmt.size]; omega
  | while_back => simp only [Stmt.size]; omega
  | @while_body k s p a c _ ih => simp only [Stmt.size]; omega
  | do_back => simp only [Stmt.size]; omega
  | do_exit => simp only [Stmt.size]; omega
  | @do_body k s p a c _ ih => simp only [Stmt.size]; omega

theorem SStep.inv_ite1 {k : Cond} {s : Stmt} {p a c : Nat} (h : SStep (.ite1 k s) p a c) (ha : a = p) :
    c = p + 1 + s.size ∨ c = p + 1 := by
  cases h <;> first | omega | exact Or.inl rfl | exact Or.inr rfl | (rename_i h'; have := h'.range; omega)

theorem SStep.inv_ite_start {k : Cond} {s t : Stmt} {p a c : Nat} (h : SStep (.ite k s t) p a c) (ha : a = p) :
    c = p + 2 + s.size ∨ c = p + 1 := by
  cases h <;> first | omega | exact Or.inl rfl | exact Or.inr rfl | (rename_i h'; have := h'.range; omega)

theorem SStep.inv_ite_jmp {k : Cond} {s t : Stmt} {p a c : Nat} (h : SStep (.ite k s t) p a c) (ha : a = p + 1 + s.size) :
    c = p + 2 + s.size + t.size := by
  cases h <;> first | omega | rfl | (rename_i h'; have := h'.range; omega)

theorem SStep.inv_while_start {k : Cond} {s : Stmt} {p a c : Nat} (h : SStep (.while k s) p a c) (ha : a = p) :
    c = p + 2 + s.size ∨ c = p + 1 := by
  cases h <;> first | omega | exact Or.inl rfl | exact Or.inr rfl | (rename_i h'; have := h'.range; omega)

theorem SStep.inv_while_back {k : Cond} {s : Stmt} {p a c : Nat} (h : SStep (.while k s) p a c) (ha : a = p + 1 + s.size) :
    c = p := by
  cases h <;> first | omega | rfl | (rename_i h'; have := h'.range; omega)

theorem SStep.inv_do {k : Cond} {s : Stmt} {p a c : Nat} (h : SStep (.doWhile s k) p a c) (ha : a = p + s.size) :
    c = p ∨ c = p + s.size + 1 := by
  cases h <;> first | omega | exact Or.inl rfl | exact Or.inr rfl | (rename_i h'; have := h'.range; omega)

/-- The successor relation of the flat code of a structured statement is `SStep`. -/
theorem SStep_iff (labs : List (Nat × Nat)) (code : List Instr) : ∀ (s : Stmt) (p : Nat), Structured s →
    AtAddr code p (comp labs p s) → ∀ a c, p ≤ a → a < p + s.size → (StepI code a c ↔ SStep s p a c) := by
  intro s
  induction s with
  | skip => intro p _ _ a c h1 h2; simp [Stmt.size] at h2; omega
  | blk b =>
    intro p _ hat a c h1 h2
    simp only [Stmt.size] at h2
    have ha : a = p := by omega
    subst ha
    have hi : code.getD a .halt = .blk b := by simpa [comp] using hat.get (j := 0) (by simp [comp])
    unfold StepI
    rw [hi]
    constructor
    · intro h; subst h; exact .blk
    · intro h; cases h; rfl
  | seq s t ihs iht =>
    intro p hst hat a c h1 h2
    have hat' : AtAddr code p (comp labs p s ++ comp labs (p + s.size) t) := hat
    have hl := hat'.append_left
    have hr := hat'.append_right
    rw [comp_length] at hr
    simp only [Stmt.size] at h2
    by_cases hlt : a < p + s.size
    · rw [ihs p hst.1 hl a c h1 hlt]
      constructor
      · exact .seqL
      · intro h
        cases h with
        | seqL h => exact h
        | seqR h => have := h.range; omega
    · rw [iht (p + s.size) hst.2 hr a c (by omega) (by omega)]
      constructor
      · exact .seqR
      · intro h
        cases h with
        | seqL h => have := h.range; omega
        | seqR h => exact h
  | ite1 k s ih =>
    intro p hs hat a c h1 h2
    have hat' : AtAddr code p (.jmpIf (.neg k) (p + 1 + s.size) :: comp labs (p + 1) s) := hat
    obtain ⟨hi, hr⟩ := hat'.cons
    simp only [Stmt.size] at h2
    by_cases ha : a = p
    · have hia : code.getD a .halt = .jmpIf (.neg k) (p + 1 + s.size) := by rw [ha]; exact hi
      unfold StepI
      rw [hia]
      constructor
      · rintro (h | h)
        · subst ha; subst h; exact .ite1_skip
        · subst ha; rw [h]; exact .ite1_in
      · intro h
        rcases h.inv_ite1 ha with h' | h'
        · exact Or.inl h'
        · right; rw [h', ha]
    · rw [ih (p + 1) hs hr a c (by omega) (by omega)]
      constructor
      · exact .ite1_body
      · intro h
        cases h with
        | ite1_skip => omega
        | ite1_in => omega
        | ite1_body h => exact h
  | ite k s t ihs iht =>
    intro p hst hat a c h1 h2
    have hat' : AtAddr code p (.jmpIf (.neg k) (p + 2 + s.size) ::
        (comp labs (p + 1) s ++ (.jmp (p + 2 + s.size + t.size) :: comp labs (p + 2 + s.size) t))) := hat
    obtain ⟨hi, hr⟩ := hat'.cons
    have hl := hr.append_left
    have hr2 := hr.append_right
    rw [comp_length] at hr2
    obtain ⟨hj, ht⟩ := hr2.cons
    have e1 : p + 1 + s.size + 1 = p + 2 + s.size := by omega
    rw [e1] at ht
    have hj' : code.getD (p + 1 + s.size) .halt = .jmp (p + 2 + s.size + t.size) := hj
    simp only [Stmt.size] at h2
    by_cases ha : a = p
    · have hia : code.getD a .halt = .jmpIf (.neg k) (p + 2 + s.size) := by rw [ha]; exact hi
      unfold StepI
      rw [hia]
      constructor
      · rintro (h | h)
        · subst ha; subst h; exact .ite_else
        · subst ha; rw [h]; exact .ite_then
      · intro h
        rcases h.inv_ite_start ha with h' | h'
        · exact Or.inl h'
        · right; rw [h', ha]
    · by_cases hb : a < p + 1 + s.size
      · rw [ihs (p + 1) hst.1 hl a c (by omega) hb]
        constructor
        · exact .ite_s
        · intro h
          cases h with
          | ite_else => omega
          | ite_then => omega
          | ite_jmp => omega
          | ite_s h => exact h
          | ite_t h => have := h.range; omega
      · by_cases hc : a = p + 1 + s.size
        · have hia : code.getD a .halt = .jmp (p + 2 + s.size + t.size) := by rw [hc]; exact hj'
          unfold StepI
          rw [hia]
          constructor
          · intro h; subst hc; subst h; exact .ite_jmp
          · intro h
            exact h.inv_ite_jmp hc
        · rw [iht (p + 2 + s.size) hst.2 ht a c (by omega) (by omega)]
          constructor
          · exact .ite_t
          · intro h
            cases h with
            | ite_else => omega
            | ite_then => omega
            | ite_jmp => omega
            | ite_s h => have := h.range; omega
            | ite_t h => exact h
  | «while» k s ih =>
    intro p hs hat a c h1 h2
    have hat' : AtAddr code p (.jmpIf (.neg k) (p + 2 + s.size) :: (comp labs (p + 1) s ++ [.jmp p])) := hat
    obtain ⟨hi, hr⟩ := hat'.cons
    have hl := hr.append_left
    have hr2 := hr.append_right
    rw [comp_length] at hr2
    have hj : code.getD (p + 1 + s.size) .halt = .jmp p := by simpa using hr2.get (j := 0) (by simp)
    simp only [Stmt.size] at h2
    by_cases ha : a = p
    · have hia : code.getD a .halt = .jmpIf (.neg k) (p + 2 + s.size) := by rw [ha]; exact hi
      unfold StepI
      rw [hia]
      constructor
      · rintro (h | h)
        · subst ha; subst h; exact .while_exit
        · subst ha; rw [h]; exact .while_in
      · intro h
        rcases h.inv_while_start ha with h' | h'
        · exact Or.inl h'
        · right; rw [h', ha]
    · by_cases hb : a < p + 1 + s.size
      · rw [ih (p + 1) hs hl a c (by omega) hb]
        constructor
        · exact .while_body
        · intro h
          cases h with
          | while_exit => omega
          | while_in => omega
          | while_back => omega
          | while_body h => exact h
      · have hc : a = p + 1 + s.size := by omega
        have hia : code.getD a .halt = .jmp p := by rw [hc]; exact hj
        unfold StepI
        rw [hia]
        constructor
        · intro h; subst hc; subst h; exact .while_back
        · intro h
          exact h.inv_while_back hc
  | doWhile s k ih =>
    intro p hs hat a c h1 h2
    have hat' : AtAddr code p (comp labs p s ++ [.jmpIf k p]) := hat
    have hl := hat'.append_left
    have hr := hat'.append_right
    rw [comp_length] at hr
    have hj : code.getD (p + s.size) .halt = .jmpIf k p := by simpa using hr.get (j := 0) (by simp)
    simp only [Stmt.size] at h2
    by_cases hb : a < p + s.size
    · rw [ih p hs hl a c h1 hb]
      constructor
      · exact .do_body
      · intro h
        cases h with
        | do_back => omega
        | do_exit => omega
        | do_body h => exact h
    · have hc : a = p + s.size := by omega
      have hia : code.getD a .halt = .jmpIf k p := by rw [hc]; exact hj
      unfold StepI
      rw [hia]
      constructor
      · rintro (h | h)
        · subst hc; subst h; exact .do_back
        · subst hc; rw [h]; exact .do_exit
      · intro h
        rcases h.inv_do hc with h' | h'
        · exact Or.inl h'
        · right; rw [h', hc]
  | goto _ => intro p h; exact h.elim
  | ifGoto _ _ => intro p h; exact h.elim
  | lab _ s _ => intro p h; exact h.elim


/-- `u` occurs in `s` at address `q` when `s` is placed at address `p`. -/
inductive Sub : Stmt → Nat → Stmt → Nat → Prop
  | refl {s : Stmt} {p : Nat} : Sub s p s p
  | seqL {u s t : Stmt} {q p : Nat} : Sub u q s p → Sub u q (.seq s t) p
  | seqR {u s t : Stmt} {q p : Nat} : Sub u q t (p + s.size) → Sub u q (.seq s t) p
  | ite1 {u s : Stmt} {k : Cond} {q p : Nat} : Sub u q s (p + 1) → Sub u q (.ite1 k s) p
  | iteS {u s t : Stmt} {k : Cond} {q p : Nat} : Sub u q s (p + 1) → Sub u q (.ite k s t) p
  | iteT {u s t : Stmt} {k : Cond} {q p : Nat} : Sub u q t (p + 2 + s.size) → Sub u q (.ite k s t) p
  | whl {u s : Stmt} {k : Cond} {q p : Nat} : Sub u q s (p + 1) → Sub u q (.while k s) p
  | dow {u s : Stmt} {k : Cond} {q p : Nat} : Sub u q s p → Sub u q (.doWhile s k) p

theorem Sub.range {u s : Stmt} {q p : Nat} (h : Sub u q s p) : p ≤ q ∧ q + u.size ≤ p + s.size := by
  induction h with
  | refl => omega
  | seqL _ ih => simp only [Stmt.size]; omega
  | seqR _ ih => simp only [Stmt.size]; omega
  | ite1 _ ih => simp only [Stmt.size]; omega
  | iteS _ ih => simp only [Stmt.size]; omega
  | iteT _ ih => simp only [Stmt.size]; omega
  | whl _ ih => simp only [Stmt.size]; omega
  | dow _ ih => simp only [Stmt.size]; omega

/-- A region of a structured program is entered from outside only at its first address: a step into the interior of the
occurrence of `u` starts inside it. -/
theorem Sub.entry {u s : Stmt} {q p : Nat} (h : Sub u q s p) : ∀ {a c : Nat}, SStep s p a c → q < c → c < q + u.size →
    q ≤ a ∧ a < q + u.size := by
  induction h with
  | refl => intro a c hs _ _; have := hs.range; omega
  | seqL hsub ih =>
    intro a c hs h1 h2
    have hr := hsub.range
    cases hs with
    | seqL h => exact ih h h1 h2
    | seqR h => have := h.range; omega
  | seqR hsub ih =>
    intro a c hs h1 h2
    have hr := hsub.range
    cases hs with
    | seqL h => have := h.range; omega
    | seqR h => exact ih h h1 h2
  | ite1 hsub ih =>
    intro a c hs h1 h2
    have hr := hsub.range
    cases hs with
    | ite1_skip => omega
    | ite1_in => omega
    | ite1_body h => exact ih h h1 h2
  | iteS hsub ih =>
    intro a c hs h1 h2
    have hr := hsub.range
    cases hs with
    | ite_else => omega
    | ite_then => omega
    | ite_jmp => omega
    | ite_s h => exact ih h h1 h2
    | ite_t h => have := h.range; omega
  | iteT hsub ih =>
    intro a c hs h1 h2
    have hr := hsub.range
    cases hs with
    | ite_else => omega
    | ite_then => omega
    | ite_jmp => omega
    | ite_s h => have := h.range; omega
    | ite_t h => exact ih h h1 h2
  | whl hsub ih =>
    intro a c hs h1 h2
    have hr := hsub.range
    cases hs with
    | while_exit => omega
    | while_in => omega
    | while_back => omega
    | while_body h => exact ih h h1 h2
  | dow hsub ih =>
    intro a c hs h1 h2
    have hr := hsub.range
    cases hs with
    | do_back => omega
    | do_exit => omega
    | do_body h => exact ih h h1 h2

end SmcIrred.Lang
