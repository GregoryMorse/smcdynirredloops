module

public import SmcIrred.Lang.Fwd

public section

namespace SmcIrred.Lang

/-! # Protection of arbitrary code (G33 b, C65): functional equivalence

`prot h S T k` is the form of Figures 5(b) and 6(b) for arbitrary goto-free `S`, `T`. When the two added conditions are
false the run of the protected code is the run of the original: whatever `exec` returns for one, it returns for the other
(`prot5_equiv`, `prot6_equiv`), for every environment and every state of the toggled variable. -/

/-- Shift every jump target by `d`. -/
@[expose] def shiftI (d : Nat) : Instr → Instr
  | .blk a => .blk a
  | .jmp t => .jmp (t + d)
  | .jmpIf k t => .jmpIf k (t + d)
  | .halt => .halt

theorem shiftI_zero (i : Instr) : shiftI 0 i = i := by cases i <;> rfl

theorem comp_shift (labs : List (Nat × Nat)) (d : Nat) : ∀ (s : Stmt), Structured s → ∀ p,
    comp labs (p + d) s = (comp labs p s).map (shiftI d) := by
  intro s
  induction s with
  | skip => intro _ p; rfl
  | blk _ => intro _ p; rfl
  | seq s t ihs iht =>
    intro h p
    simp only [comp, List.map_append]
    rw [ihs h.1 p, show p + d + s.size = p + s.size + d by omega, iht h.2 (p + s.size)]
  | ite1 k s ih =>
    intro h p
    simp only [comp, List.map_cons, shiftI]
    rw [show p + d + 1 = p + 1 + d by omega, ih h (p + 1)]
    simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  | ite k s t ihs iht =>
    intro h p
    simp only [comp, List.map_cons, List.map_append, shiftI]
    rw [show p + d + 1 = p + 1 + d by omega, ihs h.1 (p + 1),
      show p + d + 2 + s.size = p + 2 + s.size + d by omega, iht h.2 (p + 2 + s.size)]
    simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  | «while» k s ih =>
    intro h p
    simp only [comp, List.map_cons, List.map_append, List.map_nil, shiftI]
    rw [show p + d + 1 = p + 1 + d by omega, ih h (p + 1)]
    simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  | doWhile s k ih =>
    intro h p
    simp only [comp, List.map_append, List.map_cons, List.map_nil, shiftI]
    rw [ih h p]
  | goto _ => intro h; exact h.elim
  | ifGoto _ _ => intro h; exact h.elim
  | lab _ _ _ => intro h; exact h.elim

theorem exec_blk {code : List Instr} {sol : Nat → Bool} {env : Bool} {pc a : Nat} {v : Bool} {tr : List Nat} {f : Nat}
    (h : code.getD pc .halt = .blk a) :
    exec (f + 1) code sol env pc v tr = exec f code sol env (pc + 1) v (tr ++ [a]) := by simp only [exec, h]

theorem exec_jmp {code : List Instr} {sol : Nat → Bool} {env : Bool} {pc t : Nat} {v : Bool} {tr : List Nat} {f : Nat}
    (h : code.getD pc .halt = .jmp t) : exec (f + 1) code sol env pc v tr = exec f code sol env t v tr := by
  simp only [exec, h]

theorem exec_jmpIf {code : List Instr} {sol : Nat → Bool} {env : Bool} {pc t : Nat} {k : Cond} {v : Bool} {tr : List Nat}
    {f : Nat} (h : code.getD pc .halt = .jmpIf k t) :
    exec (f + 1) code sol env pc v tr =
      exec f code sol env (if (k.eval sol env v).1 then t else pc + 1) (k.eval sol env v).2 tr := by
  simp only [exec, h]

theorem exec_halt {code : List Instr} {sol : Nat → Bool} {env : Bool} {pc : Nat} {v : Bool} {tr : List Nat} {f : Nat}
    (h : code.getD pc .halt = .halt) : exec (f + 1) code sol env pc v tr = some (tr, v) := by
  simp only [exec, h]

/-- The simulation of a run by a run of code that agrees with it on `[0, sz)` up to the shift `d`, whose jump targets stay
in `[0, sz]`, and that ends in `halt` at `sz` where the other has a jump on a false condition and then `halt`. -/
structure Agree (P Q : List Instr) (sol : Nat → Bool) (env : Bool) (d sz : Nat) (kk : Cond) : Prop where
  body : ∀ a, a < sz → Q.getD (a + d) .halt = shiftI d (P.getD a .halt)
  tgt : ∀ a t, a < sz → (P.getD a .halt).target = some t → t ≤ sz
  endP : P.getD sz .halt = .halt
  endQ : ∃ t, Q.getD (sz + d) .halt = .jmpIf kk t
  endQ' : Q.getD (sz + d + 1) .halt = .halt
  kkf : ∀ v, (kk.eval sol env v).1 = false ∧ (kk.eval sol env v).2 = v

theorem Agree.fwd {P Q : List Instr} {sol : Nat → Bool} {env : Bool} {d sz : Nat} {kk : Cond}
    (h : Agree P Q sol env d sz kk) : ∀ f a v tr r, a ≤ sz → exec f P sol env a v tr = some r →
      exec (f + 1) Q sol env (a + d) v tr = some r := by
  intro f
  induction f with
  | zero => intro a v tr r _ h0; simp [exec] at h0
  | succ f ih =>
    intro a v tr r ha hex
    by_cases hlt : a < sz
    · have hq := h.body a hlt
      cases hi : P.getD a .halt with
      | blk b =>
        have hqq : Q.getD (a + d) .halt = .blk b := by rw [hq, hi]; rfl
        rw [exec_blk hi] at hex
        rw [exec_blk hqq, show a + d + 1 = a + 1 + d by omega]
        exact ih (a + 1) v (tr ++ [b]) r (by omega) hex
      | jmp t =>
        have hqq : Q.getD (a + d) .halt = .jmp (t + d) := by rw [hq, hi]; rfl
        rw [exec_jmp hi] at hex
        rw [exec_jmp hqq]
        exact ih t v tr r (h.tgt a t hlt (by rw [hi]; rfl)) hex
      | jmpIf k t =>
        have hqq : Q.getD (a + d) .halt = .jmpIf k (t + d) := by rw [hq, hi]; rfl
        have ht := h.tgt a t hlt (by rw [hi]; rfl)
        rw [exec_jmpIf hi] at hex
        rw [exec_jmpIf hqq]
        by_cases hc : (k.eval sol env v).1 = true
        · simp only [hc, ↓reduceIte] at hex ⊢
          exact ih t _ tr r ht hex
        · simp only [hc, ↓reduceIte] at hex ⊢
          rw [show a + d + 1 = a + 1 + d by omega]
          exact ih (a + 1) _ tr r (by omega) hex
      | halt =>
        have hqq : Q.getD (a + d) .halt = .halt := by rw [hq, hi]; rfl
        rw [exec_halt hi] at hex
        rw [exec_halt hqq]
        exact hex
    · have has : a = sz := by omega
      subst has
      rw [exec_halt h.endP] at hex
      obtain ⟨t, ht⟩ := h.endQ
      obtain ⟨hk1, hk2⟩ := h.kkf v
      rw [exec_jmpIf ht]
      simp only [hk1, hk2, Bool.false_eq_true, ↓reduceIte]
      rw [exec_halt h.endQ']
      exact hex

theorem Agree.bwd {P Q : List Instr} {sol : Nat → Bool} {env : Bool} {d sz : Nat} {kk : Cond}
    (h : Agree P Q sol env d sz kk) : ∀ f a v tr r, a ≤ sz → exec f Q sol env (a + d) v tr = some r →
      ∃ f', exec f' P sol env a v tr = some r := by
  intro f
  induction f with
  | zero => intro a v tr r _ h0; simp [exec] at h0
  | succ f ih =>
    intro a v tr r ha hex
    by_cases hlt : a < sz
    · have hq := h.body a hlt
      cases hi : P.getD a .halt with
      | blk b =>
        have hqq : Q.getD (a + d) .halt = .blk b := by rw [hq, hi]; rfl
        rw [exec_blk hqq, show a + d + 1 = a + 1 + d by omega] at hex
        obtain ⟨f', hf'⟩ := ih (a + 1) v (tr ++ [b]) r (by omega) hex
        exact ⟨f' + 1, by rw [exec_blk hi]; exact hf'⟩
      | jmp t =>
        have hqq : Q.getD (a + d) .halt = .jmp (t + d) := by rw [hq, hi]; rfl
        rw [exec_jmp hqq] at hex
        obtain ⟨f', hf'⟩ := ih t v tr r (h.tgt a t hlt (by rw [hi]; rfl)) hex
        exact ⟨f' + 1, by rw [exec_jmp hi]; exact hf'⟩
      | jmpIf k t =>
        have hqq : Q.getD (a + d) .halt = .jmpIf k (t + d) := by rw [hq, hi]; rfl
        have ht := h.tgt a t hlt (by rw [hi]; rfl)
        rw [exec_jmpIf hqq] at hex
        by_cases hc : (k.eval sol env v).1 = true
        · simp only [hc, ↓reduceIte] at hex
          obtain ⟨f', hf'⟩ := ih t _ tr r ht hex
          exact ⟨f' + 1, by rw [exec_jmpIf hi]; simp only [hc, ↓reduceIte]; exact hf'⟩
        · simp only [hc, ↓reduceIte] at hex
          rw [show a + d + 1 = a + 1 + d by omega] at hex
          obtain ⟨f', hf'⟩ := ih (a + 1) _ tr r (by omega) hex
          exact ⟨f' + 1, by rw [exec_jmpIf hi]; simp only [hc, ↓reduceIte]; exact hf'⟩
      | halt =>
        have hqq : Q.getD (a + d) .halt = .halt := by rw [hq, hi]; rfl
        rw [exec_halt hqq] at hex
        exact ⟨1, by rw [exec_halt hi]; exact hex⟩
    · have has : a = sz := by omega
      subst has
      obtain ⟨t, ht⟩ := h.endQ
      obtain ⟨hk1, hk2⟩ := h.kkf v
      rw [exec_jmpIf ht] at hex
      simp only [hk1, hk2, Bool.false_eq_true, ↓reduceIte] at hex
      cases f with
      | zero => simp [exec] at hex
      | succ f' =>
        rw [exec_halt h.endQ'] at hex
        exact ⟨1, by rw [exec_halt h.endP]; exact hex⟩

/-! ### The code of the protected forms -/

theorem labelsOf_structured : ∀ (s : Stmt), Structured s → ∀ p, labelsOf p s = [] := by
  intro s
  induction s with
  | skip => intro _ p; rfl
  | blk _ => intro _ p; rfl
  | seq s t ihs iht => intro h p; simp [labelsOf, ihs h.1, iht h.2]
  | ite1 k s ih => intro h p; simp [labelsOf, ih h]
  | ite k s t ihs iht => intro h p; simp [labelsOf, ihs h.1, iht h.2]
  | «while» k s ih => intro h p; simp [labelsOf, ih h]
  | doWhile s k ih => intro h p; simp [labelsOf, ih h]
  | goto _ => intro h; exact h.elim
  | ifGoto _ _ => intro h; exact h.elim
  | lab _ _ _ => intro h; exact h.elim

theorem comp_labs (labs labs' : List (Nat × Nat)) : ∀ (s : Stmt), Structured s → ∀ p,
    comp labs p s = comp labs' p s := by
  intro s
  induction s with
  | skip => intro _ p; rfl
  | blk _ => intro _ p; rfl
  | seq s t ihs iht => intro h p; simp only [comp, ihs h.1, iht h.2]
  | ite1 k s ih => intro h p; simp only [comp, ih h]
  | ite k s t ihs iht => intro h p; simp only [comp, ihs h.1, iht h.2]
  | «while» k s ih => intro h p; simp only [comp, ih h]
  | doWhile s k ih => intro h p; simp only [comp, ih h]
  | goto _ => intro h; exact h.elim
  | ifGoto _ _ => intro h; exact h.elim
  | lab _ _ _ => intro h; exact h.elim

theorem compile_structured {s : Stmt} (hs : Structured s) : compile s = comp [] 0 s ++ [.halt] := by
  unfold compile
  rw [labelsOf_structured s hs 0, comp_labs [] [] s hs 0]

/-- The code of the protected form: the entry jump, the shared body, the closing jump, `halt`. -/
theorem compile_prot {S T : Stmt} (hS : Structured S) (hT : Structured T) (h k : Cond) :
    compile (prot h S T k) = .jmpIf h (1 + S.size) :: (comp [] 1 S ++ (comp [] (1 + S.size) T ++ [.jmpIf k 1, .halt])) := by
  have hl : labelsOf 0 (prot h S T k) = [(9, 1 + S.size)] := by
    simp [prot, labelsOf, Stmt.size, labelsOf_structured S hS, labelsOf_structured T hT]
  unfold compile
  rw [hl]
  simp only [prot, comp, Stmt.size, lookupLabel, List.find?_cons, List.find?_nil]
  rw [comp_labs _ [] S hS, comp_labs _ [] T hT]
  simp [Nat.add_comm]

theorem getD_app_l {l m : List Instr} {a : Nat} (h : a < l.length) : (l ++ m).getD a .halt = l.getD a .halt := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_app_r (l m : List Instr) (a : Nat) : (l ++ m).getD (l.length + a) .halt = m.getD a .halt := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_add_right _ _)]

theorem getD_map_shift (l : List Instr) (d a : Nat) : (l.map (shiftI d)).getD a .halt = shiftI d (l.getD a .halt) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases h : l[a]? <;> simp [shiftI]

theorem tgt_le {s : Stmt} (hs : Structured s) {a t : Nat}
    (h : ((compile s).getD a .halt).target = some t) : t ≤ s.size := by
  have hst : StepI (compile s) a t := by
    unfold StepI
    cases hi : (compile s).getD a .halt <;> simp only [hi, Instr.target] at h
    · exact absurd h (by simp)
    · cases h; exact rfl
    · cases h; exact Or.inl rfl
    · exact absurd h (by simp)
  have := (compile_step hs hst).range
  omega

/-- Figure 5(b) for arbitrary code: with the two added conditions false the protected code and `S; T` return the same
trace and state. -/
theorem prot5_equiv {S T : Stmt} (hS : Structured S) (hT : Structured T) {sol : Nat → Bool} (h1 : sol 1 = false)
    (h2 : sol 2 = false) (env v : Bool) (r : List Nat × Bool) :
    (∃ f, exec f (compile (.seq S T)) sol env 0 v [] = some r) ↔
      ∃ f, exec f (compile (prot5 S T)) sol env 0 v [] = some r := by
  have hst : Structured (.seq S T) := ⟨hS, hT⟩
  have hsh1 : comp [] 1 S = (comp [] 0 S).map (shiftI 1) := comp_shift [] 1 S hS 0
  have hsh2 : comp [] (1 + S.size) T = (comp [] S.size T).map (shiftI 1) := by
    rw [Nat.add_comm]; exact comp_shift [] 1 T hT S.size
  have hK : (comp [] 0 S ++ comp [] S.size T).length = S.size + T.size := by
    rw [List.length_append, comp_length, comp_length]
  have hP : compile (.seq S T) = (comp [] 0 S ++ comp [] S.size T) ++ [.halt] := by
    have := compile_structured hst
    rw [this]; simp [comp]
  have hQ : compile (prot5 S T) = .jmpIf (.out 1) (1 + S.size) ::
      ((comp [] 0 S ++ comp [] S.size T).map (shiftI 1) ++ [.jmpIf (.out 2) 1, .halt]) := by
    show compile (prot (.out 1) S T (.out 2)) = _
    rw [compile_prot hS hT, hsh1, hsh2]
    simp [List.map_append]
  have hKm : ((comp [] 0 S ++ comp [] S.size T).map (shiftI 1)).length = S.size + T.size := by rw [List.length_map, hK]
  have hag : Agree (compile (.seq S T)) (compile (prot5 S T)) sol env 1 (S.size + T.size) (.out 2) := by
    refine ⟨fun a ha => ?_, fun a t ha ht => ?_, ?_, ⟨1, ?_⟩, ?_, fun v => ?_⟩
    · rw [hP, hQ, getD_app_l (by omega), List.getD_cons_succ, getD_app_l (by rw [hKm]; omega),
        getD_map_shift]
    · have := tgt_le hst ht
      simpa [Stmt.size] using this
    · rw [hP, ← hK]
      simpa using getD_app_r (comp [] 0 S ++ comp [] S.size T) [.halt] 0
    · rw [hQ, List.getD_cons_succ, ← hKm]
      simpa using getD_app_r ((comp [] 0 S ++ comp [] S.size T).map (shiftI 1)) [.jmpIf (.out 2) 1, .halt] 0
    · rw [hQ, List.getD_cons_succ, ← hKm]
      simpa using getD_app_r ((comp [] 0 S ++ comp [] S.size T).map (shiftI 1)) [.jmpIf (.out 2) 1, .halt] 1
    · simp [Cond.eval, h2]
  have hjmp : (compile (prot5 S T)).getD 0 .halt = .jmpIf (.out 1) (1 + S.size) := by rw [hQ]; rfl
  constructor
  · rintro ⟨f, hf⟩
    have := hag.fwd f 0 v [] r (by omega) hf
    refine ⟨f + 1 + 1, ?_⟩
    rw [exec_jmpIf hjmp]
    simp only [Cond.eval, h1, Bool.false_eq_true, ↓reduceIte]
    exact this
  · rintro ⟨f, hf⟩
    cases f with
    | zero => simp [exec] at hf
    | succ f =>
      rw [exec_jmpIf hjmp] at hf
      simp only [Cond.eval, h1, Bool.false_eq_true, ↓reduceIte] at hf
      exact hag.bwd f 0 v [] r (by omega) hf

/-- Figure 6(b) for arbitrary code: with the added condition false the protected code and `if (c) S; T` return the same
trace and state. -/
theorem prot6_equiv {S T : Stmt} (hS : Structured S) (hT : Structured T) (cd : Cond) {sol : Nat → Bool}
    (h1 : sol 1 = false) (env v : Bool) (r : List Nat × Bool) :
    (∃ f, exec f (compile (.seq (.ite1 cd S) T)) sol env 0 v [] = some r) ↔
      ∃ f, exec f (compile (prot6 cd S T)) sol env 0 v [] = some r := by
  have hst : Structured (.seq (.ite1 cd S) T) := ⟨hS, hT⟩
  have hP : compile (.seq (.ite1 cd S) T) =
      (.jmpIf (.neg cd) (1 + S.size) :: (comp [] 1 S ++ comp [] (1 + S.size) T)) ++ [.halt] := by
    rw [compile_structured hst]
    simp only [comp, Stmt.size, Nat.zero_add, List.cons_append, List.append_assoc]
  have hQ : compile (prot6 cd S T) =
      (.jmpIf (.neg cd) (1 + S.size) :: (comp [] 1 S ++ comp [] (1 + S.size) T)) ++ [.jmpIf (.out 1) 1, .halt] := by
    show compile (prot (.neg cd) S T (.out 1)) = _
    rw [compile_prot hS hT]
    simp only [List.cons_append, List.append_assoc]
  have hK : (Instr.jmpIf (.neg cd) (1 + S.size) :: (comp [] 1 S ++ comp [] (1 + S.size) T)).length = S.size + T.size + 1 := by
    simp only [List.length_cons, List.length_append, comp_length]
  have hag : Agree (compile (.seq (.ite1 cd S) T)) (compile (prot6 cd S T)) sol env 0 (S.size + T.size + 1) (.out 1) := by
    refine ⟨fun a ha => ?_, fun a t ha ht => ?_, ?_, ⟨1, ?_⟩, ?_, fun v => ?_⟩
    · rw [hP, hQ, Nat.add_zero, getD_app_l (by omega), getD_app_l (by omega), shiftI_zero]
    · have := tgt_le hst ht
      simp only [Stmt.size] at this
      omega
    · rw [hP, ← hK]
      simpa using getD_app_r (Instr.jmpIf (.neg cd) (1 + S.size) :: (comp [] 1 S ++ comp [] (1 + S.size) T)) [.halt] 0
    · rw [hQ, Nat.add_zero, ← hK]
      simpa using getD_app_r (Instr.jmpIf (.neg cd) (1 + S.size) :: (comp [] 1 S ++ comp [] (1 + S.size) T))
        [.jmpIf (.out 1) 1, .halt] 0
    · rw [hQ, ← hK]
      simpa using getD_app_r (Instr.jmpIf (.neg cd) (1 + S.size) :: (comp [] 1 S ++ comp [] (1 + S.size) T))
        [.jmpIf (.out 1) 1, .halt] 1
    · simp [Cond.eval, h1]
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨f + 1, hag.fwd f 0 v [] r (by omega) hf⟩
  · rintro ⟨f, hf⟩
    exact hag.bwd f 0 v [] r (by omega) hf

end SmcIrred.Lang
