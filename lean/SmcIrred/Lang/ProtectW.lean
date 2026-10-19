module

public import SmcIrred.Lang.Window
public import SmcIrred.Lang.Protect
public import SmcIrred.Lang.ProtIrred
public import SmcIrred.Lang.EntryCycle
public import SmcIrred.Spec.LangFigs

public section

namespace SmcIrred.Lang

/-! # Figures 5(c), 6(c) for arbitrary code: functional equivalence (G32 a2)

The toggled variable of `while (trueThenFalse)` starts true, is false inside the loop body and true after the loop.  The
conditions of `S`, `T` do not read it (`PureS`).  With the added entry condition false the protected program has the result
of the original. -/

@[expose] def PureC (sol : Nat → Bool) (env : Bool) (k : Cond) : Prop := ∃ b, ∀ v, k.eval sol env v = (b, v)

@[expose] def PureS (sol : Nat → Bool) (env : Bool) : Stmt → Prop
  | .skip => True
  | .blk _ => True
  | .seq s t => PureS sol env s ∧ PureS sol env t
  | .ite1 k s => PureC sol env k ∧ PureS sol env s
  | .ite k s t => PureC sol env k ∧ PureS sol env s ∧ PureS sol env t
  | .while k s => PureC sol env k ∧ PureS sol env s
  | .doWhile s k => PureS sol env s ∧ PureC sol env k
  | .goto _ => True
  | .ifGoto _ _ => True
  | .lab _ s => PureS sol env s

theorem PureC.neg {sol env k} (h : PureC sol env k) : PureC sol env (.neg k) := by
  obtain ⟨b, hb⟩ := h
  exact ⟨!b, fun v => by simp [Cond.eval, hb]⟩

theorem comp_inv {sol : Nat → Bool} {env : Bool} : ∀ (s : Stmt), Structured s → PureS sol env s → ∀ p,
    ∀ i ∈ comp [] p s, i ≠ .halt ∧ ∀ k t, i = .jmpIf k t → PureC sol env k := by
  intro s
  induction s with
  | skip => intro _ _ p i hi; simp [comp] at hi
  | blk a => intro _ _ p i hi; simp [comp] at hi; subst hi; simp
  | seq s t ihs iht =>
    intro h hp p i hi
    simp only [comp, List.mem_append] at hi
    rcases hi with hi | hi
    · exact ihs h.1 hp.1 p i hi
    · exact iht h.2 hp.2 _ i hi
  | ite1 k s ih =>
    intro h hp p i hi
    simp only [comp, List.mem_cons] at hi
    rcases hi with hi | hi
    · subst hi; exact ⟨by simp, fun k' t e => by cases e; exact hp.1.neg⟩
    · exact ih h hp.2 _ i hi
  | ite k s t ihs iht =>
    intro h hp p i hi
    simp only [comp, List.mem_cons, List.mem_append] at hi
    rcases hi with hi | hi | hi | hi
    · subst hi; exact ⟨by simp, fun k' t e => by cases e; exact hp.1.neg⟩
    · exact ihs h.1 hp.2.1 _ i hi
    · subst hi; simp
    · exact iht h.2 hp.2.2 _ i hi
  | «while» k s ih =>
    intro h hp p i hi
    simp only [comp, List.mem_cons, List.mem_append, List.mem_singleton] at hi
    rcases hi with hi | hi | hi
    · subst hi; exact ⟨by simp, fun k' t e => by cases e; exact hp.1.neg⟩
    · exact ih h hp.2 _ i hi
    · simp at hi; subst hi; simp
  | doWhile s k ih =>
    intro h hp p i hi
    simp only [comp, List.mem_cons, List.mem_append, List.mem_singleton] at hi
    rcases hi with hi | hi
    · exact ih h hp.1 _ i hi
    · simp at hi; subst hi; exact ⟨by simp, fun k' t e => by cases e; exact hp.2⟩
  | goto _ => intro h; exact h.elim
  | ifGoto _ _ => intro h; exact h.elim
  | lab _ _ _ => intro h; exact h.elim

theorem compile_protC {S T : Stmt} (hS : Structured S) (hT : Structured T) (h : Cond) :
    compile (protC h S T) = .jmpIf h (2 + S.size) :: .jmpIf (.neg .ttf) (3 + (S.size + T.size)) ::
      (((comp [] 0 S ++ comp [] S.size T).map (shiftI 2)) ++ [.jmp 1, .halt]) := by
  have hl : labelsOf 0 (protC h S T) = [(9, 2 + S.size)] := by
    simp [protC, labelsOf, Stmt.size, labelsOf_structured S hS, labelsOf_structured T hT, Nat.add_comm]
  have hsh1 : comp [] 2 S = (comp [] 0 S).map (shiftI 2) := comp_shift [] 2 S hS 0
  have hsh2 : comp [] (2 + S.size) T = (comp [] S.size T).map (shiftI 2) := by
    rw [Nat.add_comm]; exact comp_shift [] 2 T hT S.size
  unfold compile
  rw [hl]
  simp only [protC, comp, Stmt.size, lookupLabel, List.find?_cons, List.find?_nil]
  rw [comp_labs _ [] S hS, comp_labs _ [] T hT]
  simp [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, hsh1, hsh2, List.map_append]


section inv

variable {code : List Instr} {sol : Nat → Bool} {env : Bool}

theorem Halts.inv_halt {pc : Nat} {v : Bool} {tr : List Nat} {r : List Nat × Bool}
    (h : Halts code sol env pc v tr r) (hi : code.getD pc .halt = .halt) : r = (tr, v) := by
  cases h <;> simp_all

theorem Halts.inv_jmp {pc t : Nat} {v : Bool} {tr : List Nat} {r : List Nat × Bool}
    (h : Halts code sol env pc v tr r) (hi : code.getD pc .halt = .jmp t) : Halts code sol env t v tr r := by
  cases h <;> simp_all

theorem Halts.inv_jmpIf {pc t : Nat} {k : Cond} {v : Bool} {tr : List Nat} {r : List Nat × Bool}
    (h : Halts code sol env pc v tr r) (hi : code.getD pc .halt = .jmpIf k t) :
    Halts code sol env (if (k.eval sol env v).1 then t else pc + 1) (k.eval sol env v).2 tr r := by
  cases h <;> simp_all

end inv

/-- Figure 5(c) for arbitrary code: with the entry condition false and the toggled variable true, the protected program
returns what `S; T` returns. -/
theorem protC_equiv {S T : Stmt} (hS : Structured S) (hT : Structured T) {sol : Nat → Bool} {env : Bool}
    (hpS : PureS sol env S) (hpT : PureS sol env T) {h : Cond} (hh : h.eval sol env true = (false, true))
    (r : List Nat × Bool) :
    (∃ f, exec f (compile (.seq S T)) sol env 0 true [] = some r) ↔
      ∃ f, exec f (compile (protC h S T)) sol env 0 true [] = some r := by
  have hst : Structured (.seq S T) := ⟨hS, hT⟩
  have hK : (comp [] 0 S ++ comp [] S.size T).length = S.size + T.size := by
    rw [List.length_append, comp_length, comp_length]
  have hP : compile (.seq S T) = (comp [] 0 S ++ comp [] S.size T) ++ [.halt] := by
    have := compile_structured hst
    rw [this]; simp [comp]
  have hQ := compile_protC hS hT h
  have hKm : ((comp [] 0 S ++ comp [] S.size T).map (shiftI 2)).length = S.size + T.size := by
    rw [List.length_map, hK]
  have hQ0 : (compile (protC h S T)).getD 0 .halt = .jmpIf h (2 + S.size) := by rw [hQ]; rfl
  have hQ1 : (compile (protC h S T)).getD 1 .halt = .jmpIf (.neg .ttf) (3 + (S.size + T.size)) := by rw [hQ]; rfl
  have hQj : (compile (protC h S T)).getD (S.size + T.size + 2) .halt = .jmp 1 := by
    rw [hQ, List.getD_cons_succ, List.getD_cons_succ, ← hKm]
    simpa using getD_app_r ((comp [] 0 S ++ comp [] S.size T).map (shiftI 2)) [.jmp 1, .halt] 0
  have hQh : (compile (protC h S T)).getD (S.size + T.size + 3) .halt = .halt := by
    rw [hQ, List.getD_cons_succ, List.getD_cons_succ, ← hKm]
    simpa using getD_app_r ((comp [] 0 S ++ comp [] S.size T).map (shiftI 2)) [.jmp 1, .halt] 1
  have hPh : (compile (.seq S T)).getD (S.size + T.size) .halt = .halt := by
    rw [hP, ← hK]
    simpa using getD_app_r (comp [] 0 S ++ comp [] S.size T) [.halt] 0
  have hw : Win (compile (.seq S T)) (compile (protC h S T)) sol env 0 (S.size + T.size) 2 true false := by
    have hmem : ∀ a, a < S.size + T.size → ((compile (.seq S T)).getD a .halt ∈ comp [] 0 S ++ comp [] S.size T) := by
      intro a ha
      rw [hP, getD_app_l (l := comp [] 0 S ++ comp [] S.size T) (by rw [hK]; omega)]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hK]; omega)]
      exact List.getElem_mem _
    have hinv : ∀ i ∈ comp [] 0 S ++ comp [] S.size T, i ≠ .halt ∧ ∀ k t, i = .jmpIf k t → PureC sol env k := by
      intro i hi
      rcases List.mem_append.1 hi with hi | hi
      · exact comp_inv S hS hpS 0 i hi
      · exact comp_inv T hT hpT _ i hi
    refine ⟨fun a _ ha => ?_, fun a t _ ha ht => ?_, fun a k t _ ha hk => ?_, fun a _ ha => ?_⟩
    · have hlt : a < ((comp [] 0 S ++ comp [] S.size T).map (shiftI 2)).length := by rw [hKm]; omega
      rw [hQ, show a + 2 = (a + 1) + 1 by omega, List.getD_cons_succ, List.getD_cons_succ,
        getD_app_l hlt, getD_map_shift, hP, getD_app_l (l := comp [] 0 S ++ comp [] S.size T) (by rw [hK]; omega)]
    · have := tgt_le hst ht
      simpa [Stmt.size] using this
    · obtain ⟨b, hb⟩ := (hinv _ (hmem a (by omega))).2 k t hk
      exact ⟨b, hb true, hb false⟩
    · exact (hinv _ (hmem a (by omega))).1
  have hexitF : ∀ tr r, Halts (compile (.seq S T)) sol env (0 + (S.size + T.size)) true tr r →
      Halts (compile (protC h S T)) sol env (0 + (S.size + T.size) + 2) false tr r := by
    intro tr r' hr
    rw [Nat.zero_add] at hr ⊢
    have := hr.inv_halt hPh
    subst this
    refine .jmp hQj (.jmpIf hQ1 ?_)
    simp only [Cond.eval, Bool.not_false, ↓reduceIte, Bool.not_true]
    exact .halt (by rw [show 1 + 2 + (S.size + T.size) = S.size + T.size + 3 by omega]; exact hQh)
  have hexitB : ∀ tr r, Halts (compile (protC h S T)) sol env (0 + (S.size + T.size) + 2) false tr r →
      Halts (compile (.seq S T)) sol env (0 + (S.size + T.size)) true tr r := by
    intro tr r' hr
    rw [Nat.zero_add] at hr ⊢
    have h1 := hr.inv_jmp hQj
    have h2 := h1.inv_jmpIf hQ1
    simp only [Cond.eval, Bool.not_false, ↓reduceIte, Bool.not_true] at h2
    have := h2.inv_halt (by rw [show 1 + 2 + (S.size + T.size) = S.size + T.size + 3 by omega]; exact hQh)
    subst this
    exact .halt hPh
  rw [← halts_iff_exec, ← halts_iff_exec]
  constructor
  · intro hp
    have := hw.fwd hexitF hp (by omega) (by omega) rfl
    refine .jmpIf hQ0 ?_
    rw [hh]
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine .jmpIf hQ1 ?_
    simp only [Cond.eval, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    simpa using this
  · intro hq
    have h1 := hq.inv_jmpIf hQ0
    rw [hh] at h1
    simp only [Bool.false_eq_true, ↓reduceIte] at h1
    have h2 := h1.inv_jmpIf hQ1
    simp only [Cond.eval, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h2
    exact hw.bwd hexitB h2 0 rfl (by omega) (by omega) rfl


/-! ### Irreducibility

The code of `protC` is an entry jump followed by the code of a loop statement; the entry jump lands in the middle of the
loop body, so the loop has two entries. -/

theorem tail_fwd {W : Stmt} (hW : Structured W) {Q : List Instr} {c0 : Cond} {L : Nat}
    (hcode : Q = .jmpIf c0 L :: (comp [] 1 W ++ [.halt])) :
    Q.length = W.size + 2 ∧ (∀ a c, SStep W 1 a c → StepI Q a c) ∧ (∀ x, x < Q.length → Fwd (StepI Q) 0 x) := by
  have hlen : Q.length = W.size + 2 := by rw [hcode]; simp [comp_length]
  have hQ0 : Q.getD 0 .halt = .jmpIf c0 L := by rw [hcode]; rfl
  have hat : AtAddr Q 1 (comp [] 1 W) := by
    have : AtAddr Q 1 (comp [] 1 W ++ [.halt]) := by
      intro j _
      rw [hcode, Nat.add_comm 1 j, List.getD_cons_succ]
    exact this.append_left
  have hsteps : ∀ a c, SStep W 1 a c → StepI Q a c := by
    intro a c hs
    have hr := hs.range
    exact (SStep_iff [] Q _ 1 hW hat a c (by omega) (by omega)).2 hs
  have hStep0 : StepI Q 0 1 := by unfold StepI; rw [hQ0]; exact Or.inr rfl
  refine ⟨hlen, hsteps, fun x hx => ?_⟩
  by_cases h0 : x = 0
  · subst h0; exact .refl _
  · exact .step hStep0 (by omega)
      ((sstep_fwd W hW 1 x (by omega) (by omega)).mono hsteps)

theorem compile_protC' {S T : Stmt} (hS : Structured S) (hT : Structured T) (h : Cond) :
    compile (protC h S T) = .jmpIf h (2 + S.size) :: (comp [] 1 (.while .ttf (.seq S T)) ++ [.halt]) := by
  have hsh1 : comp [] 2 S = (comp [] 0 S).map (shiftI 2) := comp_shift [] 2 S hS 0
  have hsh2 : comp [] (2 + S.size) T = (comp [] S.size T).map (shiftI 2) := by
    rw [Nat.add_comm]; exact comp_shift [] 2 T hT S.size
  rw [compile_protC hS hT]
  simp only [comp, Stmt.size, List.cons_append, List.append_assoc, List.nil_append, hsh1, hsh2, List.map_append]

theorem protC_isCFG {S T : Stmt} (hS : Structured S) (hT : Structured T) (h : Cond) :
    (cfgOf (compile (protC h S T))).IsCFG 0 := by
  obtain ⟨hlen, _, hfwd0⟩ := tail_fwd (W := .while .ttf (.seq S T)) (show Structured (.while .ttf (.seq S T)) from ⟨hS, hT⟩) (compile_protC' hS hT h)
  have hroot := fwd_root _ hfwd0
  have hn : 0 < (cfgOf (compile (protC h S T))).n := by
    show 0 < (leaders (compile (protC h S T))).length
    have := blockOf_lt (compile (protC h S T)) (x := 0) (by omega)
    omega
  exact ⟨hn, fun v hv => (hroot v hv).reach⟩


theorem protC_not_reducible {S T : Stmt} (hS : Structured S) (hT : Structured T) (h : Cond) :
    ¬ (cfgOf (compile (protC h S T))).Reducible 0 := by
  have hW : Structured (.while .ttf (.seq S T)) := ⟨hS, hT⟩
  have hcode := compile_protC' hS hT h
  obtain ⟨hlen, hsteps, hfwd0⟩ := tail_fwd hW hcode
  have hcode2 := compile_protC hS hT h
  have hQ0 : (compile (protC h S T)).getD 0 .halt = .jmpIf h (2 + S.size) := by rw [hcode]; rfl
  have hlen' : (compile (protC h S T)).length = S.size + T.size + 4 := by
    rw [hlen]; simp [Stmt.size]; omega
  have hQc : (compile (protC h S T)).getD (S.size + T.size + 2) .halt = .jmp 1 := by
    rw [hcode2, List.getD_cons_succ, List.getD_cons_succ]
    have hK : ((comp [] 0 S ++ comp [] S.size T).map (shiftI 2)).length = S.size + T.size := by
      simp [comp_length]
    rw [← hK]
    simpa using getD_app_r ((comp [] 0 S ++ comp [] S.size T).map (shiftI 2)) [.jmp 1, .halt] 0
  have hsubT : Sub T (2 + S.size) (.while .ttf (.seq S T)) 1 := .whl (.seqR .refl)
  refine entry_cycle_not_reducible (compile (protC h S T)) (e0 := 0) (L := 2 + S.size) (c := S.size + T.size + 2)
    (h := h) (by omega) hQ0 hfwd0 (by omega) (by omega) ?_ ?_ ?_
  · exact (sstep_fwd (.while .ttf (.seq S T)) hW 1 _ (by omega) (by simp only [Stmt.size]; omega)).mono hsteps
  · exact (sstep_fwd T hT (2 + S.size) _ (by omega) (by omega)).mono (fun a c h' => hsteps a c (hsubT.sstep h'))
  · unfold StepI; rw [hQc]

/-- Every valid depth-first jungle of the Figure 5(c) form has an irreducible loop. -/
theorem protC_irreducible {S T : Stmt} (hS : Structured S) (hT : Structured T) (h : Cond)
    {J : Jungle} (hv : J.Valid (cfgOf (compile (protC h S T))) 0) :
    ∃ w, (cfgOf (compile (protC h S T))).Irreducible J w :=
  exists_irreducible_loop hv (protC_not_reducible hS hT h)

/-- Figure 5(c) for arbitrary goto-free code, as `protection5` is for 5(b). -/
theorem protection5c {S T : Stmt} (hS : Structured S) (hT : Structured T) :
    (cfgOf (compile (.seq S T))).Reducible 0 ∧
    (∀ {J : Jungle}, J.Valid (cfgOf (compile (.seq S T))) 0 → ∀ w, ¬ (cfgOf (compile (.seq S T))).Irreducible J w) ∧
    (∀ {h : Cond} {J : Jungle}, J.Valid (cfgOf (compile (protC h S T))) 0 →
      ∃ w, (cfgOf (compile (protC h S T))).Irreducible J w) ∧
    (∀ h : Cond, ∃ J : Jungle, J.Valid (cfgOf (compile (protC h S T))) 0) ∧
    (∀ {sol : Nat → Bool} {env : Bool}, PureS sol env S → PureS sol env T → ∀ {h : Cond},
      h.eval sol env true = (false, true) → ∀ r : List Nat × Bool,
      ((∃ f, exec f (compile (.seq S T)) sol env 0 true [] = some r) ↔
        ∃ f, exec f (compile (protC h S T)) sol env 0 true [] = some r)) := by
  have hred := structured_reducible (show Structured (.seq S T) from ⟨hS, hT⟩)
  refine ⟨hred, fun hv w => reducible_no_irreducible hv hred w, fun hv => protC_irreducible hS hT _ hv,
    fun h => ⟨_, dfsRun_valid (protC_isCFG hS hT h) (Nat.le_refl 1)⟩,
    fun {sol env} hpS hpT {h} hh r => protC_equiv hS hT hpS hpT hh r⟩


/-! ### Figure 6(c) -/

theorem shiftI_shiftI (a b : Nat) (i : Instr) : shiftI a (shiftI b i) = shiftI (b + a) i := by
  cases i <;> simp [shiftI, Nat.add_assoc]

theorem target_shiftI (a : Nat) (i : Instr) : (shiftI a i).target = i.target.map (· + a) := by
  cases i <;> simp [shiftI, Instr.target]

/-- A window given by a code piece `cs` placed (shifted by its address) at `a0` in `P` and at `a0 + d` in `Q`. -/
theorem win_of_code {P Q cs : List Instr} {sol : Nat → Bool} {env : Bool} {a0 d len : Nat} {v0 v1 : Bool}
    (hlen : cs.length = len)
    (hP : ∀ j, j < len → P.getD (a0 + j) .halt = shiftI a0 (cs.getD j .halt))
    (hQ : ∀ j, j < len → Q.getD (a0 + d + j) .halt = shiftI (a0 + d) (cs.getD j .halt))
    (htg : ∀ j t, j < len → (cs.getD j .halt).target = some t → t ≤ len)
    (hinv : ∀ i ∈ cs, i ≠ .halt ∧ ∀ k t, i = .jmpIf k t → PureC sol env k) :
    Win P Q sol env a0 len d v0 v1 := by
  have hmem : ∀ j, j < len → cs.getD j .halt ∈ cs := by
    intro j hj
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    exact List.getElem_mem _
  refine ⟨fun a h1 h2 => ?_, fun a t h1 h2 ht => ?_, fun a k t h1 h2 hk => ?_, fun a h1 h2 => ?_⟩
  · obtain ⟨j, rfl⟩ : ∃ j, a = a0 + j := ⟨a - a0, by omega⟩
    rw [show a0 + j + d = a0 + d + j by omega, hQ j (by omega), hP j (by omega), shiftI_shiftI]
  · obtain ⟨j, rfl⟩ : ∃ j, a = a0 + j := ⟨a - a0, by omega⟩
    rw [hP j (by omega), target_shiftI] at ht
    cases hc : (cs.getD j .halt).target with
    | none => rw [hc] at ht; simp at ht
    | some t0 =>
      rw [hc] at ht
      simp at ht
      have := htg j t0 (by omega) hc
      omega
  · obtain ⟨j, rfl⟩ : ∃ j, a = a0 + j := ⟨a - a0, by omega⟩
    rw [hP j (by omega)] at hk
    cases hc : cs.getD j .halt <;> rw [hc] at hk <;> simp [shiftI] at hk
    rename_i k0 t0
    obtain ⟨hk1, _⟩ := hk
    subst hk1
    obtain ⟨b, hb⟩ := (hinv _ (hmem j (by omega))).2 k0 t0 hc
    exact ⟨b, hb v0, hb v1⟩
  · obtain ⟨j, rfl⟩ : ∃ j, a = a0 + j := ⟨a - a0, by omega⟩
    rw [hP j (by omega)]
    intro h
    have := (hinv _ (hmem j (by omega))).1
    cases hc : cs.getD j .halt <;> rw [hc] at h this <;> simp [shiftI] at h this


theorem compile_protC6 {S T : Stmt} (hS : Structured S) (hT : Structured T) (cd h : Cond) :
    compile (protC6 cd h S T) = .jmpIf h 2 :: .jmpIf (.neg (.and cd .ttf)) (3 + S.size) ::
      ((comp [] 0 S).map (shiftI 2) ++ (.jmp 1 :: ((comp [] 0 T).map (shiftI (3 + S.size)) ++ [.halt]))) := by
  have hl : labelsOf 0 (protC6 cd h S T) = [(8, 2)] := by
    simp [protC6, labelsOf, Stmt.size, labelsOf_structured S hS, labelsOf_structured T hT]
  have hsh1 : comp [] 2 S = (comp [] 0 S).map (shiftI 2) := comp_shift [] 2 S hS 0
  have hsh2 : comp [] (3 + S.size) T = (comp [] 0 T).map (shiftI (3 + S.size)) := by
    have := comp_shift [] (3 + S.size) T hT 0; rwa [Nat.zero_add] at this
  unfold compile
  rw [hl]
  simp only [protC6, comp, Stmt.size, lookupLabel, List.find?_cons, List.find?_nil]
  rw [comp_labs _ [] S hS, comp_labs _ [] T hT]
  rw [show 1 + (2 + S.size) = 3 + S.size by omega, hsh2]
  simp [hsh1]

theorem compile_ite1_seq {S T : Stmt} (hS : Structured S) (hT : Structured T) (cd : Cond) :
    compile (.seq (.ite1 cd S) T) = .jmpIf (.neg cd) (1 + S.size) ::
      ((comp [] 0 S).map (shiftI 1) ++ ((comp [] 0 T).map (shiftI (1 + S.size)) ++ [.halt])) := by
  have hst : Structured (.seq (.ite1 cd S) T) := ⟨hS, hT⟩
  have hsh1 : comp [] 1 S = (comp [] 0 S).map (shiftI 1) := comp_shift [] 1 S hS 0
  have hsh2 : comp [] (1 + S.size) T = (comp [] 0 T).map (shiftI (1 + S.size)) := by
    have := comp_shift [] (1 + S.size) T hT 0; rwa [Nat.zero_add] at this
  rw [compile_structured hst]
  simp only [comp, Stmt.size, List.cons_append, List.append_assoc, Nat.zero_add]
  rw [hsh1, hsh2]


/-- Figure 6(c) for arbitrary code: `if (cd) S; T` against `if (h) goto labelS; while (cd && trueThenFalse) { labelS: S; } T;`
with the toggled variable true at entry, the entry condition false and `cd` and the conditions of `S`, `T` not reading the
toggled variable. -/
theorem protC6_equiv {S T : Stmt} (hS : Structured S) (hT : Structured T) {sol : Nat → Bool} {env : Bool}
    (hpS : PureS sol env S) (hpT : PureS sol env T) {cd : Cond} (hcd : PureC sol env cd) {h : Cond}
    (hh : h.eval sol env true = (false, true)) (r : List Nat × Bool) :
    (∃ f, exec f (compile (.seq (.ite1 cd S) T)) sol env 0 true [] = some r) ↔
      ∃ f, exec f (compile (protC6 cd h S T)) sol env 0 true [] = some r := by
  obtain ⟨b, hb⟩ := hcd
  have hP := compile_ite1_seq hS hT cd
  have hQ := compile_protC6 hS hT cd h
  generalize compile (.seq (.ite1 cd S) T) = P at hP ⊢
  generalize compile (protC6 cd h S T) = Q at hQ ⊢
  have hlS : ((comp [] 0 S).map (shiftI 2)).length = S.size := by simp [comp_length]
  have hlS1 : ((comp [] 0 S).map (shiftI 1)).length = S.size := by simp [comp_length]
  have hlT : ((comp [] 0 T).map (shiftI (3 + S.size))).length = T.size := by simp [comp_length]
  have hlT1 : ((comp [] 0 T).map (shiftI (1 + S.size))).length = T.size := by simp [comp_length]
  have hP0 : P.getD 0 .halt = .jmpIf (.neg cd) (1 + S.size) := by rw [hP]; rfl
  have hQ0 : Q.getD 0 .halt = .jmpIf h 2 := by rw [hQ]; rfl
  have hQ1 : Q.getD 1 .halt = .jmpIf (.neg (.and cd .ttf)) (3 + S.size) := by rw [hQ]; rfl
  have hQj : Q.getD (S.size + 2) .halt = .jmp 1 := by
    rw [hQ, List.getD_cons_succ, List.getD_cons_succ, ← hlS]
    simpa using getD_app_r ((comp [] 0 S).map (shiftI 2)) (.jmp 1 :: ((comp [] 0 T).map (shiftI (3 + S.size)) ++ [.halt])) 0
  have hPh : P.getD (1 + S.size + T.size) .halt = .halt := by
    rw [hP, show 1 + S.size + T.size = (S.size + T.size) + 1 by omega, List.getD_cons_succ]
    have := getD_app_r ((comp [] 0 S).map (shiftI 1))
      ((comp [] 0 T).map (shiftI (1 + S.size)) ++ [.halt]) (T.size)
    rw [hlS1] at this
    rw [show S.size + T.size = S.size + T.size by rfl, this]
    have := getD_app_r ((comp [] 0 T).map (shiftI (1 + S.size))) [.halt] 0
    rw [hlT1] at this
    simpa using this
  have hQh : Q.getD (3 + S.size + T.size) .halt = .halt := by
    rw [hQ, show 3 + S.size + T.size = (S.size + (T.size + 1)) + 1 + 1 by omega, List.getD_cons_succ, List.getD_cons_succ]
    have := getD_app_r ((comp [] 0 S).map (shiftI 2))
      (.jmp 1 :: ((comp [] 0 T).map (shiftI (3 + S.size)) ++ [.halt])) (T.size + 1)
    rw [hlS] at this
    rw [this, List.getD_cons_succ]
    have := getD_app_r ((comp [] 0 T).map (shiftI (3 + S.size))) [.halt] 0
    rw [hlT] at this
    simpa using this
  have hinvS := comp_inv (sol := sol) (env := env) S hS hpS 0
  have hinvT := comp_inv (sol := sol) (env := env) T hT hpT 0
  have tgtc : ∀ {s : Stmt}, Structured s → ∀ j t, j < s.size → ((comp [] 0 s).getD j .halt).target = some t →
      t ≤ s.size := by
    intro s hs j t hj ht
    apply tgt_le hs (a := j)
    rw [compile_structured hs, getD_app_l (by rw [comp_length]; exact hj)]
    exact ht
  have hwS : Win P Q sol env 1 S.size 1 true false := by
    refine win_of_code (cs := comp [] 0 S) (comp_length _ _ _) (fun j hj => ?_) (fun j hj => ?_)
      (fun j t hj ht => tgtc hS j t hj ht) hinvS
    · rw [hP, show 1 + j = j + 1 by omega, List.getD_cons_succ, getD_app_l (by rw [hlS1]; exact hj), getD_map_shift]
    · rw [hQ, show 1 + 1 + j = j + 1 + 1 by omega, List.getD_cons_succ, List.getD_cons_succ,
        getD_app_l (by rw [hlS]; exact hj), getD_map_shift]
  have hwT : Win P Q sol env (1 + S.size) T.size 2 true true := by
    refine win_of_code (cs := comp [] 0 T) (comp_length _ _ _) (fun j hj => ?_) (fun j hj => ?_)
      (fun j t hj ht => tgtc hT j t hj ht) hinvT
    · rw [hP, show 1 + S.size + j = (S.size + j) + 1 by omega, List.getD_cons_succ]
      rw [show S.size + j = ((comp [] 0 S).map (shiftI 1)).length + j by rw [hlS1]]
      rw [getD_app_r, getD_app_l (by rw [hlT1]; exact hj), getD_map_shift]
    · rw [hQ, show 1 + S.size + 2 + j = (S.size + (j + 1)) + 1 + 1 by omega, List.getD_cons_succ, List.getD_cons_succ]
      rw [show S.size + (j + 1) = ((comp [] 0 S).map (shiftI 2)).length + (j + 1) by rw [hlS]]
      rw [getD_app_r, List.getD_cons_succ, getD_app_l (by rw [hlT]; exact hj), getD_map_shift,
        show 1 + S.size + 2 = 3 + S.size by omega]
  have e1 : 1 + S.size + 2 = 3 + S.size := by omega
  have e2 : 1 + S.size + T.size + 2 = 3 + S.size + T.size := by omega
  have hexitTF : ∀ tr r, Halts P sol env (1 + S.size + T.size) true tr r →
      Halts Q sol env (1 + S.size + T.size + 2) true tr r := by
    intro tr r' hr
    have := hr.inv_halt hPh
    subst this
    exact .halt (by rw [e2]; exact hQh)
  have hexitTB : ∀ tr r, Halts Q sol env (1 + S.size + T.size + 2) true tr r →
      Halts P sol env (1 + S.size + T.size) true tr r := by
    intro tr r' hr
    have := hr.inv_halt (by rw [e2]; exact hQh)
    subst this
    exact .halt hPh
  have hQj' : Q.getD (1 + S.size + 1) .halt = .jmp 1 := by
    rw [show 1 + S.size + 1 = S.size + 2 by omega]; exact hQj
  have hentry : ∀ {pc v tr r'}, Halts Q sol env 0 true tr r' → pc = 0 → v = true →
      Halts Q sol env (if (Cond.eval sol env (.neg (.and cd .ttf)) true).1 then 3 + S.size else 2)
        (Cond.eval sol env (.neg (.and cd .ttf)) true).2 tr r' := by
    intro pc v tr r' hq _ _
    have h1 := hq.inv_jmpIf hQ0
    rw [hh] at h1
    simpa using h1.inv_jmpIf hQ1
  rw [← halts_iff_exec, ← halts_iff_exec]
  cases hbv : b
  · -- cd false: S is skipped
    have hev : Cond.eval sol env (.neg (.and cd .ttf)) true = (true, true) := by simp [Cond.eval, hb, hbv]
    constructor
    · intro hp
      have h1 := hp.inv_jmpIf hP0
      simp only [Cond.eval, hb, hbv, Bool.not_false, ↓reduceIte] at h1
      have h2 := hwT.fwd hexitTF h1 (by omega) (by omega) rfl
      rw [e1] at h2
      refine .jmpIf hQ0 ?_
      rw [hh]
      simp only [Bool.false_eq_true, ↓reduceIte]
      refine .jmpIf hQ1 ?_
      rw [hev]
      simpa using h2
    · intro hq
      have h1 := hentry hq rfl rfl
      rw [hev] at h1
      simp only [↓reduceIte] at h1
      have h2 := hwT.bwd hexitTB h1 (1 + S.size) (by omega) (by omega) (by omega) rfl
      refine .jmpIf hP0 ?_
      simpa [Cond.eval, hb, hbv] using h2
  · -- cd true: S runs once with the toggled variable false
    have hev : Cond.eval sol env (.neg (.and cd .ttf)) true = (false, false) := by simp [Cond.eval, hb, hbv]
    have hexitSF : ∀ tr r, Halts P sol env (1 + S.size) true tr r → Halts Q sol env (1 + S.size + 1) false tr r := by
      intro tr r' hr
      refine .jmp hQj' (.jmpIf hQ1 ?_)
      simp only [Cond.eval, hb, hbv, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.not_true]
      have := hwT.fwd hexitTF hr (by omega) (by omega) rfl
      rw [e1] at this
      simpa using this
    have hexitSB : ∀ tr r, Halts Q sol env (1 + S.size + 1) false tr r → Halts P sol env (1 + S.size) true tr r := by
      intro tr r' hr
      have h1 := (hr.inv_jmp hQj').inv_jmpIf hQ1
      simp only [Cond.eval, hb, hbv, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.not_true] at h1
      exact hwT.bwd hexitTB h1 (1 + S.size) (by omega) (by omega) (by omega) rfl
    constructor
    · intro hp
      have h1 := hp.inv_jmpIf hP0
      simp only [Cond.eval, hb, hbv, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h1
      have h2 := hwS.fwd hexitSF h1 (by omega) (by omega) rfl
      refine .jmpIf hQ0 ?_
      rw [hh]
      simp only [Bool.false_eq_true, ↓reduceIte]
      refine .jmpIf hQ1 ?_
      rw [hev]
      simpa using h2
    · intro hq
      have h1 := hentry hq rfl rfl
      rw [hev] at h1
      simp only [Bool.false_eq_true, ↓reduceIte] at h1
      have h2 := hwS.bwd hexitSB h1 1 rfl (by omega) (by omega) rfl
      refine .jmpIf hP0 ?_
      simpa [Cond.eval, hb, hbv] using h2


theorem compile_protC6' {S T : Stmt} (hS : Structured S) (hT : Structured T) (cd h : Cond) :
    compile (protC6 cd h S T) =
      .jmpIf h 2 :: (comp [] 1 (.seq (.while (.and cd .ttf) S) T) ++ [.halt]) := by
  have hsh1 : comp [] 2 S = (comp [] 0 S).map (shiftI 2) := comp_shift [] 2 S hS 0
  have hsh2 : comp [] (3 + S.size) T = (comp [] 0 T).map (shiftI (3 + S.size)) := by
    have := comp_shift [] (3 + S.size) T hT 0; rwa [Nat.zero_add] at this
  rw [compile_protC6 hS hT]
  simp only [comp, Stmt.size, List.cons_append, List.append_assoc, List.nil_append]
  rw [show 1 + (2 + S.size) = 3 + S.size by omega, hsh1, hsh2]

theorem protC6_isCFG {S T : Stmt} (hS : Structured S) (hT : Structured T) (cd h : Cond) :
    (cfgOf (compile (protC6 cd h S T))).IsCFG 0 := by
  obtain ⟨hlen, _, hfwd0⟩ := tail_fwd (W := .seq (.while (.and cd .ttf) S) T) ⟨hS, hT⟩ (compile_protC6' hS hT cd h)
  have hroot := fwd_root _ hfwd0
  have hn : 0 < (cfgOf (compile (protC6 cd h S T))).n := by
    show 0 < (leaders (compile (protC6 cd h S T))).length
    have := blockOf_lt (compile (protC6 cd h S T)) (x := 0) (by omega)
    omega
  exact ⟨hn, fun v hv => (hroot v hv).reach⟩

theorem protC6_not_reducible {S T : Stmt} (hS : Structured S) (hT : Structured T) (cd h : Cond) :
    ¬ (cfgOf (compile (protC6 cd h S T))).Reducible 0 := by
  have hW : Structured (.seq (.while (.and cd .ttf) S) T) := ⟨hS, hT⟩
  have hcode := compile_protC6' hS hT cd h
  obtain ⟨hlen, hsteps, hfwd0⟩ := tail_fwd hW hcode
  have hcode2 := compile_protC6 hS hT cd h
  have hQ0 : (compile (protC6 cd h S T)).getD 0 .halt = .jmpIf h 2 := by rw [hcode]; rfl
  have hlen' : (compile (protC6 cd h S T)).length = S.size + T.size + 4 := by
    rw [hlen]; simp [Stmt.size]; omega
  have hQc : (compile (protC6 cd h S T)).getD (S.size + 2) .halt = .jmp 1 := by
    rw [hcode2, List.getD_cons_succ, List.getD_cons_succ]
    have hK : ((comp [] 0 S).map (shiftI 2)).length = S.size := by simp [comp_length]
    rw [← hK]
    simpa using getD_app_r ((comp [] 0 S).map (shiftI 2))
      (.jmp 1 :: ((comp [] 0 T).map (shiftI (3 + S.size)) ++ [.halt])) 0
  have hsubS : Sub S 2 (.seq (.while (.and cd .ttf) S) T) 1 := .seqL (.whl .refl)
  refine entry_cycle_not_reducible (compile (protC6 cd h S T)) (e0 := 0) (L := 2) (c := S.size + 2)
    (h := h) (by omega) hQ0 hfwd0 (by omega) (by omega) ?_ ?_ ?_
  · exact (sstep_fwd _ hW 1 _ (by omega) (by simp only [Stmt.size]; omega)).mono hsteps
  · exact (sstep_fwd S hS 2 _ (by omega) (by omega)).mono (fun a c h' => hsteps a c (hsubS.sstep h'))
  · unfold StepI; rw [hQc]

theorem protC6_irreducible {S T : Stmt} (hS : Structured S) (hT : Structured T) (cd h : Cond)
    {J : Jungle} (hv : J.Valid (cfgOf (compile (protC6 cd h S T))) 0) :
    ∃ w, (cfgOf (compile (protC6 cd h S T))).Irreducible J w :=
  exists_irreducible_loop hv (protC6_not_reducible hS hT cd h)

/-- Figure 6(c) for arbitrary goto-free code. -/
theorem protection6c {S T : Stmt} (hS : Structured S) (hT : Structured T) (cd : Cond) :
    (cfgOf (compile (.seq (.ite1 cd S) T))).Reducible 0 ∧
    (∀ {J : Jungle}, J.Valid (cfgOf (compile (.seq (.ite1 cd S) T))) 0 →
      ∀ w, ¬ (cfgOf (compile (.seq (.ite1 cd S) T))).Irreducible J w) ∧
    (∀ {h : Cond} {J : Jungle}, J.Valid (cfgOf (compile (protC6 cd h S T))) 0 →
      ∃ w, (cfgOf (compile (protC6 cd h S T))).Irreducible J w) ∧
    (∀ h : Cond, ∃ J : Jungle, J.Valid (cfgOf (compile (protC6 cd h S T))) 0) ∧
    (∀ {sol : Nat → Bool} {env : Bool}, PureS sol env S → PureS sol env T → PureC sol env cd → ∀ {h : Cond},
      h.eval sol env true = (false, true) → ∀ r : List Nat × Bool,
      ((∃ f, exec f (compile (.seq (.ite1 cd S) T)) sol env 0 true [] = some r) ↔
        ∃ f, exec f (compile (protC6 cd h S T)) sol env 0 true [] = some r)) := by
  have hred := structured_reducible (show Structured (.seq (.ite1 cd S) T) from ⟨hS, hT⟩)
  refine ⟨hred, fun hv w => reducible_no_irreducible hv hred w, fun hv => protC6_irreducible hS hT _ _ hv,
    fun h => ⟨_, dfsRun_valid (protC6_isCFG hS hT cd h) (Nat.le_refl 1)⟩,
    fun {sol env} hpS hpT hcd {h} hh r => protC6_equiv hS hT hpS hpT hcd hh r⟩

end SmcIrred.Lang
