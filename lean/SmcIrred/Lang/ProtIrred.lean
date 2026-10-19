module

public import SmcIrred.Lang.Protect
public import SmcIrred.Lang.NonRed

public section

namespace SmcIrred.Lang

/-! # The protected forms of arbitrary code have an irreducible loop (G33 b, C65)

For goto-free `S` (with at least one instruction) and `T` the block graph of `prot h S T k` is not reducible: the forward
path through `S; T` closed by the back edge of the `do ... while` is a cycle of non-dominating edges, because the entry jump
reaches `T` without passing the first block of `S`. Hence every valid depth-first jungle has an irreducible loop
(`exists_irreducible_loop`). -/

theorem blockSucc_jmpIf (code : List Instr) {B : Nat} {c : Cond} {t : Nat}
    (h : code.getD (blockEnd code B) .halt = .jmpIf c t) :
    blockSucc code B = [blockOf code t, blockOf code (blockEnd code B + 1)] := by
  unfold blockSucc
  simp only [h]

theorem blockOf_zero (code : List Instr) (hp : 0 < code.length) : blockOf code 0 = 0 := by
  rw [blockOf_eq code hp, pos_one]

theorem fwd_root (code : List Instr) (h : ∀ x, x < code.length → Fwd (StepI code) 0 x) :
    ∀ v, v < (cfgOf code).n → BFwd (cfgOf code) 0 v := by
  intro v hv
  have hv' : v < (leaders code).length := hv
  have hspec := fl_getD_spec (ldr code) code.length v hv'
  rw [leaders_eq] at hv'
  obtain ⟨h1, h2, h3⟩ := hspec
  have := fwd_blocks code h2 (h _ h2)
  rw [blockOf_lead code h2 h1, h3, blockOf_zero code (by omega)] at this
  exact this

theorem prot_not_reducible {S T : Stmt} (hS : Structured S) (hT : Structured T) (hS1 : 1 ≤ S.size) (h k : Cond) :
    ¬ (cfgOf (compile (prot h S T k))).Reducible 0 := by
  have hW : Structured (.doWhile (.seq S T) k) := ⟨hS, hT⟩
  have hcode : compile (prot h S T k) =
      (.jmpIf h (1 + S.size) :: (comp [] 1 S ++ comp [] (1 + S.size) T)) ++ [.jmpIf k 1, .halt] := by
    rw [compile_prot hS hT]; simp only [List.cons_append, List.append_assoc]
  have hcode' : compile (prot h S T k) =
      .jmpIf h (1 + S.size) :: (comp [] 1 (.doWhile (.seq S T) k) ++ [.halt]) := by
    rw [hcode]; simp only [comp, List.cons_append, List.append_assoc, List.nil_append]
  generalize hQ : compile (prot h S T k) = Q at hcode hcode'
  have hlenA : (comp [] 1 S).length = S.size := comp_length _ _ _
  have hlenB : (comp [] (1 + S.size) T).length = T.size := comp_length _ _ _
  have hX : (Instr.jmpIf h (1 + S.size) :: (comp [] 1 S ++ comp [] (1 + S.size) T)).length = S.size + T.size + 1 := by
    simp only [List.length_cons, List.length_append, hlenA, hlenB]
  have hn : Q.length = S.size + T.size + 3 := by rw [hcode, List.length_append, hX]; rfl
  have hQ0 : Q.getD 0 .halt = .jmpIf h (1 + S.size) := by rw [hcode', ]; rfl
  have hQc : Q.getD (S.size + T.size + 1) .halt = .jmpIf k 1 := by
    rw [hcode, ← hX]; simpa using getD_app_r (Instr.jmpIf h (1 + S.size) :: (comp [] 1 S ++ comp [] (1 + S.size) T))
      [.jmpIf k 1, .halt] 0
  have hat : AtAddr Q 1 (comp [] 1 (.doWhile (.seq S T) k)) := by
    have : AtAddr Q 1 (comp [] 1 (.doWhile (.seq S T) k) ++ [.halt]) := by
      intro j _
      rw [hcode', Nat.add_comm 1 j, List.getD_cons_succ]
    exact this.append_left
  have hsteps : ∀ a c, SStep (.doWhile (.seq S T) k) 1 a c → StepI Q a c := by
    intro a c hs
    have hr := hs.range
    simp only [Stmt.size] at hr
    exact (SStep_iff [] Q _ 1 hW hat a c (by omega) (by simp only [Stmt.size]; omega)).2 hs
  have hStep0 : StepI Q 0 1 := by unfold StepI; rw [hQ0]; exact Or.inr rfl
  have hfwdW : ∀ x, 1 ≤ x → x ≤ S.size + T.size + 2 → Fwd (StepI Q) 1 x := fun x h1 h2 =>
    (sstep_fwd (.doWhile (.seq S T) k) hW 1 x h1 (by simp only [Stmt.size]; omega)).mono hsteps
  have hfwd0 : ∀ x, x < Q.length → Fwd (StepI Q) 0 x := by
    intro x hx
    by_cases h0 : x = 0
    · subst h0; exact .refl _
    · exact .step hStep0 (by omega) (hfwdW x (by omega) (by omega))
  have hroot := fwd_root Q hfwd0
  have hl1 : ldr Q 1 = true := ldr_next Q (e := 0) (by omega) (by rw [hQ0]; rfl)
  have hlL : ldr Q (1 + S.size) = true := ldr_target Q (e := 0) (by omega) (by rw [hQ0]; rfl)
  have hlc : ldr Q (S.size + T.size + 2) = true := ldr_next Q (e := S.size + T.size + 1) (by omega) (by rw [hQc]; rfl)
  have hz := blockOf_zero Q (by omega)
  have hlt1 : blockOf Q 1 < blockOf Q (1 + S.size) := blockOf_strict Q (by omega) (by omega) hlL
  have hlt0 : blockOf Q 0 < blockOf Q 1 := blockOf_strict Q (by omega) (by omega) hl1
  have hmc : blockOf Q (1 + S.size) ≤ blockOf Q (S.size + T.size + 1) := blockOf_mono Q (by omega) (by omega)
  have hf1 : BFwd (cfgOf Q) (blockOf Q 1) (blockOf Q (S.size + T.size + 1)) :=
    fwd_blocks Q (by omega) (hfwdW _ (by omega) (by omega))
  have hsubT : Sub T (1 + S.size) (.doWhile (.seq S T) k) 1 := .dow (.seqR .refl)
  have hfL : BFwd (cfgOf Q) (blockOf Q (1 + S.size)) (blockOf Q (S.size + T.size + 1)) := by
    apply fwd_blocks Q (by omega)
    exact (sstep_fwd T hT (1 + S.size) (S.size + T.size + 1) (by omega) (by omega)).mono
      (fun a c h => hsteps a c (hsubT.sstep h))
  have hnd := BFwd.nondom hroot hf1 (by omega)
  have hcB : blockOf Q (S.size + T.size + 1) < (cfgOf Q).n := blockOf_lt Q (by omega)
  have heb : (cfgOf Q).edge (blockOf Q (S.size + T.size + 1)) (blockOf Q 1) := by
    refine ⟨hcB, blockOf_lt Q (by omega), ?_⟩
    show blockOf Q 1 ∈ blockSucc Q (blockOf Q (S.size + T.size + 1))
    have hend := end_of_block Q (e := S.size + T.size + 1) (by omega) hlc
    rw [blockSucc_jmpIf Q (by rw [hend]; exact hQc), hend]
    simp
  have he0 : (cfgOf Q).edge 0 (blockOf Q (1 + S.size)) := by
    refine ⟨show 0 < (leaders Q).length from hz ▸ blockOf_lt Q (by omega), blockOf_lt Q (by omega), ?_⟩
    show blockOf Q (1 + S.size) ∈ blockSucc Q 0
    have hend := end_of_block Q (e := 0) (by omega) hl1
    rw [hz] at hend
    rw [blockSucc_jmpIf Q (by rw [hend]; exact hQ0), hend]
    simp
  have hnotdom : ¬ (cfgOf Q).Dom 0 (blockOf Q 1) (blockOf Q (S.size + T.size + 1)) := by
    intro hd
    apply hd.2
    refine .step (a := 0) (by omega) he0 ?_
    have h0 := hfL.path
    exact h0.mono (fun z hz' => by omega)
  have hPc : PathIn (cfgOf Q) (fun _ => True) 0 (blockOf Q (S.size + T.size + 1)) :=
    (hroot _ hcB).path.mono (fun _ _ => trivial)
  intro hred
  exact hred (blockOf Q 1) (hnd.snoc heb hPc hnotdom)

/-- Every valid depth-first jungle of the protected form has an irreducible loop. -/
theorem prot_irreducible {S T : Stmt} (hS : Structured S) (hT : Structured T) (hS1 : 1 ≤ S.size) (h k : Cond)
    {J : Jungle} (hv : J.Valid (cfgOf (compile (prot h S T k))) 0) :
    ∃ w, (cfgOf (compile (prot h S T k))).Irreducible J w :=
  exists_irreducible_loop hv (prot_not_reducible hS hT hS1 h k)

theorem BFwd.reach {g : Digraph} {a b : Nat} (h : BFwd g a b) : g.Reach a b := by
  induction h with
  | refl _ => exact .refl _
  | step he _ _ ih => exact .step he ih

/-- Every block of the protected form is reached from the entry block. -/
theorem prot_isCFG {S T : Stmt} (hS : Structured S) (hT : Structured T) (h k : Cond) :
    (cfgOf (compile (prot h S T k))).IsCFG 0 := by
  have hW : Structured (.doWhile (.seq S T) k) := ⟨hS, hT⟩
  have hcode' : compile (prot h S T k) =
      .jmpIf h (1 + S.size) :: (comp [] 1 (.doWhile (.seq S T) k) ++ [.halt]) := by
    rw [compile_prot hS hT]; simp only [comp, List.cons_append, List.append_assoc, List.nil_append]
  generalize hQ : compile (prot h S T k) = Q at hcode'
  have hlen : Q.length = S.size + T.size + 3 := by
    rw [hcode']; simp [comp_length, Stmt.size]
  have hQ0 : Q.getD 0 .halt = .jmpIf h (1 + S.size) := by rw [hcode']; rfl
  have hat : AtAddr Q 1 (comp [] 1 (.doWhile (.seq S T) k)) := by
    have : AtAddr Q 1 (comp [] 1 (.doWhile (.seq S T) k) ++ [.halt]) := by
      intro j _
      rw [hcode', Nat.add_comm 1 j, List.getD_cons_succ]
    exact this.append_left
  have hsteps : ∀ a c, SStep (.doWhile (.seq S T) k) 1 a c → StepI Q a c := by
    intro a c hs
    have hr := hs.range
    simp only [Stmt.size] at hr
    exact (SStep_iff [] Q _ 1 hW hat a c (by omega) (by simp only [Stmt.size]; omega)).2 hs
  have hStep0 : StepI Q 0 1 := by unfold StepI; rw [hQ0]; exact Or.inr rfl
  have hfwd0 : ∀ x, x < Q.length → Fwd (StepI Q) 0 x := by
    intro x hx
    by_cases h0 : x = 0
    · subst h0; exact .refl _
    · exact .step hStep0 (by omega)
        ((sstep_fwd (.doWhile (.seq S T) k) hW 1 x (by omega) (by simp only [Stmt.size]; omega)).mono hsteps)
  have hroot := fwd_root Q hfwd0
  have hn : 0 < (cfgOf Q).n := by
    show 0 < (leaders Q).length
    have := blockOf_lt Q (x := 0) (by omega)
    omega
  exact ⟨hn, fun v hv => (hroot v hv).reach⟩

/-- Protection of arbitrary goto-free code by Figure 5(b): `S; T` has a reducible flow graph (so no irreducible loop in any
depth-first jungle), the protected code has an irreducible loop in every valid jungle (and valid jungles exist), and with the
two added conditions false both return the same trace and state. -/
theorem protection5 {S T : Stmt} (hS : Structured S) (hT : Structured T) (hS1 : 1 ≤ S.size) :
    (cfgOf (compile (.seq S T))).Reducible 0 ∧
    (∀ {J : Jungle}, J.Valid (cfgOf (compile (.seq S T))) 0 → ∀ w, ¬ (cfgOf (compile (.seq S T))).Irreducible J w) ∧
    (∀ {J : Jungle}, J.Valid (cfgOf (compile (prot5 S T))) 0 → ∃ w, (cfgOf (compile (prot5 S T))).Irreducible J w) ∧
    (∃ J : Jungle, J.Valid (cfgOf (compile (prot5 S T))) 0) ∧
    (∀ {sol : Nat → Bool}, sol 1 = false → sol 2 = false → ∀ (env v : Bool) (r : List Nat × Bool),
      ((∃ f, exec f (compile (.seq S T)) sol env 0 v [] = some r) ↔
        ∃ f, exec f (compile (prot5 S T)) sol env 0 v [] = some r)) := by
  have hred := structured_reducible (show Structured (.seq S T) from ⟨hS, hT⟩)
  refine ⟨hred, fun hv w => reducible_no_irreducible hv hred w, fun hv => prot_irreducible hS hT hS1 _ _ hv,
    ⟨_, dfsRun_valid (prot_isCFG hS hT (.out 1) (.out 2)) (Nat.le_refl 1)⟩, fun h1 h2 env v r => prot5_equiv hS hT h1 h2 env v r⟩

/-- The same for Figure 6(b): `if (c) S; T` against `if (!c) goto labelT; do { S; labelT: T; } while (out 1);`. -/
theorem protection6 {S T : Stmt} (hS : Structured S) (hT : Structured T) (hS1 : 1 ≤ S.size) (cd : Cond) :
    (cfgOf (compile (.seq (.ite1 cd S) T))).Reducible 0 ∧
    (∀ {J : Jungle}, J.Valid (cfgOf (compile (.seq (.ite1 cd S) T))) 0 →
      ∀ w, ¬ (cfgOf (compile (.seq (.ite1 cd S) T))).Irreducible J w) ∧
    (∀ {J : Jungle}, J.Valid (cfgOf (compile (prot6 cd S T))) 0 → ∃ w, (cfgOf (compile (prot6 cd S T))).Irreducible J w) ∧
    (∃ J : Jungle, J.Valid (cfgOf (compile (prot6 cd S T))) 0) ∧
    (∀ {sol : Nat → Bool}, sol 1 = false → ∀ (env v : Bool) (r : List Nat × Bool),
      ((∃ f, exec f (compile (.seq (.ite1 cd S) T)) sol env 0 v [] = some r) ↔
        ∃ f, exec f (compile (prot6 cd S T)) sol env 0 v [] = some r)) := by
  have hred := structured_reducible (show Structured (.seq (.ite1 cd S) T) from ⟨hS, hT⟩)
  refine ⟨hred, fun hv w => reducible_no_irreducible hv hred w, fun hv => prot_irreducible hS hT hS1 _ _ hv,
    ⟨_, dfsRun_valid (prot_isCFG hS hT (.neg cd) (.out 1)) (Nat.le_refl 1)⟩, fun h1 env v r => prot6_equiv hS hT cd h1 env v r⟩

/-- Goto-free programs (the structured statements of the language, no `goto`, `if ... goto` or label) have no irreducible loop
in any valid depth-first jungle of their block graph (C30, C32): an irreducible loop needs a `goto`. -/
theorem structured_no_irreducible {p : Stmt} (hp : Structured p) {J : Jungle} (hv : J.Valid (cfgOf (compile p)) 0) :
    ∀ w, ¬ (cfgOf (compile p)).Irreducible J w :=
  fun w => reducible_no_irreducible hv (structured_reducible hp) w

theorem irreducible_needs_goto {p : Stmt} {J : Jungle} (hv : J.Valid (cfgOf (compile p)) 0)
    (hi : ∃ w, (cfgOf (compile p)).Irreducible J w) : ¬ Structured p := by
  intro hp
  obtain ⟨w, hw⟩ := hi
  exact structured_no_irreducible hp hv w hw

/-- Figure 5(b) with `A`, `B` as the one-block statements is an instance of `protection5`. -/
theorem fig5bS_protection :
    (∀ {J : Jungle}, J.Valid (cfgOf (compile fig5bS)) 0 → ∃ w, (cfgOf (compile fig5bS)).Irreducible J w) :=
  fun hv => (protection5 (S := blkA) (T := blkB) trivial trivial (by decide)).2.2.1 hv

end SmcIrred.Lang
