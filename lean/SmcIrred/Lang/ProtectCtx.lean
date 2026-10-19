module

public import SmcIrred.Lang.ProtectCode
public import SmcIrred.Lang.ProtIrred

public section

namespace SmcIrred.Lang

/-! # Protection of any adjacent pair inside any goto-free program (G32 a, G33 b, C14, C73)

For a goto-free program `s` and **any occurrence** `S; T` in it (`Sub (S; T) q s 0`: under any nesting of `;`, `if`, `while`,
`do ... while`), the code `protectCode (compile s) q (q + |S|) (q + |S| + |T|)` of Figure 5(b) applied at that place

* returns what `s` returns when the two added conditions are false (`insert_equiv`),
* has an irreducible loop in **every** valid depth-first jungle of its block graph, while `compile s` has none,
* and its block graph is a flow graph (valid jungles exist). -/

theorem Sub.structured {u s : Stmt} {q p : Nat} (h : Sub u q s p) : Structured s → Structured u := by
  induction h with
  | refl => exact id
  | seqL _ ih => intro hs; exact ih hs.1
  | seqR _ ih => intro hs; exact ih hs.2
  | ite1 _ ih => intro hs; exact ih hs
  | iteS _ ih => intro hs; exact ih hs.1
  | iteT _ ih => intro hs; exact ih hs.2
  | whl _ ih => intro hs; exact ih hs
  | dow _ ih => intro hs; exact ih hs

/-- The statement steps of a structured program are steps of its code. -/
theorem sstep_stepI {s : Stmt} (hs : Structured s) {a c : Nat} (h : SStep s 0 a c) : StepI (compile s) a c := by
  have hr := h.range
  exact (SStep_iff (labelsOf 0 s) (compile s) s 0 hs (compile_at s) a c (by omega) (by omega)).2 h

theorem blocks_isCFG {Q : List Instr} (hn : 0 < Q.length) (hroot : ∀ x, x < Q.length → Fwd (StepI Q) 0 x) :
    (cfgOf Q).IsCFG 0 := by
  have hr := fwd_root Q hroot
  have h0 : 0 < (cfgOf Q).n := by
    show 0 < (leaders Q).length
    have := blockOf_lt Q (x := 0) hn
    omega
  exact ⟨h0, fun v hv => (hr v hv).reach⟩

theorem protect_structured {s S T : Stmt} {q : Nat} (hs : Structured s) (hsub : Sub (.seq S T) q s 0)
    (hS : 1 ≤ S.size) (hT : 1 ≤ T.size) (h k : Cond) :
    (cfgOf (compile s)).Reducible 0 ∧
    (∀ {J : Jungle}, J.Valid (cfgOf (compile s)) 0 → ∀ w, ¬ (cfgOf (compile s)).Irreducible J w) ∧
    (∀ {J : Jungle}, J.Valid (cfgOf (protectCode (compile s) q (q + S.size) (q + S.size + T.size) h k)) 0 →
      ∃ w, (cfgOf (protectCode (compile s) q (q + S.size) (q + S.size + T.size) h k)).Irreducible J w) ∧
    (∃ J : Jungle, J.Valid (cfgOf (protectCode (compile s) q (q + S.size) (q + S.size + T.size) h k)) 0) ∧
    (∀ {sol : Nat → Bool} {env : Bool}, (∀ v, h.eval sol env v = (false, v)) → (∀ v, k.eval sol env v = (false, v)) →
      ∀ (v : Bool) (r : List Nat × Bool),
        ((∃ f, exec f (compile s) sol env 0 v [] = some r) ↔
          ∃ f, exec f (protectCode (compile s) q (q + S.size) (q + S.size + T.size) h k) sol env 0 v [] = some r)) := by
  have hseq : Structured (.seq S T) := hsub.structured hs
  have hr := hsub.range
  simp only [Stmt.size] at hr
  have hlen : (compile s).length = s.size + 1 := compile_length s
  have hhP : q + S.size + T.size < (compile s).length := by omega
  have hspec := protectCode_spec (P := compile s) (lo := q) (mid := q + S.size) (hi := q + S.size + T.size) (h := h)
    (k := k) (by omega) (by omega)
  have hlenQ := protectCode_length (P := compile s) (lo := q) (mid := q + S.size) (hi := q + S.size + T.size) (h := h)
    (k := k) (by omega) (by omega)
  have hroot : ∀ x, x < (compile s).length → Fwd (StepI (compile s)) 0 x := fun x hx =>
    (sstep_fwd s hs 0 x (by omega) (by omega)).mono (fun a c => sstep_stepI hs)
  have hf1 : Fwd (StepI (compile s)) q (q + S.size + T.size) :=
    (sstep_fwd (.seq S T) hseq q _ (by omega) (by simp only [Stmt.size]; omega)).mono
      (fun a c hh' => sstep_stepI hs (hsub.sstep hh'))
  have hT' : Structured T := hseq.2
  have hfL : Fwd (StepI (compile s)) (q + S.size) (q + S.size + T.size) :=
    (sstep_fwd T hT' (q + S.size) _ (by omega) (by omega)).mono
      (fun a c hh' => sstep_stepI hs (hsub.sstep (.seqR hh')))
  have hred := structured_reducible hs
  have hrQ := protect_fwd_root hspec hlenQ (by omega) (by omega) hhP hroot
  refine ⟨hred, fun hv w => reducible_no_irreducible hv hred w,
    fun hv => protect_irreducible hspec hlenQ (by omega) (by omega) hhP hroot hf1 hfL hv,
    ⟨_, dfsRun_valid (blocks_isCFG (by omega) hrQ) (Nat.le_refl 1)⟩, ?_⟩
  intro sol env hh hk v r
  exact insert_equiv hspec (by omega) hh hk v r

end SmcIrred.Lang
