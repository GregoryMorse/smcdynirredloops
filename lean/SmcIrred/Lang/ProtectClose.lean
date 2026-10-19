module

public import SmcIrred.Lang.Insert1
public import SmcIrred.Lang.ProtectCtx
public import SmcIrred.Lang.SubAt

public section

namespace SmcIrred.Lang

/-! # Figure 6(b) inside any goto-free program (G32 a, C14, C73, C76)

The entry test of Figure 6 is the `if` of the program itself; only the closing test is inserted.  For any occurrence
`(if (c) S); T` of a goto-free program the protected code returns the same, has an irreducible loop in every valid depth-first
jungle, while the original has none. -/

@[expose] def protectClose (P : List Instr) (lo hi : Nat) (k : Cond) : List Instr :=
  let R := P.map (remapI1 hi)
  R.take hi ++ (.jmpIf k (lo + 1) :: R.drop hi)

theorem protectClose_length {P : List Instr} {lo hi : Nat} {k : Cond} (hhi : hi ≤ P.length) :
    (protectClose P lo hi k).length = P.length + 1 := by
  simp only [protectClose, List.length_append, List.length_cons, List.length_take, List.length_drop, List.length_map]
  omega

theorem getD_remap1_map (P : List Instr) (hi a : Nat) :
    (P.map (remapI1 hi)).getD a .halt = remapI1 hi (P.getD a .halt) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases P[a]? <;> simp [remapI1]

theorem getElem?_ins1 (R : List Instr) (hi : Nat) (c : Instr) (hhi : hi ≤ R.length) (i : Nat) :
    (R.take hi ++ (c :: R.drop hi))[i]? = if i < hi then R[i]? else if i = hi then some c else R[i - 1]? := by
  have hl1 : (R.take hi).length = hi := by simp; omega
  by_cases h1 : i < hi
  · rw [List.getElem?_append_left (by omega), List.getElem?_take]; simp [h1]
  · rw [List.getElem?_append_right (by omega), hl1]
    by_cases h2 : i = hi
    · subst h2; simp
    · have : i - hi = (i - hi - 1) + 1 := by omega
      rw [this, List.getElem?_cons_succ, List.getElem?_drop]
      simp [h1, h2]
      congr 1; omega

theorem protectClose_spec {P : List Instr} {lo hi : Nat} {k : Cond} (hhi : hi ≤ P.length) :
    InsertSpec1 P (protectClose P lo hi k) lo hi k := by
  have hR : ∀ a, (P.map (remapI1 hi)).getD a .halt = remapI1 hi (P.getD a .halt) := getD_remap1_map P hi
  have hlen : (P.map (remapI1 hi)).length = P.length := List.length_map _
  have hQ := getElem?_ins1 (P.map (remapI1 hi)) hi (.jmpIf k (lo + 1)) (by omega)
  refine ⟨fun a => ?_, ?_⟩
  · unfold protectClose
    simp only
    rw [List.getD_eq_getElem?_getD, hQ, ← hR a, List.getD_eq_getElem?_getD]
    unfold gA1
    by_cases h1 : a < hi
    · simp [h1]
    · simp [h1, show ¬ a + 1 < hi by omega, show ¬ a + 1 = hi by omega]
  · unfold protectClose
    simp only
    rw [List.getD_eq_getElem?_getD, hQ]; simp

/-! ### Forward paths survive the insertion -/

section Transport
variable {P Q : List Instr} {lo hi : Nat} {k : Cond}

theorem rmT1_succ (a : Nat) : rmT1 hi (a + 1) = gA1 hi a + 1 := by
  unfold rmT1 gA1
  by_cases h1 : a + 1 ≤ hi
  · simp [h1, show a < hi by omega]
  · simp [h1, show ¬ a < hi by omega]

theorem gA1_lt_rmT1 {a c : Nat} (hac : a < c) : gA1 hi a < rmT1 hi c := by
  unfold rmT1 gA1
  by_cases h1 : a < hi <;> by_cases h2 : c ≤ hi <;> simp [h1, h2] <;> omega

theorem step_rm1 (hs : InsertSpec1 P Q lo hi k) {a c : Nat} (hp : StepI P a c) : StepI Q (gA1 hi a) (rmT1 hi c) := by
  unfold StepI at hp ⊢
  rw [hs.body]
  cases hi' : P.getD a .halt <;> simp only [hi', remapI1] at hp ⊢
  · subst hp; exact rmT1_succ a
  · subst hp; rfl
  · rcases hp with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (rmT1_succ a)

theorem rm1_to_gA (hs : InsertSpec1 P Q lo hi k) (c : Nat) :
    rmT1 hi c = gA1 hi c ∨ (c = hi ∧ StepI Q hi (gA1 hi hi)) := by
  by_cases h2 : c = hi
  · right
    refine ⟨h2, ?_⟩
    subst h2
    unfold StepI; rw [hs.closing]; simp [gA1]
  · left
    unfold rmT1 gA1
    by_cases h4 : c < hi
    · simp [h4, show c ≤ hi by omega]
    · simp [h4, show ¬ c ≤ hi by omega]

theorem fwd_gA1 (hs : InsertSpec1 P Q lo hi k) {a b : Nat} (hp : Fwd (StepI P) a b) :
    Fwd (StepI Q) (gA1 hi a) (gA1 hi b) := by
  induction hp with
  | refl => exact .refl _
  | @step a c b hr hlt _ ih =>
    refine Fwd.trans ?_ ih
    have h1 := step_rm1 hs hr
    have h2 := gA1_lt_rmT1 (hi := hi) hlt
    rcases rm1_to_gA hs c with he | ⟨hc, hst⟩
    · rw [he] at h1 h2; exact .step h1 h2 (.refl _)
    · rw [hc] at h1 h2 ⊢
      rw [show rmT1 hi hi = hi by simp [rmT1]] at h1 h2
      refine .step h1 h2 (.step hst ?_ (.refl _))
      simp [gA1]

theorem fwd_rmT1 (hs : InsertSpec1 P Q lo hi k) {a b : Nat} (hp : Fwd (StepI P) a b) (hab : a < b) :
    Fwd (StepI Q) (gA1 hi a) (rmT1 hi b) := by
  induction hp with
  | refl => omega
  | @step a c b hr hlt hrest ih =>
    have h1 := step_rm1 hs hr
    have h2 := gA1_lt_rmT1 (hi := hi) hlt
    rcases Nat.eq_or_lt_of_le hrest.le with hcb | hcb
    · subst hcb; exact .step h1 h2 (.refl _)
    · have ih' := ih hcb
      refine Fwd.trans ?_ ih'
      rcases rm1_to_gA hs c with he | ⟨hc, hst⟩
      · rw [he] at h1 h2; exact .step h1 h2 (.refl _)
      · rw [hc] at h1 h2 ⊢
        rw [show rmT1 hi hi = hi by simp [rmT1]] at h1 h2
        refine .step h1 h2 (.step hst ?_ (.refl _))
        simp [gA1]

end Transport

theorem protect1_fwd_root {P Q : List Instr} {lo hi : Nat} {k : Cond} (hs : InsertSpec1 P Q lo hi k)
    (hlen : Q.length = P.length + 1) (hhi : 0 < hi) (hhP : hi < P.length)
    (hroot : ∀ x, x < P.length → Fwd (StepI P) 0 x) : ∀ x, x < Q.length → Fwd (StepI Q) 0 x := by
  intro x hx
  have e0 : gA1 hi 0 = 0 := by simp [gA1, hhi]
  by_cases h1 : x = hi
  · subst h1
    have := fwd_rmT1 hs (hroot x hhP) hhi
    rwa [e0, show rmT1 x x = x by simp [rmT1]] at this
  · have hy : ∃ y, y < P.length ∧ gA1 hi y = x := by
      by_cases h3 : x < hi
      · exact ⟨x, by omega, by simp [gA1, h3]⟩
      · exact ⟨x - 1, by omega, by simp [gA1, show ¬ x - 1 < hi by omega]; omega⟩
    obtain ⟨y, hy1, rfl⟩ := hy
    have := fwd_gA1 hs (hroot y hy1)
    rwa [e0] at this

/-- The closing test closes a cycle of non-dominating edges at the existing entry test. -/
theorem protect1_not_reducible {P Q : List Instr} {lo mid hi : Nat} {h k : Cond} (hs : InsertSpec1 P Q lo hi k)
    (hlen : Q.length = P.length + 1) (hentry : P.getD lo .halt = .jmpIf h mid) (hlm : lo + 1 < mid) (hmh : mid < hi)
    (hhP : hi < P.length) (hroot : ∀ x, x < P.length → Fwd (StepI P) 0 x)
    (hf1 : Fwd (StepI P) (lo + 1) hi) (hfL : Fwd (StepI P) mid hi) : ¬ (cfgOf Q).Reducible 0 := by
  have hQe : Q.getD lo .halt = .jmpIf h mid := by
    have := hs.body lo
    rw [hentry] at this
    simp only [gA1, show lo < hi by omega, ↓reduceIte, remapI1, rmT1, show mid ≤ hi by omega] at this
    exact this
  have hrQ := protect1_fwd_root hs hlen (by omega) hhP hroot
  have hf1Q : Fwd (StepI Q) (lo + 1) hi := by
    have := fwd_rmT1 hs hf1 (by omega)
    rwa [show gA1 hi (lo + 1) = lo + 1 by simp [gA1, show lo + 1 < hi by omega], show rmT1 hi hi = hi by simp [rmT1]] at this
  have hfLQ : Fwd (StepI Q) mid hi := by
    have := fwd_rmT1 hs hfL hmh
    rwa [show gA1 hi mid = mid by simp [gA1, hmh], show rmT1 hi hi = hi by simp [rmT1]] at this
  refine entry_cycle_not_reducible Q (e0 := lo) (L := mid) (c := hi) (h := h) (by omega) hQe hrQ
    (by omega) (by omega) hf1Q hfLQ ?_
  unfold StepI; rw [hs.closing]; exact Or.inl rfl

theorem protect1_irreducible {P Q : List Instr} {lo mid hi : Nat} {h k : Cond} (hs : InsertSpec1 P Q lo hi k)
    (hlen : Q.length = P.length + 1) (hentry : P.getD lo .halt = .jmpIf h mid) (hlm : lo + 1 < mid) (hmh : mid < hi)
    (hhP : hi < P.length) (hroot : ∀ x, x < P.length → Fwd (StepI P) 0 x)
    (hf1 : Fwd (StepI P) (lo + 1) hi) (hfL : Fwd (StepI P) mid hi) {J : Jungle} (hv : J.Valid (cfgOf Q) 0) :
    ∃ w, (cfgOf Q).Irreducible J w :=
  exists_irreducible_loop hv (protect1_not_reducible hs hlen hentry hlm hmh hhP hroot hf1 hfL)

theorem protect6_structured {s S T : Stmt} {q : Nat} {cd : Cond} (hs : Structured s)
    (hsub : Sub (.seq (.ite1 cd S) T) q s 0) (hS : 1 ≤ S.size) (hT : 1 ≤ T.size) (k : Cond) :
    let Q := protectClose (compile s) q (q + 1 + S.size + T.size) k
    (cfgOf (compile s)).Reducible 0 ∧
    (∀ {J : Jungle}, J.Valid (cfgOf (compile s)) 0 → ∀ w, ¬ (cfgOf (compile s)).Irreducible J w) ∧
    (∀ {J : Jungle}, J.Valid (cfgOf Q) 0 → ∃ w, (cfgOf Q).Irreducible J w) ∧
    (∃ J : Jungle, J.Valid (cfgOf Q) 0) ∧
    (∀ {sol : Nat → Bool} {env : Bool}, (∀ v, k.eval sol env v = (false, v)) → ∀ (v : Bool) (r : List Nat × Bool),
      ((∃ f, exec f (compile s) sol env 0 v [] = some r) ↔ ∃ f, exec f Q sol env 0 v [] = some r)) := by
  have hseq : Structured (.seq (.ite1 cd S) T) := hsub.structured hs
  have hr := hsub.range
  simp only [Stmt.size] at hr
  have hlen : (compile s).length = s.size + 1 := compile_length s
  have hhP : q + 1 + S.size + T.size < (compile s).length := by omega
  have hspec := protectClose_spec (P := compile s) (lo := q) (hi := q + 1 + S.size + T.size) (k := k) (by omega)
  have hlenQ := protectClose_length (P := compile s) (lo := q) (hi := q + 1 + S.size + T.size) (k := k) (by omega)
  have hroot : ∀ x, x < (compile s).length → Fwd (StepI (compile s)) 0 x := fun x hx =>
    (sstep_fwd s hs 0 x (by omega) (by omega)).mono (fun a c => sstep_stepI hs)
  have hat : AtAddr (compile s) q (comp (labelsOf 0 s) q (.seq (.ite1 cd S) T)) :=
    hsub.atAddr (labelsOf 0 s) (compile_at s)
  have hat1 := hat.append_left
  have hentry : (compile s).getD q .halt = .jmpIf (.neg cd) (q + 1 + S.size) := by
    have := (hat1.cons).1
    simpa [comp] using this
  have hT' : Structured T := hseq.2
  have hS' : Structured S := hseq.1
  have hM : q + (Stmt.ite1 cd S).size = q + 1 + S.size := by simp only [Stmt.size]; omega
  have hfS : Fwd (StepI (compile s)) (q + 1) (q + 1 + S.size) :=
    (sstep_fwd S hS' (q + 1) _ (by omega) (by omega)).mono
      (fun a c hh' => sstep_stepI hs (hsub.sstep (.seqL (.ite1_body hh'))))
  have hfL : Fwd (StepI (compile s)) (q + 1 + S.size) (q + 1 + S.size + T.size) :=
    (sstep_fwd T hT' (q + 1 + S.size) _ (by omega) (by omega)).mono
      (fun a c hh' => sstep_stepI hs (hsub.sstep (.seqR (by rw [hM]; exact hh'))))
  have hf1 : Fwd (StepI (compile s)) (q + 1) (q + 1 + S.size + T.size) := hfS.trans hfL
  have hred := structured_reducible hs
  have hrQ := protect1_fwd_root hspec hlenQ (by omega) hhP hroot
  refine ⟨hred, fun hv w => reducible_no_irreducible hv hred w,
    fun hv => protect1_irreducible hspec hlenQ hentry (by omega) (by omega) hhP hroot hf1 hfL hv,
    ⟨_, dfsRun_valid (blocks_isCFG (by omega) hrQ) (Nat.le_refl 1)⟩, ?_⟩
  intro sol env hk v r
  exact insert1_equiv hspec hk (by omega) v r

end SmcIrred.Lang
