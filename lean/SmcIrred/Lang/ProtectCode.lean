module

public import SmcIrred.Lang.Insert
public import SmcIrred.Lang.EntryCycle

public section

namespace SmcIrred.Lang

/-! # The protection of a region of given code, as code (R19b, G32 a, G33 b)

`protectCode P lo mid hi h k` is `P` with the entry test `if (h) goto mid` inserted at `lo` and the closing test
`if (k) goto lo` after the region `[lo, hi)`, all jump targets redirected.  It satisfies `InsertSpec`, so by
`insert_equiv` it returns what `P` returns, and the irreducible loop of the protected region is proved from forward paths
of `P` in `protect_not_reducible`. -/

@[expose] def protectCode (P : List Instr) (lo mid hi : Nat) (h k : Cond) : List Instr :=
  let R := P.map (remapI lo hi)
  R.take lo ++ (.jmpIf h (mid + 1) :: ((R.drop lo).take (hi - lo) ++ (.jmpIf k (lo + 1) :: R.drop hi)))

theorem protectCode_length {P : List Instr} {lo mid hi : Nat} {h k : Cond} (hlh : lo ≤ hi) (hhi : hi ≤ P.length) :
    (protectCode P lo mid hi h k).length = P.length + 2 := by
  simp only [protectCode, List.length_append, List.length_cons, List.length_take, List.length_drop, List.length_map]
  omega

theorem getD_remap_map (P : List Instr) (lo hi a : Nat) :
    (P.map (remapI lo hi)).getD a .halt = remapI lo hi (P.getD a .halt) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases P[a]? <;> simp [remapI]

theorem getElem?_ins (R : List Instr) (lo hi : Nat) (e c : Instr) (hlh : lo ≤ hi) (hhi : hi ≤ R.length) (i : Nat) :
    (R.take lo ++ (e :: ((R.drop lo).take (hi - lo) ++ (c :: R.drop hi))))[i]? =
      if i < lo then R[i]? else if i = lo then some e else if i ≤ hi then R[i - 1]?
      else if i = hi + 1 then some c else R[i - 2]? := by
  have hl1 : (R.take lo).length = lo := by simp; omega
  have hl2 : ((R.drop lo).take (hi - lo)).length = hi - lo := by simp; omega
  by_cases h1 : i < lo
  · rw [List.getElem?_append_left (by omega), List.getElem?_take]; simp [h1]
  · rw [List.getElem?_append_right (by omega), hl1]
    by_cases h2 : i = lo
    · subst h2; simp
    · have : i - lo = (i - lo - 1) + 1 := by omega
      rw [this, List.getElem?_cons_succ]
      by_cases h3 : i ≤ hi
      · rw [List.getElem?_append_left (by omega), List.getElem?_take, List.getElem?_drop]
        simp [h1, h2, h3, show i - lo - 1 < hi - lo by omega]
        congr 1; omega
      · rw [List.getElem?_append_right (by omega), hl2]
        by_cases h4 : i = hi + 1
        · subst h4
          have : hi + 1 - lo - 1 - (hi - lo) = 0 := by omega
          rw [this]; simp [h1, h2, h3]
        · have : i - lo - 1 - (hi - lo) = (i - hi - 2) + 1 := by omega
          rw [this, List.getElem?_cons_succ, List.getElem?_drop]
          simp [h1, h2, h3, h4]
          congr 1; omega

theorem protectCode_spec {P : List Instr} {lo mid hi : Nat} {h k : Cond} (hlh : lo < hi) (hhi : hi ≤ P.length) :
    InsertSpec P (protectCode P lo mid hi h k) lo mid hi h k := by
  have hR : ∀ a, (P.map (remapI lo hi)).getD a .halt = remapI lo hi (P.getD a .halt) := getD_remap_map P lo hi
  have hlen : (P.map (remapI lo hi)).length = P.length := List.length_map _
  have hQ := getElem?_ins (P.map (remapI lo hi)) lo hi (.jmpIf h (mid + 1)) (.jmpIf k (lo + 1)) (by omega) (by omega)
  refine ⟨fun a => ?_, ?_, ?_⟩
  · unfold protectCode
    simp only
    rw [List.getD_eq_getElem?_getD, hQ, ← hR a, List.getD_eq_getElem?_getD]
    unfold gA
    by_cases h1 : a < lo
    · simp [h1]
    · by_cases h2 : a < hi
      · simp [h1, h2, show ¬ a + 1 < lo by omega, show ¬ a + 1 = lo by omega, show a + 1 ≤ hi by omega]
      · simp [h1, h2, show ¬ a + 2 < lo by omega, show ¬ a + 2 = lo by omega, show ¬ a + 2 ≤ hi by omega,
          show ¬ a + 2 = hi + 1 by omega]
  · unfold protectCode
    simp only
    rw [List.getD_eq_getElem?_getD, hQ]; simp
  · unfold protectCode
    simp only
    rw [List.getD_eq_getElem?_getD, hQ]
    simp [show ¬ hi + 1 < lo by omega, show ¬ hi + 1 = lo by omega, show ¬ hi + 1 ≤ hi by omega]

/-! ### Forward paths survive the insertion -/

section Transport
variable {P Q : List Instr} {lo mid hi : Nat} {h k : Cond}

theorem rmT_succ (a : Nat) : rmT lo hi (a + 1) = gA lo hi a + 1 := by
  unfold rmT gA
  by_cases h1 : a + 1 ≤ lo
  · simp [h1, show a < lo by omega]
  · by_cases h2 : a + 1 ≤ hi
    · simp [h1, h2, show ¬ a < lo by omega, show a < hi by omega]
    · simp [h1, h2, show ¬ a < lo by omega, show ¬ a < hi by omega]

theorem gA_lt_rmT {a c : Nat} (hac : a < c) : gA lo hi a < rmT lo hi c := by
  unfold rmT gA
  by_cases h1 : a < lo
  · by_cases h2 : c ≤ lo <;> simp [h1, h2] <;> try omega
    by_cases h3 : c ≤ hi <;> simp [h3] <;> omega
  · by_cases h2 : a < hi
    · simp [h1, h2, show ¬ c ≤ lo by omega]
      by_cases h3 : c ≤ hi <;> simp [h3] <;> omega
    · simp [h1, h2, show ¬ c ≤ lo by omega, show ¬ c ≤ hi by omega]; omega

theorem rmT_lo : rmT lo hi lo = lo := by simp [rmT]

theorem rmT_hi (hlh : lo < hi) : rmT lo hi hi = hi + 1 := by simp [rmT, show ¬ hi ≤ lo by omega]

theorem step_rm (hs : InsertSpec P Q lo mid hi h k) {a c : Nat} (hp : StepI P a c) : StepI Q (gA lo hi a) (rmT lo hi c) := by
  unfold StepI at hp ⊢
  rw [hs.body]
  cases hi' : P.getD a .halt <;> simp only [hi', remapI] at hp ⊢
  · subst hp; exact rmT_succ a
  · subst hp; rfl
  · rcases hp with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (rmT_succ a)

/-- From the shifted address a step of the inserted code reaches the image of the target. -/
theorem rm_to_gA (hs : InsertSpec P Q lo mid hi h k) (hlh : lo < hi) (c : Nat) :
    rmT lo hi c = gA lo hi c ∨ (c = lo ∧ StepI Q lo (gA lo hi lo)) ∨ (c = hi ∧ StepI Q (hi + 1) (gA lo hi hi)) := by
  by_cases h1 : c = lo
  · right; left
    refine ⟨h1, ?_⟩
    subst h1
    unfold StepI; rw [hs.entry, gA_lo hlh]; exact Or.inr rfl
  · by_cases h2 : c = hi
    · right; right
      refine ⟨h2, ?_⟩
      subst h2
      unfold StepI; rw [hs.closing, gA_hi hlh]; exact Or.inr rfl
    · left
      unfold rmT gA
      by_cases h3 : c < lo
      · simp [h3, show c ≤ lo by omega]
      · by_cases h4 : c < hi
        · simp [h3, h4, show ¬ c ≤ lo by omega, show c ≤ hi by omega]
        · simp [h3, h4, show ¬ c ≤ lo by omega, show ¬ c ≤ hi by omega]

theorem gA_le_rmT_of_ne {c : Nat} (hlh : lo < hi) : gA lo hi c ≤ rmT lo hi c + 1 := by
  unfold rmT gA
  by_cases h1 : c < lo <;> by_cases h2 : c ≤ lo <;> by_cases h3 : c < hi <;> by_cases h4 : c ≤ hi <;> simp [*] <;> omega

/-- A forward path of the original code, shifted: it reaches the image of its end. -/
theorem fwd_gA (hs : InsertSpec P Q lo mid hi h k) (hlh : lo < hi) {a b : Nat} (hp : Fwd (StepI P) a b) :
    Fwd (StepI Q) (gA lo hi a) (gA lo hi b) := by
  induction hp with
  | refl => exact .refl _
  | @step a c b hr hlt _ ih =>
    refine Fwd.trans ?_ ih
    have h1 := step_rm hs hr
    have h2 := gA_lt_rmT (lo := lo) (hi := hi) hlt
    rcases rm_to_gA hs hlh c with he | ⟨hc, hst⟩ | ⟨hc, hst⟩
    · rw [he] at h1 h2; exact .step h1 h2 (.refl _)
    · rw [hc] at h1 h2 ⊢
      rw [rmT_lo] at h1 h2
      refine .step h1 h2 (.step hst ?_ (.refl _))
      rw [gA_lo hlh]; omega
    · rw [hc] at h1 h2 ⊢
      rw [rmT_hi hlh] at h1 h2
      refine .step h1 h2 (.step hst ?_ (.refl _))
      rw [gA_hi hlh]; omega

/-- A forward path of the original code, shifted: it reaches the (redirected) end, the entry or closing test when the end
is the start or the end of the region. -/
theorem fwd_rmT (hs : InsertSpec P Q lo mid hi h k) (hlh : lo < hi) {a b : Nat} (hp : Fwd (StepI P) a b) (hab : a < b) :
    Fwd (StepI Q) (gA lo hi a) (rmT lo hi b) := by
  induction hp with
  | refl => omega
  | @step a c b hr hlt hrest ih =>
    have h1 := step_rm hs hr
    have h2 := gA_lt_rmT (lo := lo) (hi := hi) hlt
    rcases Nat.eq_or_lt_of_le hrest.le with hcb | hcb
    · subst hcb; exact .step h1 h2 (.refl _)
    · have ih' := ih hcb
      refine Fwd.trans ?_ ih'
      rcases rm_to_gA hs hlh c with he | ⟨hc, hst⟩ | ⟨hc, hst⟩
      · rw [he] at h1 h2; exact .step h1 h2 (.refl _)
      · rw [hc] at h1 h2 ⊢
        rw [rmT_lo] at h1 h2
        refine .step h1 h2 (.step hst ?_ (.refl _))
        rw [gA_lo hlh]; omega
      · rw [hc] at h1 h2 ⊢
        rw [rmT_hi hlh] at h1 h2
        refine .step h1 h2 (.step hst ?_ (.refl _))
        rw [gA_hi hlh]; omega

end Transport

/-- Every address of the protected code is reached from the entry by a forward path. -/
theorem protect_fwd_root {P Q : List Instr} {lo mid hi : Nat} {h k : Cond}
    (hs : InsertSpec P Q lo mid hi h k) (hlen : Q.length = P.length + 2) (hlm : lo < mid) (hmh : mid < hi)
    (hhP : hi < P.length) (hroot : ∀ x, x < P.length → Fwd (StepI P) 0 x) :
    ∀ x, x < Q.length → Fwd (StepI Q) 0 x := by
  have hlh : lo < hi := by omega
  have hrt : Fwd (StepI Q) 0 (gA lo hi 0) := by
    by_cases h0 : lo = 0
    · subst h0
      rw [gA_lo hlh]
      refine .step ?_ (by omega) (.refl _)
      unfold StepI; rw [hs.entry]; exact Or.inr rfl
    · have : gA lo hi 0 = 0 := by simp [gA, show 0 < lo by omega]
      rw [this]; exact .refl _
  intro x hx
  by_cases h1 : x = lo
  · subst h1
    by_cases h0 : x = 0
    · subst h0; exact .refl _
    · have := fwd_rmT hs hlh (hroot x (by omega)) (by omega)
      have e : gA x hi 0 = 0 := by simp [gA, show 0 < x by omega]
      rw [e] at this
      simpa [rmT] using this
  · by_cases h2 : x = hi + 1
    · subst h2
      have := fwd_rmT hs hlh (hroot hi hhP) (by omega)
      refine Fwd.trans hrt ?_
      have e : rmT lo hi hi = hi + 1 := by simp [rmT, show ¬ hi ≤ lo by omega]
      rwa [e] at this
    · have hy : ∃ y, y < P.length ∧ gA lo hi y = x := by
        by_cases h3 : x < lo
        · exact ⟨x, by omega, by simp [gA, h3]⟩
        · by_cases h4 : x ≤ hi
          · exact ⟨x - 1, by omega, by simp [gA, show ¬ x - 1 < lo by omega, show x - 1 < hi by omega]; omega⟩
          · exact ⟨x - 2, by omega, by simp [gA, show ¬ x - 2 < lo by omega, show ¬ x - 2 < hi by omega]; omega⟩
      obtain ⟨y, hy1, rfl⟩ := hy
      exact Fwd.trans hrt (fwd_gA hs hlh (hroot y hy1))

/-- The protected region closes a cycle of non-dominating edges in the block graph of the protected code, for **any** code `P`
with forward paths from the region start and from the middle to the end of the region and from the entry to every address. -/
theorem protect_not_reducible {P Q : List Instr} {lo mid hi : Nat} {h k : Cond}
    (hs : InsertSpec P Q lo mid hi h k) (hlen : Q.length = P.length + 2) (hlm : lo < mid) (hmh : mid < hi)
    (hhP : hi < P.length) (hroot : ∀ x, x < P.length → Fwd (StepI P) 0 x)
    (hf1 : Fwd (StepI P) lo hi) (hfL : Fwd (StepI P) mid hi) : ¬ (cfgOf Q).Reducible 0 := by
  have hlh : lo < hi := by omega
  have hrQ := protect_fwd_root hs hlen hlm hmh hhP hroot
  have hf1Q : Fwd (StepI Q) (lo + 1) (hi + 1) := by
    have := fwd_rmT hs hlh hf1 hlh
    rwa [gA_lo hlh, show rmT lo hi hi = hi + 1 by simp [rmT, show ¬ hi ≤ lo by omega]] at this
  have hfLQ : Fwd (StepI Q) (mid + 1) (hi + 1) := by
    have := fwd_rmT hs hlh hfL hmh
    rwa [show gA lo hi mid = mid + 1 by simp [gA, show ¬ mid < lo by omega, hmh],
      show rmT lo hi hi = hi + 1 by simp [rmT, show ¬ hi ≤ lo by omega]] at this
  refine entry_cycle_not_reducible Q (e0 := lo) (L := mid + 1) (c := hi + 1) (h := h) (by omega) hs.entry hrQ
    (by omega) (by omega) hf1Q hfLQ ?_
  unfold StepI; rw [hs.closing]; exact Or.inl rfl

/-- Every valid depth-first jungle of the protected code has an irreducible loop. -/
theorem protect_irreducible {P Q : List Instr} {lo mid hi : Nat} {h k : Cond}
    (hs : InsertSpec P Q lo mid hi h k) (hlen : Q.length = P.length + 2) (hlm : lo < mid) (hmh : mid < hi)
    (hhP : hi < P.length) (hroot : ∀ x, x < P.length → Fwd (StepI P) 0 x)
    (hf1 : Fwd (StepI P) lo hi) (hfL : Fwd (StepI P) mid hi) {J : Jungle} (hv : J.Valid (cfgOf Q) 0) :
    ∃ w, (cfgOf Q).Irreducible J w :=
  exists_irreducible_loop hv (protect_not_reducible hs hlen hlm hmh hhP hroot hf1 hfL)

end SmcIrred.Lang
