module

public import SmcIrred.Lang.ProtectCtx

public section

namespace SmcIrred.Lang

/-! # Several protections in one program (G32 a3, G11)

`protectMany P rs` applies `protectCode` for the regions `rs` one after the other. The regions are given from the highest
address to the lowest, each ending at or before the start of the previous one, so a protection never moves the addresses
of the regions still to come. Equivalence for false conditions, forward reachability and the irreducible loop of the
lowest region hold for any number of protections. -/

structure Reg where
  lo : Nat
  mid : Nat
  hi : Nat
  h : Cond
  k : Cond

@[expose] def protectMany (P : List Instr) : List Reg → List Instr
  | [] => P
  | r :: rs => protectMany (protectCode P r.lo r.mid r.hi r.h r.k) rs

/-- The regions are well formed for code of length `L` and in descending order. -/
@[expose] def RegsOk : Nat → List Reg → Prop
  | _, [] => True
  | L, r :: rs => r.lo < r.mid ∧ r.mid < r.hi ∧ r.hi < L ∧ (∀ r' ∈ rs, r'.hi ≤ r.lo) ∧ RegsOk (L + 2) rs

theorem protectMany_length : ∀ (rs : List Reg) (P : List Instr), RegsOk P.length rs →
    (protectMany P rs).length = P.length + 2 * rs.length := by
  intro rs
  induction rs with
  | nil => intro P _; simp [protectMany]
  | cons r rs ih =>
    intro P hok
    obtain ⟨h1, h2, h3, _, h5⟩ := hok
    have hl := protectCode_length (P := P) (lo := r.lo) (mid := r.mid) (hi := r.hi) (h := r.h) (k := r.k)
      (by omega) (by omega)
    simp only [protectMany, List.length_cons]
    rw [ih _ (by rw [hl]; exact h5), hl]
    omega

theorem protectMany_equiv {sol : Nat → Bool} {env : Bool} : ∀ (rs : List Reg) (P : List Instr), RegsOk P.length rs →
    (∀ r ∈ rs, (∀ v, r.h.eval sol env v = (false, v)) ∧ (∀ v, r.k.eval sol env v = (false, v))) →
    ∀ (v : Bool) (res : List Nat × Bool),
      ((∃ f, exec f P sol env 0 v [] = some res) ↔ ∃ f, exec f (protectMany P rs) sol env 0 v [] = some res) := by
  intro rs
  induction rs with
  | nil => intro P _ _ v res; simp [protectMany]
  | cons r rs ih =>
    intro P hok hc v res
    obtain ⟨h1, h2, h3, _, h5⟩ := hok
    have hspec := protectCode_spec (P := P) (lo := r.lo) (mid := r.mid) (hi := r.hi) (h := r.h) (k := r.k)
      (by omega) (by omega)
    have hl := protectCode_length (P := P) (lo := r.lo) (mid := r.mid) (hi := r.hi) (h := r.h) (k := r.k)
      (by omega) (by omega)
    have hr := hc r (by simp)
    simp only [protectMany]
    rw [insert_equiv hspec (by omega) hr.1 hr.2 v res]
    exact ih _ (by rw [hl]; exact h5) (fun r' hr' => hc r' (by simp [hr'])) v res

theorem protectMany_root : ∀ (rs : List Reg) (P : List Instr), RegsOk P.length rs →
    (∀ x, x < P.length → Fwd (StepI P) 0 x) → ∀ x, x < (protectMany P rs).length → Fwd (StepI (protectMany P rs)) 0 x := by
  intro rs
  induction rs with
  | nil => intro P _ hr; simpa [protectMany] using hr
  | cons r rs ih =>
    intro P hok hr
    obtain ⟨h1, h2, h3, _, h5⟩ := hok
    have hspec := protectCode_spec (P := P) (lo := r.lo) (mid := r.mid) (hi := r.hi) (h := r.h) (k := r.k)
      (by omega) (by omega)
    have hl := protectCode_length (P := P) (lo := r.lo) (mid := r.mid) (hi := r.hi) (h := r.h) (k := r.k)
      (by omega) (by omega)
    have hq := protect_fwd_root hspec hl h1 h2 h3 hr
    simp only [protectMany]
    exact ih _ (by rw [hl]; exact h5) hq

/-- A forward path of the original code that ends at or before the start of every region survives all the protections. -/
theorem protectMany_fwd {a b : Nat} : ∀ (rs : List Reg) (P : List Instr), RegsOk P.length rs → (∀ r ∈ rs, b ≤ r.lo) →
    a < b → Fwd (StepI P) a b → Fwd (StepI (protectMany P rs)) a b := by
  intro rs
  induction rs with
  | nil => intro P _ _ _ hp; simpa [protectMany] using hp
  | cons r rs ih =>
    intro P hok hb hab hp
    obtain ⟨h1, h2, h3, _, h5⟩ := hok
    have hspec := protectCode_spec (P := P) (lo := r.lo) (mid := r.mid) (hi := r.hi) (h := r.h) (k := r.k)
      (by omega) (by omega)
    have hl := protectCode_length (P := P) (lo := r.lo) (mid := r.mid) (hi := r.hi) (h := r.h) (k := r.k)
      (by omega) (by omega)
    have hbr : b ≤ r.lo := hb r (by simp)
    have := fwd_rmT hspec (by omega) hp hab
    have e1 : gA r.lo r.hi a = a := by simp [gA, show a < r.lo by omega]
    have e2 : rmT r.lo r.hi b = b := by simp [rmT, hbr]
    rw [e1, e2] at this
    simp only [protectMany]
    exact ih _ (by rw [hl]; exact h5) (fun r' hr' => hb r' (by simp [hr'])) hab this

theorem protectMany_append : ∀ (rs : List Reg) (P : List Instr) (r : Reg),
    protectMany P (rs ++ [r]) = protectCode (protectMany P rs) r.lo r.mid r.hi r.h r.k := by
  intro rs
  induction rs with
  | nil => intro P r; simp [protectMany]
  | cons r' rs ih => intro P r; simp only [List.cons_append, protectMany]; exact ih _ r

theorem regsOk_append : ∀ (rs : List Reg) (L : Nat) (r : Reg), RegsOk L (rs ++ [r]) →
    RegsOk L rs ∧ r.lo < r.mid ∧ r.mid < r.hi ∧ r.hi < L + 2 * rs.length ∧ ∀ r' ∈ rs, r.hi ≤ r'.lo := by
  intro rs
  induction rs with
  | nil => intro L r hok; obtain ⟨h1, h2, h3, _⟩ := hok; simp [RegsOk]; omega
  | cons r' rs ih =>
    intro L r hok
    obtain ⟨h1, h2, h3, h4, h5⟩ := hok
    obtain ⟨i1, i2, i3, i4, i5⟩ := ih (L + 2) r h5
    refine ⟨⟨h1, h2, h3, fun x hx => h4 x (by simp [hx]), i1⟩, i2, i3, by simp; omega, ?_⟩
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h4 r (by simp)
    · exact i5 x hx

/-- Any number of protections inside any goto-free program (Figure 5(b) with several pairs): the code returns the same
when all the conditions are false, the original has a reducible control-flow graph without irreducible loops, and the
protected code has an irreducible loop in every valid depth-first jungle (from its lowest region). `rs` are the regions
above, the last region is the lowest, `Sub (S; T) q s 0` places its pair. -/
theorem protect_many_structured {s S T : Stmt} {q : Nat} (hs : Structured s) (hsub : Sub (.seq S T) q s 0)
    (hS : 1 ≤ S.size) (hT : 1 ≤ T.size) (h k : Cond) (rs : List Reg)
    (hok : RegsOk (compile s).length (rs ++ [⟨q, q + S.size, q + S.size + T.size, h, k⟩])) :
    (cfgOf (compile s)).Reducible 0 ∧
    (∀ {J : Jungle}, J.Valid (cfgOf (compile s)) 0 → ∀ w, ¬ (cfgOf (compile s)).Irreducible J w) ∧
    (∀ {J : Jungle}, J.Valid (cfgOf (protectMany (compile s) (rs ++ [⟨q, q + S.size, q + S.size + T.size, h, k⟩]))) 0 →
      ∃ w, (cfgOf (protectMany (compile s) (rs ++ [⟨q, q + S.size, q + S.size + T.size, h, k⟩]))).Irreducible J w) ∧
    (∃ J : Jungle, J.Valid (cfgOf (protectMany (compile s) (rs ++ [⟨q, q + S.size, q + S.size + T.size, h, k⟩]))) 0) ∧
    (∀ {sol : Nat → Bool} {env : Bool},
      (∀ r ∈ rs ++ [⟨q, q + S.size, q + S.size + T.size, h, k⟩],
        (∀ v, r.h.eval sol env v = (false, v)) ∧ (∀ v, r.k.eval sol env v = (false, v))) →
      ∀ (v : Bool) (res : List Nat × Bool),
        ((∃ f, exec f (compile s) sol env 0 v [] = some res) ↔
          ∃ f, exec f (protectMany (compile s) (rs ++ [⟨q, q + S.size, q + S.size + T.size, h, k⟩])) sol env 0 v [] = some res)) := by
  have hseq : Structured (.seq S T) := hsub.structured hs
  have hr := hsub.range
  simp only [Stmt.size] at hr
  obtain ⟨hok1, o1, o2, o3, o4⟩ := regsOk_append rs _ _ hok
  have hlen : (compile s).length = s.size + 1 := compile_length s
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
  have hrootQ := protectMany_root rs _ hok1 hroot
  have hlQ := protectMany_length rs _ hok1
  have hf1Q := protectMany_fwd (a := q) (b := q + S.size + T.size) rs _ hok1 (fun r' hr' => by simpa using o4 r' hr')
    (by omega) hf1
  have hfLQ := protectMany_fwd (a := q + S.size) (b := q + S.size + T.size) rs _ hok1
    (fun r' hr' => by simpa using o4 r' hr') (by omega) hfL
  have hspec := protectCode_spec (P := protectMany (compile s) rs) (lo := q) (mid := q + S.size)
    (hi := q + S.size + T.size) (h := h) (k := k) (by omega) (by omega)
  have hlen2 := protectCode_length (P := protectMany (compile s) rs) (lo := q) (mid := q + S.size)
    (hi := q + S.size + T.size) (h := h) (k := k) (by omega) (by omega)
  rw [protectMany_append]
  refine ⟨hred, fun hv w => reducible_no_irreducible hv hred w, ?_, ?_, ?_⟩
  · intro J hv
    exact protect_irreducible hspec hlen2 (by omega) (by omega) (by omega) hrootQ hf1Q hfLQ hv
  · have hrf := protect_fwd_root hspec hlen2 (by omega) (by omega) (by omega) hrootQ
    exact ⟨_, dfsRun_valid (blocks_isCFG (by rw [hlen2]; omega) hrf) (Nat.le_refl 1)⟩
  · intro sol env hc v res
    have := protectMany_equiv (sol := sol) (env := env) (rs ++ [⟨q, q + S.size, q + S.size + T.size, h, k⟩]) (compile s)
      hok hc v res
    rw [protectMany_append] at this
    exact this

end SmcIrred.Lang
