module

public import SmcIrred.Lang.CtxLoop
public import SmcIrred.Lang.SubAt

public section

namespace SmcIrred.Lang

/-! # Figure 6(c) inside a larger program (G32 a3, R17b)

`protectCodeD P lo hi h cd` replaces the code of `if (cd) S;` at `[lo, hi)` (the test at `lo`, the body `S` at `lo + 1 .. hi - 1`)
by `if (h) goto labelS; while (cd && trueThenFalse) { labelS: S }`: the entry jump at `lo`, the loop test at `lo + 1`, the body
(shifted by 1) at `lo + 2 .. hi`, the back jump at `hi + 1` and the code after the statement (shifted by 2) at `hi + 2`. -/

@[expose] def mapD (lo t : Nat) : Nat := if t ≤ lo then t else t + 2

@[expose] def remapD (lo : Nat) : Instr → Instr
  | .blk a => .blk a
  | .jmp t => .jmp (mapD lo t)
  | .jmpIf k t => .jmpIf k (mapD lo t)
  | .halt => .halt

@[expose] def gD (lo hi a : Nat) : Nat := if a ≤ lo then a else if a < hi then a + 1 else a + 2

@[expose] def vD (lo hi a : Nat) : Bool := decide (a ≤ lo ∨ hi ≤ a)

@[expose] def protectCodeD (P : List Instr) (lo hi : Nat) (h cd : Cond) : List Instr :=
  (P.take lo).map (remapD lo) ++ (.jmpIf h (lo + 2) :: .jmpIf (.neg (.and cd .ttf)) (hi + 2) ::
    (((P.drop (lo + 1)).take (hi - (lo + 1))).map (shiftI 1) ++ (.jmp (lo + 1) :: (P.drop hi).map (remapD lo))))

structure SpecD (P Q : List Instr) (lo hi : Nat) (h cd : Cond) : Prop where
  pre : ∀ a, a < lo → Q.getD a .halt = remapD lo (P.getD a .halt)
  entry : Q.getD lo .halt = .jmpIf h (lo + 2)
  head : Q.getD (lo + 1) .halt = .jmpIf (.neg (.and cd .ttf)) (hi + 2)
  body : ∀ a, lo + 1 ≤ a → a < hi → Q.getD (a + 1) .halt = shiftI 1 (P.getD a .halt)
  back : Q.getD (hi + 1) .halt = .jmp (lo + 1)
  post : ∀ a, hi ≤ a → Q.getD (a + 2) .halt = remapD lo (P.getD a .halt)

theorem protectCodeD_length {P : List Instr} {lo hi : Nat} {h cd : Cond} (hlh : lo < hi) (hhi : hi ≤ P.length) :
    (protectCodeD P lo hi h cd).length = P.length + 2 := by
  simp only [protectCodeD, List.length_append, List.length_cons, List.length_take, List.length_drop, List.length_map]
  omega

theorem protectCodeD_spec {P : List Instr} {lo hi : Nat} {h cd : Cond} (hlh : lo < hi) (hhi : hi ≤ P.length) :
    SpecD P (protectCodeD P lo hi h cd) lo hi h cd := by
  have hA : ((P.take lo).map (remapD lo)).length = lo := by simp; omega
  have hB : (((P.drop (lo + 1)).take (hi - (lo + 1))).map (shiftI 1)).length = hi - (lo + 1) := by simp; omega
  unfold protectCodeD
  refine ⟨fun a ha => ?_, ?_, ?_, fun a h1 h2 => ?_, ?_, fun a ha => ?_⟩
  · rw [getD_app_l (by omega), getD_mapF _ rfl, getD_takeI P ha]
  · have := getD_app_r ((P.take lo).map (remapD lo)) (.jmpIf h (lo + 2) :: .jmpIf (.neg (.and cd .ttf)) (hi + 2) ::
      (((P.drop (lo + 1)).take (hi - (lo + 1))).map (shiftI 1) ++ (.jmp (lo + 1) :: (P.drop hi).map (remapD lo)))) 0
    rw [hA] at this
    simpa using this
  · have := getD_app_r ((P.take lo).map (remapD lo)) (.jmpIf h (lo + 2) :: .jmpIf (.neg (.and cd .ttf)) (hi + 2) ::
      (((P.drop (lo + 1)).take (hi - (lo + 1))).map (shiftI 1) ++ (.jmp (lo + 1) :: (P.drop hi).map (remapD lo)))) 1
    rw [hA] at this
    simpa using this
  · have e : a + 1 = ((P.take lo).map (remapD lo)).length + ((a - (lo + 1)) + 1 + 1) := by omega
    rw [e, getD_app_r ((P.take lo).map (remapD lo)) _ ((a - (lo + 1)) + 1 + 1)]
    rw [List.getD_cons_succ, List.getD_cons_succ, getD_app_l (by omega), getD_map_shift, getD_takeI _ (by omega),
      getD_dropI]
    congr 2; omega
  · have e : hi + 1 = ((P.take lo).map (remapD lo)).length + ((hi - (lo + 1)) + 1 + 1) := by omega
    rw [e, getD_app_r ((P.take lo).map (remapD lo)) _ ((hi - (lo + 1)) + 1 + 1)]
    rw [List.getD_cons_succ, List.getD_cons_succ]
    have := getD_app_r (((P.drop (lo + 1)).take (hi - (lo + 1))).map (shiftI 1))
      (.jmp (lo + 1) :: (P.drop hi).map (remapD lo)) 0
    rw [hB] at this
    simpa using this
  · have e : a + 2 = ((P.take lo).map (remapD lo)).length + ((hi - (lo + 1)) + 1 + (a - hi) + 1 + 1) := by omega
    rw [e, getD_app_r ((P.take lo).map (remapD lo)) _ ((hi - (lo + 1)) + 1 + (a - hi) + 1 + 1)]
    rw [List.getD_cons_succ, List.getD_cons_succ]
    have := getD_app_r (((P.drop (lo + 1)).take (hi - (lo + 1))).map (shiftI 1))
      (.jmp (lo + 1) :: (P.drop hi).map (remapD lo)) ((a - hi) + 1)
    rw [hB] at this
    rw [show hi - (lo + 1) + 1 + (a - hi) = hi - (lo + 1) + ((a - hi) + 1) by omega, this, List.getD_cons_succ,
      getD_mapF _ rfl, getD_dropI]
    congr 2; omega

/-! ### Simulation -/

/-- The code outside the head is entered and left only at the ends; the head is `if (!cd) goto hi`; the conditions are pure. -/
structure CtxOKD (P : List Instr) (sol : Nat → Bool) (env : Bool) (lo hi : Nat) (cd : Cond) : Prop where
  head : P.getD lo .halt = .jmpIf (.neg cd) hi
  tin : ∀ a t, lo + 1 ≤ a → a < hi → (P.getD a .halt).target = some t → lo + 1 ≤ t ∧ t ≤ hi
  tout : ∀ a t, (a < lo ∨ hi ≤ a) → (P.getD a .halt).target = some t → t ≤ lo ∨ hi ≤ t
  nohalt : ∀ a, lo + 1 ≤ a → a < hi → P.getD a .halt ≠ .halt
  pure : ∀ a k t, P.getD a .halt = .jmpIf k t → PureC sol env k

variable {P Q : List Instr} {lo hi : Nat} {h cd : Cond} {sol : Nat → Bool} {env : Bool}

theorem vD_out {a : Nat} (ha : a ≤ lo ∨ hi ≤ a) : vD lo hi a = true := by simp [vD, ha]

theorem vD_in {a : Nat} (h1 : lo + 1 ≤ a) (h2 : a < hi) : vD lo hi a = false := by
  simp only [vD, decide_eq_false_iff_not]; omega

theorem gD_le {a : Nat} (h1 : a ≤ lo) : gD lo hi a = a := by simp [gD, h1]

theorem gD_in {a : Nat} (h1 : lo + 1 ≤ a) (h2 : a < hi) : gD lo hi a = a + 1 := by
  simp [gD, show ¬ a ≤ lo by omega, h2]

theorem gD_ge {a : Nat} (h1 : hi ≤ a) (hlh : lo < hi) : gD lo hi a = a + 2 := by
  simp [gD, show ¬ a ≤ lo by omega, show ¬ a < hi by omega]

/-- The back jump and the loop test with the variable false and `cd` true: out of the loop with the variable true. -/
theorem runJD (hs : SpecD P Q lo hi h cd) {b0 : Bool} (hb0 : b0 = true) (hcd : ∀ v, cd.eval sol env v = (b0, v))
    {tr : List Nat} {r : List Nat × Bool} (hq : Halts Q sol env (hi + 2) true tr r) :
    Halts Q sol env (hi + 1) false tr r := by
  refine .jmp hs.back (.jmpIf hs.head ?_)
  subst hb0
  simp only [Cond.eval, hcd, ↓reduceIte, Bool.not_false, Bool.not_true]
  simpa using hq

theorem arrOutD (hlh : lo < hi) {t : Nat} (ht : t ≤ lo ∨ hi ≤ t) {tr : List Nat} {r : List Nat × Bool}
    (hq : Halts Q sol env (gD lo hi t) (vD lo hi t) tr r) : Halts Q sol env (mapD lo t) true tr r := by
  by_cases h1 : t ≤ lo
  · rw [gD_le h1, vD_out (Or.inl h1)] at hq
    simpa [mapD, h1] using hq
  · rw [gD_ge (by omega) hlh, vD_out (Or.inr (by omega))] at hq
    simpa [mapD, h1] using hq

theorem arrInD (hs : SpecD P Q lo hi h cd) (hlh : lo < hi) {b0 : Bool} (hb0 : b0 = true)
    (hcd : ∀ v, cd.eval sol env v = (b0, v)) {t : Nat} (ht : lo + 1 ≤ t ∧ t ≤ hi) {tr : List Nat}
    {r : List Nat × Bool} (hq : Halts Q sol env (gD lo hi t) (vD lo hi t) tr r) : Halts Q sol env (t + 1) false tr r := by
  by_cases h1 : t < hi
  · rw [gD_in ht.1 h1, vD_in ht.1 h1] at hq; exact hq
  · have h2 : t = hi := by omega
    subst h2
    rw [gD_ge (Nat.le_refl _) hlh, vD_out (Or.inr (Nat.le_refl _))] at hq
    exact runJD hs hb0 hcd hq

theorem instrQD (hs : SpecD P Q lo hi h cd) (hlh : lo < hi) {pc : Nat} (hne : pc ≠ lo) :
    Q.getD (gD lo hi pc) .halt =
      if lo + 1 ≤ pc ∧ pc < hi then shiftI 1 (P.getD pc .halt) else remapD lo (P.getD pc .halt) := by
  by_cases h1 : pc < lo
  · rw [gD_le (by omega), if_neg (by omega)]; exact hs.pre pc h1
  · by_cases h2 : pc < hi
    · rw [gD_in (by omega) h2, if_pos ⟨by omega, h2⟩]; exact hs.body pc (by omega) h2
    · rw [gD_ge (by omega) hlh, if_neg (by omega)]; exact hs.post pc (by omega)

theorem succ_arrD (hs : SpecD P Q lo hi h cd) (hlh : lo < hi) {b0 : Bool} (hcd : ∀ v, cd.eval sol env v = (b0, v))
    {pc : Nat} (hne : pc ≠ lo) (hg : lo + 1 ≤ pc → pc < hi → b0 = true) {tr : List Nat} {r : List Nat × Bool}
    (hq : Halts Q sol env (gD lo hi (pc + 1)) (vD lo hi (pc + 1)) tr r) :
    Halts Q sol env (gD lo hi pc + 1) (vD lo hi pc) tr r := by
  by_cases h1 : pc < lo
  · rw [gD_le (by omega), vD_out (Or.inl (by omega))]
    rw [gD_le (by omega), vD_out (Or.inl (by omega))] at hq
    exact hq
  · by_cases h2 : pc < hi
    · have := arrInD hs hlh (hg (by omega) h2) hcd (t := pc + 1) ⟨by omega, by omega⟩ hq
      rw [gD_in (by omega) h2, vD_in (by omega) h2]
      exact this
    · rw [gD_ge (by omega) hlh, vD_out (Or.inr (by omega))]
      rw [gD_ge (by omega) hlh, vD_out (Or.inr (by omega))] at hq
      exact hq

theorem ctx_fwdD (hs : SpecD P Q lo hi h cd) (hlh : lo + 1 < hi) (hc : CtxOKD P sol env lo hi cd) {b0 : Bool}
    (hcd : ∀ v, cd.eval sol env v = (b0, v)) (hh : h.eval sol env true = (false, true))
    {pc : Nat} {v : Bool} {tr : List Nat} {r : List Nat × Bool} (hp : Halts P sol env pc v tr r) :
    v = true → (lo + 1 ≤ pc → pc < hi → b0 = true) → Halts Q sol env (gD lo hi pc) (vD lo hi pc) tr r := by
  induction hp with
  | @halt pc v tr hi' =>
    intro hv hg; subst hv
    have hne : pc ≠ lo := by
      intro e; rw [e, hc.head] at hi'; cases hi'
    have hout : pc ≤ lo ∨ hi ≤ pc := by
      by_cases hn : pc ≤ lo ∨ hi ≤ pc
      · exact hn
      · exact absurd hi' (hc.nohalt pc (by omega) (by omega))
    have hq : Q.getD (gD lo hi pc) .halt = .halt := by
      rw [instrQD hs (by omega) hne, if_neg (by omega), hi']; rfl
    rw [vD_out hout]
    exact .halt hq
  | @blk pc a v tr r hi' _ ih =>
    intro hv hg; subst hv
    have hne : pc ≠ lo := by
      intro e; rw [e, hc.head] at hi'; cases hi'
    have hq : Q.getD (gD lo hi pc) .halt = .blk a := by
      rw [instrQD hs (by omega) hne]; split <;> rw [hi'] <;> rfl
    refine .blk hq (succ_arrD hs (by omega) hcd hne hg (ih rfl ?_))
    intro h1 h2
    exact hg (by omega) (by omega)
  | @jmp pc t v tr r hi' _ ih =>
    intro hv hg; subst hv
    have hne : pc ≠ lo := by
      intro e; rw [e, hc.head] at hi'; cases hi'
    have ht : (P.getD pc .halt).target = some t := by rw [hi']; rfl
    by_cases hin : lo + 1 ≤ pc ∧ pc < hi
    · have hb := hg hin.1 hin.2
      have hq : Q.getD (gD lo hi pc) .halt = .jmp (t + 1) := by rw [instrQD hs (by omega) hne, if_pos hin, hi']; rfl
      have htt := hc.tin pc t hin.1 hin.2 ht
      have hq' := arrInD hs (by omega) hb hcd htt (ih rfl (fun h1 h2 => hb))
      rw [vD_in hin.1 hin.2]
      exact .jmp hq hq'
    · have hq : Q.getD (gD lo hi pc) .halt = .jmp (mapD lo t) := by
        rw [instrQD hs (by omega) hne, if_neg hin, hi']; rfl
      have htt := hc.tout pc t (by omega) ht
      rw [vD_out (by omega)]
      refine .jmp hq (arrOutD (by omega) htt (ih rfl ?_))
      intro h1 h2
      omega
  | @jmpIf pc t kk v tr r hi' _ ih =>
    intro hv hg; subst hv
    by_cases hpl : pc = lo
    · -- the head of the statement
      have hpl' : lo = pc := hpl.symm
      subst hpl'
      rw [hc.head] at hi'
      cases hi'
      rw [gD_le (Nat.le_refl _), vD_out (Or.inl (Nat.le_refl _))]
      refine .jmpIf hs.entry ?_
      rw [hh]
      simp only [Bool.false_eq_true, ↓reduceIte]
      refine .jmpIf hs.head ?_
      have hneg : (Cond.neg cd).eval sol env true = (!b0, true) := by simp [Cond.eval, hcd]
      rw [hneg] at ih
      cases hb : b0
      · rw [hb] at ih
        simp only [Bool.not_false, ↓reduceIte] at ih
        have := ih (by first | rfl | trivial) (by first | trivial | (intro h1 h2; omega) | exact fun _ _ => hb | exact fun _ _ => trivial)
        rw [gD_ge (Nat.le_refl _) (by omega), vD_out (Or.inr (Nat.le_refl _))] at this
        simpa [Cond.eval, hcd, hb] using this
      · rw [hb] at ih
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at ih
        have := ih (by first | rfl | trivial) (by first | trivial | (intro h1 h2; omega) | exact fun _ _ => hb | exact fun _ _ => trivial)
        rw [gD_in (by omega) (by omega), vD_in (by omega) (by omega)] at this
        simpa [Cond.eval, hcd, hb] using this
    · have ht : (P.getD pc .halt).target = some t := by rw [hi']; rfl
      obtain ⟨b, hb⟩ := hc.pure pc kk t hi'
      have hbt : kk.eval sol env true = (b, true) := hb true
      rw [hbt] at ih
      by_cases hin : lo + 1 ≤ pc ∧ pc < hi
      · have hbb := hg hin.1 hin.2
        have hq : Q.getD (gD lo hi pc) .halt = .jmpIf kk (t + 1) := by
          rw [instrQD hs (by omega) hpl, if_pos hin, hi']; rfl
        rw [vD_in hin.1 hin.2]
        refine .jmpIf hq ?_
        rw [hb false]
        cases b
        · simp only [Bool.false_eq_true, ↓reduceIte] at ih ⊢
          have := succ_arrD hs (by omega) hcd hpl hg (ih trivial (by
            intro h1 h2
            exact hg (by omega) (by omega)))
          rw [vD_in hin.1 hin.2] at this
          exact this
        · simp only [↓reduceIte] at ih ⊢
          exact arrInD hs (by omega) hbb hcd (hc.tin pc t hin.1 hin.2 ht) (ih trivial (fun h1 h2 => hbb))
      · have hq : Q.getD (gD lo hi pc) .halt = .jmpIf kk (mapD lo t) := by
          rw [instrQD hs (by omega) hpl, if_neg hin, hi']; rfl
        rw [vD_out (by omega)]
        refine .jmpIf hq ?_
        rw [hbt]
        cases b
        · simp only [Bool.false_eq_true, ↓reduceIte] at ih ⊢
          have := succ_arrD hs (by omega) hcd hpl hg (ih trivial (by
            intro h1 h2
            omega))
          rw [vD_out (by omega)] at this
          exact this
        · simp only [↓reduceIte] at ih ⊢
          exact arrOutD (by omega) (hc.tout pc t (by omega) ht) (ih trivial (by
            intro h1 h2
            have := hc.tout pc t (by omega) ht
            omega))


/-! ### Backward direction -/

@[expose] def RelD (lo hi : Nat) (b0 : Bool) (pP pQ : Nat) (vQ : Bool) : Prop :=
  (pQ = gD lo hi pP ∧ vQ = vD lo hi pP ∧ (lo + 1 ≤ pP → pP < hi → b0 = true)) ∨ (pP = lo ∧ pQ = lo + 1 ∧ vQ = true) ∨
    (pP = hi ∧ pQ = hi + 1 ∧ vQ = false ∧ b0 = true) ∨ (pP = hi ∧ pQ = lo + 1 ∧ vQ = false ∧ b0 = true)

theorem relT_outD (hlh : lo < hi) {b0 : Bool} {t : Nat} (ht : t ≤ lo ∨ hi ≤ t) :
    RelD lo hi b0 t (mapD lo t) true := by
  left
  by_cases h1 : t ≤ lo
  · rw [gD_le h1, vD_out (Or.inl h1)]
    exact ⟨by simp [mapD, h1], rfl, fun h2 h3 => by omega⟩
  · rw [gD_ge (by omega) hlh, vD_out (Or.inr (by omega))]
    exact ⟨by simp [mapD, h1], rfl, fun h2 h3 => by omega⟩

theorem relT_inD (hlh : lo < hi) {b0 : Bool} (hb0 : b0 = true) {t : Nat} (ht : lo + 1 ≤ t ∧ t ≤ hi) :
    RelD lo hi b0 t (t + 1) false := by
  by_cases h1 : t < hi
  · left; rw [gD_in ht.1 h1, vD_in ht.1 h1]; exact ⟨rfl, rfl, fun _ _ => hb0⟩
  · right; right; left; exact ⟨by omega, by omega, rfl, hb0⟩

theorem relSD (hlh : lo < hi) {b0 : Bool} {pc : Nat} (hne : pc ≠ lo) (hg : lo + 1 ≤ pc → pc < hi → b0 = true) :
    RelD lo hi b0 (pc + 1) (gD lo hi pc + 1) (vD lo hi pc) := by
  by_cases h1 : pc < lo
  · rw [gD_le (by omega), vD_out (Or.inl (by omega))]
    left
    rw [gD_le (by omega), vD_out (Or.inl (by omega))]
    exact ⟨rfl, rfl, fun h2 h3 => by omega⟩
  · by_cases h2 : pc < hi
    · have hb := hg (by omega) h2
      rw [gD_in (by omega) h2, vD_in (by omega) h2]
      by_cases h3 : pc + 1 < hi
      · left; rw [gD_in (by omega) h3, vD_in (by omega) h3]; exact ⟨rfl, rfl, fun _ _ => hb⟩
      · right; right; left; exact ⟨by omega, by omega, rfl, hb⟩
    · rw [gD_ge (by omega) hlh, vD_out (Or.inr (by omega))]
      left
      rw [gD_ge (by omega) hlh, vD_out (Or.inr (by omega))]
      exact ⟨rfl, rfl, fun h2 h3 => by omega⟩

theorem instrQD_blk (hs : SpecD P Q lo hi h cd) (hlh : lo < hi) {pc a : Nat} (hne : pc ≠ lo)
    (hq : Q.getD (gD lo hi pc) .halt = .blk a) : P.getD pc .halt = .blk a := by
  rw [instrQD hs hlh hne] at hq
  by_cases hin : lo + 1 ≤ pc ∧ pc < hi
  · rw [if_pos hin] at hq
    cases hp : P.getD pc .halt with
    | blk a' => rw [hp] at hq; simp only [shiftI, Instr.blk.injEq] at hq; rw [hq]
    | jmp t => rw [hp] at hq; simp [shiftI] at hq
    | jmpIf k t => rw [hp] at hq; simp [shiftI] at hq
    | halt => rw [hp] at hq; simp [shiftI] at hq
  · rw [if_neg hin] at hq
    cases hp : P.getD pc .halt with
    | blk a' => rw [hp] at hq; simp only [remapD, Instr.blk.injEq] at hq; rw [hq]
    | jmp t => rw [hp] at hq; simp [remapD] at hq
    | jmpIf k t => rw [hp] at hq; simp [remapD] at hq
    | halt => rw [hp] at hq; simp [remapD] at hq

theorem instrQD_halt (hs : SpecD P Q lo hi h cd) (hlh : lo < hi) {pc : Nat} (hne : pc ≠ lo)
    (hq : Q.getD (gD lo hi pc) .halt = .halt) : P.getD pc .halt = .halt := by
  rw [instrQD hs hlh hne] at hq
  by_cases hin : lo + 1 ≤ pc ∧ pc < hi
  · rw [if_pos hin] at hq
    cases hp : P.getD pc .halt with
    | blk a' => rw [hp] at hq; simp [shiftI] at hq
    | jmp t => rw [hp] at hq; simp [shiftI] at hq
    | jmpIf k t => rw [hp] at hq; simp [shiftI] at hq
    | halt => rfl
  · rw [if_neg hin] at hq
    cases hp : P.getD pc .halt with
    | blk a' => rw [hp] at hq; simp [remapD] at hq
    | jmp t => rw [hp] at hq; simp [remapD] at hq
    | jmpIf k t => rw [hp] at hq; simp [remapD] at hq
    | halt => rfl

theorem instrQD_jmp (hs : SpecD P Q lo hi h cd) (hlh : lo < hi) {pc t' : Nat} (hne : pc ≠ lo)
    (hq : Q.getD (gD lo hi pc) .halt = .jmp t') :
    ∃ t, P.getD pc .halt = .jmp t ∧ t' = (if lo + 1 ≤ pc ∧ pc < hi then t + 1 else mapD lo t) := by
  rw [instrQD hs hlh hne] at hq
  by_cases hin : lo + 1 ≤ pc ∧ pc < hi
  · rw [if_pos hin] at hq
    cases hp : P.getD pc .halt with
    | blk a' => rw [hp] at hq; simp [shiftI] at hq
    | jmp t =>
      rw [hp] at hq; simp only [shiftI, Instr.jmp.injEq] at hq
      exact ⟨t, rfl, by rw [if_pos hin]; omega⟩
    | jmpIf k t => rw [hp] at hq; simp [shiftI] at hq
    | halt => rw [hp] at hq; simp [shiftI] at hq
  · rw [if_neg hin] at hq
    cases hp : P.getD pc .halt with
    | blk a' => rw [hp] at hq; simp [remapD] at hq
    | jmp t =>
      rw [hp] at hq; simp only [remapD, Instr.jmp.injEq] at hq
      exact ⟨t, rfl, by rw [if_neg hin]; omega⟩
    | jmpIf k t => rw [hp] at hq; simp [remapD] at hq
    | halt => rw [hp] at hq; simp [remapD] at hq

theorem instrQD_jmpIf (hs : SpecD P Q lo hi h cd) (hlh : lo < hi) {pc t' : Nat} {kk : Cond} (hne : pc ≠ lo)
    (hq : Q.getD (gD lo hi pc) .halt = .jmpIf kk t') :
    ∃ t, P.getD pc .halt = .jmpIf kk t ∧ t' = (if lo + 1 ≤ pc ∧ pc < hi then t + 1 else mapD lo t) := by
  rw [instrQD hs hlh hne] at hq
  by_cases hin : lo + 1 ≤ pc ∧ pc < hi
  · rw [if_pos hin] at hq
    cases hp : P.getD pc .halt with
    | blk a' => rw [hp] at hq; simp [shiftI] at hq
    | jmp t => rw [hp] at hq; simp [shiftI] at hq
    | jmpIf k t =>
      rw [hp] at hq; simp only [shiftI, Instr.jmpIf.injEq] at hq
      obtain ⟨rfl, h2⟩ := hq
      exact ⟨t, rfl, by rw [if_pos hin]; omega⟩
    | halt => rw [hp] at hq; simp [shiftI] at hq
  · rw [if_neg hin] at hq
    cases hp : P.getD pc .halt with
    | blk a' => rw [hp] at hq; simp [remapD] at hq
    | jmp t => rw [hp] at hq; simp [remapD] at hq
    | jmpIf k t =>
      rw [hp] at hq; simp only [remapD, Instr.jmpIf.injEq] at hq
      obtain ⟨rfl, h2⟩ := hq
      exact ⟨t, rfl, by rw [if_neg hin]; omega⟩
    | halt => rw [hp] at hq; simp [remapD] at hq

theorem ctx_bwdD (hs : SpecD P Q lo hi h cd) (hlh : lo + 1 < hi) (hc : CtxOKD P sol env lo hi cd) {b0 : Bool}
    (hcd : ∀ v, cd.eval sol env v = (b0, v)) (hh : h.eval sol env true = (false, true))
    {pcQ : Nat} {vQ : Bool} {tr : List Nat} {r : List Nat × Bool} (hq : Halts Q sol env pcQ vQ tr r) :
    ∀ pP, RelD lo hi b0 pP pcQ vQ → Halts P sol env pP true tr r := by
  induction hq with
  | @halt pcQ v tr hi' =>
    intro pP hr
    rcases hr with ⟨h1, h2, h3⟩ | ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩
    · by_cases hpl : pP = lo
      · have hlo : lo = pP := hpl.symm
        subst hlo
        rw [gD_le (Nat.le_refl _)] at h1
        have h1' : lo = pcQ := h1.symm
        subst h1'
        rw [hs.entry] at hi'; cases hi'
      · subst h1; subst h2
        have hP := instrQD_halt hs (by omega) hpl hi'
        have hout : pP ≤ lo ∨ hi ≤ pP := by
          by_cases hn : pP ≤ lo ∨ hi ≤ pP
          · exact hn
          · exact absurd hP (hc.nohalt pP (by omega) (by omega))
        rw [vD_out hout]
        exact .halt hP
    · rw [hs.head] at hi'; cases hi'
    · rw [hs.back] at hi'; cases hi'
    · rw [hs.head] at hi'; cases hi'
  | @blk pcQ a v tr r hi' _ ih =>
    intro pP hr
    rcases hr with ⟨h1, h2, h3⟩ | ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩
    · by_cases hpl : pP = lo
      · have hlo : lo = pP := hpl.symm
        subst hlo
        rw [gD_le (Nat.le_refl _)] at h1
        have h1' : lo = pcQ := h1.symm
        subst h1'
        rw [hs.entry] at hi'; cases hi'
      · subst h1; subst h2
        exact .blk (instrQD_blk hs (by omega) hpl hi') (ih (pP + 1) (relSD (by omega) hpl h3))
    · rw [hs.head] at hi'; cases hi'
    · rw [hs.back] at hi'; cases hi'
    · rw [hs.head] at hi'; cases hi'
  | @jmp pcQ t' v tr r hi' _ ih =>
    intro pP hr
    rcases hr with ⟨h1, h2, h3⟩ | ⟨_, rfl, _⟩ | ⟨hP, rfl, hv, _⟩ | ⟨_, rfl, _⟩
    · by_cases hpl : pP = lo
      · have hlo : lo = pP := hpl.symm
        subst hlo
        rw [gD_le (Nat.le_refl _)] at h1
        have h1' : lo = pcQ := h1.symm
        subst h1'
        rw [hs.entry] at hi'; cases hi'
      · subst h1; subst h2
        obtain ⟨t, hP, ht'⟩ := instrQD_jmp hs (by omega) hpl hi'
        have htg : (P.getD pP .halt).target = some t := by rw [hP]; rfl
        refine .jmp hP ?_
        by_cases hin : lo + 1 ≤ pP ∧ pP < hi
        · rw [if_pos hin] at ht'; subst ht'
          exact ih t (by rw [vD_in hin.1 hin.2]; exact relT_inD (by omega) (h3 hin.1 hin.2) (hc.tin pP t hin.1 hin.2 htg))
        · rw [if_neg hin] at ht'; subst ht'
          exact ih t (by rw [vD_out (by omega)]; exact relT_outD (by omega) (hc.tout pP t (by omega) htg))
    · rw [hs.head] at hi'; cases hi'
    · rw [hs.back] at hi'
      cases hi'
      rw [hP]
      exact ih hi (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, hv, by assumption⟩)))
    · rw [hs.head] at hi'; cases hi'
  | @jmpIf pcQ t' kk v tr r hi' hrest ih =>
    intro pP hr
    rcases hr with ⟨h1, h2, h3⟩ | ⟨hP, hQ, hv⟩ | ⟨_, rfl, _⟩ | ⟨hP, hQ, hv, hb0⟩
    · by_cases hpl : pP = lo
      · -- the entry test
        have hlo : lo = pP := hpl.symm
        subst hlo
        rw [gD_le (Nat.le_refl _)] at h1
        have h1' : lo = pcQ := h1.symm
        subst h1'
        rw [vD_out (Or.inl (Nat.le_refl _))] at h2
        subst h2
        rw [hs.entry] at hi'
        cases hi'
        rw [hh] at ih
        simp only [Bool.false_eq_true, ↓reduceIte] at ih
        exact ih lo (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))
      · subst h1; subst h2
        obtain ⟨t, hP, ht'⟩ := instrQD_jmpIf hs (by omega) hpl hi'
        have htg : (P.getD pP .halt).target = some t := by rw [hP]; rfl
        obtain ⟨b, hb⟩ := hc.pure pP kk t hP
        refine .jmpIf hP ?_
        rw [hb true]
        rw [hb (vD lo hi pP)] at ih hrest
        by_cases hin : lo + 1 ≤ pP ∧ pP < hi
        · rw [if_pos hin] at ht'; subst ht'
          cases b
          · simp only [Bool.false_eq_true, ↓reduceIte] at ih ⊢
            exact ih (pP + 1) (relSD (by omega) hpl h3)
          · simp only [↓reduceIte] at ih ⊢
            exact ih t (by rw [vD_in hin.1 hin.2]; exact relT_inD (by omega) (h3 hin.1 hin.2) (hc.tin pP t hin.1 hin.2 htg))
        · rw [if_neg hin] at ht'; subst ht'
          cases b
          · simp only [Bool.false_eq_true, ↓reduceIte] at ih ⊢
            exact ih (pP + 1) (relSD (by omega) hpl h3)
          · simp only [↓reduceIte] at ih ⊢
            exact ih t (by rw [vD_out (by omega)]; exact relT_outD (by omega) (hc.tout pP t (by omega) htg))
    · -- the loop test entered from the entry test: the variable is true
      have hQ' : lo + 1 = pcQ := hQ.symm
      subst hQ'
      subst hv
      rw [hP]
      rw [hs.head] at hi'
      cases hi'
      refine .jmpIf hc.head ?_
      have hneg : (Cond.neg cd).eval sol env true = (!b0, true) := by simp [Cond.eval, hcd]
      rw [hneg]
      cases hb : b0
      · simp only [Cond.eval, hcd, hb, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.not_true] at ih ⊢
        have := ih hi (Or.inl ⟨by rw [gD_ge (Nat.le_refl _) (by omega)], by rw [vD_out (Or.inr (Nat.le_refl _))],
          fun h1 h2 => by omega⟩)
        exact this
      · simp only [Cond.eval, hcd, hb, ↓reduceIte, Bool.not_true, Bool.false_eq_true] at ih ⊢
        exact ih (lo + 1) (Or.inl ⟨by rw [gD_in (Nat.le_refl _) (by omega)],
          by rw [vD_in (Nat.le_refl _) (by omega)], fun _ _ => rfl⟩)
    · rw [hs.back] at hi'; cases hi'
    · -- the loop test entered from the back jump: the variable is false, `cd` true, so out of the loop
      have hQ' : lo + 1 = pcQ := hQ.symm
      subst hQ'
      subst hv
      rw [hP]
      rw [hs.head] at hi'
      cases hi'
      subst hb0
      simp only [Cond.eval, hcd, ↓reduceIte, Bool.not_false, Bool.not_true] at ih
      simpa using ih hi (Or.inl ⟨by rw [gD_ge (Nat.le_refl _) (by omega)], by rw [vD_out (Or.inr (Nat.le_refl _))],
        fun h1 h2 => by omega⟩)

theorem ctx_equivD (hs : SpecD P Q lo hi h cd) (hlh : lo + 1 < hi) (hc : CtxOKD P sol env lo hi cd) {b0 : Bool}
    (hcd : ∀ v, cd.eval sol env v = (b0, v)) (hh : h.eval sol env true = (false, true)) (r : List Nat × Bool) :
    (∃ f, exec f P sol env 0 true [] = some r) ↔ ∃ f, exec f Q sol env 0 true [] = some r := by
  rw [← halts_iff_exec, ← halts_iff_exec]
  constructor
  · intro hp
    have := ctx_fwdD hs hlh hc hcd hh hp rfl (fun h1 h2 => by omega)
    rw [gD_le (Nat.zero_le _), vD_out (Or.inl (Nat.zero_le _))] at this
    exact this
  · intro hq
    exact ctx_bwdD hs hlh hc hcd hh hq 0
      (Or.inl ⟨by rw [gD_le (Nat.zero_le _)], by rw [vD_out (Or.inl (Nat.zero_le _))], fun h1 h2 => by omega⟩)

/-! ### Forward paths and the irreducible loop -/

theorem stepQ_inD (hs : SpecD P Q lo hi h cd) {a c : Nat} (h1 : lo + 1 ≤ a) (h2 : a < hi) (hp : StepI P a c) :
    StepI Q (a + 1) (c + 1) := by
  unfold StepI at hp ⊢
  rw [hs.body a h1 h2]
  cases hi' : P.getD a .halt <;> simp only [hi', shiftI] at hp ⊢
  · subst hp; rfl
  · subst hp; rfl
  · rcases hp with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl

theorem stepQ_preD (hs : SpecD P Q lo hi h cd) {a c : Nat} (h1 : a < lo) (hc : c ≤ lo) (hp : StepI P a c) :
    StepI Q a c := by
  unfold StepI at hp ⊢
  rw [hs.pre a h1]
  cases hi' : P.getD a .halt <;> simp only [hi', remapD] at hp ⊢
  · subst hp; simp [mapD, hc]
  · subst hp; simp [mapD, hc]
  · rcases hp with rfl | rfl
    · exact Or.inl (by simp [mapD, hc])
    · exact Or.inr rfl

theorem stepQ_pre_farD (hs : SpecD P Q lo hi h cd) {a c : Nat} (h1 : a < lo) (hc : lo < c)
    (ht : (P.getD a .halt).target = some c) : StepI Q a (c + 2) := by
  unfold StepI
  rw [hs.pre a h1]
  cases hi' : P.getD a .halt <;> simp only [hi', Instr.target] at ht
  · cases ht
  · cases ht; simp [remapD, mapD, show ¬ c ≤ lo by omega]
  · cases ht; exact Or.inl (by simp [mapD, show ¬ c ≤ lo by omega])
  · cases ht

theorem stepQ_postD (hs : SpecD P Q lo hi h cd) {a c : Nat} (h1 : hi ≤ a) (hc : lo < c) (hp : StepI P a c) :
    StepI Q (a + 2) (c + 2) := by
  unfold StepI at hp ⊢
  rw [hs.post a h1]
  cases hi' : P.getD a .halt <;> simp only [hi', remapD] at hp ⊢
  · subst hp; rfl
  · subst hp; simp [mapD, show ¬ c ≤ lo by omega]
  · rcases hp with rfl | rfl
    · exact Or.inl (by simp [mapD, show ¬ c ≤ lo by omega])
    · exact Or.inr rfl

theorem fwd_preD (hs : SpecD P Q lo hi h cd) {a b : Nat} (hp : Fwd (StepI P) a b) (hb : b ≤ lo) :
    Fwd (StepI Q) a b := by
  induction hp with
  | refl => exact .refl _
  | @step a c b hr hlt hrest ih =>
    have hcb := hrest.le
    exact .step (stepQ_preD hs (by omega) (by omega) hr) hlt (ih hb)

theorem fwd_shift1 (hs : SpecD P Q lo hi h cd) {a b : Nat} (hp : Fwd (StepI P) a b) (ha : lo + 1 ≤ a) (hb : b ≤ hi) :
    Fwd (StepI Q) (a + 1) (b + 1) := by
  induction hp with
  | refl => exact .refl _
  | @step a c b hr hlt hrest ih =>
    have hcb := hrest.le
    exact .step (stepQ_inD hs ha (by omega) hr) (by omega) (ih (by omega) hb)

theorem ctx_not_reducibleD (hs : SpecD P Q lo hi h cd) (hlh : lo + 1 < hi) (hhP : hi < P.length)
    (hlen : Q.length = P.length + 2) (hhead : P.getD lo .halt = .jmpIf (.neg cd) hi)
    (htin : ∀ a t, lo + 1 ≤ a → a < hi → (P.getD a .halt).target = some t → lo + 1 ≤ t ∧ t ≤ hi)
    (htout : ∀ a t, (a < lo ∨ hi ≤ a) → (P.getD a .halt).target = some t → t ≤ lo ∨ hi ≤ t)
    (hroot : ∀ x, x < P.length → Fwd (StepI P) 0 x) (hf1 : Fwd (StepI P) (lo + 1) hi) :
    ¬ (cfgOf Q).Reducible 0 ∧ ∀ x, x < Q.length → Fwd (StepI Q) 0 x := by
  have hE : StepI Q lo (lo + 1) := by unfold StepI; rw [hs.entry]; exact Or.inr rfl
  have hEj : StepI Q lo (lo + 2) := by unfold StepI; rw [hs.entry]; exact Or.inl rfl
  have hHs : StepI Q (lo + 1) (lo + 2) := by unfold StepI; rw [hs.head]; exact Or.inr rfl
  have hHj : StepI Q (lo + 1) (hi + 2) := by unfold StepI; rw [hs.head]; exact Or.inl rfl
  have hJ : StepI Q (hi + 1) (lo + 1) := by unfold StepI; rw [hs.back]
  have hQlo : Fwd (StepI Q) 0 lo := fwd_preD hs (hroot lo (by omega)) (Nat.le_refl _)
  have hH : Fwd (StepI Q) 0 (lo + 1) := Fwd.trans hQlo (.step hE (by omega) (.refl _))
  have hH2 : Fwd (StepI Q) 0 (lo + 2) := Fwd.trans hH (.step hHs (by omega) (.refl _))
  have hX : Fwd (StepI Q) 0 (hi + 2) := Fwd.trans hH (.step hHj (by omega) (.refl _))
  have hstep : ∀ a c, StepI P a c → a < c → Fwd (StepI Q) 0 (gD lo hi a) → Fwd (StepI Q) 0 (gD lo hi c) := by
    intro a c hp hac hq
    by_cases h1 : a < lo
    · have hcs := step_cases hp
      have hco : c ≤ lo ∨ hi ≤ c := by
        rcases hcs with rfl | ht
        · left; omega
        · exact htout a c (Or.inl h1) ht
      rw [gD_le (by omega)] at hq
      by_cases h2 : c ≤ lo
      · rw [gD_le h2]
        exact Fwd.trans hq (.step (stepQ_preD hs h1 h2 hp) hac (.refl _))
      · rw [gD_ge (by omega) (by omega)]
        have hmo : StepI Q a (c + 2) := by
          rcases hcs with rfl | ht
          · omega
          · exact stepQ_pre_farD hs h1 (by omega) ht
        exact Fwd.trans hq (.step hmo (by omega) (.refl _))
    · by_cases h1' : a = lo
      · subst h1'
        unfold StepI at hp
        rw [hhead] at hp
        rw [gD_le (Nat.le_refl _)] at hq
        rcases hp with rfl | rfl
        · rw [gD_ge (Nat.le_refl _) (by omega)]; exact hX
        · rw [gD_in (Nat.le_refl _) (by omega)]; exact hH2
      · by_cases h2 : a < hi
        · have hcs := step_cases hp
          have hci : lo + 1 ≤ c ∧ c ≤ hi := by
            rcases hcs with rfl | ht
            · omega
            · exact htin a c (by omega) h2 ht
          rw [gD_in (by omega) h2] at hq
          by_cases h3 : c < hi
          · rw [gD_in hci.1 h3]
            exact Fwd.trans hq (.step (stepQ_inD hs (by omega) h2 hp) (by omega) (.refl _))
          · have : c = hi := by omega
            subst this
            rw [gD_ge (Nat.le_refl _) (by omega)]
            exact hX
        · rw [gD_ge (by omega) (by omega)] at hq
          rw [gD_ge (by omega) (by omega)]
          exact Fwd.trans hq (.step (stepQ_postD hs (by omega) (by omega) hp) (by omega) (.refl _))
  have hcq : ∀ y, Fwd (StepI P) 0 y → Fwd (StepI Q) 0 (gD lo hi y) := by
    intro y hy
    have key : ∀ a b, Fwd (StepI P) a b → Fwd (StepI Q) 0 (gD lo hi a) → Fwd (StepI Q) 0 (gD lo hi b) := by
      intro a b hab
      induction hab with
      | refl => intro h; exact h
      | @step a c b hr hlt _ ih => intro h; exact ih (hstep a c hr hlt h)
    exact key 0 y hy (by rw [gD_le (Nat.zero_le _)]; exact .refl _)
  have hroot' : ∀ x, x < Q.length → Fwd (StepI Q) 0 x := by
    intro x hx
    by_cases h1 : x < lo
    · exact fwd_preD hs (hroot x (by omega)) (by omega)
    · by_cases h2 : x = lo
      · subst h2; exact hQlo
      · by_cases h3 : x = lo + 1
        · subst h3; exact hH
        · by_cases h4 : x ≤ hi
          · have := hcq (x - 1) (hroot (x - 1) (by omega))
            rw [gD_in (by omega) (by omega)] at this
            simpa [show x - 1 + 1 = x by omega] using this
          · by_cases h5 : x = hi + 1
            · subst h5
              exact Fwd.trans hH2 (fwd_shift1 hs hf1 (Nat.le_refl _) (Nat.le_refl _))
            · have := hcq (x - 2) (hroot (x - 2) (by omega))
              rw [gD_ge (by omega) (by omega)] at this
              simpa [show x - 2 + 2 = x by omega] using this
  refine ⟨?_, hroot'⟩
  have hf1Q : Fwd (StepI Q) (lo + 1) (hi + 1) :=
    .step hHs (by omega) (fwd_shift1 hs hf1 (Nat.le_refl _) (Nat.le_refl _))
  have hfLQ : Fwd (StepI Q) (lo + 2) (hi + 1) := fwd_shift1 hs hf1 (Nat.le_refl _) (Nat.le_refl _)
  exact entry_cycle_not_reducible Q (e0 := lo) (L := lo + 2) (c := hi + 1) (h := h) (by omega) hs.entry hroot'
    (by omega) (by omega) hf1Q hfLQ hJ

/-! ### Figure 6(c) inside any goto-free program -/

theorem ctx_head {s : Stmt} {q : Nat} {cd : Cond} {S : Stmt} (hsub : Sub (.ite1 cd S) q s 0) :
    (compile s).getD q .halt = .jmpIf (.neg cd) (q + 1 + S.size) := by
  have hat := hsub.atAddr (labelsOf 0 s) (compile_at s)
  have := hat.get (j := 0) (by rw [comp_length]; simp only [Stmt.size]; omega)
  simpa [comp] using this

theorem protectD_structured {s S : Stmt} {q : Nat} {cd : Cond} (hs : Structured s) (hsub : Sub (.ite1 cd S) q s 0)
    (hS : 1 ≤ S.size) (h : Cond) :
    (cfgOf (compile s)).Reducible 0 ∧
    (∀ {J : Jungle}, J.Valid (cfgOf (compile s)) 0 → ∀ w, ¬ (cfgOf (compile s)).Irreducible J w) ∧
    (∀ {J : Jungle}, J.Valid (cfgOf (protectCodeD (compile s) q (q + 1 + S.size) h cd)) 0 →
      ∃ w, (cfgOf (protectCodeD (compile s) q (q + 1 + S.size) h cd)).Irreducible J w) ∧
    (∃ J : Jungle, J.Valid (cfgOf (protectCodeD (compile s) q (q + 1 + S.size) h cd)) 0) ∧
    (∀ {sol : Nat → Bool} {env : Bool}, PureS sol env s → h.eval sol env true = (false, true) →
      ∀ (r : List Nat × Bool),
        ((∃ f, exec f (compile s) sol env 0 true [] = some r) ↔
          ∃ f, exec f (protectCodeD (compile s) q (q + 1 + S.size) h cd) sol env 0 true [] = some r)) := by
  have hite : Structured (.ite1 cd S) := hsub.structured hs
  have hr := hsub.range
  simp only [Stmt.size] at hr
  have hlen : (compile s).length = s.size + 1 := compile_length s
  have hhP : q + 1 + S.size < (compile s).length := by omega
  have hspec := protectCodeD_spec (P := compile s) (lo := q) (hi := q + 1 + S.size) (h := h) (cd := cd)
    (by omega) (by omega)
  have hlenQ := protectCodeD_length (P := compile s) (lo := q) (hi := q + 1 + S.size) (h := h) (cd := cd)
    (by omega) (by omega)
  have hroot : ∀ x, x < (compile s).length → Fwd (StepI (compile s)) 0 x := fun x hx =>
    (sstep_fwd s hs 0 x (by omega) (by omega)).mono (fun a c => sstep_stepI hs)
  have hf1 : Fwd (StepI (compile s)) (q + 1) (q + 1 + S.size) :=
    (sstep_fwd S hite (q + 1) _ (by omega) (by omega)).mono
      (fun a c hh' => sstep_stepI hs (hsub.sstep (.ite1_body hh')))
  have hhead := ctx_head hsub
  have htin : ∀ a t, q + 1 ≤ a → a < q + 1 + S.size → ((compile s).getD a .halt).target = some t →
      q + 1 ≤ t ∧ t ≤ q + 1 + S.size := by
    intro a t h1 h2 ht
    have hst := (SStep_iff (labelsOf 0 s) (compile s) s 0 hs (compile_at s) a t (by omega) (by omega)).1 (target_step ht)
    have hin := hsub.inner hst (by omega) (by simp only [Stmt.size]; omega)
    cases hin with
    | ite1_skip => omega
    | ite1_in => omega
    | ite1_body hb => have := hb.range; omega
  have htout : ∀ a t, (a < q ∨ q + 1 + S.size ≤ a) → ((compile s).getD a .halt).target = some t →
      t ≤ q ∨ q + 1 + S.size ≤ t := by
    intro a t ha ht
    have := ctx_tout hs hsub (a := a) (t := t) (by simp only [Stmt.size]; omega) ht
    simp only [Stmt.size] at this
    omega
  obtain ⟨hnr, hrQ⟩ := ctx_not_reducibleD hspec (by omega) hhP hlenQ hhead htin htout hroot hf1
  have hred := structured_reducible hs
  refine ⟨hred, fun hv w => reducible_no_irreducible hv hred w,
    fun hv => exists_irreducible_loop hv hnr,
    ⟨_, dfsRun_valid (blocks_isCFG (by omega) hrQ) (Nat.le_refl 1)⟩, ?_⟩
  intro sol env hp hh r
  have hinv := comp_inv (sol := sol) (env := env) s hs hp 0
  have hmemH : (compile s).getD q .halt ∈ comp [] 0 s := compile_getD_mem hs (a := q) (by omega)
  obtain ⟨b, hb⟩ := (hinv _ hmemH).2 _ _ hhead
  have hcd : ∀ v, cd.eval sol env v = (!b, v) := by
    intro v
    have := hb v
    simp only [Cond.eval] at this
    have h1 := congrArg Prod.fst this
    have h2 := congrArg Prod.snd this
    simp only at h1 h2
    refine Prod.ext ?_ h2
    simp only
    cases hc : (cd.eval sol env v).1 <;> simp_all
  refine ctx_equivD hspec (by omega) ⟨hhead, htin, htout, ?_, ?_⟩ hcd hh r
  · intro a h1 h2
    have hmem := compile_getD_mem hs (a := a) (by omega)
    exact (hinv _ hmem).1
  · intro a k t hk
    have hlt : a < s.size := by
      by_cases hlt : a < s.size
      · exact hlt
      · rw [compile_halt s (by omega)] at hk; cases hk
    have hmem := compile_getD_mem hs hlt
    exact (hinv _ hmem).2 k t hk

end SmcIrred.Lang
