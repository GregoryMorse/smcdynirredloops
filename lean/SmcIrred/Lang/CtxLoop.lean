module

public import SmcIrred.Lang.ProtectW
public import SmcIrred.Lang.ProtectCode
public import SmcIrred.Lang.ProtectCtx

public section

namespace SmcIrred.Lang

/-! # Figure 5(c) inside a larger program (G32 a3, R17b)

`protectCodeC P lo mid hi h` wraps the region `[lo, hi)` of any code `P` in the loop of Figure 5(c):
`if (h) goto mid; while (trueThenFalse) { region }`. The entry jump sits at `lo`, the loop head at `lo + 1`, the region
(shifted by 2) at `lo + 2 .. hi + 1`, the back jump at `hi + 2`, and the code after the region (shifted by 3) at `hi + 3`.
Jumps from outside the region to its start run the entry test; jumps from outside past the region skip the loop.
The toggled variable is true outside the loop and false inside it. -/

@[expose] def mapO (lo t : Nat) : Nat := if t ≤ lo then t else t + 3

@[expose] def remapO (lo : Nat) : Instr → Instr
  | .blk a => .blk a
  | .jmp t => .jmp (mapO lo t)
  | .jmpIf k t => .jmpIf k (mapO lo t)
  | .halt => .halt

/-- Address of an original instruction, and the toggled variable there. -/
@[expose] def gC (lo hi a : Nat) : Nat := if a < lo then a else if a < hi then a + 2 else a + 3

@[expose] def protectCodeC (P : List Instr) (lo mid hi : Nat) (h : Cond) : List Instr :=
  (P.take lo).map (remapO lo) ++ (.jmpIf h (mid + 2) :: .jmpIf (.neg .ttf) (hi + 3) ::
    (((P.drop lo).take (hi - lo)).map (shiftI 2) ++ (.jmp (lo + 1) :: (P.drop hi).map (remapO lo))))

theorem getD_mapF (f : Instr → Instr) (hf : f .halt = .halt) (l : List Instr) (a : Nat) :
    (l.map f).getD a .halt = f (l.getD a .halt) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases h : l[a]? <;> simp [hf]

theorem getD_takeI (P : List Instr) {n a : Nat} (h : a < n) : (P.take n).getD a .halt = P.getD a .halt := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_take, h]

theorem getD_dropI (P : List Instr) (n a : Nat) : (P.drop n).getD a .halt = P.getD (n + a) .halt := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.add_comm]

theorem remapO_halt (lo : Nat) : remapO lo .halt = .halt := rfl

structure SpecC (P Q : List Instr) (lo mid hi : Nat) (h : Cond) : Prop where
  pre : ∀ a, a < lo → Q.getD a .halt = remapO lo (P.getD a .halt)
  entry : Q.getD lo .halt = .jmpIf h (mid + 2)
  head : Q.getD (lo + 1) .halt = .jmpIf (.neg .ttf) (hi + 3)
  body : ∀ a, lo ≤ a → a < hi → Q.getD (a + 2) .halt = shiftI 2 (P.getD a .halt)
  back : Q.getD (hi + 2) .halt = .jmp (lo + 1)
  post : ∀ a, hi ≤ a → Q.getD (a + 3) .halt = remapO lo (P.getD a .halt)

theorem protectCodeC_length {P : List Instr} {lo mid hi : Nat} {h : Cond} (hlh : lo ≤ hi) (hhi : hi ≤ P.length) :
    (protectCodeC P lo mid hi h).length = P.length + 3 := by
  simp only [protectCodeC, List.length_append, List.length_cons, List.length_take, List.length_drop, List.length_map]
  omega

theorem protectCodeC_spec {P : List Instr} {lo mid hi : Nat} {h : Cond} (hlh : lo < hi) (hhi : hi ≤ P.length) :
    SpecC P (protectCodeC P lo mid hi h) lo mid hi h := by
  have hA : ((P.take lo).map (remapO lo)).length = lo := by simp; omega
  have hB : (((P.drop lo).take (hi - lo)).map (shiftI 2)).length = hi - lo := by simp; omega
  unfold protectCodeC
  refine ⟨fun a ha => ?_, ?_, ?_, fun a h1 h2 => ?_, ?_, fun a ha => ?_⟩
  · rw [getD_app_l (by omega), getD_mapF _ rfl, getD_takeI P ha]
  · have := getD_app_r ((P.take lo).map (remapO lo)) (.jmpIf h (mid + 2) :: .jmpIf (.neg .ttf) (hi + 3) ::
      (((P.drop lo).take (hi - lo)).map (shiftI 2) ++ (.jmp (lo + 1) :: (P.drop hi).map (remapO lo)))) 0
    rw [hA] at this
    simpa using this
  · have := getD_app_r ((P.take lo).map (remapO lo)) (.jmpIf h (mid + 2) :: .jmpIf (.neg .ttf) (hi + 3) ::
      (((P.drop lo).take (hi - lo)).map (shiftI 2) ++ (.jmp (lo + 1) :: (P.drop hi).map (remapO lo)))) 1
    rw [hA] at this
    simpa using this
  · have e : a + 2 = ((P.take lo).map (remapO lo)).length + ((a - lo) + 1 + 1) := by omega
    rw [e, getD_app_r ((P.take lo).map (remapO lo)) _ ((a - lo) + 1 + 1)]
    rw [List.getD_cons_succ, List.getD_cons_succ, getD_app_l (by omega), getD_map_shift, getD_takeI _ (by omega),
      getD_dropI]
    congr 2; omega
  · have e : hi + 2 = ((P.take lo).map (remapO lo)).length + ((hi - lo) + 1 + 1) := by omega
    rw [e, getD_app_r ((P.take lo).map (remapO lo)) _ ((hi - lo) + 1 + 1)]
    rw [List.getD_cons_succ, List.getD_cons_succ]
    have := getD_app_r (((P.drop lo).take (hi - lo)).map (shiftI 2)) (.jmp (lo + 1) :: (P.drop hi).map (remapO lo)) 0
    rw [hB] at this
    simpa using this
  · have e : a + 3 = ((P.take lo).map (remapO lo)).length + ((hi - lo) + 1 + (a - hi) + 1 + 1) := by omega
    rw [e, getD_app_r ((P.take lo).map (remapO lo)) _ ((hi - lo) + 1 + (a - hi) + 1 + 1)]
    rw [List.getD_cons_succ, List.getD_cons_succ]
    have := getD_app_r (((P.drop lo).take (hi - lo)).map (shiftI 2)) (.jmp (lo + 1) :: (P.drop hi).map (remapO lo)) ((a - hi) + 1)
    rw [hB] at this
    rw [show hi - lo + 1 + (a - hi) = hi - lo + ((a - hi) + 1) by omega, this, List.getD_cons_succ,
      getD_mapF _ rfl, getD_dropI]
    congr 2; omega


/-! ### Hypotheses on the code, and the simulation -/

/-- Variable of the code at an address of the protected code. -/
@[expose] def vC (lo hi a : Nat) : Bool := decide (a < lo ∨ hi ≤ a)

/-- The region `[lo, hi)` is entered from outside only at `lo`, left only to `hi`, never halts, and every condition of the code
is pure (does not read the toggled variable). -/
structure CtxOK (P : List Instr) (sol : Nat → Bool) (env : Bool) (lo hi : Nat) : Prop where
  tin : ∀ a t, lo ≤ a → a < hi → (P.getD a .halt).target = some t → lo ≤ t ∧ t ≤ hi
  tout : ∀ a t, (a < lo ∨ hi ≤ a) → (P.getD a .halt).target = some t → t ≤ lo ∨ hi ≤ t
  nohalt : ∀ a, lo ≤ a → a < hi → P.getD a .halt ≠ .halt
  pure : ∀ a k t, P.getD a .halt = .jmpIf k t → PureC sol env k

variable {P Q : List Instr} {lo mid hi : Nat} {h : Cond} {sol : Nat → Bool} {env : Bool}

theorem vC_out {a : Nat} (ha : a < lo ∨ hi ≤ a) : vC lo hi a = true := by simp [vC, ha]

theorem vC_in {a : Nat} (h1 : lo ≤ a) (h2 : a < hi) : vC lo hi a = false := by
  simp only [vC, decide_eq_false_iff_not]; omega

theorem gC_lt {a : Nat} (h1 : a < lo) : gC lo hi a = a := by simp [gC, h1]

theorem gC_in {a : Nat} (h1 : lo ≤ a) (h2 : a < hi) : gC lo hi a = a + 2 := by
  simp [gC, show ¬ a < lo by omega, h2]

theorem gC_ge {a : Nat} (h1 : hi ≤ a) (hlh : lo < hi) : gC lo hi a = a + 3 := by
  simp [gC, show ¬ a < lo by omega, show ¬ a < hi by omega]

theorem runE (hs : SpecC P Q lo mid hi h) (hlh : lo < hi) (hh : h.eval sol env true = (false, true)) {tr : List Nat}
    {r : List Nat × Bool} (hq : Halts Q sol env (lo + 2) false tr r) : Halts Q sol env lo true tr r := by
  refine .jmpIf hs.entry ?_
  rw [hh]
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine .jmpIf hs.head ?_
  simpa [Cond.eval] using hq

theorem runJ (hs : SpecC P Q lo mid hi h) {tr : List Nat} {r : List Nat × Bool}
    (hq : Halts Q sol env (hi + 3) true tr r) : Halts Q sol env (hi + 2) false tr r := by
  refine .jmp hs.back (.jmpIf hs.head ?_)
  simpa [Cond.eval] using hq

theorem arrOut (hs : SpecC P Q lo mid hi h) (hlh : lo < hi) (hh : h.eval sol env true = (false, true)) {t : Nat}
    (ht : t ≤ lo ∨ hi ≤ t) {tr : List Nat} {r : List Nat × Bool}
    (hq : Halts Q sol env (gC lo hi t) (vC lo hi t) tr r) : Halts Q sol env (mapO lo t) true tr r := by
  by_cases h1 : t < lo
  · simpa [gC, vC, mapO, h1, show t ≤ lo by omega] using hq
  · by_cases h2 : t = lo
    · subst h2
      rw [gC_in (Nat.le_refl _) hlh, vC_in (Nat.le_refl _) hlh] at hq
      simpa [mapO] using runE hs hlh hh hq
    · simpa [gC, vC, mapO, h1, show ¬ t < hi by omega, show ¬ t ≤ lo by omega, show hi ≤ t by omega] using hq

theorem arrIn (hs : SpecC P Q lo mid hi h) (hlh : lo < hi) {t : Nat} (ht : lo ≤ t ∧ t ≤ hi) {tr : List Nat}
    {r : List Nat × Bool} (hq : Halts Q sol env (gC lo hi t) (vC lo hi t) tr r) : Halts Q sol env (t + 2) false tr r := by
  by_cases h1 : t < hi
  · rw [gC_in ht.1 h1, vC_in ht.1 h1] at hq; exact hq
  · have h2 : t = hi := by omega
    subst h2
    rw [gC_ge (Nat.le_refl _) hlh, vC_out (Or.inr (Nat.le_refl _))] at hq
    exact runJ hs hq

theorem instrQ (hs : SpecC P Q lo mid hi h) (hlh : lo < hi) (pc : Nat) :
    Q.getD (gC lo hi pc) .halt =
      if lo ≤ pc ∧ pc < hi then shiftI 2 (P.getD pc .halt) else remapO lo (P.getD pc .halt) := by
  by_cases h1 : pc < lo
  · simp [gC, h1, show ¬ (lo ≤ pc ∧ pc < hi) by omega]; exact hs.pre pc h1
  · by_cases h2 : pc < hi
    · simp [gC, h1, h2, show lo ≤ pc by omega]; exact hs.body pc (by omega) h2
    · simp [gC, h1, h2, show ¬ (lo ≤ pc ∧ pc < hi) by omega]; exact hs.post pc (by omega)

theorem succ_arr (hs : SpecC P Q lo mid hi h) (hlh : lo < hi) (hh : h.eval sol env true = (false, true)) (pc : Nat)
    {tr : List Nat} {r : List Nat × Bool}
    (hq : Halts Q sol env (gC lo hi (pc + 1)) (vC lo hi (pc + 1)) tr r) :
    Halts Q sol env (gC lo hi pc + 1) (vC lo hi pc) tr r := by
  by_cases h1 : pc < lo
  · have := arrOut hs hlh hh (t := pc + 1) (Or.inl (by omega)) hq
    rw [gC_lt h1, vC_out (Or.inl h1)]
    simpa [mapO, show pc + 1 ≤ lo by omega] using this
  · by_cases h2 : pc < hi
    · have := arrIn hs hlh (t := pc + 1) ⟨by omega, by omega⟩ hq
      rw [gC_in (by omega) h2, vC_in (by omega) h2]
      exact this
    · have := arrOut hs hlh hh (t := pc + 1) (Or.inr (by omega)) hq
      rw [gC_ge (by omega) hlh, vC_out (Or.inr (by omega))]
      simpa [mapO, show ¬ pc + 1 ≤ lo by omega] using this

theorem ctx_fwd (hs : SpecC P Q lo mid hi h) (hlh : lo < hi) (hc : CtxOK P sol env lo hi)
    (hh : h.eval sol env true = (false, true)) {pc : Nat} {v : Bool} {tr : List Nat} {r : List Nat × Bool}
    (hp : Halts P sol env pc v tr r) : v = true → Halts Q sol env (gC lo hi pc) (vC lo hi pc) tr r := by
  induction hp with
  | @halt pc v tr hi' =>
    intro hv; subst hv
    have hout : pc < lo ∨ hi ≤ pc := by
      by_cases hn : pc < lo ∨ hi ≤ pc
      · exact hn
      · exact absurd hi' (hc.nohalt pc (by omega) (by omega))
    have hq : Q.getD (gC lo hi pc) .halt = .halt := by
      rw [instrQ hs hlh, if_neg (by omega), hi']; rfl
    rw [vC_out hout]
    exact .halt hq
  | @blk pc a v tr r hi' _ ih =>
    intro hv; subst hv
    have hq : Q.getD (gC lo hi pc) .halt = .blk a := by
      rw [instrQ hs hlh]; split <;> rw [hi'] <;> rfl
    exact .blk hq (succ_arr hs hlh hh pc (ih rfl))
  | @jmp pc t v tr r hi' _ ih =>
    intro hv; subst hv
    have ht : (P.getD pc .halt).target = some t := by rw [hi']; rfl
    by_cases hin : lo ≤ pc ∧ pc < hi
    · have hq : Q.getD (gC lo hi pc) .halt = .jmp (t + 2) := by rw [instrQ hs hlh, if_pos hin, hi']; rfl
      have := hc.tin pc t hin.1 hin.2 ht
      have hq' := arrIn hs hlh this (ih rfl)
      have hv' : vC lo hi pc = false := vC_in hin.1 hin.2
      rw [hv']
      exact .jmp hq hq'
    · have hq : Q.getD (gC lo hi pc) .halt = .jmp (mapO lo t) := by rw [instrQ hs hlh, if_neg hin, hi']; rfl
      have := hc.tout pc t (by omega) ht
      have hv' : vC lo hi pc = true := vC_out (by omega)
      rw [hv']
      exact .jmp hq (arrOut hs hlh hh this (ih rfl))
  | @jmpIf pc t kk v tr r hi' _ ih =>
    intro hv; subst hv
    have ht : (P.getD pc .halt).target = some t := by rw [hi']; rfl
    obtain ⟨b, hb⟩ := hc.pure pc kk t hi'
    have hbt : kk.eval sol env true = (b, true) := hb true
    rw [hbt] at ih
    by_cases hin : lo ≤ pc ∧ pc < hi
    · have hq : Q.getD (gC lo hi pc) .halt = .jmpIf kk (t + 2) := by rw [instrQ hs hlh, if_pos hin, hi']; rfl
      have hv' : vC lo hi pc = false := vC_in hin.1 hin.2
      rw [hv']
      refine .jmpIf hq ?_
      rw [hb false]
      cases b
      · simp only [Bool.false_eq_true, ↓reduceIte] at ih ⊢
        have := succ_arr hs hlh hh pc (ih trivial)
        simpa [hv'] using this
      · simp only [↓reduceIte] at ih ⊢
        exact arrIn hs hlh (hc.tin pc t hin.1 hin.2 ht) (ih trivial)
    · have hq : Q.getD (gC lo hi pc) .halt = .jmpIf kk (mapO lo t) := by rw [instrQ hs hlh, if_neg hin, hi']; rfl
      have hv' : vC lo hi pc = true := vC_out (by omega)
      rw [hv']
      refine .jmpIf hq ?_
      rw [hbt]
      cases b
      · simp only [Bool.false_eq_true, ↓reduceIte] at ih ⊢
        have := succ_arr hs hlh hh pc (ih trivial)
        simpa [hv'] using this
      · simp only [↓reduceIte] at ih ⊢
        exact arrOut hs hlh hh (hc.tout pc t (by omega) ht) (ih trivial)


/-! ### Backward direction -/

/-- Related states: the canonical address, or one of the inserted instructions. -/
@[expose] def RelB (lo hi pP pQ : Nat) (vQ : Bool) : Prop :=
  (pQ = gC lo hi pP ∧ vQ = vC lo hi pP) ∨ (pP = lo ∧ pQ = lo ∧ vQ = true) ∨ (pP = lo ∧ pQ = lo + 1 ∧ vQ = true) ∨
    (pP = hi ∧ pQ = hi + 2 ∧ vQ = false) ∨ (pP = hi ∧ pQ = lo + 1 ∧ vQ = false)

theorem relT_out (hlh : lo < hi) {t : Nat} (ht : t ≤ lo ∨ hi ≤ t) : RelB lo hi t (mapO lo t) true := by
  by_cases h1 : t < lo
  · left; rw [gC_lt h1, vC_out (Or.inl h1)]; simp [mapO, show t ≤ lo by omega]
  · by_cases h2 : t = lo
    · subst h2; right; left; simp [mapO]
    · left
      rw [gC_ge (by omega) hlh, vC_out (Or.inr (by omega))]
      simp [mapO, show ¬ t ≤ lo by omega]

theorem relT_in (hlh : lo < hi) {t : Nat} (ht : lo ≤ t ∧ t ≤ hi) : RelB lo hi t (t + 2) false := by
  by_cases h1 : t < hi
  · left; rw [gC_in ht.1 h1, vC_in ht.1 h1]; simp
  · right; right; right; left; exact ⟨by omega, by omega, rfl⟩

theorem relS (hlh : lo < hi) (pc : Nat) : RelB lo hi (pc + 1) (gC lo hi pc + 1) (vC lo hi pc) := by
  by_cases h1 : pc < lo
  · rw [gC_lt h1, vC_out (Or.inl h1)]
    by_cases h2 : pc + 1 < lo
    · left; rw [gC_lt h2, vC_out (Or.inl h2)]; simp
    · right; left; exact ⟨by omega, by omega, rfl⟩
  · by_cases h2 : pc < hi
    · rw [gC_in (by omega) h2, vC_in (by omega) h2]
      by_cases h3 : pc + 1 < hi
      · left; rw [gC_in (by omega) h3, vC_in (by omega) h3]; simp
      · right; right; right; left; exact ⟨by omega, by omega, rfl⟩
    · rw [gC_ge (by omega) hlh, vC_out (Or.inr (by omega))]
      left; rw [gC_ge (by omega) hlh, vC_out (Or.inr (by omega))]; simp

theorem instrQ_blk (hs : SpecC P Q lo mid hi h) (hlh : lo < hi) {pc a : Nat}
    (hq : Q.getD (gC lo hi pc) .halt = .blk a) : P.getD pc .halt = .blk a := by
  rw [instrQ hs hlh] at hq
  by_cases hin : lo ≤ pc ∧ pc < hi
  · rw [if_pos hin] at hq
    cases hp : P.getD pc .halt with
    | blk a' => rw [hp] at hq; simp only [shiftI, Instr.blk.injEq] at hq; rw [hq]
    | jmp t => rw [hp] at hq; simp [shiftI] at hq
    | jmpIf k t => rw [hp] at hq; simp [shiftI] at hq
    | halt => rw [hp] at hq; simp [shiftI] at hq
  · rw [if_neg hin] at hq
    cases hp : P.getD pc .halt with
    | blk a' => rw [hp] at hq; simp only [remapO, Instr.blk.injEq] at hq; rw [hq]
    | jmp t => rw [hp] at hq; simp [remapO] at hq
    | jmpIf k t => rw [hp] at hq; simp [remapO] at hq
    | halt => rw [hp] at hq; simp [remapO] at hq

theorem instrQ_halt (hs : SpecC P Q lo mid hi h) (hlh : lo < hi) {pc : Nat}
    (hq : Q.getD (gC lo hi pc) .halt = .halt) : P.getD pc .halt = .halt := by
  rw [instrQ hs hlh] at hq
  by_cases hin : lo ≤ pc ∧ pc < hi
  · rw [if_pos hin] at hq
    cases hp : P.getD pc .halt with
    | blk a' => rw [hp] at hq; simp [shiftI] at hq
    | jmp t => rw [hp] at hq; simp [shiftI] at hq
    | jmpIf k t => rw [hp] at hq; simp [shiftI] at hq
    | halt => rfl
  · rw [if_neg hin] at hq
    cases hp : P.getD pc .halt with
    | blk a' => rw [hp] at hq; simp [remapO] at hq
    | jmp t => rw [hp] at hq; simp [remapO] at hq
    | jmpIf k t => rw [hp] at hq; simp [remapO] at hq
    | halt => rfl

theorem instrQ_jmp (hs : SpecC P Q lo mid hi h) (hlh : lo < hi) {pc t' : Nat}
    (hq : Q.getD (gC lo hi pc) .halt = .jmp t') :
    ∃ t, P.getD pc .halt = .jmp t ∧ t' = (if lo ≤ pc ∧ pc < hi then t + 2 else mapO lo t) := by
  rw [instrQ hs hlh] at hq
  by_cases hin : lo ≤ pc ∧ pc < hi
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
    | blk a' => rw [hp] at hq; simp [remapO] at hq
    | jmp t =>
      rw [hp] at hq; simp only [remapO, Instr.jmp.injEq] at hq
      exact ⟨t, rfl, by rw [if_neg hin]; omega⟩
    | jmpIf k t => rw [hp] at hq; simp [remapO] at hq
    | halt => rw [hp] at hq; simp [remapO] at hq

theorem instrQ_jmpIf (hs : SpecC P Q lo mid hi h) (hlh : lo < hi) {pc t' : Nat} {kk : Cond}
    (hq : Q.getD (gC lo hi pc) .halt = .jmpIf kk t') :
    ∃ t, P.getD pc .halt = .jmpIf kk t ∧ t' = (if lo ≤ pc ∧ pc < hi then t + 2 else mapO lo t) := by
  rw [instrQ hs hlh] at hq
  by_cases hin : lo ≤ pc ∧ pc < hi
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
    | blk a' => rw [hp] at hq; simp [remapO] at hq
    | jmp t => rw [hp] at hq; simp [remapO] at hq
    | jmpIf k t =>
      rw [hp] at hq; simp only [remapO, Instr.jmpIf.injEq] at hq
      obtain ⟨rfl, h2⟩ := hq
      exact ⟨t, rfl, by rw [if_neg hin]; omega⟩
    | halt => rw [hp] at hq; simp [remapO] at hq

theorem ctx_bwd (hs : SpecC P Q lo mid hi h) (hlh : lo < hi) (hc : CtxOK P sol env lo hi)
    (hh : h.eval sol env true = (false, true)) {pcQ : Nat} {vQ : Bool} {tr : List Nat}
    {r : List Nat × Bool} (hq : Halts Q sol env pcQ vQ tr r) :
    ∀ pP, RelB lo hi pP pcQ vQ → Halts P sol env pP true tr r := by
  induction hq with
  | @halt pcQ v tr hi' =>
    intro pP hr
    rcases hr with ⟨h1, h2⟩ | ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩
    · subst h1; subst h2
      have hP := instrQ_halt hs hlh hi'
      have hout : pP < lo ∨ hi ≤ pP := by
        by_cases hn : pP < lo ∨ hi ≤ pP
        · exact hn
        · exact absurd hP (hc.nohalt pP (by omega) (by omega))
      rw [vC_out hout]
      exact .halt hP
    · rw [hs.entry] at hi'; cases hi'
    · rw [hs.head] at hi'; cases hi'
    · rw [hs.back] at hi'; cases hi'
    · rw [hs.head] at hi'; cases hi'
  | @blk pcQ a v tr r hi' _ ih =>
    intro pP hr
    rcases hr with ⟨h1, h2⟩ | ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩
    · subst h1; subst h2
      exact .blk (instrQ_blk hs hlh hi') (ih (pP + 1) (relS hlh pP))
    · rw [hs.entry] at hi'; cases hi'
    · rw [hs.head] at hi'; cases hi'
    · rw [hs.back] at hi'; cases hi'
    · rw [hs.head] at hi'; cases hi'
  | @jmp pcQ t' v tr r hi' _ ih =>
    intro pP hr
    rcases hr with ⟨h1, h2⟩ | ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ | ⟨hP, rfl, hv⟩ | ⟨_, rfl, _⟩
    · subst h1; subst h2
      obtain ⟨t, hP, ht'⟩ := instrQ_jmp hs hlh hi'
      have htg : (P.getD pP .halt).target = some t := by rw [hP]; rfl
      refine .jmp hP ?_
      by_cases hin : lo ≤ pP ∧ pP < hi
      · rw [if_pos hin] at ht'; subst ht'
        exact ih t (by rw [vC_in hin.1 hin.2]; exact relT_in hlh (hc.tin pP t hin.1 hin.2 htg))
      · rw [if_neg hin] at ht'; subst ht'
        exact ih t (by rw [vC_out (by omega)]; exact relT_out hlh (hc.tout pP t (by omega) htg))
    · rw [hs.entry] at hi'; cases hi'
    · rw [hs.head] at hi'; cases hi'
    · rw [hs.back] at hi'
      cases hi'
      rw [hP]
      exact ih hi (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, hv⟩))))
    · rw [hs.head] at hi'; cases hi'
  | @jmpIf pcQ t' kk v tr r hi' hrest ih =>
    intro pP hr
    rcases hr with ⟨h1, h2⟩ | ⟨hP, hQ, hv⟩ | ⟨hP, hQ, hv⟩ | ⟨_, rfl, _⟩ | ⟨hP, hQ, hv⟩
    · subst h1; subst h2
      obtain ⟨t, hP, ht'⟩ := instrQ_jmpIf hs hlh hi'
      have htg : (P.getD pP .halt).target = some t := by rw [hP]; rfl
      obtain ⟨b, hb⟩ := hc.pure pP kk t hP
      refine .jmpIf hP ?_
      rw [hb true]
      rw [hb (vC lo hi pP)] at ih hrest
      by_cases hin : lo ≤ pP ∧ pP < hi
      · rw [if_pos hin] at ht'; subst ht'
        cases b
        · simp only [Bool.false_eq_true, ↓reduceIte] at ih ⊢
          exact ih (pP + 1) (relS hlh pP)
        · simp only [↓reduceIte] at ih ⊢
          exact ih t (by rw [vC_in hin.1 hin.2]; exact relT_in hlh (hc.tin pP t hin.1 hin.2 htg))
      · rw [if_neg hin] at ht'; subst ht'
        cases b
        · simp only [Bool.false_eq_true, ↓reduceIte] at ih ⊢
          exact ih (pP + 1) (relS hlh pP)
        · simp only [↓reduceIte] at ih ⊢
          exact ih t (by rw [vC_out (by omega)]; exact relT_out hlh (hc.tout pP t (by omega) htg))
    · have hQ' : lo = pcQ := hQ.symm
      subst hQ'
      subst hv
      rw [hP]
      rw [hs.entry] at hi'
      cases hi'
      rw [hh] at ih
      simp only [Bool.false_eq_true, ↓reduceIte] at ih
      exact ih lo (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))
    · have hQ' : lo + 1 = pcQ := hQ.symm
      subst hQ'
      subst hv
      rw [hP]
      rw [hs.head] at hi'
      cases hi'
      simp only [Cond.eval, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at ih
      exact ih lo (Or.inl ⟨by rw [gC_in (Nat.le_refl _) hlh], by rw [vC_in (Nat.le_refl _) hlh]⟩)
    · rw [hs.back] at hi'; cases hi'
    · have hQ' : lo + 1 = pcQ := hQ.symm
      subst hQ'
      subst hv
      rw [hP]
      rw [hs.head] at hi'
      cases hi'
      simp only [Cond.eval, Bool.not_false, Bool.not_true, ↓reduceIte] at ih
      exact ih hi (Or.inl ⟨by rw [gC_ge (Nat.le_refl _) hlh], by rw [vC_out (Or.inr (Nat.le_refl _))]⟩)

theorem ctx_equiv (hs : SpecC P Q lo mid hi h) (hlh : lo < hi) (hc : CtxOK P sol env lo hi)
    (hh : h.eval sol env true = (false, true)) (r : List Nat × Bool) :
    (∃ f, exec f P sol env 0 true [] = some r) ↔ ∃ f, exec f Q sol env 0 true [] = some r := by
  rw [← halts_iff_exec, ← halts_iff_exec]
  constructor
  · intro hp
    have := ctx_fwd hs hlh hc hh hp rfl
    have h0 := arrOut hs hlh hh (t := 0) (Or.inl (by omega)) this
    simpa [mapO] using h0
  · intro hq
    have := relT_out hlh (t := 0) (Or.inl (by omega))
    simp only [mapO, Nat.zero_le, ↓reduceIte] at this
    exact ctx_bwd hs hlh hc hh hq 0 this


/-! ### Forward paths and the irreducible loop -/

theorem step_cases {a c : Nat} (hp : StepI P a c) : c = a + 1 ∨ (P.getD a .halt).target = some c := by
  unfold StepI at hp
  cases hi' : P.getD a .halt <;> simp only [hi'] at hp
  · left; exact hp
  · right; subst hp; rfl
  · rcases hp with rfl | rfl
    · right; rfl
    · left; rfl

theorem stepQ_in (hs : SpecC P Q lo mid hi h) {a c : Nat} (h1 : lo ≤ a) (h2 : a < hi) (hp : StepI P a c) :
    StepI Q (a + 2) (c + 2) := by
  unfold StepI at hp ⊢
  rw [hs.body a h1 h2]
  cases hi' : P.getD a .halt <;> simp only [hi', shiftI] at hp ⊢
  · subst hp; rfl
  · subst hp; rfl
  · rcases hp with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl

theorem stepQ_pre (hs : SpecC P Q lo mid hi h) {a c : Nat} (h1 : a < lo) (hc : c ≤ lo) (hp : StepI P a c) :
    StepI Q a c := by
  unfold StepI at hp ⊢
  rw [hs.pre a h1]
  cases hi' : P.getD a .halt <;> simp only [hi', remapO] at hp ⊢
  · subst hp; simp [mapO, hc]
  · subst hp; simp [mapO, hc]
  · rcases hp with rfl | rfl
    · exact Or.inl (by simp [mapO, hc])
    · exact Or.inr rfl

theorem stepQ_post (hs : SpecC P Q lo mid hi h) (hlh : lo < hi) {a c : Nat} (h1 : hi ≤ a) (hc : lo < c) (hp : StepI P a c)
    (hcp : c = a + 1 ∨ (P.getD a .halt).target = some c) : StepI Q (a + 3) (c + 3) := by
  unfold StepI at hp ⊢
  rw [hs.post a h1]
  cases hi' : P.getD a .halt <;> simp only [hi', remapO] at hp ⊢
  · subst hp; rfl
  · subst hp; simp [mapO, show ¬ c ≤ lo by omega]
  · rcases hp with rfl | rfl
    · exact Or.inl (by simp [mapO, show ¬ c ≤ lo by omega])
    · exact Or.inr rfl

theorem stepQ_pre_far (hs : SpecC P Q lo mid hi h) {a c : Nat} (h1 : a < lo) (hc : lo < c)
    (ht : (P.getD a .halt).target = some c) : StepI Q a (c + 3) := by
  unfold StepI
  rw [hs.pre a h1]
  cases hi' : P.getD a .halt <;> simp only [hi', Instr.target] at ht
  · cases ht
  · cases ht; simp [remapO, mapO, show ¬ c ≤ lo by omega]
  · cases ht; exact Or.inl (by simp [mapO, show ¬ c ≤ lo by omega])
  · cases ht

theorem fwd_pre (hs : SpecC P Q lo mid hi h) {a b : Nat} (hp : Fwd (StepI P) a b) (hb : b ≤ lo) : Fwd (StepI Q) a b := by
  induction hp with
  | refl => exact .refl _
  | @step a c b hr hlt hrest ih =>
    have hcb := hrest.le
    exact .step (stepQ_pre hs (by omega) (by omega) hr) hlt (ih hb)

theorem fwd_shift2 (hs : SpecC P Q lo mid hi h) {a b : Nat} (hp : Fwd (StepI P) a b) (ha : lo ≤ a) (hb : b ≤ hi) :
    Fwd (StepI Q) (a + 2) (b + 2) := by
  induction hp with
  | refl => exact .refl _
  | @step a c b hr hlt hrest ih =>
    have hcb := hrest.le
    exact .step (stepQ_in hs ha (by omega) hr) (by omega) (ih (by omega) hb)

theorem ctx_not_reducible (hs : SpecC P Q lo mid hi h) (hlh : lo < hi) (hlm : lo ≤ mid) (hmh : mid ≤ hi)
    (hhP : hi < P.length) (hlen : Q.length = P.length + 3)
    (htin : ∀ a t, lo ≤ a → a < hi → (P.getD a .halt).target = some t → lo ≤ t ∧ t ≤ hi)
    (htout : ∀ a t, (a < lo ∨ hi ≤ a) → (P.getD a .halt).target = some t → t ≤ lo ∨ hi ≤ t)
    (hroot : ∀ x, x < P.length → Fwd (StepI P) 0 x)
    (hf1 : Fwd (StepI P) lo hi) (hfL : Fwd (StepI P) mid hi) : ¬ (cfgOf Q).Reducible 0 ∧
      ∀ x, x < Q.length → Fwd (StepI Q) 0 x := by
  have hE : StepI Q lo (lo + 1) := by unfold StepI; rw [hs.entry]; exact Or.inr rfl
  have hHs : StepI Q (lo + 1) (lo + 2) := by unfold StepI; rw [hs.head]; exact Or.inr rfl
  have hHj : StepI Q (lo + 1) (hi + 3) := by unfold StepI; rw [hs.head]; exact Or.inl rfl
  have hJ : StepI Q (hi + 2) (lo + 1) := by unfold StepI; rw [hs.back]
  have hQlo : Fwd (StepI Q) 0 lo := fwd_pre hs (hroot lo (by omega)) (Nat.le_refl _)
  have hH : Fwd (StepI Q) 0 (lo + 1) := Fwd.trans hQlo (.step hE (by omega) (.refl _))
  have hH2 : Fwd (StepI Q) 0 (lo + 2) := Fwd.trans hH (.step hHs (by omega) (.refl _))
  have hX : Fwd (StepI Q) 0 (hi + 3) := Fwd.trans hH (.step hHj (by omega) (.refl _))
  have hg0 : Fwd (StepI Q) 0 (gC lo hi 0) := by
    by_cases h0 : 0 < lo
    · rw [gC_lt h0]; exact .refl _
    · have : lo = 0 := by omega
      rw [gC_in (a := 0) (by omega) (by omega)]
      subst this
      simpa using hH2
  have hstep : ∀ a c, StepI P a c → a < c → Fwd (StepI Q) 0 (gC lo hi a) → Fwd (StepI Q) 0 (gC lo hi c) := by
    intro a c hp hac hq
    have hcs := step_cases hp
    by_cases h1 : a < lo
    · have hco : c ≤ lo ∨ hi ≤ c := by
        rcases hcs with rfl | ht
        · left; omega
        · exact htout a c (Or.inl h1) ht
      rw [gC_lt h1] at hq
      by_cases h2 : c < lo
      · rw [gC_lt h2]
        exact Fwd.trans hq (.step (stepQ_pre hs h1 (by omega) hp) hac (.refl _))
      · by_cases h3 : c = lo
        · subst h3
          rw [gC_in (Nat.le_refl _) hlh]
          have e1 : StepI Q a c := stepQ_pre hs h1 (by omega) hp
          exact Fwd.trans (Fwd.trans hq (.step e1 hac (.refl _))) (.step hE (by omega) (.step hHs (by omega) (.refl _)))
        · rw [gC_ge (by omega) hlh]
          have hmo : StepI Q a (c + 3) := by
            rcases hcs with rfl | ht
            · omega
            · exact stepQ_pre_far hs h1 (by omega) ht
          exact Fwd.trans hq (.step hmo (by omega) (.refl _))
    · by_cases h2 : a < hi
      · have hci : lo ≤ c ∧ c ≤ hi := by
          rcases hcs with rfl | ht
          · omega
          · exact htin a c (by omega) h2 ht
        rw [gC_in (by omega) h2] at hq
        by_cases h3 : c < hi
        · rw [gC_in hci.1 h3]
          exact Fwd.trans hq (.step (stepQ_in hs (by omega) h2 hp) (by omega) (.refl _))
        · have : c = hi := by omega
          subst this
          rw [gC_ge (Nat.le_refl _) hlh]
          exact hX
      · rw [gC_ge (by omega) hlh] at hq
        rw [gC_ge (by omega) hlh]
        exact Fwd.trans hq (.step (stepQ_post hs hlh (by omega) (by omega) hp hcs) (by omega) (.refl _))
  have hcq : ∀ y, Fwd (StepI P) 0 y → Fwd (StepI Q) 0 (gC lo hi y) := by
    intro y hy
    have key : ∀ a b, Fwd (StepI P) a b → Fwd (StepI Q) 0 (gC lo hi a) → Fwd (StepI Q) 0 (gC lo hi b) := by
      intro a b hab
      induction hab with
      | refl => intro h; exact h
      | @step a c b hr hlt _ ih => intro h; exact ih (hstep a c hr hlt h)
    exact key 0 y hy hg0
  have hroot' : ∀ x, x < Q.length → Fwd (StepI Q) 0 x := by
    intro x hx
    by_cases h1 : x < lo
    · exact fwd_pre hs (hroot x (by omega)) (by omega)
    · by_cases h2 : x = lo
      · subst h2; exact hQlo
      · by_cases h3 : x = lo + 1
        · subst h3; exact hH
        · by_cases h4 : x ≤ hi + 1
          · have := hcq (x - 2) (hroot (x - 2) (by omega))
            rw [gC_in (by omega) (by omega)] at this
            simpa [show x - 2 + 2 = x by omega] using this
          · by_cases h5 : x = hi + 2
            · subst h5
              have := fwd_shift2 hs hf1 (Nat.le_refl _) (Nat.le_refl _)
              exact Fwd.trans hH2 this
            · have := hcq (x - 3) (hroot (x - 3) (by omega))
              rw [gC_ge (by omega) hlh] at this
              simpa [show x - 3 + 3 = x by omega] using this
  refine ⟨?_, hroot'⟩
  have hf1Q : Fwd (StepI Q) (lo + 1) (hi + 2) :=
    .step hHs (by omega) (fwd_shift2 hs hf1 (Nat.le_refl _) (Nat.le_refl _))
  have hfLQ : Fwd (StepI Q) (mid + 2) (hi + 2) := fwd_shift2 hs hfL hlm (Nat.le_refl _)
  exact entry_cycle_not_reducible Q (e0 := lo) (L := mid + 2) (c := hi + 2) (h := h) (by omega) hs.entry hroot'
    (by omega) (by omega) hf1Q hfLQ hJ


/-! ### Figure 5(c) inside any goto-free program -/

/-- A step of the whole program from inside an occurrence is a step of the occurrence. -/
theorem Sub.inner {u s : Stmt} {q p : Nat} (h : Sub u q s p) : ∀ {a c : Nat}, SStep s p a c → q ≤ a → a < q + u.size →
    SStep u q a c := by
  induction h with
  | refl => intro a c hs _ _; exact hs
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

theorem target_step {P : List Instr} {a t : Nat} (h : (P.getD a .halt).target = some t) : StepI P a t := by
  unfold StepI
  cases hi : P.getD a .halt <;> simp only [hi, Instr.target] at h
  · exact absurd h (by simp)
  · cases h; exact rfl
  · cases h; exact Or.inl rfl
  · exact absurd h (by simp)

theorem ctx_tin {s u : Stmt} {q : Nat} (hs : Structured s) (hsub : Sub u q s 0) {a t : Nat} (h1 : q ≤ a)
    (h2 : a < q + u.size) (ht : ((compile s).getD a .halt).target = some t) : q ≤ t ∧ t ≤ q + u.size := by
  have hr := hsub.range
  have hst := (SStep_iff (labelsOf 0 s) (compile s) s 0 hs (compile_at s) a t (by omega) (by omega)).1 (target_step ht)
  have := (hsub.inner hst h1 h2).range
  omega

theorem ctx_tout {s u : Stmt} {q : Nat} (hs : Structured s) (hsub : Sub u q s 0) {a t : Nat}
    (ha : a < q ∨ q + u.size ≤ a) (ht : ((compile s).getD a .halt).target = some t) : t ≤ q ∨ q + u.size ≤ t := by
  by_cases hlt : a < s.size
  · have hst := (SStep_iff (labelsOf 0 s) (compile s) s 0 hs (compile_at s) a t (by omega) (by omega)).1 (target_step ht)
    by_cases h1 : q < t ∧ t < q + u.size
    · have := hsub.entry hst h1.1 h1.2
      omega
    · omega
  · rw [compile_halt s (by omega)] at ht
    simp [Instr.target] at ht

theorem compile_getD_mem {s : Stmt} (hs : Structured s) {a : Nat} (ha : a < s.size) :
    (compile s).getD a .halt ∈ comp [] 0 s := by
  rw [compile_structured hs, getD_app_l (by rw [comp_length]; exact ha)]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [comp_length]; exact ha)]
  exact List.getElem_mem _

theorem protectC_structured {s S T : Stmt} {q : Nat} (hs : Structured s) (hsub : Sub (.seq S T) q s 0)
    (hS : 1 ≤ S.size) (h : Cond) :
    (cfgOf (compile s)).Reducible 0 ∧
    (∀ {J : Jungle}, J.Valid (cfgOf (compile s)) 0 → ∀ w, ¬ (cfgOf (compile s)).Irreducible J w) ∧
    (∀ {J : Jungle}, J.Valid (cfgOf (protectCodeC (compile s) q (q + S.size) (q + S.size + T.size) h)) 0 →
      ∃ w, (cfgOf (protectCodeC (compile s) q (q + S.size) (q + S.size + T.size) h)).Irreducible J w) ∧
    (∃ J : Jungle, J.Valid (cfgOf (protectCodeC (compile s) q (q + S.size) (q + S.size + T.size) h)) 0) ∧
    (∀ {sol : Nat → Bool} {env : Bool}, PureS sol env s → h.eval sol env true = (false, true) →
      ∀ (r : List Nat × Bool),
        ((∃ f, exec f (compile s) sol env 0 true [] = some r) ↔
          ∃ f, exec f (protectCodeC (compile s) q (q + S.size) (q + S.size + T.size) h) sol env 0 true [] = some r)) := by
  have hseq : Structured (.seq S T) := hsub.structured hs
  have hr := hsub.range
  simp only [Stmt.size] at hr
  have hlen : (compile s).length = s.size + 1 := compile_length s
  have hhP : q + S.size + T.size < (compile s).length := by omega
  have hspec := protectCodeC_spec (P := compile s) (lo := q) (mid := q + S.size) (hi := q + S.size + T.size) (h := h)
    (by omega) (by omega)
  have hlenQ := protectCodeC_length (P := compile s) (lo := q) (mid := q + S.size) (hi := q + S.size + T.size) (h := h)
    (by omega) (by omega)
  have hroot : ∀ x, x < (compile s).length → Fwd (StepI (compile s)) 0 x := fun x hx =>
    (sstep_fwd s hs 0 x (by omega) (by omega)).mono (fun a c => sstep_stepI hs)
  have hf1 : Fwd (StepI (compile s)) q (q + S.size + T.size) :=
    (sstep_fwd (.seq S T) hseq q _ (by omega) (by simp only [Stmt.size]; omega)).mono
      (fun a c hh' => sstep_stepI hs (hsub.sstep hh'))
  have hT' : Structured T := hseq.2
  have hfL : Fwd (StepI (compile s)) (q + S.size) (q + S.size + T.size) :=
    (sstep_fwd T hT' (q + S.size) _ (by omega) (by omega)).mono
      (fun a c hh' => sstep_stepI hs (hsub.sstep (.seqR hh')))
  have hsz : (Stmt.seq S T).size = S.size + T.size := rfl
  have htin : ∀ a t, q ≤ a → a < q + S.size + T.size → ((compile s).getD a .halt).target = some t →
      q ≤ t ∧ t ≤ q + S.size + T.size := by
    intro a t h1 h2 ht
    have := ctx_tin hs hsub (a := a) (t := t) h1 (by omega) ht
    omega
  have htout : ∀ a t, (a < q ∨ q + S.size + T.size ≤ a) → ((compile s).getD a .halt).target = some t →
      t ≤ q ∨ q + S.size + T.size ≤ t := by
    intro a t ha ht
    have := ctx_tout hs hsub (a := a) (t := t) (by omega) ht
    omega
  obtain ⟨hnr, hrQ⟩ := ctx_not_reducible hspec (by omega) (by omega) (by omega) hhP hlenQ htin htout hroot hf1 hfL
  have hred := structured_reducible hs
  refine ⟨hred, fun hv w => reducible_no_irreducible hv hred w,
    fun hv => exists_irreducible_loop hv hnr,
    ⟨_, dfsRun_valid (blocks_isCFG (by omega) hrQ) (Nat.le_refl 1)⟩, ?_⟩
  intro sol env hp hh r
  have hinv := comp_inv (sol := sol) (env := env) s hs hp 0
  refine ctx_equiv hspec (by omega) ⟨htin, htout, ?_, ?_⟩ hh r
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
