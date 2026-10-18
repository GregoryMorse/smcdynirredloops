module

public import SmcIrred.Arith.ModExp

public section

namespace SmcIrred.Arith

/-! Fixed-window exponentiation (C59): `modexpMontgomeryWindow`. -/

section Win
variable {α : Type} {N : Nat} (mulOp : α → α → α) (ρ : α → Nat) (P : α → Prop) (one b : α)

theorem getD_append_lt (t : List α) (x d : α) {j : Nat} (h : j < t.length) :
    (t ++ [x]).getD j d = t.getD j d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_len (t : List α) (x d : α) : (t ++ [x]).getD t.length d = x := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]

/-- Invariant of the power table after `n` steps: length `n + 2`, entry `j` represents `b^j`. -/
@[expose] def TblInv (t : List α) (n : Nat) : Prop :=
  t.length = n + 2 ∧ ∀ j, j < n + 2 → P (t.getD j one) ∧ Cong N (ρ (t.getD j one)) (ρ b ^ j)

theorem tbl_inv
    (hP1 : ∀ x y, P x → P y → P (mulOp x y))
    (hm : ∀ x y, P x → P y → Cong N (ρ (mulOp x y)) (ρ x * ρ y))
    (hone : P one) (hone_c : Cong N (ρ one) 1) (hb : P b) :
    ∀ n, TblInv (N := N) ρ P one b ((List.range n).foldl (tblStep mulOp one b) [one, b]) n := by
  intro n
  induction n with
  | zero =>
    refine ⟨rfl, ?_⟩
    intro j hj
    have : j = 0 ∨ j = 1 := by omega
    rcases this with rfl | rfl
    · exact ⟨hone, by simpa using hone_c⟩
    · exact ⟨hb, by simpa using Cong.refl N (ρ b)⟩
  | succ n ih =>
    obtain ⟨hlen, hent⟩ := ih
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize (List.range n).foldl (tblStep mulOp one b) [one, b] = t at hlen hent ⊢
    have hstep : tblStep mulOp one b t n = t ++ [if (n + 2) % 2 = 0 then
        mulOp (t.getD ((n + 2) / 2) one) (t.getD ((n + 2) / 2) one) else mulOp (t.getD (n + 2 - 1) one) b] := rfl
    rw [hstep]
    refine ⟨by simp [hlen], ?_⟩
    intro j hj
    by_cases hjl : j < n + 2
    · rw [getD_append_lt _ _ _ (by omega)]
      exact hent j hjl
    · have hj2 : j = n + 2 := by omega
      subst hj2
      have hl2 : (n + 2) = t.length := by omega
      rw [hl2, getD_append_len, ← hl2]
      by_cases hev : (n + 2) % 2 = 0
      · rw [if_pos hev]
        obtain ⟨hpu, hcu⟩ := hent ((n + 2) / 2) (by omega)
        refine ⟨hP1 _ _ hpu hpu, ?_⟩
        refine (hm _ _ hpu hpu).trans ?_
        have := hcu.mul hcu
        rw [← Nat.pow_add] at this
        have e : (n + 2) / 2 + (n + 2) / 2 = n + 2 := by omega
        rwa [e] at this
      · rw [if_neg hev]
        obtain ⟨hpu, hcu⟩ := hent (n + 2 - 1) (by omega)
        refine ⟨hP1 _ _ hpu hb, ?_⟩
        refine (hm _ _ hpu hb).trans ?_
        have := hcu.mul (Cong.refl N (ρ b))
        rw [← Nat.pow_succ] at this
        have e : (n + 2 - 1).succ = n + 2 := by omega
        rwa [e] at this

/-- `w` squarings square the exponent `w` times. -/
theorem sqLoop
    (hP1 : ∀ x y, P x → P y → P (mulOp x y))
    (hm : ∀ x y, P x → P y → Cong N (ρ (mulOp x y)) (ρ x * ρ y)) :
    ∀ (w : Nat) (res : α), P res →
      P ((List.range w).foldl (fun r _ => mulOp r r) res) ∧
      Cong N (ρ ((List.range w).foldl (fun r _ => mulOp r r) res)) (ρ res ^ 2 ^ w) := by
  intro w
  induction w with
  | zero => intro res hr; exact ⟨hr, by simpa using Cong.refl N (ρ res)⟩
  | succ w ih =>
    intro res hr
    obtain ⟨hp, hc⟩ := ih res hr
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize (List.range w).foldl (fun r _ => mulOp r r) res = r at hp hc ⊢
    refine ⟨hP1 r r hp hp, (hm r r hp hp).trans ?_⟩
    have := hc.mul hc
    rw [← Nat.pow_add] at this
    rwa [← Nat.mul_two, ← Nat.pow_succ] at this

end Win

section Loop
variable {α : Type} {N : Nat} (mulOp : α → α → α) (ρ : α → Nat) (P : α → Prop) (one b : α) (tbl : List α)
  (w e : Nat)

/-- The loop body of `winExp`. -/
@[expose] def winBody (res : α) (j : Nat) : α :=
  let res := mulOp (tbl.getD ((e >>> (j * w)) &&& (2 ^ w - 1)) one) res
  if j = 0 then res else (List.range w).foldl (fun r _ => mulOp r r) res

theorem digit_split (hw : 1 ≤ w) (j : Nat) :
    e / 2 ^ (j * w) = 2 ^ w * (e / 2 ^ ((j + 1) * w)) + (e / 2 ^ (j * w)) % 2 ^ w := by
  have h1 : e / 2 ^ ((j + 1) * w) = (e / 2 ^ (j * w)) / 2 ^ w := by
    rw [Nat.succ_mul, Nat.pow_add, Nat.div_div_eq_div_mul]
  rw [h1]
  exact (Nat.div_add_mod _ _).symm

theorem loop_spec
    (hP1 : ∀ x y, P x → P y → P (mulOp x y))
    (hm : ∀ x y, P x → P y → Cong N (ρ (mulOp x y)) (ρ x * ρ y))
    (hw : 1 ≤ w)
    (hT : ∀ j, j < 2 ^ w → P (tbl.getD j one) ∧ Cong N (ρ (tbl.getD j one)) (ρ b ^ j)) :
    ∀ (m : Nat) (res : α), P res →
      Cong N (ρ res) (ρ b ^ ((e / 2 ^ ((m + 1) * w)) * 2 ^ w)) →
      P (((List.range (m + 1)).reverse).foldl (winBody mulOp one tbl w e) res) ∧
      Cong N (ρ (((List.range (m + 1)).reverse).foldl (winBody mulOp one tbl w e) res)) (ρ b ^ e) := by
  intro m
  induction m with
  | zero =>
    intro res hr hc
    have hdig : (e >>> (0 * w)) &&& (2 ^ w - 1) = (e / 2 ^ (0 * w)) % 2 ^ w := by
      rw [Nat.shiftRight_eq_div_pow, Nat.and_two_pow_sub_one_eq_mod]
    have hlt : (e / 2 ^ (0 * w)) % 2 ^ w < 2 ^ w := Nat.mod_lt _ (Nat.two_pow_pos w)
    obtain ⟨hpt, hct⟩ := hT _ hlt
    simp only [List.range_succ, List.range_zero, List.nil_append, List.reverse_cons, List.reverse_nil,
      List.foldl_cons, List.foldl_nil, winBody]
    simp only [hdig, if_true]
    refine ⟨hP1 _ _ hpt hr, (hm _ _ hpt hr).trans ?_⟩
    have h1 := hct.mul hc
    rw [← Nat.pow_add] at h1
    have hs := digit_split w e hw 0
    have e0 : e / 2 ^ (0 * w) = e := by simp
    rw [e0] at hs
    have e1 : (e / 2 ^ (0 * w)) % 2 ^ w = e % 2 ^ w := by rw [e0]
    rw [e1] at h1
    have : e % 2 ^ w + e / 2 ^ ((0 + 1) * w) * 2 ^ w = e := by
      have h2 := hs
      rw [Nat.mul_comm (e / 2 ^ ((0 + 1) * w)) (2 ^ w)]
      omega
    rw [this] at h1
    rw [e0]
    exact h1
  | succ m ih =>
    intro res hr hc
    have hdig : (e >>> ((m + 1) * w)) &&& (2 ^ w - 1) = (e / 2 ^ ((m + 1) * w)) % 2 ^ w := by
      rw [Nat.shiftRight_eq_div_pow, Nat.and_two_pow_sub_one_eq_mod]
    have hlt : (e / 2 ^ ((m + 1) * w)) % 2 ^ w < 2 ^ w := Nat.mod_lt _ (Nat.two_pow_pos w)
    obtain ⟨hpt, hct⟩ := hT _ hlt
    have hrev : (List.range (m + 1 + 1)).reverse = (m + 1) :: (List.range (m + 1)).reverse := by
      rw [List.range_succ, List.reverse_append]; rfl
    rw [hrev, List.foldl_cons]
    have hbody : winBody mulOp one tbl w e res (m + 1) =
        (List.range w).foldl (fun r _ => mulOp r r) (mulOp (tbl.getD ((e / 2 ^ ((m + 1) * w)) % 2 ^ w) one) res) := by
      unfold winBody
      rw [hdig, if_neg (by omega)]
    rw [hbody]
    have hp1 := hP1 _ _ hpt hr
    obtain ⟨hps, hcs⟩ := sqLoop mulOp ρ P hP1 hm w _ hp1
    have hmul := (hm _ _ hpt hr).trans (hct.mul hc)
    rw [← Nat.pow_add] at hmul
    have hsplit := digit_split w e hw (m + 1)
    have hcomb : (e / 2 ^ ((m + 1 + 1) * w)) % 2 ^ w * 0 = 0 := Nat.mul_zero _
    have hexp : (e / 2 ^ ((m + 1) * w)) % 2 ^ w + e / 2 ^ ((m + 1 + 1) * w) * 2 ^ w = e / 2 ^ ((m + 1) * w) := by
      rw [Nat.mul_comm (e / 2 ^ ((m + 1 + 1) * w)) (2 ^ w)]
      omega
    rw [hexp] at hmul
    have hpow := hmul.pow (2 ^ w)
    rw [← Nat.pow_mul] at hpow
    exact ih _ hps (hcs.trans hpow)

end Loop

section Main
variable {α : Type} {N : Nat} (mulOp : α → α → α) (ρ : α → Nat) (P : α → Prop) (one b : α) (B w e : Nat)

theorem nW_mul (hw : 1 ≤ w) : B ≤ ((B + w - 1) / w) * w := by
  have h1 := Nat.div_add_mod (B + w - 1) w
  have h2 := Nat.mod_lt (B + w - 1) (show 0 < w by omega)
  rw [Nat.mul_comm w ((B + w - 1) / w)] at h1
  omega

/-- Fixed-window exponentiation computes `b^e` for every window size `w ≥ 1` and every exponent `e < 2^B`. -/
theorem winExp_spec
    (hP1 : ∀ x y, P x → P y → P (mulOp x y))
    (hm : ∀ x y, P x → P y → Cong N (ρ (mulOp x y)) (ρ x * ρ y))
    (hone : P one) (hone_c : Cong N (ρ one) 1) (hb : P b) (hw : 1 ≤ w) (he : e < 2 ^ B) :
    P (winExp mulOp one b B w e) ∧ Cong N (ρ (winExp mulOp one b B w e)) (ρ b ^ e) := by
  have htbl := tbl_inv (N := N) mulOp ρ P one b hP1 hm hone hone_c hb (2 ^ w - 2)
  have hT : ∀ j, j < 2 ^ w → P ((winTbl mulOp one b w).getD j one) ∧
      Cong N (ρ ((winTbl mulOp one b w).getD j one)) (ρ b ^ j) := by
    intro j hj
    have h2 : 2 ≤ 2 ^ w := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hw
    exact htbl.2 j (by omega)
  unfold winExp
  dsimp only
  generalize winTbl mulOp one b w = tbl at hT ⊢
  by_cases hnW : (B + w - 1) / w = 0
  · rw [hnW]
    have hB : B = 0 := by
      have := nW_mul B w hw
      rw [hnW] at this; omega
    subst hB
    have : e = 0 := by simpa using he
    subst this
    refine ⟨hone, ?_⟩
    simpa using hone_c
  · obtain ⟨m, hm'⟩ := Nat.exists_eq_succ_of_ne_zero hnW
    simp only [Nat.succ_eq_add_one] at hm'
    rw [hm']
    have hdiv : e / 2 ^ ((m + 1) * w) = 0 := by
      apply Nat.div_eq_of_lt
      have h1 : B ≤ (m + 1) * w := by have := nW_mul B w hw; rwa [hm'] at this
      calc e < 2 ^ B := he
        _ ≤ 2 ^ ((m + 1) * w) := Nat.pow_le_pow_right (by decide) h1
    have hl := loop_spec mulOp ρ P one b tbl w e hP1 hm hw hT m one hone
      (by rw [hdiv]; simpa using hone_c)
    exact hl

end Main

/-! ### Montgomery instance -/

section MontWin
variable {B N Np R2 Ri : Nat}

theorem modexpMontWin_correct (hN : 0 < N) (hodd : N % 2 = 1) (hNp : (N * Np + 1) % 2 ^ B = 0)
    (hRi : Cong N (2 ^ B * Ri) 1) (hNR : N ≤ 2 ^ B) (hR2 : R2 = (2 ^ B * 2 ^ B) % N) {a : Nat} (ha : a < N)
    {w : Nat} (hw : 1 ≤ w) {e : Nat} (he : e < 2 ^ B) :
    redc B N Np (modexpMontWin B N Np R2 w (toM B N Np R2 a) e) = a ^ e % N := by
  by_cases hN1 : N = 1
  · subst hN1
    simp [modexpMontWin, redc, bound, Nat.mod_one]
  · have hR2lt : R2 < N := by rw [hR2]; exact Nat.mod_lt _ hN
    have hNN : N ≤ 2 ^ B * N := Nat.le_mul_of_pos_left N (Nat.two_pow_pos B)
    have h0lt : redc B N Np R2 < N := (redc_spec hN hNp (by omega : R2 < 2 ^ B * N)).1
    have hone_c : Cong N (redc B N Np R2 * Ri) 1 := by
      have h1 := redc_cong hN hNp hRi (by omega : R2 < 2 ^ B * N)
      have h2 : Cong N R2 (2 ^ B * 2 ^ B) := by rw [hR2]; exact Cong.of_mod N _
      have h3 : Cong N (redc B N Np R2 * Ri) ((2 ^ B * 2 ^ B) * Ri * Ri) :=
        (h1.trans (h2.mul_right Ri)).mul_right Ri
      have h4 : (2 ^ B * 2 ^ B) * Ri * Ri = (2 ^ B * Ri) * (2 ^ B * Ri) := by ac_rfl
      rw [h4] at h3
      exact h3.trans (hRi.mul hRi)
    obtain ⟨hA, hAc⟩ := toM_spec hN hNp hRi hNR hR2 ha
    have hf := winExp_spec (N := N) (fun x y : Nat => redc B N Np (x * y)) (fun x => x * Ri) (fun x => x < N)
      (redc B N Np R2) (toM B N Np R2 a) B w e
      (fun x y hx hy => (mmul_spec hN hNp hRi hNR hx hy).1)
      (fun x y hx hy => by
        have h := (mmul_spec hN hNp hRi hNR hx hy).2
        have h2 : Cong N (redc B N Np (x * y) * Ri) (x * y * Ri * Ri) := h.mul_right Ri
        have h3 : x * y * Ri * Ri = x * Ri * (y * Ri) := by ac_rfl
        rw [h3] at h2; exact h2)
      h0lt hone_c hA hw he
    obtain ⟨hr, hrc⟩ := hf
    have hrR : winExp (fun x y : Nat => redc B N Np (x * y)) (redc B N Np R2) (toM B N Np R2 a) B w e
        < 2 ^ B * N := by omega
    have h1 := redc_cong hN hNp hRi hrR
    have h2 : Cong N (toM B N Np R2 a * Ri) a := by
      have h3 : Cong N (toM B N Np R2 a * Ri) (a * 2 ^ B * Ri) := hAc.mul_right Ri
      have h4 : Cong N (a * 2 ^ B * Ri) a := by
        rw [Nat.mul_assoc]
        have := hRi.mul_left a
        rwa [Nat.mul_one] at this
      exact h3.trans h4
    have h6 := h1.trans (hrc.trans (h2.pow e))
    unfold Cong at h6
    rw [Nat.mod_eq_of_lt (redc_spec hN hNp hrR).1] at h6
    unfold modexpMontWin
    rw [if_neg hN1]
    exact h6

end MontWin

/-! ### Operation counts -/

theorem foldl_count (c0 n : Nat) : (List.range n).foldl (fun c _ => c + 1) c0 = c0 + n := by
  induction n generalizing c0 with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih]; omega

/-- The table costs `2^w - 2` products. -/
theorem tblMuls_eq (w : Nat) : tblMuls w = 2 ^ w - 2 := by
  unfold tblMuls; rw [foldl_count]; omega

theorem loop_count (w : Nat) : ∀ (m c0 : Nat), 1 ≤ m →
    ((List.range m).reverse).foldl (fun c j => c + 1 + (if j = 0 then 0 else w)) c0 = c0 + m + w * (m - 1) := by
  intro m
  induction m with
  | zero => intro c0 h; omega
  | succ m ih =>
    intro c0 _
    rw [List.range_succ, List.reverse_append, List.reverse_cons, List.reverse_nil]
    simp only [List.nil_append, List.cons_append, List.foldl_cons]
    by_cases hm : m = 0
    · subst hm; simp
    · rw [if_neg hm, ih _ (by omega)]
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      rw [Nat.mul_add, Nat.mul_one]
      omega

/-- Window loop: `⌈B/w⌉` window products and `w (⌈B/w⌉ - 1)` squarings. -/
theorem loopMuls_eq (B w : Nat) (h : 1 ≤ (B + w - 1) / w) :
    loopMuls B w = (B + w - 1) / w + w * ((B + w - 1) / w - 1) := by
  unfold loopMuls
  rw [loop_count w _ 0 h]; omega

/-- Total multiplications of the windowed method. -/
theorem winMuls_total (B w : Nat) (h : 1 ≤ (B + w - 1) / w) :
    tblMuls w + loopMuls B w = (2 ^ w - 2) + (B + w - 1) / w + w * ((B + w - 1) / w - 1) := by
  rw [tblMuls_eq, loopMuls_eq B w h]; omega

/-- The window sizes chosen by the code for the benchmark sizes, and that they minimize `⌈B/w⌉ + 2^w - 2`. -/
theorem bestW_values : bestW 32 = 3 ∧ bestW 64 = 3 ∧ bestW 128 = 4 ∧ bestW 256 = 4 ∧ bestW 512 = 5 ∧
    bestW 1024 = 6 ∧ bestW 2048 = 6 ∧ bestW 4096 = 7 := by decide +kernel

theorem bestW_minimal (B : Nat) : (List.range B.log2).all (fun i => decide (wCost B (bestW B) ≤ wCost B (i + 1))) = true →
    ∀ w, 1 ≤ w → w ≤ B.log2 → wCost B (bestW B) ≤ wCost B w := by
  intro h w h1 h2
  have := List.all_eq_true.1 h (w - 1) (List.mem_range.2 (by omega))
  simpa [show w - 1 + 1 = w by omega] using this

theorem bestW_min_32 : (List.range (Nat.log2 32)).all (fun i => decide (wCost 32 (bestW 32) ≤ wCost 32 (i + 1))) = true := by decide +kernel
theorem bestW_min_64 : (List.range (Nat.log2 64)).all (fun i => decide (wCost 64 (bestW 64) ≤ wCost 64 (i + 1))) = true := by decide +kernel
theorem bestW_min_128 : (List.range (Nat.log2 128)).all (fun i => decide (wCost 128 (bestW 128) ≤ wCost 128 (i + 1))) = true := by decide +kernel
theorem bestW_min_256 : (List.range (Nat.log2 256)).all (fun i => decide (wCost 256 (bestW 256) ≤ wCost 256 (i + 1))) = true := by decide +kernel

end SmcIrred.Arith
