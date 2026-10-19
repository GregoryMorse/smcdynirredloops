module

public import SmcIrred.Prims.Ripple
public import SmcIrred.Prims.Bridge

public section

namespace SmcIrred

/-! # The n-bit adder graph (G30 a, C48, P05)

`addition_to_virtual` (`addLoop`, `addition`) builds a ripple adder or subtractor in the generator state.  The theorems
below are about the generated graph: the wires it returns have the values of the ripple equations (`ripple`), hence the
numbers `(a + b) mod 2^n` with the final carry (`issub = false`) or `(a - b) mod 2^n` with the final borrow
(`issub = true`), and the circuit `toCirc` of the generator state evaluates to these values. -/

/-- The bits the loop returns, as pure Boolean data. -/
@[expose] def adderBits (f : Bool) (nc : Bool) : Bool → List (Bool × Bool) → List Bool
  | _, [] => []
  | c, [p] => if nc then [(p.1 != p.2) != c, cout p.1 p.2 c f] else [(p.1 != p.2) != c]
  | c, p :: q :: rest => ((p.1 != p.2) != c) :: adderBits f nc (cout p.1 p.2 c f) (q :: rest)

theorem adderBits_ripple (f nc : Bool) : ∀ (ps : List (Bool × Bool)) (c : Bool), ps ≠ [] →
    adderBits f nc c ps = if nc then (ripple f c ps).1 ++ [(ripple f c ps).2] else (ripple f c ps).1 := by
  intro ps
  induction ps with
  | nil => intro c h; exact absurd rfl h
  | cons p t ih =>
    intro c _
    cases t with
    | nil => cases nc <;> simp [adderBits, ripple]
    | cons q rest =>
      have h := ih (cout p.1 p.2 c f) (by simp)
      simp only [adderBits, ripple, h]
      cases nc <;> simp

theorem ok_of_ext {gb gb' : GB} (e : Ext gb gb') {w : Wire} (h : w.ok gb.n) : w.ok gb'.n := ok_mono h e.n_le

section Loop

variable {inp : Nat → Bool} {k : Nat}

theorem addBitNoCarry_post (hinp : ∀ i, k ≤ i → inp i = false) {gb : GB} (hk : k ≤ gb.n) (hr : Reach gb)
    {n1 n2 carry : Wire} (h1 : n1.ok gb.n) (h2 : n2.ok gb.n) (h3 : carry.ok gb.n) :
    Ext gb (addBitNoCarry gb n1 n2 carry).2 ∧ Reach (addBitNoCarry gb n1 n2 carry).2 ∧
      (addBitNoCarry gb n1 n2 carry).1.ok (addBitNoCarry gb n1 n2 carry).2.n ∧
      wev (addBitNoCarry gb n1 n2 carry).2 inp (addBitNoCarry gb n1 n2 carry).1 =
        ((wev gb inp n1 != wev gb inp n2) != wev gb inp carry) := by
  unfold addBitNoCarry
  have p := xorV_post hinp hk hr [n1, n2, carry] (ok3 h1 h2 h3)
  simp only [List.map_cons, List.map_nil, xorL_three] at p
  exact ⟨p.ext, p.reach, p.ok, p.val⟩

theorem addLoop_post (hinp : ∀ i, k ≤ i → inp i = false) (issub : Wire) (nc : Bool) :
    ∀ (ps : List (Wire × Wire)) (gb : GB) (carry : Wire), k ≤ gb.n → Reach gb → issub.ok gb.n → carry.ok gb.n →
      (∀ p ∈ ps, p.1.ok gb.n ∧ p.2.ok gb.n) →
      Ext gb (addLoop issub nc gb carry ps).2 ∧ Reach (addLoop issub nc gb carry ps).2 ∧
      (∀ w ∈ (addLoop issub nc gb carry ps).1, w.ok (addLoop issub nc gb carry ps).2.n) ∧
      (addLoop issub nc gb carry ps).1.map (wev (addLoop issub nc gb carry ps).2 inp) =
        adderBits (wev gb inp issub) nc (wev gb inp carry) (ps.map fun p => (wev gb inp p.1, wev gb inp p.2)) := by
  intro ps
  induction ps with
  | nil =>
    intro gb carry hk hr hs hc hps
    simp [addLoop, adderBits, Ext.refl, hr]
  | cons p t ih =>
    intro gb carry hk hr hs hc hps
    have hp1 : p.1.ok gb.n := (hps p (by simp)).1
    have hp2 : p.2.ok gb.n := (hps p (by simp)).2
    cases t with
    | nil =>
      cases nc with
      | true =>
        have pa := addBit_post hinp hk hr hp1 hp2 hc hs
        simp only [addLoop, ite_true]
        refine ⟨pa.1, pa.2.1, ?_, ?_⟩
        · intro w hw
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
          rcases hw with rfl | rfl
          · exact pa.2.2.1
          · exact pa.2.2.2.1
        · simp only [List.map_cons, List.map_nil, adderBits, ite_true]
          rw [pa.2.2.2.2.1, pa.2.2.2.2.2]
      | false =>
        have pa := addBitNoCarry_post hinp hk hr hp1 hp2 hc
        simp only [addLoop, Bool.false_eq_true, ite_false]
        refine ⟨pa.1, pa.2.1, ?_, ?_⟩
        · intro w hw
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
          rw [hw]; exact pa.2.2.1
        · simp only [List.map_cons, List.map_nil, adderBits, Bool.false_eq_true, ite_false]
          rw [pa.2.2.2]
    | cons q rest =>
      have pa := addBit_post hinp hk hr hp1 hp2 hc hs
      have e1 := pa.1
      have hk1 : k ≤ (addBit gb p.1 p.2 carry issub).2.n := Nat.le_trans hk e1.n_le
      have hs1 : issub.ok (addBit gb p.1 p.2 carry issub).2.n := ok_of_ext e1 hs
      have hps1 : ∀ p' ∈ q :: rest, p'.1.ok (addBit gb p.1 p.2 carry issub).2.n ∧ p'.2.ok (addBit gb p.1 p.2 carry issub).2.n :=
        fun p' hp' => ⟨ok_of_ext e1 (hps p' (by simp [hp'])).1, ok_of_ext e1 (hps p' (by simp [hp'])).2⟩
      have ihh := ih (addBit gb p.1 p.2 carry issub).2 (addBit gb p.1 p.2 carry issub).1.2 hk1 pa.2.1 hs1 pa.2.2.2.1 hps1
      simp only [addLoop]
      refine ⟨e1.trans ihh.1, ihh.2.1, ?_, ?_⟩
      · intro w hw
        simp only [List.mem_cons] at hw
        rcases hw with rfl | hw
        · exact ok_of_ext ihh.1 pa.2.2.1
        · exact ihh.2.2.1 w hw
      · simp only [List.map_cons]
        have hv : wev (addLoop issub nc (addBit gb p.1 p.2 carry issub).2 (addBit gb p.1 p.2 carry issub).1.2 (q :: rest)).2 inp
            (addBit gb p.1 p.2 carry issub).1.1 = ((wev gb inp p.1 != wev gb inp p.2) != wev gb inp carry) := by
          rw [wev_ext ihh.1 pa.2.2.1, pa.2.2.2.2.1]
        rw [hv, ihh.2.2.2]
        have s1 : wev (addBit gb p.1 p.2 carry issub).2 inp issub = wev gb inp issub := wev_ext e1 hs
        have s2 : wev (addBit gb p.1 p.2 carry issub).2 inp (addBit gb p.1 p.2 carry issub).1.2 =
            cout (wev gb inp p.1) (wev gb inp p.2) (wev gb inp carry) (wev gb inp issub) := pa.2.2.2.2.2
        have hmap : (q :: rest).map (fun p' => (wev (addBit gb p.1 p.2 carry issub).2 inp p'.1,
            wev (addBit gb p.1 p.2 carry issub).2 inp p'.2)) =
            (q :: rest).map (fun p' => (wev gb inp p'.1, wev gb inp p'.2)) :=
          List.map_congr_left (fun p' hp' => by
            rw [wev_ext e1 (hps p' (by simp [hp'])).1, wev_ext e1 (hps p' (by simp [hp'])).2])
        rw [s1, s2, hmap]
        simp only [List.map_cons, adderBits]

end Loop

/-! ### The whole adder -/

theorem bv_append (l : List Bool) : ∀ m : List Bool, bv (l ++ m) = bv l + 2 ^ l.length * bv m := by
  induction l with
  | nil => intro m; simp [bv]
  | cons b t ih =>
    intro m
    simp only [List.cons_append, bv, ih, List.length_cons, Nat.pow_succ]
    rw [Nat.mul_comm (2 ^ t.length) 2, Nat.mul_assoc, Nat.mul_add]
    omega

theorem bv_pad (l : List Bool) (k : Nat) : bv (l ++ List.replicate k false) = bv l := by
  rw [bv_append]
  have : bv (List.replicate k false) = 0 := by
    induction k with
    | zero => rfl
    | succ k ih => simp [List.replicate_succ, bv, ih]
  rw [this]; simp

theorem zeroExt_ok {n : Nat} {a : List Wire} (m : Nat) (h : ∀ w ∈ a, w.ok n) : ∀ w ∈ zeroExt m a, w.ok n := by
  intro w hw
  unfold zeroExt at hw
  rcases List.mem_append.1 hw with h1 | h1
  · exact h w h1
  · rw [(List.mem_replicate.1 h1).2]; trivial

theorem zeroExt_vals (gb : GB) (inp : Nat → Bool) (m : Nat) (a : List Wire) :
    (zeroExt m a).map (wev gb inp) = a.map (wev gb inp) ++ List.replicate (m - a.length) false := by
  unfold zeroExt
  rw [List.map_append]
  congr 1
  rw [List.map_replicate]; rfl

theorem zeroExt_length {a : List Wire} {m : Nat} (h : a.length ≤ m) : (zeroExt m a).length = m := by
  unfold zeroExt; simp; omega

theorem zip_fst_snd {α β : Type} : ∀ (as : List α) (bs : List β), as.length = bs.length →
    (as.zip bs).map Prod.fst = as ∧ (as.zip bs).map Prod.snd = bs := by
  intro as
  induction as with
  | nil => intro bs h; cases bs <;> simp_all
  | cons a t ih =>
    intro bs h
    cases bs with
    | nil => simp at h
    | cons b bt =>
      have := ih bt (by simpa using h)
      simp [this.1, this.2]

theorem map_pair_zip {α β : Type} (f : α → β) : ∀ (l1 l2 : List α),
    (l1.zip l2).map (fun p => (f p.1, f p.2)) = (l1.map f).zip (l2.map f) := by
  intro l1
  induction l1 with
  | nil => intro l2; simp
  | cons a t ih => intro l2; cases l2 <;> simp [ih]

/-- The adder graph computes the ripple equations on the (zero-extended) operands. -/
theorem addition_post {inp : Nat → Bool} {k : Nat} (hinp : ∀ i, k ≤ i → inp i = false) {gb : GB} (hk : k ≤ gb.n)
    (hr : Reach gb) {a b : List Wire} {issub : Wire} (nc : Bool) (ha : ∀ w ∈ a, w.ok gb.n) (hb : ∀ w ∈ b, w.ok gb.n)
    (hs : issub.ok gb.n) :
    Ext gb (addition gb a b issub nc).2 ∧ Reach (addition gb a b issub nc).2 ∧
    (∀ w ∈ (addition gb a b issub nc).1, w.ok (addition gb a b issub nc).2.n) ∧
    (addition gb a b issub nc).1.map (wev (addition gb a b issub nc).2 inp) =
      adderBits (wev gb inp issub) nc false
        (((a.map (wev gb inp) ++ List.replicate (max a.length b.length - a.length) false).zip
          (b.map (wev gb inp) ++ List.replicate (max a.length b.length - b.length) false))) := by
  unfold addition
  have hza := zeroExt_ok (max a.length b.length) ha
  have hzb := zeroExt_ok (max a.length b.length) hb
  have hps : ∀ p ∈ (zeroExt (max a.length b.length) a).zip (zeroExt (max a.length b.length) b), p.1.ok gb.n ∧ p.2.ok gb.n :=
    fun p hp => ⟨hza _ (List.of_mem_zip hp).1, hzb _ (List.of_mem_zip hp).2⟩
  have h := addLoop_post hinp issub nc _ gb (.cst false) hk hr hs trivial hps
  refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
  rw [h.2.2.2]
  have e : wev gb inp (.cst false) = false := rfl
  rw [e]
  congr 1
  rw [map_pair_zip, zeroExt_vals, zeroExt_vals]

/-- The padded operand pairs of the adder. -/
@[expose] def padPairs (a b : List Bool) : List (Bool × Bool) :=
  (a ++ List.replicate (max a.length b.length - a.length) false).zip (b ++ List.replicate (max a.length b.length - b.length) false)

theorem padPairs_fst (a b : List Bool) : bv ((padPairs a b).map Prod.fst) = bv a := by
  unfold padPairs
  have h := zip_fst_snd (a ++ List.replicate (max a.length b.length - a.length) false)
    (b ++ List.replicate (max a.length b.length - b.length) false) (by simp; omega)
  rw [h.1, bv_pad]

theorem padPairs_snd (a b : List Bool) : bv ((padPairs a b).map Prod.snd) = bv b := by
  unfold padPairs
  have h := zip_fst_snd (a ++ List.replicate (max a.length b.length - a.length) false)
    (b ++ List.replicate (max a.length b.length - b.length) false) (by simp; omega)
  rw [h.2, bv_pad]

theorem padPairs_length (a b : List Bool) : (padPairs a b).length = max a.length b.length := by
  unfold padPairs
  rw [List.length_zip]
  simp only [List.length_append, List.length_replicate]
  omega

/-- Addition (`issub` false, carry out wanted): the returned wires hold the number `a + b` (with the carry as top bit). -/
theorem adderBits_add_value (a b : List Bool) :
    bv (adderBits false true false (padPairs a b)) = bv a + bv b := by
  by_cases h : padPairs a b = []
  · have hl := padPairs_length a b
    rw [h] at hl
    have ha : a = [] := List.length_eq_zero_iff.1 (by simp at hl; omega)
    have hb : b = [] := List.length_eq_zero_iff.1 (by simp at hl; omega)
    subst ha; subst hb
    rw [h]; rfl
  · rw [adderBits_ripple _ _ _ _ h]
    simp only [ite_true]
    rw [bv_append, ripple_length]
    have := ripple_add (padPairs a b) false
    rw [padPairs_fst, padPairs_snd] at this
    have hb : ∀ x : Bool, bv [x] = b2n x := fun x => by simp [bv, b2n]
    have e : b2n false = 0 := rfl
    rw [hb]
    rw [e] at this
    omega

/-- Subtraction (`issub` true): the sum bits `d` and the borrow `r` satisfy `d + b = a + 2^m * r`, i.e. `d = (a - b) mod 2^m`
and `r = [a < b]`. -/
theorem adderBits_sub_value (a b : List Bool) :
    bv (adderBits true false false (padPairs a b)) + bv b = bv a + 2 ^ (max a.length b.length) * b2n (ripple true false (padPairs a b)).2 := by
  by_cases h : padPairs a b = []
  · have hl := padPairs_length a b
    rw [h] at hl
    have ha : a = [] := List.length_eq_zero_iff.1 (by simp at hl; omega)
    have hb : b = [] := List.length_eq_zero_iff.1 (by simp at hl; omega)
    subst ha; subst hb
    rw [h]; simp [adderBits, bv, ripple, b2n]
  · rw [adderBits_ripple _ _ _ _ h]
    simp only [Bool.false_eq_true, ite_false]
    have := ripple_sub (padPairs a b) false
    rw [padPairs_fst, padPairs_snd, padPairs_length] at this
    have e : b2n false = 0 := rfl
    rw [e] at this
    omega

/-- The value of a wire in the circuit of a generator state (constants are constants). -/
@[expose] def Wire.cval (gb : GB) (lib : Lib) (d : Nat) (inp : Nat → Bool) : Wire → Bool
  | .cst b => b
  | .nd i => gb.toCirc.val lib d inp i

theorem cval_eq_wev {gb : GB} (hr : Reach gb) (lib : Lib) (d : Nat) (inp : Nat → Bool) {w : Wire} (hw : w.ok gb.n) :
    w.cval gb lib d inp = wev gb inp w := by
  cases w with
  | cst b => rfl
  | nd i => exact toCirc_val_eq inp lib d hr hw

/-- **The generated adder graph adds.**  For operands that are wires of the generator state `gb`, the wires returned by
`addition_to_virtual` (carry wanted, no subtraction), read in the circuit `toCirc` of the extended state with the Boolean-CFG
evaluator at any depth and library, form the number `a + b` (the carry is the top bit). -/
theorem adder_graph_adds {inp : Nat → Bool} {k : Nat} (hinp : ∀ i, k ≤ i → inp i = false) {gb : GB} (hk : k ≤ gb.n)
    (hr : Reach gb) {a b : List Wire} (ha : ∀ w ∈ a, w.ok gb.n) (hb : ∀ w ∈ b, w.ok gb.n) (lib : Lib) (d : Nat) :
    Reach (addition gb a b (.cst false) true).2 ∧
    bv ((addition gb a b (.cst false) true).1.map (Wire.cval (addition gb a b (.cst false) true).2 lib d inp)) =
      bv (a.map (wev gb inp)) + bv (b.map (wev gb inp)) := by
  have h := addition_post hinp hk hr (issub := .cst false) true ha hb trivial
  refine ⟨h.2.1, ?_⟩
  have e : (addition gb a b (.cst false) true).1.map (Wire.cval (addition gb a b (.cst false) true).2 lib d inp) =
      (addition gb a b (.cst false) true).1.map (wev (addition gb a b (.cst false) true).2 inp) :=
    List.map_congr_left (fun w hw => cval_eq_wev h.2.1 lib d inp (h.2.2.1 w hw))
  rw [e, h.2.2.2]
  have hf : wev gb inp (.cst false) = false := rfl
  rw [hf]
  rw [show (a.map (wev gb inp) ++ List.replicate (max a.length b.length - a.length) false).zip
        (b.map (wev gb inp) ++ List.replicate (max a.length b.length - b.length) false) =
      padPairs (a.map (wev gb inp)) (b.map (wev gb inp)) by simp [padPairs]]
  exact adderBits_add_value _ _

/-- Subtraction: with `issub` true the returned sum bits `r` and the borrow `o` satisfy `r + b = a + 2^m * o`. -/
theorem adder_graph_subtracts {inp : Nat → Bool} {k : Nat} (hinp : ∀ i, k ≤ i → inp i = false) {gb : GB} (hk : k ≤ gb.n)
    (hr : Reach gb) {a b : List Wire} (ha : ∀ w ∈ a, w.ok gb.n) (hb : ∀ w ∈ b, w.ok gb.n) (lib : Lib) (d : Nat) :
    Reach (addition gb a b (.cst true) false).2 ∧
    bv ((addition gb a b (.cst true) false).1.map (Wire.cval (addition gb a b (.cst true) false).2 lib d inp)) +
        bv (b.map (wev gb inp)) =
      bv (a.map (wev gb inp)) + 2 ^ (max a.length b.length) *
        b2n (ripple true false (padPairs (a.map (wev gb inp)) (b.map (wev gb inp)))).2 := by
  have h := addition_post hinp hk hr (issub := .cst true) false ha hb trivial
  refine ⟨h.2.1, ?_⟩
  have e : (addition gb a b (.cst true) false).1.map (Wire.cval (addition gb a b (.cst true) false).2 lib d inp) =
      (addition gb a b (.cst true) false).1.map (wev (addition gb a b (.cst true) false).2 inp) :=
    List.map_congr_left (fun w hw => cval_eq_wev h.2.1 lib d inp (h.2.2.1 w hw))
  rw [e, h.2.2.2]
  have hf : wev gb inp (.cst true) = true := rfl
  rw [hf]
  rw [show (a.map (wev gb inp) ++ List.replicate (max a.length b.length - a.length) false).zip
        (b.map (wev gb inp) ++ List.replicate (max a.length b.length - b.length) false) =
      padPairs (a.map (wev gb inp)) (b.map (wev gb inp)) by simp [padPairs]]
  have := adderBits_sub_value (a.map (wev gb inp)) (b.map (wev gb inp))
  simpa using this

end SmcIrred
