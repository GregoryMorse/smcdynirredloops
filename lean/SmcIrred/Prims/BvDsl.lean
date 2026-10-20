module

public import SmcIrred.Spec.BvDsl
public import SmcIrred.Prims.AdderGraph
public import SmcIrred.Prims.MapG
public import SmcIrred.Prims.Nat
public import SmcIrred.Prims.SelPost

public section

namespace SmcIrred

/-! # Compiler correctness of the bit-vector language (C48, G30 b)

For every expression whose wires exist in the generator state, `BvExp.comp` extends the state (all old values unchanged),
keeps it reachable by simple node kinds, returns existing wires, and the returned wires evaluate to `BvExp.sem` of the old
values.  The same holds in the circuit `toCirc` of the extended state under the Boolean-CFG evaluator at any depth and
library (`comp_circuit_correct`).  `sem` itself is arithmetic: the bitwise operations act position by position, the sum is
the sum with its carry bit and the difference is taken modulo `2^m` (`sem_add_val`, `sem_sub_val`). -/

theorem Wire.inb_iff (n : Nat) (w : Wire) : w.inb n ↔ w.ok n := by cases w <;> exact Iff.rfl

theorem natBits_length (m i : Nat) : (natBits i m).length = m := by
  rw [natBits_eq_bitsOf]; exact bitsOf_length m i

theorem bv_natBits (m i : Nat) (h : i < 2 ^ m) : bv (natBits i m) = i := by
  rw [natBits_eq_bitsOf]; exact bv_bitsOf m i h

theorem padPairs_len_eq (a b : List Bool) : (padPairs a b).length = max a.length b.length := padPairs_length a b

theorem adderBits_len_add (a b : List Bool) :
    (adderBits false true false (padPairs a b)).length = addWidth (max a.length b.length) := by
  by_cases h : padPairs a b = []
  · have hl := padPairs_length a b
    rw [h] at hl
    have : max a.length b.length = 0 := by simpa using hl.symm
    rw [h, this]; rfl
  · rw [adderBits_ripple _ _ _ _ h]
    simp only [ite_true, List.length_append, ripple_length, List.length_singleton, padPairs_length]
    have : max a.length b.length ≠ 0 := by
      intro h0; apply h
      have hl := padPairs_length a b
      rw [h0] at hl
      exact List.length_eq_zero_iff.1 hl
    unfold addWidth; rw [if_neg this]

theorem adderBits_len_sub (a b : List Bool) :
    (adderBits true false false (padPairs a b)).length = max a.length b.length := by
  by_cases h : padPairs a b = []
  · have hl := padPairs_length a b
    rw [h] at hl
    have h0 : max a.length b.length = 0 := by simpa using hl.symm
    rw [h, h0]; rfl
  · rw [adderBits_ripple _ _ _ _ h]
    simp only [Bool.false_eq_true, ite_false, ripple_length, padPairs_length]

/-- The ripple adder's bits are the binary digits of the sum, with the carry bit on top. -/
theorem adderBits_add_eq (a b : List Bool) :
    adderBits false true false (padPairs a b) =
      natBits (bv a + bv b) (addWidth (max a.length b.length)) := by
  apply bv_inj
  · rw [adderBits_len_add, natBits_length]
  · rw [adderBits_add_value]
    symm
    apply bv_natBits
    have h1 := bv_lt a
    have h2 := bv_lt b
    have e1 : 2 ^ a.length ≤ 2 ^ max a.length b.length := Nat.pow_le_pow_right (by omega) (by omega)
    have e2 : 2 ^ b.length ≤ 2 ^ max a.length b.length := Nat.pow_le_pow_right (by omega) (by omega)
    unfold addWidth
    by_cases hm : max a.length b.length = 0
    · have : a.length = 0 := by omega
      have : b.length = 0 := by omega
      have h3 : bv a < 1 := by simpa [*] using h1
      have h4 : bv b < 1 := by simpa [*] using h2
      rw [if_pos hm]; simp; omega
    · rw [if_neg hm, Nat.pow_succ]
      omega

/-- The ripple subtractor's bits are the binary digits of the difference modulo `2^m`. -/
theorem adderBits_sub_eq (a b : List Bool) :
    adderBits true false false (padPairs a b) =
      natBits ((bv a + 2 ^ max a.length b.length - bv b) % 2 ^ max a.length b.length) (max a.length b.length) := by
  have hlen := adderBits_len_sub a b
  have hP : 0 < 2 ^ max a.length b.length := Nat.two_pow_pos _
  have h1 := bv_lt a
  have h2 := bv_lt b
  have e1 : 2 ^ a.length ≤ 2 ^ max a.length b.length := Nat.pow_le_pow_right (by omega) (by omega)
  have e2 : 2 ^ b.length ≤ 2 ^ max a.length b.length := Nat.pow_le_pow_right (by omega) (by omega)
  have hd := bv_lt (adderBits true false false (padPairs a b))
  rw [hlen] at hd
  have hv := adderBits_sub_value a b
  apply bv_inj
  · rw [hlen, natBits_length]
  · rw [bv_natBits _ _ (Nat.mod_lt _ hP)]
    generalize bv (adderBits true false false (padPairs a b)) = d at *
    generalize 2 ^ max a.length b.length = P at *
    generalize bv a = x at *
    generalize bv b = y at *
    cases ho : (ripple true false (padPairs a b)).2
    · rw [ho] at hv
      simp only [b2n, Bool.false_eq_true, ite_false, Nat.mul_zero, Nat.add_zero] at hv
      have : x + P - y = d + P := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hd]
    · rw [ho] at hv
      simp only [b2n, ite_true, Nat.mul_one] at hv
      have : x + P - y = d := by omega
      rw [this, Nat.mod_eq_of_lt hd]

/-- The sum is the arithmetic sum. -/
theorem sem_add_val (v : Wire → Bool) (a b : BvExp) :
    bv ((BvExp.add a b).sem v) = bv (a.sem v) + bv (b.sem v) := by
  simp only [BvExp.sem]
  apply bv_natBits
  have h1 := bv_lt (a.sem v)
  have h2 := bv_lt (b.sem v)
  have e1 : 2 ^ (a.sem v).length ≤ 2 ^ max (a.sem v).length (b.sem v).length := Nat.pow_le_pow_right (by omega) (by omega)
  have e2 : 2 ^ (b.sem v).length ≤ 2 ^ max (a.sem v).length (b.sem v).length := Nat.pow_le_pow_right (by omega) (by omega)
  unfold addWidth
  by_cases hm : max (a.sem v).length (b.sem v).length = 0
  · have : (a.sem v).length = 0 := by omega
    have : (b.sem v).length = 0 := by omega
    have h3 : bv (a.sem v) < 1 := by simpa [*] using h1
    have h4 : bv (b.sem v) < 1 := by simpa [*] using h2
    rw [if_pos hm]; simp; omega
  · rw [if_neg hm, Nat.pow_succ]
    omega

/-- The difference is taken modulo `2^m`. -/
theorem sem_sub_val (v : Wire → Bool) (a b : BvExp) :
    bv ((BvExp.sub a b).sem v) =
      (bv (a.sem v) + 2 ^ max (a.sem v).length (b.sem v).length - bv (b.sem v)) %
        2 ^ max (a.sem v).length (b.sem v).length := by
  simp only [BvExp.sem]
  exact bv_natBits _ _ (Nat.mod_lt _ (Nat.two_pow_pos _))

theorem padB_length (m : Nat) (l : List Bool) (h : l.length ≤ m) : (padB m l).length = m := by
  simp [padB]; omega

theorem bitwiseB_length (f : Bool → Bool → Bool) (a b : List Bool) :
    (bitwiseB f a b).length = max a.length b.length := by
  unfold bitwiseB
  rw [List.length_map, List.length_zip, padB_length _ _ (Nat.le_max_left _ _), padB_length _ _ (Nat.le_max_right _ _)]
  simp

/-- The static width is the length of the meaning. -/
theorem BvExp.sem_length (v : Wire → Bool) : ∀ e : BvExp, (e.sem v).length = e.width := by
  intro e
  induction e with
  | inp ws => simp [BvExp.sem, BvExp.width]
  | lit n => simp [BvExp.sem, BvExp.width, natBits_length]
  | bnot a ih => simp [BvExp.sem, BvExp.width, ih]
  | band a b iha ihb => simp [BvExp.sem, BvExp.width, bitwiseB_length, iha, ihb]
  | bor a b iha ihb => simp [BvExp.sem, BvExp.width, bitwiseB_length, iha, ihb]
  | bxor a b iha ihb => simp [BvExp.sem, BvExp.width, bitwiseB_length, iha, ihb]
  | add a b iha ihb => simp [BvExp.sem, BvExp.width, natBits_length, iha, ihb]
  | sub a b iha ihb => simp [BvExp.sem, BvExp.width, natBits_length, iha, ihb]
  | slice a i n ih => simp [BvExp.sem, BvExp.width, ih]
  | cat a b iha ihb => simp [BvExp.sem, BvExp.width, iha, ihb]
  | ite c a b ihc iha ihb =>
    simp only [BvExp.sem, BvExp.width, iha, ihb]
    split
    · exact padB_length _ _ (by rw [iha]; exact Nat.le_max_left _ _)
    · exact padB_length _ _ (by rw [ihb]; exact Nat.le_max_right _ _)
  | tbl idx tab ih => simp [BvExp.sem, BvExp.width, natBits_length]

/-! ### Congruence of `sem` under extension of the state -/

theorem sem_ext {inp : Nat → Bool} {gb gb' : GB} (h : Ext gb gb') :
    ∀ (e : BvExp), e.ok gb.n → e.sem (wev gb' inp) = e.sem (wev gb inp) := by
  intro e
  induction e with
  | inp ws =>
    intro he
    simp only [BvExp.sem]
    exact List.map_congr_left (fun w hw => wev_ext h ((Wire.inb_iff _ _).1 (he w hw)))
  | lit n => intro _; rfl
  | bnot a ih => intro he; simp only [BvExp.sem, ih he]
  | band a b iha ihb => intro he; simp only [BvExp.sem, iha he.1, ihb he.2]
  | bor a b iha ihb => intro he; simp only [BvExp.sem, iha he.1, ihb he.2]
  | bxor a b iha ihb => intro he; simp only [BvExp.sem, iha he.1, ihb he.2]
  | add a b iha ihb => intro he; simp only [BvExp.sem, iha he.1, ihb he.2]
  | sub a b iha ihb => intro he; simp only [BvExp.sem, iha he.1, ihb he.2]
  | slice a i n ih => intro he; simp only [BvExp.sem, ih he]
  | cat a b iha ihb => intro he; simp only [BvExp.sem, iha he.1, ihb he.2]
  | ite c a b ihc iha ihb => intro he; simp only [BvExp.sem, ihc he.1, iha he.2.1, ihb he.2.2]
  | tbl idx tab ih => intro he; simp only [BvExp.sem, ih he.1]

theorem BvExp.ok_mono {n n' : Nat} (h : n ≤ n') : ∀ (e : BvExp), e.ok n → e.ok n' := by
  intro e
  induction e with
  | inp ws => intro he w hw; exact (Wire.inb_iff _ _).2 (SmcIrred.ok_mono ((Wire.inb_iff _ _).1 (he w hw)) h)
  | lit n => intro _; trivial
  | bnot a ih => exact ih
  | band a b iha ihb => intro he; exact ⟨iha he.1, ihb he.2⟩
  | bor a b iha ihb => intro he; exact ⟨iha he.1, ihb he.2⟩
  | bxor a b iha ihb => intro he; exact ⟨iha he.1, ihb he.2⟩
  | add a b iha ihb => intro he; exact ⟨iha he.1, ihb he.2⟩
  | sub a b iha ihb => intro he; exact ⟨iha he.1, ihb he.2⟩
  | slice a i n ih => exact ih
  | cat a b iha ihb => intro he; exact ⟨iha he.1, ihb he.2⟩
  | ite c a b ihc iha ihb => intro he; exact ⟨ihc he.1, iha he.2.1, ihb he.2.2⟩
  | tbl idx tab ih => intro he; exact ⟨ih he.1, he.2⟩

/-! ### Bitwise gadgets over two vectors -/

section Gadgets

variable {inp : Nat → Bool} {k : Nat}

theorem map_zip_two {α : Type} (f : α → Bool) (g : Bool → Bool → Bool) : ∀ (l1 l2 : List α),
    (l1.zip l2).map (fun p => g (f p.1) (f p.2)) = ((l1.map f).zip (l2.map f)).map (fun q => g q.1 q.2) := by
  intro l1
  induction l1 with
  | nil => intro l2; simp
  | cons a t ih => intro l2; cases l2 <;> simp [ih]

theorem multiV_post (hinp : ∀ i, k ≤ i → inp i = false) (f : GB → List Wire → Wire × GB) (g : Bool → Bool → Bool)
    (hf : ∀ (gb : GB) (a b : Wire), k ≤ gb.n → Reach gb → a.ok gb.n → b.ok gb.n →
      Post gb (f gb [a, b]).2 inp (f gb [a, b]).1 (g (wev gb inp a) (wev gb inp b)))
    {gb : GB} (hk : k ≤ gb.n) (hr : Reach gb) {a b : List Wire} (ha : ∀ w ∈ a, w.ok gb.n) (hb : ∀ w ∈ b, w.ok gb.n) :
    Ext gb (multiV f gb a b).2 ∧ Reach (multiV f gb a b).2 ∧ (∀ w ∈ (multiV f gb a b).1, w.ok (multiV f gb a b).2.n) ∧
      (multiV f gb a b).1.map (wev (multiV f gb a b).2 inp) = bitwiseB g (a.map (wev gb inp)) (b.map (wev gb inp)) := by
  unfold multiV
  have hza := zeroExt_ok (max a.length b.length) ha
  have hzb := zeroExt_ok (max a.length b.length) hb
  have := mapG_wire (fun gb p => f gb [p.1, p.2]) (fun p => [p.1, p.2]) (fun _ vs => g (vs.getD 0 false) (vs.getD 1 false))
    (fun _ => True) (inp := inp) (k := k)
    (fun gb p _ hk hr hok => by
      have := hf gb p.1 p.2 hk hr (hok p.1 (by simp)) (hok p.2 (by simp))
      simpa [wev] using this)
    ((zeroExt (max a.length b.length) a).zip (zeroExt (max a.length b.length) b)) gb (fun _ _ => trivial) hk hr
    (fun p hp w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact hza _ (List.of_mem_zip hp).1
      · exact hzb _ (List.of_mem_zip hp).2)
  obtain ⟨e1, r1, o1, v1⟩ := this
  refine ⟨e1, r1, o1, ?_⟩
  rw [v1]
  have hmap : ∀ p : Wire × Wire,
      (fun _ (vs : List Bool) => g (vs.getD 0 false) (vs.getD 1 false)) p ([p.1, p.2].map (wev gb inp)) =
        g (wev gb inp p.1) (wev gb inp p.2) := fun p => rfl
  simp only [hmap]
  rw [map_zip_two (wev gb inp) g, zeroExt_vals, zeroExt_vals]
  unfold bitwiseB padB
  simp only [List.length_map]

theorem notMap_post (hinp : ∀ i, k ≤ i → inp i = false) {gb : GB} (hk : k ≤ gb.n) (hr : Reach gb) {a : List Wire}
    (ha : ∀ w ∈ a, w.ok gb.n) :
    Ext gb (mapG (fun g w => notV g w) gb a).2 ∧ Reach (mapG (fun g w => notV g w) gb a).2 ∧
      (∀ w ∈ (mapG (fun g w => notV g w) gb a).1, w.ok (mapG (fun g w => notV g w) gb a).2.n) ∧
      (mapG (fun g w => notV g w) gb a).1.map (wev (mapG (fun g w => notV g w) gb a).2 inp) =
        (a.map (wev gb inp)).map (fun b => !b) := by
  have := mapG_wire (fun g w => notV g w) (fun w => [w]) (fun _ vs => !(vs.getD 0 false)) (fun _ => True)
    (inp := inp) (k := k)
    (fun gb w _ hk hr hok => by
      have := notV_post hinp hk hr (hok w (by simp))
      simpa [wev] using this)
    a gb (fun _ _ => trivial) hk hr (fun w hw x hx => by simp at hx; rw [hx]; exact ha w hw)
  obtain ⟨e1, r1, o1, v1⟩ := this
  refine ⟨e1, r1, o1, ?_⟩
  rw [v1, List.map_map]
  rfl

end Gadgets

/-! ### The compiler theorem -/

variable {inp : Nat → Bool} {k : Nat}

theorem comp_correct (hinp : ∀ i, k ≤ i → inp i = false) :
    ∀ (e : BvExp) (gb : GB), k ≤ gb.n → Reach gb → e.ok gb.n →
      Ext gb (e.comp gb).2 ∧ Reach (e.comp gb).2 ∧ (∀ w ∈ (e.comp gb).1, w.ok (e.comp gb).2.n) ∧
      (e.comp gb).1.map (wev (e.comp gb).2 inp) = e.sem (wev gb inp) := by
  intro e
  induction e with
  | inp ws =>
    intro gb hk hr he
    exact ⟨Ext.refl _, hr, fun w hw => (Wire.inb_iff _ _).1 (he w hw), rfl⟩
  | lit n =>
    intro gb hk hr _
    refine ⟨Ext.refl _, hr, fun w hw => ?_, ?_⟩
    · simp only [BvExp.comp, constBits, List.mem_map] at hw
      obtain ⟨j, _, rfl⟩ := hw; trivial
    · simp only [BvExp.comp, BvExp.sem, constBits, List.map_map]
      rw [natBits_eq_bitsOf, ← bitsOf_range]
      rfl
  | bnot a ih =>
    intro gb hk hr he
    obtain ⟨e1, r1, o1, v1⟩ := ih gb hk hr he
    have hk1 : k ≤ (a.comp gb).2.n := Nat.le_trans hk e1.n_le
    obtain ⟨e2, r2, o2, v2⟩ := notMap_post hinp hk1 r1 o1
    refine ⟨e1.trans e2, r2, o2, ?_⟩
    simp only [BvExp.comp, BvExp.sem]
    rw [v2, v1]
  | band a b iha ihb =>
    intro gb hk hr he
    obtain ⟨e1, r1, o1, v1⟩ := iha gb hk hr he.1
    have hk1 : k ≤ (a.comp gb).2.n := Nat.le_trans hk e1.n_le
    have hb1 : b.ok (a.comp gb).2.n := BvExp.ok_mono e1.n_le b he.2
    obtain ⟨e2, r2, o2, v2⟩ := ihb (a.comp gb).2 hk1 r1 hb1
    have hk2 : k ≤ (b.comp (a.comp gb).2).2.n := Nat.le_trans hk1 e2.n_le
    have oa : ∀ w ∈ (a.comp gb).1, w.ok (b.comp (a.comp gb).2).2.n := fun w hw => ok_mono (o1 w hw) e2.n_le
    obtain ⟨e3, r3, o3, v3⟩ := multiV_post hinp andV (fun x y => x && y)
      (fun gb a b hk hr ha hb => by
        have := andV_post hinp hk hr [a, b] (by intro w hw; simp at hw; rcases hw with rfl | rfl <;> assumption)
        simpa [andL] using this)
      hk2 r2 oa o2
    refine ⟨e1.trans (e2.trans e3), r3, o3, ?_⟩
    simp only [BvExp.comp, BvExp.sem]
    rw [v3, v2, sem_ext e1 b he.2]
    have : (a.comp gb).1.map (wev (b.comp (a.comp gb).2).2 inp) = a.sem (wev gb inp) := by
      rw [← v1]
      exact List.map_congr_left (fun w hw => wev_ext e2 (o1 w hw))
    rw [this]
  | bor a b iha ihb =>
    intro gb hk hr he
    obtain ⟨e1, r1, o1, v1⟩ := iha gb hk hr he.1
    have hk1 : k ≤ (a.comp gb).2.n := Nat.le_trans hk e1.n_le
    have hb1 : b.ok (a.comp gb).2.n := BvExp.ok_mono e1.n_le b he.2
    obtain ⟨e2, r2, o2, v2⟩ := ihb (a.comp gb).2 hk1 r1 hb1
    have hk2 : k ≤ (b.comp (a.comp gb).2).2.n := Nat.le_trans hk1 e2.n_le
    have oa : ∀ w ∈ (a.comp gb).1, w.ok (b.comp (a.comp gb).2).2.n := fun w hw => ok_mono (o1 w hw) e2.n_le
    obtain ⟨e3, r3, o3, v3⟩ := multiV_post hinp orV (fun x y => x || y)
      (fun gb a b hk hr ha hb => by
        have := orV_post hinp hk hr [a, b] (by intro w hw; simp at hw; rcases hw with rfl | rfl <;> assumption)
        simpa [orL] using this)
      hk2 r2 oa o2
    refine ⟨e1.trans (e2.trans e3), r3, o3, ?_⟩
    simp only [BvExp.comp, BvExp.sem]
    rw [v3, v2, sem_ext e1 b he.2]
    have : (a.comp gb).1.map (wev (b.comp (a.comp gb).2).2 inp) = a.sem (wev gb inp) := by
      rw [← v1]
      exact List.map_congr_left (fun w hw => wev_ext e2 (o1 w hw))
    rw [this]
  | bxor a b iha ihb =>
    intro gb hk hr he
    obtain ⟨e1, r1, o1, v1⟩ := iha gb hk hr he.1
    have hk1 : k ≤ (a.comp gb).2.n := Nat.le_trans hk e1.n_le
    have hb1 : b.ok (a.comp gb).2.n := BvExp.ok_mono e1.n_le b he.2
    obtain ⟨e2, r2, o2, v2⟩ := ihb (a.comp gb).2 hk1 r1 hb1
    have hk2 : k ≤ (b.comp (a.comp gb).2).2.n := Nat.le_trans hk1 e2.n_le
    have oa : ∀ w ∈ (a.comp gb).1, w.ok (b.comp (a.comp gb).2).2.n := fun w hw => ok_mono (o1 w hw) e2.n_le
    obtain ⟨e3, r3, o3, v3⟩ := multiV_post hinp xorV (fun x y => x != y)
      (fun gb a b hk hr ha hb => by
        have := xorV_post hinp hk hr [a, b] (by intro w hw; simp at hw; rcases hw with rfl | rfl <;> assumption)
        simpa [xorL_cons, xorL_nil] using this)
      hk2 r2 oa o2
    refine ⟨e1.trans (e2.trans e3), r3, o3, ?_⟩
    simp only [BvExp.comp, BvExp.sem]
    rw [v3, v2, sem_ext e1 b he.2]
    have : (a.comp gb).1.map (wev (b.comp (a.comp gb).2).2 inp) = a.sem (wev gb inp) := by
      rw [← v1]
      exact List.map_congr_left (fun w hw => wev_ext e2 (o1 w hw))
    rw [this]
  | add a b iha ihb =>
    intro gb hk hr he
    obtain ⟨e1, r1, o1, v1⟩ := iha gb hk hr he.1
    have hk1 : k ≤ (a.comp gb).2.n := Nat.le_trans hk e1.n_le
    have hb1 : b.ok (a.comp gb).2.n := BvExp.ok_mono e1.n_le b he.2
    obtain ⟨e2, r2, o2, v2⟩ := ihb (a.comp gb).2 hk1 r1 hb1
    have hk2 : k ≤ (b.comp (a.comp gb).2).2.n := Nat.le_trans hk1 e2.n_le
    have oa : ∀ w ∈ (a.comp gb).1, w.ok (b.comp (a.comp gb).2).2.n := fun w hw => ok_mono (o1 w hw) e2.n_le
    have hp := addition_post hinp hk2 r2 (issub := .cst false) true oa o2 trivial
    refine ⟨e1.trans (e2.trans hp.1), hp.2.1, hp.2.2.1, ?_⟩
    simp only [BvExp.comp, BvExp.sem]
    rw [hp.2.2.2]
    have hmapa : (a.comp gb).1.map (wev (b.comp (a.comp gb).2).2 inp) = a.sem (wev gb inp) := by
      rw [← v1]
      exact List.map_congr_left (fun w hw => wev_ext e2 (o1 w hw))
    have hmapb : (b.comp (a.comp gb).2).1.map (wev (b.comp (a.comp gb).2).2 inp) = b.sem (wev gb inp) := by
      rw [v2, sem_ext e1 b he.2]
    have hla : (a.comp gb).1.length = (a.sem (wev gb inp)).length := by rw [← hmapa, List.length_map]
    have hlb : (b.comp (a.comp gb).2).1.length = (b.sem (wev gb inp)).length := by rw [← hmapb, List.length_map]
    rw [hmapa, hmapb, hla, hlb]
    exact adderBits_add_eq (a.sem (wev gb inp)) (b.sem (wev gb inp))
  | sub a b iha ihb =>
    intro gb hk hr he
    obtain ⟨e1, r1, o1, v1⟩ := iha gb hk hr he.1
    have hk1 : k ≤ (a.comp gb).2.n := Nat.le_trans hk e1.n_le
    have hb1 : b.ok (a.comp gb).2.n := BvExp.ok_mono e1.n_le b he.2
    obtain ⟨e2, r2, o2, v2⟩ := ihb (a.comp gb).2 hk1 r1 hb1
    have hk2 : k ≤ (b.comp (a.comp gb).2).2.n := Nat.le_trans hk1 e2.n_le
    have oa : ∀ w ∈ (a.comp gb).1, w.ok (b.comp (a.comp gb).2).2.n := fun w hw => ok_mono (o1 w hw) e2.n_le
    have hp := addition_post hinp hk2 r2 (issub := .cst true) false oa o2 trivial
    refine ⟨e1.trans (e2.trans hp.1), hp.2.1, hp.2.2.1, ?_⟩
    simp only [BvExp.comp, BvExp.sem]
    rw [hp.2.2.2]
    have hmapa : (a.comp gb).1.map (wev (b.comp (a.comp gb).2).2 inp) = a.sem (wev gb inp) := by
      rw [← v1]
      exact List.map_congr_left (fun w hw => wev_ext e2 (o1 w hw))
    have hmapb : (b.comp (a.comp gb).2).1.map (wev (b.comp (a.comp gb).2).2 inp) = b.sem (wev gb inp) := by
      rw [v2, sem_ext e1 b he.2]
    have hf : wev (b.comp (a.comp gb).2).2 inp (.cst true) = true := rfl
    have hla : (a.comp gb).1.length = (a.sem (wev gb inp)).length := by rw [← hmapa, List.length_map]
    have hlb : (b.comp (a.comp gb).2).1.length = (b.sem (wev gb inp)).length := by rw [← hmapb, List.length_map]
    rw [hf, hmapa, hmapb, hla, hlb]
    exact adderBits_sub_eq (a.sem (wev gb inp)) (b.sem (wev gb inp))

  | slice a i n ih =>
    intro gb hk hr he
    obtain ⟨e1, r1, o1, v1⟩ := ih gb hk hr he
    refine ⟨e1, r1, ?_, ?_⟩
    · intro w hw
      exact o1 w (List.mem_of_mem_drop (List.mem_of_mem_take hw))
    · simp only [BvExp.comp, BvExp.sem, List.map_take, List.map_drop, v1]
  | cat a b iha ihb =>
    intro gb hk hr he
    obtain ⟨e1, r1, o1, v1⟩ := iha gb hk hr he.1
    have hk1 : k ≤ (a.comp gb).2.n := Nat.le_trans hk e1.n_le
    have hb1 : b.ok (a.comp gb).2.n := BvExp.ok_mono e1.n_le b he.2
    obtain ⟨e2, r2, o2, v2⟩ := ihb (a.comp gb).2 hk1 r1 hb1
    refine ⟨e1.trans e2, r2, ?_, ?_⟩
    · intro w hw
      rcases List.mem_append.1 hw with h | h
      · exact ok_mono (o1 w h) e2.n_le
      · exact o2 w h
    · simp only [BvExp.comp, BvExp.sem, List.map_append]
      rw [v2, sem_ext e1 b he.2]
      have : (a.comp gb).1.map (wev (b.comp (a.comp gb).2).2 inp) = a.sem (wev gb inp) := by
        rw [← v1]
        exact List.map_congr_left (fun w hw => wev_ext e2 (o1 w hw))
      rw [this]
  | ite c a b ihc iha ihb =>
    intro gb hk hr he
    obtain ⟨e1, r1, o1, v1⟩ := ihc gb hk hr he.1
    have hk1 : k ≤ (c.comp gb).2.n := Nat.le_trans hk e1.n_le
    have ha1 : a.ok (c.comp gb).2.n := BvExp.ok_mono e1.n_le a he.2.1
    have hb1 : b.ok (c.comp gb).2.n := BvExp.ok_mono e1.n_le b he.2.2
    obtain ⟨e2, r2, o2, v2⟩ := iha (c.comp gb).2 hk1 r1 ha1
    have hk2 : k ≤ (a.comp (c.comp gb).2).2.n := Nat.le_trans hk1 e2.n_le
    have hb2 : b.ok (a.comp (c.comp gb).2).2.n := BvExp.ok_mono e2.n_le b hb1
    obtain ⟨e3, r3, o3, v3⟩ := ihb (a.comp (c.comp gb).2).2 hk2 r2 hb2
    have hk3 : k ≤ (b.comp (a.comp (c.comp gb).2).2).2.n := Nat.le_trans hk2 e3.n_le
    have hs : ((c.comp gb).1.getD 0 (.cst false)).ok (b.comp (a.comp (c.comp gb).2).2).2.n :=
      ok_mono (getD_ok o1) (Nat.le_trans e2.n_le e3.n_le)
    have ha3 : ∀ w ∈ (a.comp (c.comp gb).2).1, w.ok (b.comp (a.comp (c.comp gb).2).2).2.n :=
      fun w hw => ok_mono (o2 w hw) e3.n_le
    obtain ⟨e4, r4, o4, v4⟩ := iteV_post hinp hk3 r3 hs _ _ ha3 o3
    refine ⟨e1.trans (e2.trans (e3.trans e4)), r4, o4, ?_⟩
    have hca : (c.comp gb).1.map (wev (b.comp (a.comp (c.comp gb).2).2).2 inp) = c.sem (wev gb inp) := by
      rw [← v1]
      exact List.map_congr_left (fun w hw => wev_ext (e2.trans e3) (o1 w hw))
    have hma : (a.comp (c.comp gb).2).1.map (wev (b.comp (a.comp (c.comp gb).2).2).2 inp) = a.sem (wev gb inp) := by
      have : (a.comp (c.comp gb).2).1.map (wev (b.comp (a.comp (c.comp gb).2).2).2 inp) =
          (a.comp (c.comp gb).2).1.map (wev (a.comp (c.comp gb).2).2 inp) :=
        List.map_congr_left (fun w hw => wev_ext e3 (o2 w hw))
      rw [this, v2, sem_ext e1 a he.2.1]
    have hmb : (b.comp (a.comp (c.comp gb).2).2).1.map (wev (b.comp (a.comp (c.comp gb).2).2).2 inp) =
        b.sem (wev gb inp) := by
      rw [v3, sem_ext e2 b hb1, sem_ext e1 b he.2.2]
    have hla : (a.comp (c.comp gb).2).1.length = (a.sem (wev gb inp)).length := by rw [← hma, List.length_map]
    have hlb : (b.comp (a.comp (c.comp gb).2).2).1.length = (b.sem (wev gb inp)).length := by
      rw [← hmb, List.length_map]
    simp only [BvExp.comp, BvExp.sem]
    rw [v4]
    rw [getD_wev, hca, hla, hlb, hma, hmb]
  | tbl idx tab ih =>
    intro gb hk hr he
    obtain ⟨e1, r1, o1, v1⟩ := ih gb hk hr he.1
    have hk1 : k ≤ (idx.comp gb).2.n := Nat.le_trans hk e1.n_le
    have hlen : (idx.comp gb).1.length = idx.width := by
      rw [← BvExp.sem_length (wev gb inp) idx, ← v1, List.length_map]
    obtain ⟨e2, r2, o2, v2⟩ := tableLookupV_post hinp hk1 r1 (idx.comp gb).1 o1 tab (by rw [hlen]; exact he.2)
    refine ⟨e1.trans e2, r2, o2, ?_⟩
    simp only [BvExp.comp, BvExp.sem]
    rw [v2, v1]

/-- The same in the circuit of the extended state under the Boolean-CFG evaluator (any depth and library). -/
theorem comp_circuit_correct (hinp : ∀ i, k ≤ i → inp i = false) (e : BvExp) {gb : GB} (hk : k ≤ gb.n) (hr : Reach gb)
    (he : e.ok gb.n) (lib : Lib) (d : Nat) :
    (e.comp gb).1.map (Wire.cval (e.comp gb).2 lib d inp) = e.sem (wev gb inp) := by
  obtain ⟨_, r, o, v⟩ := comp_correct hinp e gb hk hr he
  rw [← v]
  exact List.map_congr_left (fun w hw => cval_eq_wev r lib d inp (o w hw))

end SmcIrred
