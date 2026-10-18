module

public import SmcIrred.Prims.MapG
public import SmcIrred.Prims.Nat

public section

namespace SmcIrred

theorem andL_two (a b : Bool) : andL [a, b] = (a && b) := by cases a <;> cases b <;> rfl
theorem orL_two (a b : Bool) : orL [a, b] = (a || b) := by cases a <;> cases b <;> rfl
theorem xorL_two (a b : Bool) : xorL [a, b] = (a != b) := by cases a <;> cases b <;> rfl

section Dec

variable {inp : Nat → Bool} {k : Nat}

/-- One step of `decoder_shift_to_virtual`: doubling the one-hot list by the next bit. -/
theorem decStep_post {gb : GB} (hinp : ∀ i, k ≤ i → inp i = false) (hk : k ≤ gb.n) (hr : Reach gb) (num : List Wire)
    (s : Wire) (hnum : ∀ w ∈ num, w.ok gb.n) (hs : s.ok gb.n) :
    Ext gb (decStep gb num s).2 ∧ Reach (decStep gb num s).2 ∧ (∀ w ∈ (decStep gb num s).1, w.ok (decStep gb num s).2.n) ∧
    (decStep gb num s).1.map (wev (decStep gb num s).2 inp) =
      (num.map (wev gb inp)).map (fun v => v && !wev gb inp s) ++ (num.map (wev gb inp)).map (fun v => v && wev gb inp s) := by
  unfold decStep
  dsimp only
  have p0 := notV_post hinp hk hr hs
  generalize notV gb s = r0 at p0 ⊢
  have hk0 : k ≤ r0.2.n := Nat.le_trans hk p0.ext.n_le
  have hnum0 : ∀ w ∈ num, w.ok r0.2.n := fun w hw => ok_mono (hnum w hw) p0.ext.n_le
  have hs0 : s.ok r0.2.n := ok_mono hs p0.ext.n_le
  obtain ⟨e1, rc1, o1, v1⟩ := mapG_wire (fun g w => andV g [w, r0.1]) (fun w => [w, r0.1])
    (fun _ vs => andL vs) (fun _ => True) (inp := inp) (k := k)
    (fun g a _ hk' hr' hok => andV_post hinp hk' hr' [a, r0.1] hok) num r0.2 (fun _ _ => trivial) hk0 p0.reach
    (fun a ha w hw => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
      rcases hw with h | h
      · rw [h]; exact hnum0 a ha
      · rw [h]; exact p0.ok)
  generalize hm1 : mapG (fun g w => andV g [w, r0.1]) r0.2 num = r1 at e1 rc1 o1 v1 ⊢
  have hk1 : k ≤ r1.2.n := Nat.le_trans hk0 e1.n_le
  have hnum1 : ∀ w ∈ num, w.ok r1.2.n := fun w hw => ok_mono (hnum0 w hw) e1.n_le
  have hs1 : s.ok r1.2.n := ok_mono hs0 e1.n_le
  obtain ⟨e2, rc2, o2, v2⟩ := mapG_wire (fun g w => andV g [w, s]) (fun w => [w, s])
    (fun _ vs => andL vs) (fun _ => True) (inp := inp) (k := k)
    (fun g a _ hk' hr' hok => andV_post hinp hk' hr' [a, s] hok) num r1.2 (fun _ _ => trivial) hk1 rc1
    (fun a ha w hw => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
      rcases hw with h | h
      · rw [h]; exact hnum1 a ha
      · rw [h]; exact hs1)
  generalize hm2 : mapG (fun g w => andV g [w, s]) r1.2 num = r2 at e2 rc2 o2 v2 ⊢
  refine ⟨(p0.ext.trans e1).trans e2, rc2, ?_, ?_⟩
  · intro w hw
    rcases List.mem_append.1 hw with hw | hw
    · exact ok_mono (o1 w hw) e2.n_le
    · exact o2 w hw
  · rw [List.map_append]
    have hh : r1.1.map (wev r2.2 inp) = r1.1.map (wev r1.2 inp) :=
      List.map_congr_left (fun w hw => wev_ext e2 (o1 w hw))
    rw [hh, v1, v2, List.map_map, List.map_map]
    congr 1
    · apply List.map_congr_left
      intro a ha
      simp only [Function.comp, List.map_cons, List.map_nil, andL_two]
      rw [wev_ext p0.ext (hnum a ha), p0.val]
    · apply List.map_congr_left
      intro a ha
      simp only [Function.comp, List.map_cons, List.map_nil, andL_two]
      rw [wev_ext e1 (hnum0 a ha), wev_ext p0.ext (hnum a ha), wev_ext e1 hs0, wev_ext p0.ext hs]

theorem oneHot_length (n x : Nat) : (oneHot n x).length = n := by simp [oneHot]

theorem decLoop_post (hinp : ∀ i, k ≤ i → inp i = false) : ∀ (shift : List Wire) (gb : GB) (num : List Wire),
    k ≤ gb.n → Reach gb → (∀ w ∈ num, w.ok gb.n) → (∀ s ∈ shift, s.ok gb.n) → ∀ x, x < num.length →
    num.map (wev gb inp) = oneHot num.length x →
    Ext gb (decLoop gb num shift).2 ∧ Reach (decLoop gb num shift).2 ∧
    (∀ w ∈ (decLoop gb num shift).1, w.ok (decLoop gb num shift).2.n) ∧
    (decLoop gb num shift).1.map (wev (decLoop gb num shift).2 inp) =
      oneHot (num.length * 2 ^ shift.length) (x + num.length * bv (shift.map (wev gb inp))) := by
  intro shift
  induction shift with
  | nil =>
    intro gb num hk hr hok hs x hx hv
    refine ⟨Ext.refl _, hr, hok, ?_⟩
    simp only [decLoop, List.length_nil, Nat.pow_zero, Nat.mul_one, List.map_nil, bv, Nat.mul_zero, Nat.add_zero]
    exact hv
  | cons s rest ih =>
    intro gb num hk hr hok hs x hx hv
    have hd := decStep_post hinp hk hr num s hok (hs s List.mem_cons_self)
    obtain ⟨e1, r1, o1, v1⟩ := hd
    generalize hrr : decStep gb num s = r at e1 r1 o1 v1
    have hsplit := oneHot_split num.length x hx (wev gb inp s)
    rw [← hv] at hsplit
    have hv' : r.1.map (wev r.2 inp) = oneHot (2 * num.length) (x + num.length * (if wev gb inp s then 1 else 0)) := by
      rw [v1]; exact hsplit
    have hlen : r.1.length = 2 * num.length := by
      have := congrArg List.length hv'
      rw [List.length_map, oneHot_length] at this
      exact this
    have hx' : x + num.length * (if wev gb inp s then 1 else 0) < r.1.length := by
      rw [hlen]; cases wev gb inp s <;> simp <;> omega
    have hv2 : r.1.map (wev r.2 inp) = oneHot r.1.length (x + num.length * (if wev gb inp s then 1 else 0)) := by
      rw [hlen]; exact hv'
    have hk' : k ≤ r.2.n := Nat.le_trans hk e1.n_le
    obtain ⟨f1, fr, fo, fv⟩ := ih r.2 r.1 hk' r1 o1
      (fun s' hs' => ok_mono (hs s' (List.mem_cons_of_mem _ hs')) e1.n_le) _ hx' hv2
    have hdl : decLoop gb num (s :: rest) = decLoop r.2 r.1 rest := by
      show decLoop (decStep gb num s).2 (decStep gb num s).1 rest = _
      rw [hrr]
    rw [hdl]
    refine ⟨e1.trans f1, fr, fo, ?_⟩
    rw [fv]
    have hrest : rest.map (wev r.2 inp) = rest.map (wev gb inp) :=
      List.map_congr_left (fun s' hs' => wev_ext e1 (hs s' (List.mem_cons_of_mem _ hs')))
    rw [hrest, hlen]
    simp only [List.map_cons, bv, List.length_cons, Nat.pow_succ]
    have e : 2 * num.length * bv (rest.map (wev gb inp)) = num.length * (2 * bv (rest.map (wev gb inp))) := by
      rw [Nat.mul_comm 2 num.length, Nat.mul_assoc]
    have e2 : 2 * num.length * 2 ^ rest.length = num.length * (2 ^ rest.length * 2) := by
      rw [Nat.mul_comm 2 num.length, Nat.mul_assoc, Nat.mul_comm 2 (2 ^ rest.length)]
    rw [e2, Nat.mul_add (num.length), ← Nat.add_assoc, e]

theorem decoderShift_post (hinp : ∀ i, k ≤ i → inp i = false) {gb : GB} (hk : k ≤ gb.n) (hr : Reach gb) (shift : List Wire)
    (hs : ∀ s ∈ shift, s.ok gb.n) :
    Ext gb (decoderShift gb shift).2 ∧ Reach (decoderShift gb shift).2 ∧
    (∀ w ∈ (decoderShift gb shift).1, w.ok (decoderShift gb shift).2.n) ∧
    (decoderShift gb shift).1.map (wev (decoderShift gb shift).2 inp) =
      oneHot (2 ^ shift.length) (bv (shift.map (wev gb inp))) := by
  have := decLoop_post (inp := inp) (k := k) hinp shift gb [.cst true] hk hr (by simp [Wire.ok]) hs 0 (by simp)
    (by simp [oneHot, wev, Wire.ev])
  simpa [decoderShift] using this

theorem Post.lift {gb gb1 gb2 : GB} {w : Wire} {v : Bool} (e : Ext gb gb1) (p : Post gb1 gb2 inp w v) :
    Post gb gb2 inp w v := ⟨e.trans p.ext, p.reach, p.ok, p.val⟩

theorem zip_map_ev (gb : GB) (F : Bool → Bool → Bool) : ∀ (cs ss : List Wire), cs.length = ss.length →
    (cs.zip ss).map (fun p => F (wev gb inp p.1) (wev gb inp p.2)) =
      List.zipWith F (cs.map (wev gb inp)) (ss.map (wev gb inp)) := by
  intro cs
  induction cs with
  | nil => intro ss h; cases ss with | nil => rfl | cons _ _ => simp at h
  | cons c t ih =>
    intro ss h
    cases ss with
    | nil => simp at h
    | cons s u =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      simp only [List.zip_cons_cons, List.map_cons, List.zipWith_cons_cons]
      rw [ih u h]

theorem orL_zipWith_ne : ∀ (a b : List Bool), a.length = b.length → (orL (List.zipWith (fun x y => x != y) a b) = false ↔ a = b) := by
  intro a
  induction a with
  | nil => intro b h; cases b with | nil => simp [orL] | cons _ _ => simp at h
  | cons x t ih =>
    intro b h
    cases b with
    | nil => simp at h
    | cons y u =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      simp only [List.zipWith_cons_cons, orL_cons, Bool.or_eq_false_iff, List.cons.injEq]
      rw [ih u h]
      cases x <;> cases y <;> simp

theorem decoderOne_post (hinp : ∀ i, k ≤ i → inp i = false) {gb : GB} (hk : k ≤ gb.n) (hr : Reach gb) (shift : List Wire)
    (hs : ∀ s ∈ shift, s.ok gb.n) (i : Nat) (hi : i < 2 ^ shift.length) :
    Post gb (decoderOne gb shift i).2 inp (decoderOne gb shift i).1 (decide (bv (shift.map (wev gb inp)) = i)) := by
  have hbl : bitLen i ≤ shift.length := bitLen_le i _ hi
  have hmulti : multiV xorV gb (constBits i) shift =
      mapG (fun g p => xorV g [p.1, p.2]) gb (((bitsOf i shift.length).map Wire.cst).zip shift) := by
    unfold multiV
    dsimp only
    have hmax : max (constBits i).length shift.length = shift.length := by
      simp only [constBits, List.length_map, List.length_range]; omega
    have hz : zeroExt shift.length shift = shift := by unfold zeroExt; simp
    rw [hmax, zeroExt_constBits i _ hbl, hz]
  unfold decoderOne
  dsimp only
  rw [hmulti]
  have hlen : ((bitsOf i shift.length).map Wire.cst).length = shift.length := by simp [bitsOf_length]
  obtain ⟨e1, r1, o1, v1⟩ := mapG_wire (fun g p => xorV g [p.1, p.2]) (fun p => [p.1, p.2]) (fun _ vs => xorL vs)
    (fun _ => True) (inp := inp) (k := k)
    (fun g a _ hk' hr' hok => xorV_post hinp hk' hr' [a.1, a.2] hok)
    (((bitsOf i shift.length).map Wire.cst).zip shift) gb (fun _ _ => trivial) hk hr
    (fun a ha w hw => by
      have hz := List.of_mem_zip ha
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
      rcases hw with h | h
      · rw [h]
        obtain ⟨b, _, hb⟩ := List.mem_map.1 hz.1
        rw [← hb]; trivial
      · rw [h]; exact hs _ hz.2)
  generalize hM : mapG (fun g p => xorV g [p.1, p.2]) gb (((bitsOf i shift.length).map Wire.cst).zip shift) = M at e1 r1 o1 v1 ⊢
  have hMlen : M.1.length = shift.length := by
    have := congrArg List.length v1
    simp only [List.length_map, List.length_zip, hlen, Nat.min_self] at this
    exact this
  have hc : ((bitsOf i shift.length).map Wire.cst).map (wev gb inp) = bitsOf i shift.length := by
    rw [List.map_map]
    simp [Function.comp_def, wev, Wire.ev]
  have hvals : M.1.map (wev M.2 inp) = List.zipWith (fun x y => x != y) (bitsOf i shift.length) (shift.map (wev gb inp)) := by
    rw [v1]
    have hz := zip_map_ev (inp := inp) gb (fun a b => a != b) ((bitsOf i shift.length).map Wire.cst) shift hlen
    rw [hc] at hz
    rw [← hz]
    apply List.map_congr_left
    intro p _
    simp [xorL_two]
  have hbits : (bitsOf i shift.length).length = (shift.map (wev gb inp)).length := by
    simp [bitsOf_length]
  have heq : (shift.map (wev gb inp) = bitsOf i shift.length) ↔ bv (shift.map (wev gb inp)) = i := by
    constructor
    · intro h; rw [h]; exact bv_bitsOf _ _ hi
    · intro h
      apply bv_inj _ _ (by simp [bitsOf_length])
      rw [h, bv_bitsOf _ _ hi]
  unfold cmpZeroV
  by_cases hm0 : shift.length = 0
  · have hl0 : (M.1.length == 0) = true := by simp [hMlen, hm0]
    rw [if_pos hl0]
    refine ⟨e1, r1, trivial, ?_⟩
    have hsn : shift = [] := List.length_eq_zero_iff.1 hm0
    subst hsn
    simp only [List.length_nil, Nat.pow_zero] at hi
    have : i = 0 := by omega
    subst this
    simp [wev, Wire.ev, bv]
  · have hl0 : ¬ (M.1.length == 0) = true := by simp [hMlen, hm0]
    rw [if_neg hl0]
    have hk1 : k ≤ M.2.n := Nat.le_trans hk e1.n_le
    have po := orV_post hinp hk1 r1 M.1 o1
    have pn := notV_post hinp (Nat.le_trans hk1 po.ext.n_le) po.reach po.ok
    refine ⟨(e1.trans po.ext).trans pn.ext, pn.reach, pn.ok, ?_⟩
    rw [pn.val, po.val, hvals]
    apply Bool.eq_iff_iff.2
    simp only [Bool.not_eq_true', decide_eq_true_eq]
    rw [orL_zipWith_ne _ _ hbits, ← heq]
    exact ⟨fun h => h.symm, fun h => h.symm⟩

theorem decoder_post (hinp : ∀ i, k ≤ i → inp i = false) {gb : GB} (hk : k ≤ gb.n) (hr : Reach gb) (shift : List Wire)
    (hs : ∀ s ∈ shift, s.ok gb.n) :
    Ext gb (decoder gb shift).2 ∧ Reach (decoder gb shift).2 ∧
    (∀ w ∈ (decoder gb shift).1, w.ok (decoder gb shift).2.n) ∧
    (decoder gb shift).1.map (wev (decoder gb shift).2 inp) = oneHot (2 ^ shift.length) (bv (shift.map (wev gb inp))) := by
  have := mapG_wire (fun g i => decoderOne g shift i) (fun _ => shift) (fun i vs => decide (bv vs = i))
    (fun i => i < 2 ^ shift.length) (inp := inp) (k := k)
    (fun g a ha hk' hr' hok => decoderOne_post hinp hk' hr' shift hok a ha)
    (List.range (2 ^ shift.length)) gb (fun a ha => List.mem_range.1 ha) hk hr (fun _ _ => hs)
  obtain ⟨e, r, o, v⟩ := this
  refine ⟨e, r, o, ?_⟩
  unfold decoder
  rw [v]
  unfold oneHot
  apply List.map_congr_left
  intro i _
  apply Bool.eq_iff_iff.2
  simp only [decide_eq_true_eq, beq_iff_eq]
  omega

end Dec

end SmcIrred
