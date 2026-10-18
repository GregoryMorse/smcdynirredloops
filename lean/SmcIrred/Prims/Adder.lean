module

public import SmcIrred.Prims.Decoder

public section

namespace SmcIrred

/-- The carry (borrow) out of one bit: `(a ⊕ s) ∧ b ⊕ c ∧ (a ⊕ b ⊕ s)` where `s` selects subtraction. -/
@[expose] def cout (a b c f : Bool) : Bool := ((f != a) && b) != (c && (f != (a != b)))

theorem cout_case1 : ∀ a b c f : Bool, (f != a) = true → (((f != a) && b) || c) = cout a b c f := by decide
theorem cout_case2 : ∀ a b c f : Bool, b = true → (((f != a) && b) || c) = cout a b c f := by decide
theorem cout_case3 : ∀ a b f : Bool, ((f != a) || b) = cout a b true f := by decide
theorem xorL_three : ∀ a b c : Bool, xorL [a, b, c] = ((a != b) != c) := by decide

theorem ok2 {n : Nat} {a b : Wire} (ha : a.ok n) (hb : b.ok n) : ∀ w ∈ [a, b], w.ok n := by
  intro w hw
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
  rcases hw with h | h <;> rw [h] <;> assumption

theorem ok3 {n : Nat} {a b c : Wire} (ha : a.ok n) (hb : b.ok n) (hc : c.ok n) : ∀ w ∈ [a, b, c], w.ok n := by
  intro w hw
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
  rcases hw with h | h | h <;> rw [h] <;> assumption

section Add

variable {inp : Nat → Bool} {k : Nat}

theorem addBit_post (hinp : ∀ i, k ≤ i → inp i = false) {gb : GB} (hk : k ≤ gb.n) (hr : Reach gb)
    {n1 n2 carry issub : Wire} (h1 : n1.ok gb.n) (h2 : n2.ok gb.n) (h3 : carry.ok gb.n) (h4 : issub.ok gb.n) :
    Ext gb (addBit gb n1 n2 carry issub).2 ∧ Reach (addBit gb n1 n2 carry issub).2 ∧
    (addBit gb n1 n2 carry issub).1.1.ok (addBit gb n1 n2 carry issub).2.n ∧
    (addBit gb n1 n2 carry issub).1.2.ok (addBit gb n1 n2 carry issub).2.n ∧
    wev (addBit gb n1 n2 carry issub).2 inp (addBit gb n1 n2 carry issub).1.1 =
      ((wev gb inp n1 != wev gb inp n2) != wev gb inp carry) ∧
    wev (addBit gb n1 n2 carry issub).2 inp (addBit gb n1 n2 carry issub).1.2 =
      cout (wev gb inp n1) (wev gb inp n2) (wev gb inp carry) (wev gb inp issub) := by
  unfold addBit
  dsimp only
  have pa := xorV_post hinp hk hr [issub, n1] (ok2 h4 h1)
  generalize xorV gb [issub, n1] = A at pa ⊢
  simp only [List.map_cons, List.map_nil, xorL_two] at pa
  have hkA : k ≤ A.2.n := Nat.le_trans hk pa.ext.n_le
  have o1 : n1.ok A.2.n := ok_mono h1 pa.ext.n_le
  have o2 : n2.ok A.2.n := ok_mono h2 pa.ext.n_le
  have o3 : carry.ok A.2.n := ok_mono h3 pa.ext.n_le
  have o4 : issub.ok A.2.n := ok_mono h4 pa.ext.n_le
  have s1 : wev A.2 inp n1 = wev gb inp n1 := wev_ext pa.ext h1
  have s2 : wev A.2 inp n2 = wev gb inp n2 := wev_ext pa.ext h2
  have s3 : wev A.2 inp carry = wev gb inp carry := wev_ext pa.ext h3
  have ok_e : ∀ {g g' : GB} {w : Wire}, Ext g g' → w.ok g.n → w.ok g'.n := fun e h => ok_mono h e.n_le
  by_cases hc : (!carry.isc && ((n1.isc && A.1 == .cst true && !n2.isc) || (!n1.isc && n2.isc && n2 == .cst true))) = true
  · rw [if_pos hc]
    have pr := xorV_post hinp hkA pa.reach [n1, n2, carry] (ok3 o1 o2 o3)
    generalize xorV A.2 [n1, n2, carry] = R at pr ⊢
    simp only [List.map_cons, List.map_nil, xorL_three, s1, s2, s3] at pr
    have hkR : k ≤ R.2.n := Nat.le_trans hkA pr.ext.n_le
    have pt := andV_post hinp hkR pr.reach [A.1, n2] (ok2 (ok_e pr.ext pa.ok) (ok_e pr.ext o2))
    generalize andV R.2 [A.1, n2] = T at pt ⊢
    simp only [List.map_cons, List.map_nil, andL_two] at pt
    have hkT : k ≤ T.2.n := Nat.le_trans hkR pt.ext.n_le
    have pc := orV_post hinp hkT pt.reach [T.1, carry] (ok2 pt.ok (ok_e pt.ext (ok_e pr.ext o3)))
    generalize orV T.2 [T.1, carry] = C at pc ⊢
    simp only [List.map_cons, List.map_nil, orL_two] at pc
    refine ⟨(((pa.ext).trans pr.ext).trans pt.ext).trans pc.ext, pc.reach, ?_, pc.ok, ?_, ?_⟩
    · exact ok_e pc.ext (ok_e pt.ext pr.ok)
    · rw [wev_ext (pt.ext.trans pc.ext) pr.ok, pr.val]
    · have vT1 : wev T.2 inp T.1 = ((wev gb inp issub != wev gb inp n1) && wev gb inp n2) := by
        rw [pt.val, wev_ext pr.ext pa.ok, pa.val, wev_ext pr.ext o2, s2]
      have vc : wev T.2 inp carry = wev gb inp carry := by
        rw [wev_ext pt.ext (ok_e pr.ext o3), wev_ext pr.ext o3, s3]
      rw [pc.val, vT1, vc]
      have hcc := hc
      simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at hcc
      obtain ⟨_, hcase⟩ := hcc
      rcases hcase with ⟨⟨_, hA⟩, _⟩ | ⟨⟨_, _⟩, hn2⟩
      · have hx : (wev gb inp issub != wev gb inp n1) = true := by rw [← pa.val, hA]; rfl
        exact cout_case1 _ _ _ _ hx
      · have hb : wev gb inp n2 = true := by rw [hn2]; rfl
        exact cout_case2 _ _ _ _ hb
  · rw [if_neg hc]
    have ps := xorV_post hinp hkA pa.reach [n1, n2] (ok2 o1 o2)
    generalize xorV A.2 [n1, n2] = S at ps ⊢
    simp only [List.map_cons, List.map_nil, xorL_two, s1, s2] at ps
    have hkS : k ≤ S.2.n := Nat.le_trans hkA ps.ext.n_le
    have pres := xorV_post hinp hkS ps.reach [carry, S.1] (ok2 (ok_e ps.ext o3) ps.ok)
    generalize xorV S.2 [carry, S.1] = Rs at pres ⊢
    simp only [List.map_cons, List.map_nil, xorL_two] at pres
    have hkRs : k ≤ Rs.2.n := Nat.le_trans hkS pres.ext.n_le
    have vsum : wev Rs.2 inp Rs.1 = ((wev gb inp n1 != wev gb inp n2) != wev gb inp carry) := by
      rw [pres.val, ps.val, wev_ext ps.ext o3, s3]
      cases wev gb inp n1 <;> cases wev gb inp n2 <;> cases wev gb inp carry <;> rfl
    by_cases hct : (carry.isc && carry == .cst true) = true
    · rw [if_pos hct]
      have pc := orV_post hinp hkRs pres.reach [A.1, n2]
        (ok2 (ok_e (ps.ext.trans pres.ext) pa.ok) (ok_e (ps.ext.trans pres.ext) o2))
      generalize orV Rs.2 [A.1, n2] = C at pc ⊢
      simp only [List.map_cons, List.map_nil, orL_two] at pc
      refine ⟨((pa.ext.trans ps.ext).trans pres.ext).trans pc.ext, pc.reach, ?_, pc.ok, ?_, ?_⟩
      · exact ok_e pc.ext pres.ok
      · rw [wev_ext pc.ext pres.ok, vsum]
      · rw [pc.val, wev_ext (ps.ext.trans pres.ext) pa.ok, pa.val, wev_ext (ps.ext.trans pres.ext) o2, s2]
        have hcc := hct
        simp only [Bool.and_eq_true, beq_iff_eq] at hcc
        have hcv : wev gb inp carry = true := by rw [hcc.2]; rfl
        rw [hcv]
        exact cout_case3 _ _ _
    · rw [if_neg hct]
      have px := xorV_post hinp hkRs pres.reach [issub, S.1]
        (ok2 (ok_e (ps.ext.trans pres.ext) o4) (ok_e pres.ext ps.ok))
      generalize xorV Rs.2 [issub, S.1] = X at px ⊢
      simp only [List.map_cons, List.map_nil, xorL_two] at px
      have hkX : k ≤ X.2.n := Nat.le_trans hkRs px.ext.n_le
      have pc0 := andV_post hinp hkX px.reach [carry, X.1]
        (ok2 (ok_e (ps.ext.trans (pres.ext.trans px.ext)) o3) px.ok)
      generalize andV X.2 [carry, X.1] = C0 at pc0 ⊢
      simp only [List.map_cons, List.map_nil, andL_two] at pc0
      have hkC0 : k ≤ C0.2.n := Nat.le_trans hkX pc0.ext.n_le
      have e1 : Ext gb C0.2 := (((pa.ext.trans ps.ext).trans pres.ext).trans px.ext).trans pc0.ext
      have pt := andV_post hinp hkC0 pc0.reach [A.1, n2]
        (ok2 (ok_e (ps.ext.trans (pres.ext.trans (px.ext.trans pc0.ext))) pa.ok)
          (ok_e (ps.ext.trans (pres.ext.trans (px.ext.trans pc0.ext))) o2))
      generalize andV C0.2 [A.1, n2] = T at pt ⊢
      simp only [List.map_cons, List.map_nil, andL_two] at pt
      have hkT : k ≤ T.2.n := Nat.le_trans hkC0 pt.ext.n_le
      have pf := xorV_post hinp hkT pt.reach [T.1, C0.1] (ok2 pt.ok (ok_e pt.ext pc0.ok))
      generalize xorV T.2 [T.1, C0.1] = F at pf ⊢
      simp only [List.map_cons, List.map_nil, xorL_two] at pf
      refine ⟨(e1.trans pt.ext).trans pf.ext, pf.reach, ?_, pf.ok, ?_, ?_⟩
      · exact ok_e (px.ext.trans (pc0.ext.trans (pt.ext.trans pf.ext))) pres.ok
      · rw [wev_ext (px.ext.trans (pc0.ext.trans (pt.ext.trans pf.ext))) pres.ok, vsum]
      · have vT1 : wev T.2 inp T.1 = ((wev gb inp issub != wev gb inp n1) && wev gb inp n2) := by
          rw [pt.val, wev_ext (ps.ext.trans (pres.ext.trans (px.ext.trans pc0.ext))) pa.ok, pa.val,
            wev_ext (ps.ext.trans (pres.ext.trans (px.ext.trans pc0.ext))) o2, s2]
        have vC0 : wev T.2 inp C0.1 = (wev gb inp carry && (wev gb inp issub != (wev gb inp n1 != wev gb inp n2))) := by
          rw [wev_ext pt.ext pc0.ok, pc0.val, wev_ext px.ext (ok_e (ps.ext.trans pres.ext) o3), px.val,
            wev_ext pres.ext ps.ok, ps.val, wev_ext (ps.ext.trans pres.ext) o3, s3,
            wev_ext (ps.ext.trans pres.ext) o4]
          have : wev A.2 inp issub = wev gb inp issub := wev_ext pa.ext h4
          rw [this]
        rw [pf.val, vT1, vC0]
        rfl

end Add

end SmcIrred
