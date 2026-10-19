module

public import SmcIrred.Smc.VmEnter

public section

namespace SmcIrred.Vm

theorem VR.congr {g : Digraph} {s : SState} {oc : Nat} {m m' : VM} (h : VR g s oc m) (hst : m'.st = .run)
    (hmem : m'.mem = m.mem) (hstk : m'.stk = m.stk) (hsol : m'.sol = m.sol) : VR g s oc m' :=
  ⟨hst, by rw [hsol]; exact h.sol, by rw [hstk]; exact h.stk, by rw [hmem]; exact h.mem, h.nodup⟩

theorem sPre_fields (x w : Nat) (s : SState) :
    (sPre x w s).idx = s.idx ∧ (sPre x w s).low = s.low ∧ (sPre x w s).chk = s.chk ∧ (sPre x w s).set = s.set ∧
    (sPre x w s).chain = s.chain ∧ (sPre x w s).stk = some x :: s.stk ∧
    (sPre x w s).pk = (if s.stk.length = s.dep x then fupd s.pk w true else s.pk) := by
  unfold sPre
  by_cases hc : s.stk.length = s.dep x <;> simp [hc]

theorem blk_sPre {g : Digraph} (x w : Nat) (s : SState) (y i : Nat) (hi : y ≠ w ∨ i ≠ 5) :
    blk g (sPre x w s) y i = blk g s y i := by
  obtain ⟨_, hlow, hchk, hset, hchain, _, hpk⟩ := sPre_fields x w s
  have hent := sPre_ent x w s
  have hdep := sPre_dep x w s
  by_cases h5 : i = 5
  · have hy : y ≠ w := by
      rcases hi with h | h
      · exact h
      · exact absurd h5 h
    have hp : (sPre x w s).pk y = s.pk y := by
      rw [hpk]; by_cases hc : s.stk.length = s.dep x <;> simp [hc, fupd, hy]
    unfold blk
    simp [h5, hp, hlow, hchk, hset, hchain, hent, hdep]
  · unfold blk
    simp [h5, hlow, hchk, hset, hchain, hent, hdep]

/-- Steps 13–15 of the successor loop: the patch of the successor's `pop` into `peek` (only when nothing was pushed since
the entry of `x`) and the call, which pushes the return address inside `x`. -/
theorem vm_pre {g : Digraph} {s : SState} {oc : Nat} {m : VM} {x w c : Nat} (h : VR g s oc m) (hx : x < g.n)
    (hxe : s.ent x ≠ none) (hw : w < g.n) (hpc : m.pc = base g.n x + 13) (hreg : m.reg = (c : Int)) (hc : 1 ≤ c)
    (hwc : (g.succ x).getD (c - 1) 0 = w) :
    ∃ m1, Rn g m m1 ∧ m1.pc = base g.n w ∧ VR g (sPre x w s) oc m1 ∧
      (∀ a, FreeC g s a → m1.mem a = m.mem a) := by
  obtain ⟨k, hk⟩ : ∃ k, s.ent x = some k := by
    cases h' : s.ent x
    · exact absurd h' hxe
    · exact ⟨_, rfl⟩
  have f13 : m.mem (base g.n x + 13) = .jc (.stkNe (s.dep x)) 2 := by
    rw [h.fetch hx (by omega) (Or.inl ⟨by omega, by omega⟩)]; simp [blk, hk]
  have f14 : m.mem (base g.n x + 14) = .modinst .peek (.peekOf x) := by
    rw [h.fetch_bp hx (by omega) (Or.inl ⟨by omega, by omega⟩) (by decide)]; rfl
  have f15 : m.mem (base g.n x + 15) = .callS x := by
    rw [h.fetch_bp hx (by omega) (Or.inl ⟨by omega, by omega⟩) (by decide)]; rfl
  have hlen : m.stk.length = s.stk.length := by rw [h.stk, List.length_map]
  have hcn : ((c : Int) - 1).toNat = c - 1 := by omega
  obtain ⟨hidx, hlow, hchk, hset, hchain, hstkP, hpk⟩ := sPre_fields x w s
  have hentP := sPre_ent x w s
  have hdepP := sPre_dep x w s
  by_cases hd : s.stk.length = s.dep x
  · obtain ⟨m1, R1, st1, mem1, pc1, reg1, stk1, sol1⟩ :=
      eff_jc_false (g := g) (m := m) h.st (by rw [hpc]; exact f13) (by simp [Cnd.eval, hlen, hd])
    have p1 : m1.pc = base g.n x + 14 := by omega
    obtain ⟨m2, R2, st2, mem2, pc2, reg2, stk2, sol2⟩ :=
      eff_modinst (g := g) (m := m1) st1 (by rw [mem1, p1]; exact f14) (a := base g.n w + 5)
        (by simp only [MAddr.eval]; rw [reg1, hreg, hcn, hwc])
    have p2 : m2.pc = base g.n x + 15 := by omega
    obtain ⟨m3, R3, st3, mem3, pc3, reg3, stk3, sol3⟩ :=
      eff_callS (g := g) (m := m2) st2
        (by rw [mem2, p2, memUpd_ne _ _ (by unfold base; omega : base g.n x + 15 ≠ base g.n w + 5), mem1]; exact f15)
    have hb : Mk.build m1 .peek = .peek := rfl
    rw [hb] at mem2
    rw [mem1] at mem2
    refine ⟨m3, R1.trans (R2.trans R3), ?_, ⟨st3, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [pc3, reg2, reg1, hreg, hcn, hwc]
    · rw [sol3, sol2, sol1, h.sol]
    · rw [stk3, stk2, stk1, h.stk, hstkP, p2]; rfl
    · intro a
      rw [mem3, mem2]
      by_cases ha : a = base g.n w + 5
      · left; subst ha
        rw [memUpd_same, img_blk g _ hw (by decide : 5 < 36)]
        simp [blk, hpk, hd, fupd]
      · rw [memUpd_ne _ _ ha]
        rcases h.mem a with hi | hf
        · left; rw [hi]
          apply img_congr
          · intro _; exact hidx.symm
          · intro _; rw [hchain]
          · intro _; rw [hchain]
          · intro y i hy hi' hya
            symm
            apply blk_sPre
            by_cases hyw : y = w
            · right; subst hyw; intro h5; apply ha; rw [hya, h5]
            · left; exact hyw
        · right; exact hf.mono (fun y hy hn => hy (by rw [hentP] at hn; exact hn))
    · rw [hchain]; exact h.nodup
    · intro a ha
      obtain ⟨y, i, hy, e, hi, hne⟩ := ha
      rw [mem3, mem2, memUpd_ne _ _ (by unfold base at e ⊢; omega)]
  · obtain ⟨m1, R1, st1, mem1, pc1, reg1, stk1, sol1⟩ :=
      eff_jc_true (g := g) (m := m) h.st (by rw [hpc]; exact f13)
        (by simp [Cnd.eval, hlen, hd, Ne.symm hd])
    have p1 : m1.pc = base g.n x + 15 := by omega
    obtain ⟨m3, R3, st3, mem3, pc3, reg3, stk3, sol3⟩ :=
      eff_callS (g := g) (m := m1) st1 (by rw [mem1, p1]; exact f15)
    have hpk' : (sPre x w s).pk = s.pk := by rw [hpk]; simp [hd]
    refine ⟨m3, R1.trans R3, ?_, ⟨st3, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [pc3, reg1, hreg, hcn, hwc]
    · rw [sol3, sol1, h.sol]
    · rw [stk3, stk1, h.stk, hstkP, p1]; rfl
    · intro a
      rw [mem3, mem1]
      rcases h.mem a with hi | hf
      · left; rw [hi]
        apply img_congr
        · intro _; exact hidx.symm
        · intro _; rw [hchain]
        · intro _; rw [hchain]
        · intro y i hy hi' hya
          symm
          exact blk_congr_fields i (by rw [hentP]) (by rw [hpk']) (by rw [hdepP]) (by rw [hchk]) (by rw [hlow])
            (by rw [hset]) (fun _ => by rw [hchain])
      · right; exact hf.mono (fun y hy hn => hy (by rw [hentP] at hn; exact hn))
    · rw [hchain]; exact h.nodup
    · intro a _; rw [mem3, mem1]

end SmcIrred.Vm
