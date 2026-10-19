module

public import SmcIrred.Smc.VmCall

public section

namespace SmcIrred.Vm

theorem sStep_pos {x r : Nat} {s : SState} (h : r < s.low x) :
    sStep x (r, s) = { s with low := fupd s.low x r, chk := fupd s.chk x true } := by
  unfold sStep; simp [h]

theorem sStep_neg {x r : Nat} {s : SState} (h : ¬ r < s.low x) : sStep x (r, s) = s := by
  unfold sStep; simp [h]

theorem blk_lowchk {g : Digraph} (s : SState) (x r y i : Nat) (hi : y ≠ x ∨ (i ≠ 22 ∧ i ≠ 29)) :
    blk g { s with low := fupd s.low x r, chk := fupd s.chk x true } y i = blk g s y i := by
  by_cases hy : y = x
  · subst hy
    have h' : i ≠ 22 ∧ i ≠ 29 := by
      rcases hi with h | h
      · exact absurd rfl h
      · exact h
    obtain ⟨h22, h29⟩ := h'
    unfold blk
    simp [h22, h29]
  · apply blk_congr_fields <;> simp [fupd, hy]

/-- A call of an already visited node `w` (offsets 0 and 1 of its block): its marker is returned, the pushed return
address is popped and jumped to. -/
theorem vm_visited {g : Digraph} {s1 : SState} {oc : Nat} {m : VM} {w k : Nat} (h : VR g s1 oc m) (hw : w < g.n)
    (hk : s1.ent w = some k) (hpc : m.pc = base g.n w) {c0 : Option Nat} {rest : List (Option Nat)}
    (hstk : s1.stk = c0 :: rest) :
    ∃ m', Rn g m m' ∧ m'.pc = enc g.n oc c0 ∧ m'.reg = (k : Int) ∧ VR g { s1 with stk := rest } oc m' := by
  have hmstk : m.stk = enc g.n oc c0 :: rest.map (enc g.n oc) := by rw [h.stk, hstk]; rfl
  have f0 : m.mem (base g.n w) = .data (k : Int) := by
    have := h.fetch hw (i := 0) (by omega) (Or.inl ⟨by omega, by omega⟩)
    simpa [blk, hk] using this
  have f1 : m.mem (base g.n w + 1) = .ret := by
    rw [h.fetch hw (by omega) (Or.inl ⟨by omega, by omega⟩)]; simp [blk, hk]
  obtain ⟨m1, R1, st1, mem1, pc1, reg1, stk1, sol1⟩ := eff_data (g := g) (m := m) h.st (by rw [hpc]; exact f0)
  have p1 : m1.pc = base g.n w + 1 := by omega
  obtain ⟨m2, R2, st2, mem2, pc2, reg2, stk2, sol2⟩ :=
    eff_ret (g := g) (m := m1) st1 (by rw [mem1, p1]; exact f1) (a := enc g.n oc c0) (r := rest.map (enc g.n oc))
      (by rw [stk1, hmstk])
  refine ⟨m2, R1.trans R2, pc2, by rw [reg2, reg1], ?_⟩
  exact ⟨st2, by rw [sol2, sol1, h.sol], by rw [stk2], by rw [mem2, mem1]; exact h.mem, h.nodup⟩

/-- Steps 10–12 of the successor loop with a positive counter: the counter cell is read and decremented. -/
theorem vm_iter_head {g : Digraph} {s : SState} {oc : Nat} {m : VM} {x c : Nat} (h : VR g s oc m) (hx : x < g.n)
    (hxe : s.ent x ≠ none) (hpc : m.pc = base g.n x + 10) (hcell : m.mem (base g.n x + 10) = .data (c : Int))
    (hc1 : 1 ≤ c) :
    ∃ m1, Rn g m m1 ∧ m1.pc = base g.n x + 13 ∧ m1.reg = (c : Int) ∧ VR g s oc m1 ∧
      m1.mem (base g.n x + 10) = .data ((c - 1 : Nat) : Int) ∧
      (∀ a, a ≠ base g.n x + 10 → m1.mem a = m.mem a) := by
  have f11 : m.mem (base g.n x + 11) = .jc .regZ 9 := by
    rw [h.fetch_bp hx (by omega) (Or.inl ⟨by omega, by omega⟩) (by decide)]; rfl
  have f12 : m.mem (base g.n x + 12) = .store (.rp (-1)) (.k (base g.n x + 10)) := by
    rw [h.fetch_bp hx (by omega) (Or.inl ⟨by omega, by omega⟩) (by decide)]; rfl
  obtain ⟨m1, R1, st1, mem1, pc1, reg1, stk1, sol1⟩ := eff_data (g := g) (m := m) h.st (by rw [hpc]; exact hcell)
  have p1 : m1.pc = base g.n x + 11 := by omega
  obtain ⟨m2, R2, st2, mem2, pc2, reg2, stk2, sol2⟩ :=
    eff_jc_false (g := g) (m := m1) st1 (by rw [mem1, p1]; exact f11) (by simp [Cnd.eval, reg1]; omega)
  have p2 : m2.pc = base g.n x + 12 := by omega
  obtain ⟨m3, R3, st3, mem3, pc3, reg3, stk3, sol3⟩ :=
    eff_store (g := g) (m := m2) st2 (by rw [mem2, mem1, p2]; exact f12) (by rw [mem2, mem1]; exact hcell)
  simp only [Dst.eval, Src.eval, mem2, mem1] at mem3
  have p3 : m3.pc = base g.n x + 13 := by omega
  have hr3 : m3.reg = (c : Int) := by rw [reg3, reg2, reg1]
  have hm3 : m3.mem (base g.n x + 10) = .data ((c - 1 : Nat) : Int) := by
    rw [mem3, memUpd_same]
    have : ((c : Int) + -1) = ((c - 1 : Nat) : Int) := by omega
    rw [reg2, reg1, this]
  refine ⟨m3, R1.trans (R2.trans R3), p3, hr3, ⟨st3, by rw [sol3, sol2, sol1, h.sol], by rw [stk3, stk2, stk1, h.stk],
    ?_, h.nodup⟩, hm3, ?_⟩
  · intro a
    by_cases ha : a = base g.n x + 10
    · right; subst ha
      exact ⟨x, 10, hx, rfl, Or.inl rfl, hxe⟩
    · rw [mem3, memUpd_ne _ _ ha]; exact h.mem a
  · intro a ha
    rw [mem3, memUpd_ne _ _ ha]

theorem vm_after_call {g : Digraph} {s : SState} {oc : Nat} {m : VM} {x r : Nat} (h : VR g s oc m) (hx : x < g.n)
    (hxe : s.ent x ≠ none) (hpc : m.pc = base g.n x + 16) (hreg : m.reg = (r : Int)) :
    ∃ m', Rn g m m' ∧ m'.pc = base g.n x + 10 ∧ VR g (sStep x (r, s)) oc m' ∧
      (∀ a, FreeC g s a → m'.mem a = m.mem a) := by
  obtain ⟨k, hk⟩ : ∃ k, s.ent x = some k := by
    cases h' : s.ent x
    · exact absurd h' hxe
    · exact ⟨_, rfl⟩
  have f16 : m.mem (base g.n x + 16) = .jc (.regGeLow x) (-6) := by
    rw [h.fetch_bp hx (by omega) (Or.inl ⟨by omega, by omega⟩) (by decide)]; rfl
  have f29 : m.mem (base g.n x + 29) = .data (s.low x : Nat) := by
    rw [h.fetch hx (by omega) (Or.inl ⟨by omega, by omega⟩)]; simp [blk, hk]
  have f17 : m.mem (base g.n x + 17) = .store (.rp 0) (.k (base g.n x + 29)) := by
    rw [h.fetch_bp hx (by omega) (Or.inl ⟨by omega, by omega⟩) (by decide)]; rfl
  have f18 : m.mem (base g.n x + 18) = .modinst (.jcTrue 7) (.k (base g.n x + 22)) := by
    rw [h.fetch_bp hx (by omega) (Or.inl ⟨by omega, by omega⟩) (by decide)]; rfl
  have f19 : m.mem (base g.n x + 19) = .jc .tru (-9) := by
    rw [h.fetch_bp hx (by omega) (Or.inl ⟨by omega, by omega⟩) (by decide)]; rfl
  by_cases hge : s.low x ≤ r
  · obtain ⟨m1, R1, st1, mem1, pc1, reg1, stk1, sol1⟩ :=
      eff_jc_true (g := g) (m := m) h.st (by rw [hpc]; exact f16)
        (by simp [Cnd.eval, dataAt, f29, hreg, hge])
    have hn : ¬ r < s.low x := by omega
    rw [sStep_neg hn]
    refine ⟨m1, R1, by omega, h.congr st1 mem1 stk1 sol1, fun a _ => by rw [mem1]⟩
  · obtain ⟨m1, R1, st1, mem1, pc1, reg1, stk1, sol1⟩ :=
      eff_jc_false (g := g) (m := m) h.st (by rw [hpc]; exact f16)
        (by simp [Cnd.eval, dataAt, f29, hreg]; omega)
    have hlt : r < s.low x := by omega
    rw [sStep_pos hlt]
    have p1 : m1.pc = base g.n x + 17 := by omega
    obtain ⟨m2, R2, st2, mem2, pc2, reg2, stk2, sol2⟩ :=
      eff_store (g := g) (m := m1) st1 (by rw [mem1, p1]; exact f17) (by rw [mem1]; exact f29)
    simp only [Dst.eval, Src.eval, mem1] at mem2
    have p2 : m2.pc = base g.n x + 18 := by omega
    obtain ⟨m3, R3, st3, mem3, pc3, reg3, stk3, sol3⟩ :=
      eff_modinst (g := g) (m := m2) st2
        (by rw [mem2, p2, memUpd_ne _ _ (by omega : base g.n x + 18 ≠ base g.n x + 29)]; exact f18)
        (a := base g.n x + 22) (by simp [MAddr.eval])
    have p3 : m3.pc = base g.n x + 19 := by omega
    obtain ⟨m4, R4, st4, mem4, pc4, reg4, stk4, sol4⟩ :=
      eff_jc_true (g := g) (m := m3) st3
        (by rw [mem3, p3, memUpd_ne _ _ (by omega : base g.n x + 19 ≠ base g.n x + 22), mem2,
          memUpd_ne _ _ (by omega : base g.n x + 19 ≠ base g.n x + 29)]; exact f19)
        (by simp [Cnd.eval])
    have hb : Mk.build m2 (.jcTrue 7) = .jc .tru 7 := rfl
    rw [hb] at mem3
    rw [mem2] at mem3
    simp only [reg1, hreg, Int.add_zero] at mem3
    have hLow : ({ s with low := fupd s.low x r, chk := fupd s.chk x true } : SState).low x = r := by simp [fupd]
    have hChk : ({ s with low := fupd s.low x r, chk := fupd s.chk x true } : SState).chk x = true := by simp [fupd]
    refine ⟨m4, R1.trans (R2.trans (R3.trans R4)), by omega, ⟨st4, ?_, ?_, ?_, h.nodup⟩, ?_⟩
    · rw [sol4, sol3, sol2, sol1, h.sol]
    · rw [stk4, stk3, stk2, stk1, h.stk]
    · intro a
      rw [mem4, mem3]
      by_cases a22 : a = base g.n x + 22
      · left; subst a22
        rw [memUpd_same, img_blk g _ hx (by decide : 22 < 36)]
        simp [blk, hk, fupd]
      by_cases a29 : a = base g.n x + 29
      · left; subst a29
        rw [memUpd_ne _ _ (by omega : base g.n x + 29 ≠ base g.n x + 22), memUpd_same,
          img_blk g _ hx (by decide : 29 < 36)]
        simp [blk, hk, fupd]
      rw [memUpd_ne _ _ a22, memUpd_ne _ _ a29]
      rcases h.mem a with hi | hf
      · left; rw [hi]
        apply img_congr
        · intro _; rfl
        · intro _; rfl
        · intro _; rfl
        · intro y i hy hi' hya
          symm
          apply blk_lowchk
          by_cases hyx : y = x
          · right; subst hyx
            constructor <;> (intro hh; subst hh; first | exact a22 hya | exact a29 hya)
          · left; exact hyx
      · right; exact hf
    · intro a ha
      obtain ⟨y, i, hy, e, hi, hne⟩ := ha
      rw [mem4, mem3, memUpd_ne _ _ (by unfold base at e ⊢; omega), memUpd_ne _ _ (by unfold base at e ⊢; omega)]

end SmcIrred.Vm
