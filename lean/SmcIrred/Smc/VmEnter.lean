module

public import SmcIrred.Smc.VmRel

public section

namespace SmcIrred.Vm

theorem base_ge (n x : Nat) : n + 3 ≤ base n x := by unfold base; omega

theorem base_eq (n x : Nat) : base n x = n + 3 + 36 * x := rfl

theorem sEnter_stk (w : Nat) (s : SState) : (sEnter w s).stk = if s.pk w then s.stk else s.stk.tail := by
  simp [sEnter]

theorem blk_sEnter {g : Digraph} (s : SState) {w : Nat} (hent : s.ent w = none) (x i : Nat)
    (hi : x ≠ w ∨ i ∉ [0, 1, 13, 20, 29]) : blk g (sEnter w s) x i = blk g s x i := by
  by_cases hx : x = w
  · subst hx
    have hi' : i ∉ [0, 1, 13, 20, 29] := by
      rcases hi with h | h
      · exact absurd rfl h
      · exact h
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi'
    obtain ⟨h0, h1, h13, h20, h29⟩ := hi'
    unfold blk
    simp [sEnter, fupd, hent, h0, h1, h13, h20, h29]
    try rfl
  · apply blk_congr_fields
    all_goals simp [sEnter, fupd, hx]

/-- Entering an unvisited node `w` (offsets 0–9 of its block): the machine realises `sEnter w s`, the counter cell is the
original `succ[w].size()` and the return jump holds the popped return address. -/
theorem vm_enter {g : Digraph} {s : SState} {oc : Nat} {m : VM} {w : Nat} (h : VR g s oc m) (hw : w < g.n)
    (hent : s.ent w = none) (hpc : m.pc = base g.n w) {c0 : Option Nat} {rest : List (Option Nat)}
    (hstk : s.stk = c0 :: rest) :
    ∃ m', Rn g m m' ∧ m'.pc = base g.n w + 10 ∧ VR g (sEnter w s) oc m' ∧
      m'.mem (base g.n w + 10) = .data ((g.succ w).length : Nat) ∧
      m'.mem (base g.n w + 30) = .jmp (.at (enc g.n oc c0)) ∧ (∀ a, FreeC g s a → m'.mem a = m.mem a) := by
  have hb3 := base_ge g.n w
  have hb0 : base g.n w ≠ 0 := by omega
  have hb0' : 0 ≠ base g.n w := by omega
  have hmstk : m.stk = enc g.n oc c0 :: rest.map (enc g.n oc) := by rw [h.stk, hstk]; rfl
  have f0 : m.mem (base g.n w) = .data (-1) := by
    have := h.fetch hw (i := 0) (by omega) (Or.inr hent)
    simpa [blk, hent] using this
  have f1 : m.mem (base g.n w + 1) = .load 0 := by
    rw [h.fetch hw (by omega) (Or.inr hent)]; simp [blk, hent]
  have f2 : m.mem (base g.n w + 2) = .store (.rp 0) (.k (base g.n w)) := by
    rw [h.fetch_bp hw (by omega) (Or.inr hent) (by decide)]; rfl
  have f3 : m.mem (base g.n w + 3) = .store (.rp 0) (.k (base g.n w + 29)) := by
    rw [h.fetch_bp hw (by omega) (Or.inr hent) (by decide)]; rfl
  have f4 : m.mem (base g.n w + 4) = .store (.rp 1) (.k 0) := by
    rw [h.fetch_bp hw (by omega) (Or.inr hent) (by decide)]; rfl
  have f5 : m.mem (base g.n w + 5) = (if s.pk w then .peek else .pop) := by
    rw [h.fetch hw (by omega) (Or.inr hent)]; simp [blk]
  have f6 : m.mem (base g.n w + 6) = .modinst .jmpReg (.k (base g.n w + 30)) := by
    rw [h.fetch_bp hw (by omega) (Or.inr hent) (by decide)]; rfl
  have f7 : m.mem (base g.n w + 7) = .modinst (.jcStkNe 2) (.k (base g.n w + 20)) := by
    rw [h.fetch_bp hw (by omega) (Or.inr hent) (by decide)]; rfl
  have f8 : m.mem (base g.n w + 8) = .modinst (.jcStkNe 2) (.k (base g.n w + 13)) := by
    rw [h.fetch_bp hw (by omega) (Or.inr hent) (by decide)]; rfl
  have f9 : m.mem (base g.n w + 9) = .modinst .ret (.k (base g.n w + 1)) := by
    rw [h.fetch_bp hw (by omega) (Or.inr hent) (by decide)]; rfl
  have f10 : m.mem (base g.n w + 10) = .data ((g.succ w).length : Nat) := by
    rw [h.fetch hw (by omega) (Or.inr hent), blk_other s (by decide)]; rfl
  have f29 : m.mem (base g.n w + 29) = .data (-1) := by
    rw [h.fetch hw (by omega) (Or.inr hent)]; simp [blk, hent]
  have f30 : m.mem (base g.n w + 30) = .jmp (.at 0) := by
    rw [h.fetch hw (by omega) (Or.inr hent), blk_other s (by decide)]; rfl
  obtain ⟨m1, R1, st1, mem1, pc1, reg1, stk1, sol1⟩ := eff_data (g := g) (m := m) h.st (by rw [hpc]; exact f0)
  have p1 : m1.pc = base g.n w + 1 := by omega
  obtain ⟨m2, R2, st2, mem2, pc2, reg2, stk2, sol2⟩ :=
    eff_load (g := g) (m := m1) st1 (by rw [mem1, p1]; exact f1) (by rw [mem1, h.mem_zero])
  have p2 : m2.pc = base g.n w + 2 := by omega
  obtain ⟨m3, R3, st3, mem3, pc3, reg3, stk3, sol3⟩ :=
    eff_store (g := g) (m := m2) st2 (by rw [mem2, mem1, p2]; exact f2) (by rw [mem2, mem1]; exact f0)
  simp only [Dst.eval, Src.eval, mem2, mem1, reg2, Int.add_zero] at mem3
  have p3 : m3.pc = base g.n w + 3 := by omega
  obtain ⟨m4, R4, st4, mem4, pc4, reg4, stk4, sol4⟩ :=
    eff_store (g := g) (m := m3) st3
      (by rw [mem3, p3]; simp [memUpd]; exact f3)
      (by rw [mem3]; simp [memUpd, Dst.eval]; exact f29)
  simp only [Dst.eval, Src.eval, mem3, reg3, reg2, Int.add_zero] at mem4
  have p4 : m4.pc = base g.n w + 4 := by omega
  obtain ⟨m5, R5, st5, mem5, pc5, reg5, stk5, sol5⟩ :=
    eff_store (g := g) (m := m4) st4
      (by rw [mem4, p4]; simp [memUpd]; exact f4)
      (by rw [mem4]; simp [memUpd, Dst.eval, hb0, hb0']; rw [h.mem_zero])
  simp only [Dst.eval, Src.eval, mem4, reg4, reg3, reg2] at mem5
  have p5 : m5.pc = base g.n w + 5 := by omega
  have g5 : m5.mem (base g.n w + 5) = (if s.pk w then .peek else .pop) := by
    rw [mem5]; simp [memUpd]; exact f5
  have hs5 : m5.stk = enc g.n oc c0 :: rest.map (enc g.n oc) := by rw [stk5, stk4, stk3, stk2, stk1, hmstk]
  obtain ⟨m6, R6, st6, mem6, pc6, reg6, stk6, sol6⟩ : ∃ m6, Rn g m5 m6 ∧ m6.st = .run ∧ m6.mem = m5.mem ∧
      m6.pc = m5.pc + 1 ∧ m6.reg = (enc g.n oc c0 : Nat) ∧ m6.stk = (sEnter w s).stk.map (enc g.n oc) ∧
      m6.sol = m5.sol := by
    by_cases hp : s.pk w = true
    · obtain ⟨m6, R6, st6, mem6, pc6, reg6, stk6, sol6⟩ :=
        eff_peek (g := g) (m := m5) st5 (by rw [p5, g5]; simp [hp]) hs5
      refine ⟨m6, R6, st6, mem6, pc6, reg6, ?_, sol6⟩
      rw [stk6, hs5, sEnter_stk, if_pos hp, hstk]; rfl
    · obtain ⟨m6, R6, st6, mem6, pc6, reg6, stk6, sol6⟩ :=
        eff_pop (g := g) (m := m5) st5 (by rw [p5, g5]; simp [hp]) hs5
      refine ⟨m6, R6, st6, mem6, pc6, reg6, ?_, sol6⟩
      rw [stk6, sEnter_stk, if_neg hp, hstk]; rfl
  have p6 : m6.pc = base g.n w + 6 := by omega
  obtain ⟨m7, R7, st7, mem7, pc7, reg7, stk7, sol7⟩ :=
    eff_modinst (g := g) (m := m6) st6 (by rw [mem6, p6, mem5]; simp [memUpd]; exact f6)
      (a := base g.n w + 30) (by simp [MAddr.eval])
  have p7 : m7.pc = base g.n w + 7 := by omega
  have hj : (Mk.build m6 .jmpReg) = .jmp (.at (enc g.n oc c0)) := by simp [Mk.build, reg6]
  rw [hj] at mem7
  rw [mem6] at mem7
  obtain ⟨m8, R8, st8, mem8, pc8, reg8, stk8, sol8⟩ :=
    eff_modinst (g := g) (m := m7) st7 (by rw [mem7, p7, mem5]; simp [memUpd]; exact f7)
      (a := base g.n w + 20) (by simp [MAddr.eval])
  have p8 : m8.pc = base g.n w + 8 := by omega
  obtain ⟨m9, R9, st9, mem9, pc9, reg9, stk9, sol9⟩ :=
    eff_modinst (g := g) (m := m8) st8 (by rw [mem8, p8, mem7, mem5]; simp [memUpd]; exact f8)
      (a := base g.n w + 13) (by simp [MAddr.eval])
  have p9 : m9.pc = base g.n w + 9 := by omega
  obtain ⟨m10, R10, st10, mem10, pc10, reg10, stk10, sol10⟩ :=
    eff_modinst (g := g) (m := m9) st9 (by rw [mem9, p9, mem8, mem7, mem5]; simp [memUpd]; exact f9)
      (a := base g.n w + 1) (by simp [MAddr.eval])
  have p10 : m10.pc = base g.n w + 10 := by omega
  have hL7 : m7.stk.length = (sEnter w s).stk.length := by rw [stk7, stk6, List.length_map]
  have hL8 : m8.stk.length = (sEnter w s).stk.length := by rw [stk8, stk7, stk6, List.length_map]
  have hmem7 : ∀ a, a ≠ base g.n w + 30 → m7.mem a = m5.mem a := by
    intro a n; rw [mem7]; exact memUpd_ne _ _ n
  have hother : ∀ a, a ≠ base g.n w + 1 → a ≠ base g.n w + 13 → a ≠ base g.n w + 20 → a ≠ base g.n w + 30 →
      a ≠ base g.n w + 29 → a ≠ base g.n w → a ≠ 0 → m10.mem a = m.mem a := by
    intro a n1 n13 n20 n30 n29 n0 nz
    rw [mem10, memUpd_ne _ _ n1, mem9, memUpd_ne _ _ n13, mem8, memUpd_ne _ _ n20, mem7, memUpd_ne _ _ n30, mem5]
    simp only [Dst.eval, memUpd, if_neg nz, if_neg n29, if_neg n0, mem2, mem1]
  have e1 : m10.mem (base g.n w + 1) = .ret := by
    rw [mem10]; simp [memUpd, Mk.build]
  have e13 : m10.mem (base g.n w + 13) = .jc (.stkNe (sEnter w s).stk.length) 2 := by
    rw [mem10, memUpd_ne _ _ (by omega : base g.n w + 13 ≠ base g.n w + 1), mem9]
    simp [memUpd, Mk.build, hL8]
  have e20 : m10.mem (base g.n w + 20) = .jc (.stkNe (sEnter w s).stk.length) 2 := by
    rw [mem10, memUpd_ne _ _ (by omega : base g.n w + 20 ≠ base g.n w + 1), mem9,
      memUpd_ne _ _ (by omega : base g.n w + 20 ≠ base g.n w + 13), mem8]
    simp [memUpd, Mk.build, hL7]
  have e30 : m10.mem (base g.n w + 30) = .jmp (.at (enc g.n oc c0)) := by
    rw [mem10, memUpd_ne _ _ (by omega : base g.n w + 30 ≠ base g.n w + 1), mem9,
      memUpd_ne _ _ (by omega : base g.n w + 30 ≠ base g.n w + 13), mem8,
      memUpd_ne _ _ (by omega : base g.n w + 30 ≠ base g.n w + 20), mem7]
    simp [memUpd]
  have e29 : m10.mem (base g.n w + 29) = .data (s.idx : Nat) := by
    rw [mem10, memUpd_ne _ _ (by omega : base g.n w + 29 ≠ base g.n w + 1), mem9,
      memUpd_ne _ _ (by omega : base g.n w + 29 ≠ base g.n w + 13), mem8,
      memUpd_ne _ _ (by omega : base g.n w + 29 ≠ base g.n w + 20), mem7,
      memUpd_ne _ _ (by omega : base g.n w + 29 ≠ base g.n w + 30), mem5]
    simp [memUpd, Dst.eval, hb0, hb0']
  have e0 : m10.mem (base g.n w) = .data (s.idx : Nat) := by
    rw [mem10, memUpd_ne _ _ (by omega : base g.n w ≠ base g.n w + 1), mem9,
      memUpd_ne _ _ (by omega : base g.n w ≠ base g.n w + 13), mem8,
      memUpd_ne _ _ (by omega : base g.n w ≠ base g.n w + 20), mem7,
      memUpd_ne _ _ (by omega : base g.n w ≠ base g.n w + 30), mem5]
    simp [memUpd, Dst.eval, hb0, hb0']
  have ez : m10.mem 0 = .data ((s.idx : Nat) + 1 : Int) := by
    rw [mem10, memUpd_ne _ _ (by omega : 0 ≠ base g.n w + 1), mem9,
      memUpd_ne _ _ (by omega : 0 ≠ base g.n w + 13), mem8,
      memUpd_ne _ _ (by omega : 0 ≠ base g.n w + 20), mem7,
      memUpd_ne _ _ (by omega : 0 ≠ base g.n w + 30), mem5]
    simp [memUpd, Dst.eval, hb0, hb0']
  have hsol : m10.sol = [] := by
    rw [sol10, sol9, sol8, sol7, sol6, sol5, sol4, sol3, sol2, sol1, h.sol]
  have hstk10 : m10.stk = (sEnter w s).stk.map (enc g.n oc) := by rw [stk10, stk9, stk8, stk7, stk6]
  have hent2 : (sEnter w s).ent w = some s.idx := by simp [sEnter, fupd]
  have hlow2 : (sEnter w s).low w = s.idx := by simp [sEnter, fupd]
  have hdep2 := sEnter_dep w s
  refine ⟨m10, R1.trans (R2.trans (R3.trans (R4.trans (R5.trans (R6.trans (R7.trans (R8.trans (R9.trans R10)))))))),
    p10, ⟨st10, hsol, hstk10, ?_, by simpa [sEnter] using h.nodup⟩, ?_, e30, ?_⟩
  · intro a
    by_cases a1 : a = base g.n w + 1
    · left; subst a1
      rw [e1, img_blk g _ hw (by decide : 1 < 36)]; simp [blk, hent2]
    by_cases a13 : a = base g.n w + 13
    · left; subst a13
      rw [e13, img_blk g _ hw (by decide : 13 < 36)]; simp [blk, hent2, hdep2]
    by_cases a20 : a = base g.n w + 20
    · left; subst a20
      rw [e20, img_blk g _ hw (by decide : 20 < 36)]; simp [blk, hent2, hdep2]
    by_cases a30 : a = base g.n w + 30
    · right; subst a30
      exact ⟨w, 30, hw, rfl, Or.inr rfl, by rw [hent2]; simp⟩
    by_cases a29 : a = base g.n w + 29
    · left; subst a29
      rw [e29, img_blk g _ hw (by decide : 29 < 36)]; simp [blk, hent2, hlow2]
    by_cases a0 : a = base g.n w
    · left; subst a0
      have := img_blk g (sEnter w s) hw (by decide : 0 < 36)
      rw [Nat.add_zero] at this
      rw [e0, this]; simp [blk, hent2]
    by_cases az : a = 0
    · left; subst az
      rw [ez, img_zero]; simp [sEnter]
    rw [hother a a1 a13 a20 a30 a29 a0 az]
    rcases h.mem a with hi | hf
    · left
      rw [hi]
      apply img_congr
      · intro h0; exact absurd h0 az
      · intro _; rfl
      · intro _; rfl
      · intro x i hx hi' hxa
        symm
        apply blk_sEnter s hent
        by_cases hxw : x = w
        · right; subst hxw
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
          omega
        · left; exact hxw
    · right
      exact hf.mono (fun x hx hn => by
        by_cases e : x = w
        · subst e; exact hx hent
        · simp [sEnter, fupd, e] at hn; exact hx hn)
  · rw [hother _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]; exact f10
  · intro a ha
    obtain ⟨x, i, hx, e, hi, hne⟩ := ha
    have hxw : x ≠ w := fun e' => hne (e' ▸ hent)
    apply hother
    all_goals (first | (unfold base at e hb3 ⊢; omega) | (unfold base at e hb3; omega))

end SmcIrred.Vm
