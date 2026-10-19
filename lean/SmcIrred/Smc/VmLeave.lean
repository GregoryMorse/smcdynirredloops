module

public import SmcIrred.Smc.VmExtract

public section

namespace SmcIrred.Vm

/-- The component extraction loop (offsets 23–28 of the block of the root `w`), by induction on the popped cells. -/
theorem vm_extract {g : Digraph} {w : Nat} (hw : w < g.n) : ∀ (N tl : List Nat) (s : SState) (fuel : Nat) (oc : Nat)
    (m : VM), w ∉ N → N.length + 1 ≤ fuel → s.stk = (N ++ w :: tl).map some → (N ++ w :: tl).Nodup →
    (∀ u ∈ N ++ [w], u < g.n) → (∀ u ∈ N ++ [w], s.ent u ≠ none ∧ s.ent u ≠ some g.n) →
    (∀ u ∈ s.chain, s.ent u = some g.n) → (∀ u ∈ s.chain, u < g.n) → VR g s oc m → m.pc = base g.n w + 23 →
    ∃ m', Rn g m m' ∧ m'.pc = base g.n w + 29 ∧ VR g (sExtract g.n w fuel s) oc m' ∧
      (∀ a, FreeC g s a → m'.mem a = m.mem a) := by
  intro N
  induction N with
  | nil =>
    intro tl s fuel oc m _ hf hs hnd hlt hent hch hchlt h hpc
    obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
    have hs' : s.stk = some w :: tl.map some := by simpa using hs
    have hwc : w ∉ s.chain := fun hm => by
      have := hch w hm
      exact (hent w (by simp)).2 this
    obtain ⟨m', R, hpc', hvr, hfr⟩ :=
      vm_extract_step (g := g) (s := s) (oc := oc) (m := m) (w := w) (y := w) (rest := tl.map some) h hw hw hwc
        (hent w (by simp)).1 hchlt hpc hs'
    have e : sExtract g.n w (k + 1) s = { s with stk := tl.map some, chain := s.chain ++ [w], set := fupd s.set w w, ent := fupd s.ent w (some g.n) } := by
      simp only [sExtract, hs', ↓reduceIte]
    rw [e]
    exact ⟨m', R, by simpa using hpc', hvr, hfr⟩
  | cons u0 N ih =>
    intro tl s fuel oc m hw0 hf hs hnd hlt hent hch hchlt h hpc
    obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    have hs' : s.stk = some u0 :: ((N ++ w :: tl).map some) := by simpa using hs
    have hne : u0 ≠ w := fun e => hw0 (by simp [e])
    have hwN : w ∉ N := fun hm => hw0 (List.mem_cons_of_mem _ hm)
    have hfk : N.length + 1 ≤ k := by simp at hf; omega
    have hu0 : u0 < g.n := hlt u0 (by simp)
    have hu0e := hent u0 (by simp)
    have hu0c : u0 ∉ s.chain := fun hm => hu0e.2 (hch u0 hm)
    obtain ⟨m1, R1, hpc1, hvr1, hfr1⟩ :=
      vm_extract_step (g := g) (s := s) (oc := oc) (m := m) (w := w) (y := u0) (rest := (N ++ w :: tl).map some) h hw hu0
        hu0c hu0e.1 hchlt hpc hs'
    have hpc1' : m1.pc = base g.n w + 23 := by rw [hpc1]; simp [hne]
    have hstep : sExtract g.n w (k + 1) s = sExtract g.n w k { s with stk := (N ++ w :: tl).map some, chain := s.chain ++ [u0], set := fupd s.set u0 w, ent := fupd s.ent u0 (some g.n) } := by
      simp only [sExtract, hs']
      simp [hne]
    rw [hstep]
    have hndu : u0 ∉ N ++ w :: tl := (List.nodup_cons.1 (by simpa using hnd)).1
    have hentN : ∀ u ∈ N ++ [w], u ≠ u0 := by
      intro u hu e
      subst e
      apply hndu
      rcases List.mem_append.1 hu with h1 | h1
      · exact List.mem_append_left _ h1
      · rw [List.mem_singleton] at h1; subst h1; simp
    obtain ⟨m2, R2, hpc2, hvr2, hfr2⟩ := ih tl
      { s with stk := (N ++ w :: tl).map some, chain := s.chain ++ [u0], set := fupd s.set u0 w, ent := fupd s.ent u0 (some g.n) } k oc m1 hwN hfk rfl (List.nodup_cons.1 (by simpa using hnd)).2
      (fun u hu => hlt u (List.mem_cons_of_mem _ hu))
      (fun u hu => by
        have := hentN u hu
        simp [fupd, this]
        exact hent u (List.mem_cons_of_mem _ hu))
      (fun u hu => by
        rcases List.mem_append.1 hu with hu | hu
        · have : u ≠ u0 := fun e => hu0c (e ▸ hu)
          simp [fupd, this]
          exact hch u hu
        · rw [List.mem_singleton] at hu; subst hu; simp [fupd])
      (fun u hu => by
        rcases List.mem_append.1 hu with hu | hu
        · exact hchlt u hu
        · rw [List.mem_singleton] at hu; subst hu; exact hu0)
      hvr1 hpc1'
    refine ⟨m2, R1.trans R2, hpc2, hvr2, fun a ha => ?_⟩
    rw [hfr2 a (ha.mono (fun x hx hn => by
      by_cases e : x = u0
      · subst e; simp [fupd] at hn
      · simp [fupd, e] at hn; exact hx hn)), hfr1 a ha]

/-- The return of a node (offsets 29 and 30): its lowlink is loaded and the return jump taken. -/
theorem vm_ret {g : Digraph} {s : SState} {oc : Nat} {m : VM} {w ra : Nat} (h : VR g s oc m) (hw : w < g.n)
    (hwe : s.ent w ≠ none) (hpc : m.pc = base g.n w + 29) (hj : m.mem (base g.n w + 30) = .jmp (.at ra)) :
    ∃ m', Rn g m m' ∧ m'.pc = ra ∧ m'.reg = ((s.low w : Nat) : Int) ∧ VR g s oc m' ∧ m'.mem = m.mem := by
  obtain ⟨k, hk⟩ : ∃ k, s.ent w = some k := by
    cases h' : s.ent w
    · exact absurd h' hwe
    · exact ⟨_, rfl⟩
  have f29 : m.mem (base g.n w + 29) = .data (s.low w : Nat) := by
    rw [h.fetch hw (by omega) (Or.inl ⟨by omega, by omega⟩)]; simp [blk, hk]
  obtain ⟨m1, R1, st1, mem1, pc1, reg1, stk1, sol1⟩ := eff_data (g := g) (m := m) h.st (by rw [hpc]; exact f29)
  have p1 : m1.pc = base g.n w + 30 := by rw [pc1, hpc]
  obtain ⟨m2, R2, st2, mem2, pc2, reg2, stk2, sol2⟩ :=
    eff_jmp (g := g) (m := m1) st1 (by rw [mem1, p1]; exact hj)
  refine ⟨m2, R1.trans R2, pc2, by rw [reg2, reg1], ?_, by rw [mem2, mem1]⟩
  exact ⟨st2, by rw [sol2, sol1, h.sol], by rw [stk2, stk1, h.stk], by rw [mem2, mem1]; exact h.mem, h.nodup⟩

/-- The exit of the successor loop (counter 0, offsets 10 and 11) lands at offset 20. -/
theorem vm_exit {g : Digraph} {s : SState} {oc : Nat} {m : VM} {w : Nat} (h : VR g s oc m) (hw : w < g.n)
    (hpc : m.pc = base g.n w + 10) (hcell : m.mem (base g.n w + 10) = .data 0) :
    ∃ m', Rn g m m' ∧ m'.pc = base g.n w + 20 ∧ VR g s oc m' ∧ m'.mem = m.mem := by
  have f11 : m.mem (base g.n w + 11) = .jc .regZ 9 := by
    rw [h.fetch_bp hw (by omega) (Or.inl ⟨by omega, by omega⟩) (by decide)]; rfl
  obtain ⟨m1, R1, st1, mem1, pc1, reg1, stk1, sol1⟩ := eff_data (g := g) (m := m) h.st (by rw [hpc]; exact hcell)
  have p1 : m1.pc = base g.n w + 11 := by rw [pc1, hpc]
  obtain ⟨m2, R2, st2, mem2, pc2, reg2, stk2, sol2⟩ :=
    eff_jc_true (g := g) (m := m1) st1 (by rw [mem1, p1]; exact f11) (by simp [Cnd.eval, reg1])
  refine ⟨m2, R1.trans R2, by omega, h.congr st2 (by rw [mem2, mem1]) (by rw [stk2, stk1]) (by rw [sol2, sol1]),
    by rw [mem2, mem1]⟩

theorem vm_push {g : Digraph} {s4 : SState} {oc : Nat} {m : VM} {w : Nat} (h : VR g s4 oc m) (hw : w < g.n)
    (hwe : s4.ent w ≠ none) (hpc : m.pc = base g.n w + 20) :
    ∃ m', Rn g m m' ∧ m'.pc = base g.n w + 22 ∧ VR g (leave5 w s4) oc m' ∧ m'.mem = m.mem := by
  obtain ⟨k, hk⟩ : ∃ k, s4.ent w = some k := by
    cases h' : s4.ent w
    · exact absurd h' hwe
    · exact ⟨_, rfl⟩
  have f20 : m.mem (base g.n w + 20) = .jc (.stkNe (s4.dep w)) 2 := by
    rw [h.fetch hw (by omega) (Or.inl ⟨by omega, by omega⟩)]; simp [blk, hk]
  have f21 : m.mem (base g.n w + 21) = .push (base g.n w + 16) := by
    rw [h.fetch_bp hw (by omega) (Or.inl ⟨by omega, by omega⟩) (by decide)]; rfl
  have hlen : m.stk.length = s4.stk.length := by rw [h.stk, List.length_map]
  by_cases hd : s4.stk.length = s4.dep w
  · obtain ⟨m1, R1, st1, mem1, pc1, reg1, stk1, sol1⟩ :=
      eff_jc_false (g := g) (m := m) h.st (by rw [hpc]; exact f20) (by simp [Cnd.eval, hlen, hd])
    have p1 : m1.pc = base g.n w + 21 := by rw [pc1, hpc]
    obtain ⟨m2, R2, st2, mem2, pc2, reg2, stk2, sol2⟩ :=
      eff_push (g := g) (m := m1) st1 (by rw [mem1, p1]; exact f21)
    have e : leave5 w s4 = { s4 with stk := some w :: s4.stk } := by unfold leave5; simp [hd]
    rw [e]
    refine ⟨m2, R1.trans R2, by rw [pc2, p1], ⟨st2, by rw [sol2, sol1, h.sol], ?_, ?_, h.nodup⟩, by rw [mem2, mem1]⟩
    · show m2.stk = (some w :: s4.stk).map (enc g.n oc)
      rw [stk2, stk1, h.stk]; rfl
    · rw [mem2, mem1]; exact h.mem
  · obtain ⟨m1, R1, st1, mem1, pc1, reg1, stk1, sol1⟩ :=
      eff_jc_true (g := g) (m := m) h.st (by rw [hpc]; exact f20) (by simp [Cnd.eval, hlen, hd, Ne.symm hd])
    have e : leave5 w s4 = s4 := by unfold leave5; simp [hd]
    rw [e]
    exact ⟨m1, R1, by omega, h.congr st1 mem1 stk1 sol1, mem1⟩

theorem vm_chk {g : Digraph} {s : SState} {oc : Nat} {m : VM} {w : Nat} (h : VR g s oc m) (hw : w < g.n)
    (hwe : s.ent w ≠ none) (hpc : m.pc = base g.n w + 22) :
    ∃ m', Rn g m m' ∧ m'.pc = (if s.chk w = true then base g.n w + 29 else base g.n w + 23) ∧ VR g s oc m' ∧
      m'.mem = m.mem := by
  obtain ⟨k, hk⟩ : ∃ k, s.ent w = some k := by
    cases h' : s.ent w
    · exact absurd h' hwe
    · exact ⟨_, rfl⟩
  have f22 : m.mem (base g.n w + 22) = (if s.chk w = true then .jc .tru 7 else .jc .fls 7) := by
    rw [h.fetch hw (by omega) (Or.inl ⟨by omega, by omega⟩)]; simp [blk, hk]
  by_cases hc : s.chk w = true
  · rw [if_pos hc] at f22
    obtain ⟨m1, R1, st1, mem1, pc1, reg1, stk1, sol1⟩ :=
      eff_jc_true (g := g) (m := m) h.st (by rw [hpc]; exact f22) (by simp [Cnd.eval])
    exact ⟨m1, R1, by rw [if_pos hc]; omega, h.congr st1 mem1 stk1 sol1, mem1⟩
  · rw [if_neg hc] at f22
    obtain ⟨m1, R1, st1, mem1, pc1, reg1, stk1, sol1⟩ :=
      eff_jc_false (g := g) (m := m) h.st (by rw [hpc]; exact f22) (by simp [Cnd.eval])
    exact ⟨m1, R1, by rw [if_neg hc]; omega, h.congr st1 mem1 stk1 sol1, mem1⟩

/-- The end of the block of `w` (offsets 10, 11, 20–30): push the own return cell, extract the component when no lowlink
was lowered, return the lowlink to the caller. -/
theorem vm_leave {g : Digraph} {s4 : SState} {oc : Nat} {m : VM} {w ra : Nat} {N tl : List Nat} (h : VR g s4 oc m)
    (hw : w < g.n) (hwe : s4.ent w ≠ none) (hpc : m.pc = base g.n w + 10) (hcell : m.mem (base g.n w + 10) = .data 0)
    (hj : m.mem (base g.n w + 30) = .jmp (.at ra))
    (hs5 : leave5 w s4 = { s4 with stk := (N ++ w :: tl).map some }) (hnd : (N ++ w :: tl).Nodup)
    (hlt : ∀ u ∈ N ++ [w], u < g.n) (hentu : ∀ u ∈ N ++ [w], s4.ent u ≠ none ∧ s4.ent u ≠ some g.n)
    (hch : ∀ u ∈ s4.chain, s4.ent u = some g.n) (hchlt : ∀ u ∈ s4.chain, u < g.n) :
    ∃ m', Rn g m m' ∧ m'.pc = ra ∧ m'.reg = (((sLeave g.n w s4).low w : Nat) : Int) ∧ VR g (sLeave g.n w s4) oc m' ∧
      (∀ a, FreeC g s4 a → m'.mem a = m.mem a) := by
  obtain ⟨m1, R1, hpc1, hvr1, hmem1⟩ := vm_exit h hw hpc hcell
  obtain ⟨m2, R2, hpc2, hvr2, hmem2⟩ := vm_push hvr1 hw hwe hpc1
  rw [hs5] at hvr2
  have hj2 : m2.mem (base g.n w + 30) = .jmp (.at ra) := by rw [hmem2, hmem1]; exact hj
  obtain ⟨m3, R3, hpc3, hvr3, hmem3⟩ := vm_chk hvr2 hw hwe hpc2
  have hj3 : m3.mem (base g.n w + 30) = .jmp (.at ra) := by rw [hmem3]; exact hj2
  have hchk : ({ s4 with stk := (N ++ w :: tl).map some } : SState).chk w = s4.chk w := rfl
  by_cases hc : s4.chk w = true
  · have e : sLeave g.n w s4 = { s4 with stk := (N ++ w :: tl).map some } := by
      rw [sLeave_def, hs5]; simp [hc]
    rw [e]
    have hpc3' : m3.pc = base g.n w + 29 := by rw [hpc3]; simp [hc]
    obtain ⟨m4, R4, hpc4, hreg4, hvr4, hmem4⟩ := vm_ret hvr3 hw hwe hpc3' hj3
    refine ⟨m4, R1.trans (R2.trans (R3.trans R4)), hpc4, hreg4, hvr4, fun a _ => ?_⟩
    rw [hmem4, hmem3, hmem2, hmem1]
  · have hwN : w ∉ N := fun hm => (List.nodup_append.1 hnd).2.2 w hm w List.mem_cons_self rfl
    have hlen : N.length + 1 ≤ (N ++ w :: tl).length := by simp
    have e : sLeave g.n w s4 = sExtract g.n w (N ++ w :: tl).length { s4 with stk := (N ++ w :: tl).map some } := by
      rw [sLeave_def, hs5]; simp [hc]
    have hpc3' : m3.pc = base g.n w + 23 := by rw [hpc3]; simp [hc]
    obtain ⟨m4, R4, hpc4, hvr4, hfr4⟩ := vm_extract hw N tl { s4 with stk := (N ++ w :: tl).map some }
      (N ++ w :: tl).length oc m3 hwN hlen rfl hnd hlt hentu hch hchlt hvr3 hpc3'
    obtain ⟨_, _, _, hentS, _⟩ := sExtract_spec g.n w N tl { s4 with stk := (N ++ w :: tl).map some }
      (N ++ w :: tl).length hwN hlen rfl
    have hwe' : (sExtract g.n w (N ++ w :: tl).length { s4 with stk := (N ++ w :: tl).map some }).ent w ≠ none := by
      rw [hentS w]; simp
    have hj4 : m4.mem (base g.n w + 30) = .jmp (.at ra) := by
      rw [hfr4 _ ⟨w, 30, hw, rfl, Or.inr rfl, hwe⟩]; exact hj3
    obtain ⟨m5, R5, hpc5, hreg5, hvr5, hmem5⟩ := vm_ret hvr4 hw hwe' hpc4 hj4
    rw [e]
    refine ⟨m5, R1.trans (R2.trans (R3.trans (R4.trans R5))), hpc5, hreg5, hvr5, fun a ha => ?_⟩
    rw [hmem5, hfr4 a ha, hmem3, hmem2, hmem1]

end SmcIrred.Vm
