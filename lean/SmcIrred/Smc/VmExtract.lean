module

public import SmcIrred.Smc.VmLoop

public section

namespace SmcIrred.Vm

theorem tailSlot_append (n : Nat) (ch : List Nat) (y : Nat) : tailSlot n (ch ++ [y]) = base n y + 35 := by
  simp [tailSlot]

theorem headT_append (n : Nat) (ch : List Nat) (y : Nat) :
    headT n (ch ++ [y]) = if ch = [] then Tgt.at (base n y + 31) else headT n ch := by
  cases ch <;> simp [headT]

theorem tailSlot_cases (n : Nat) (ch : List Nat) :
    (ch = [] ∧ tailSlot n ch = n + 2) ∨ ∃ u, ch.getLast? = some u ∧ tailSlot n ch = base n u + 35 := by
  cases h : ch.getLast? with
  | none =>
    left
    have : ch = [] := by simpa using h
    exact ⟨this, by simp [tailSlot, h]⟩
  | some u => right; exact ⟨u, rfl, by simp [tailSlot, h]⟩

theorem mem_of_getLast {ch : List Nat} {u : Nat} (h : ch.getLast? = some u) : u ∈ ch := by
  obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.1 h
  rw [hys]; simp

theorem lnk_append (n y : Nat) : ∀ (ch : List Nat), (ch ++ [y]).Nodup → ∀ x,
    lnk n (ch ++ [y]) x = if ch.getLast? = some x then Tgt.at (base n y + 31) else lnk n ch x := by
  intro ch
  induction ch with
  | nil => intro _ x; simp [lnk]
  | cons a rest ih =>
    intro hnd x
    cases rest with
    | nil =>
      by_cases hx : x = a
      · subst hx; simp [lnk]
      · simp [lnk, hx, Ne.symm hx]
    | cons b t =>
      have hnd' : (b :: t ++ [y]).Nodup := (List.nodup_cons.1 hnd).2
      have ih' := ih hnd' x
      have hl : (a :: b :: t).getLast? = (b :: t).getLast? := List.getLast?_cons_cons
      have e1 : lnk n ((a :: b :: t) ++ [y]) x = if x = a then Tgt.at (base n b + 31) else lnk n (b :: t ++ [y]) x := by
        simp only [List.cons_append]
        rfl
      have e2 : lnk n (a :: b :: t) x = if x = a then Tgt.at (base n b + 31) else lnk n (b :: t) x := rfl
      rw [e1, hl, e2]
      by_cases hx : x = a
      · subst hx
        have hne : (b :: t).getLast? ≠ some x := by
          intro hh
          have hm := mem_of_getLast hh
          have : x ∉ b :: t ++ [y] := (List.nodup_cons.1 hnd).1
          exact this (List.mem_append_left _ hm)
        simp [hne]
      · simp only [hx, if_false]
        exact ih'

theorem lnk_nil (n x : Nat) : lnk n [] x = Tgt.sat := rfl

/-- The image of the state after one extraction step, at every cell, given the cells the VM wrote. -/
theorem extract_mem {g : Digraph} {s : SState} {w y T : Nat} (mem mem' : Nat → Ins) (hw : w < g.n) (hy : y < g.n)
    (hyc : y ∉ s.chain) (hye : s.ent y ≠ none) (hlt : ∀ u ∈ s.chain, u < g.n) (hnodup : (s.chain ++ [y]).Nodup)
    (hT : (s.chain = [] ∧ T = g.n + 2) ∨ ∃ u, s.chain.getLast? = some u ∧ T = base g.n u + 35)
    (hmem : ∀ a, mem a = img g s a ∨ FreeC g s a)
    (hM_T : mem' T = .jmp (.at (base g.n y + 31))) (hM_31 : mem' (base g.n y + 31) = .data ((base g.n w : Nat) : Int))
    (hM_n1 : mem' (g.n + 1) = .data (((base g.n y + 16 : Nat) : Int) + 19))
    (hM_0 : mem' (base g.n y) = .data ((g.n : Nat) : Int))
    (hother : ∀ a, a ≠ T → a ≠ base g.n y + 31 → a ≠ g.n + 1 → a ≠ base g.n y → mem' a = mem a) :
    ∀ a, mem' a = img g { s with chain := s.chain ++ [y], set := fupd s.set y w, ent := fupd s.ent y (some g.n) } a ∨
      FreeC g { s with chain := s.chain ++ [y], set := fupd s.set y w, ent := fupd s.ent y (some g.n) } a := by
  intro a
  by_cases aT : a = T
  · left; subst aT
    rw [hM_T]
    rcases hT with ⟨hch, hT⟩ | ⟨u, hu, hT⟩
    · rw [hT, img_n2]
      show Ins.jmp _ = Ins.jmp (headT g.n (s.chain ++ [y]))
      rw [headT_append, if_pos hch]
    · rw [hT, img_blk g _ (hlt u (mem_of_getLast hu)) (by decide : 35 < 36)]
      simp only [blk]
      simp only [show (35 = 0) = False by decide, show (35 = 1) = False by decide, show (35 = 5) = False by decide,
        show (35 = 13) = False by decide, show (35 = 20) = False by decide, show (35 = 22) = False by decide,
        show (35 = 29) = False by decide, show (35 = 31) = False by decide, if_false, if_true, or_self]
      show Ins.jmp _ = Ins.jmp (lnk g.n (s.chain ++ [y]) u)
      rw [lnk_append g.n y s.chain hnodup u]
      simp [hu]
  by_cases a31 : a = base g.n y + 31
  · left; subst a31
    rw [hM_31, img_blk g _ hy (by decide : 31 < 36)]
    have hwn : ¬ w = g.n := by omega
    simp [blk, fupd, hwn]
  by_cases a1 : a = g.n + 1
  · left; subst a1
    rw [hM_n1, img_n1]
    show Ins.data _ = Ins.data ((tailSlot g.n (s.chain ++ [y]) : Nat) : Int)
    rw [tailSlot_append]
    congr 1
  by_cases a0 : a = base g.n y
  · left; subst a0
    have := img_blk g ({ s with chain := s.chain ++ [y], set := fupd s.set y w, ent := fupd s.ent y (some g.n) } :
      SState) hy (by decide : 0 < 36)
    rw [Nat.add_zero] at this
    rw [hM_0, this]
    simp [blk, fupd]
  rw [hother a aT a31 a1 a0]
  rcases hmem a with hi | hf
  · left; rw [hi]
    apply img_congr
    · intro _; rfl
    · intro ha1; exact absurd ha1 a1
    · intro ha2
      have hne : s.chain ≠ [] := by
        intro hnil
        rcases hT with ⟨_, hT⟩ | ⟨u, hu, hT⟩
        · exact aT (by rw [ha2, hT])
        · simp [hnil] at hu
      show headT g.n s.chain = headT g.n (s.chain ++ [y])
      rw [headT_append, if_neg hne]
    · intro x i hx hi' hxa
      by_cases hxy : x = y
      · subst hxy
        obtain ⟨k, hk⟩ : ∃ k, s.ent x = some k := by
          cases h' : s.ent x
          · exact absurd h' hye
          · exact ⟨_, rfl⟩
        have h0 : i ≠ 0 := by intro hh; subst hh; exact a0 (by rw [hxa, Nat.add_zero])
        have h31 : i ≠ 31 := by intro hh; subst hh; exact a31 (by rw [hxa])
        have hl : lnk g.n s.chain x = lnk g.n (s.chain ++ [x]) x := by
          rw [lnk_append g.n x s.chain hnodup x]
          have : s.chain.getLast? ≠ some x := fun hh => hyc (mem_of_getLast hh)
          simp [this]
        unfold blk
        by_cases h35 : i = 35
        · subst h35
          simp [hk, fupd]
          exact hl
        · simp [hk, fupd, h0, h31, h35]
      · apply blk_congr_fields
        · simp [fupd, hxy]
        · rfl
        · rfl
        · rfl
        · rfl
        · simp [fupd, hxy]
        · intro h35
          show lnk g.n s.chain x = lnk g.n (s.chain ++ [y]) x
          rw [lnk_append g.n y s.chain hnodup x]
          have : s.chain.getLast? ≠ some x := by
            intro hh
            rcases hT with ⟨hnil, _⟩ | ⟨u, hu, hT⟩
            · simp [hnil] at hh
            · rw [hu] at hh
              have hux : u = x := Option.some.inj hh
              exact aT (by rw [hxa, h35, ← hux, hT])
          simp [this]
  · right
    exact hf.mono (fun x hx hn => by
      by_cases e : x = y
      · subst e; simp [fupd] at hn
      · simp [fupd, e] at hn; exact hx hn)

/-- Steps 23–27 of one extraction round: the cell is popped, the chain link, the set cell, the tail pointer and the finished
marker are written. -/
theorem extract_exec {g : Digraph} {s : SState} {oc : Nat} {m : VM} {w y T : Nat} {rest : List (Option Nat)}
    (h : VR g s oc m) (hw : w < g.n) (hy : y < g.n) (hpc : m.pc = base g.n w + 23) (hstk : s.stk = some y :: rest)
    (hn1 : m.mem (g.n + 1) = .data (T : Nat)) (hT1 : T ≠ base g.n y + 31) (hT2 : T ≠ base g.n y) (hT3 : T ≠ g.n + 1)
    (hT5 : T ≠ base g.n w + 25) (hT6 : T ≠ base g.n w + 26) (hT7 : T ≠ base g.n w + 27) (hT8 : T ≠ base g.n w + 28)
    (hbw : base g.n w = g.n + 3 + 36 * w) (hby : base g.n y = g.n + 3 + 36 * y) :
    ∃ m5, Rn g m m5 ∧ m5.st = .run ∧ m5.pc = base g.n w + 28 ∧ m5.reg = ((base g.n y + 16 : Nat) : Int) ∧
      m5.stk = rest.map (enc g.n oc) ∧ m5.sol = m.sol ∧
      m5.mem = memUpd (memUpd (memUpd (memUpd m.mem T (.jmp (.at (base g.n y + 31)))) (base g.n y + 31)
        (.data ((base g.n w : Nat) : Int))) (g.n + 1) (.data (((base g.n y + 16 : Nat) : Int) + 19)))
        (base g.n y) (.data ((g.n : Nat) : Int)) := by
  have hmstk : m.stk = (base g.n y + 16) :: rest.map (enc g.n oc) := by rw [h.stk, hstk]; rfl
  have f23 : m.mem (base g.n w + 23) = .pop := by
    rw [h.fetch_bp hw (by omega) (Or.inl ⟨by omega, by omega⟩) (by decide)]; rfl
  have f24 : m.mem (base g.n w + 24) = .modinst (.jmpRegPlus 15) (.deref (g.n + 1)) := by
    rw [h.fetch_bp hw (by omega) (Or.inl ⟨by omega, by omega⟩) (by decide)]; rfl
  have f25 : m.mem (base g.n w + 25) = .store (.k (base g.n w : Nat)) (.rp 15) := by
    rw [h.fetch_bp hw (by omega) (Or.inl ⟨by omega, by omega⟩) (by decide)]; rfl
  have f26 : m.mem (base g.n w + 26) = .store (.rp 19) (.k (g.n + 1)) := by
    rw [h.fetch_bp hw (by omega) (Or.inl ⟨by omega, by omega⟩) (by decide)]; rfl
  have f27 : m.mem (base g.n w + 27) = .store (.k (g.n : Nat)) (.rp (-16)) := by
    rw [h.fetch_bp hw (by omega) (Or.inl ⟨by omega, by omega⟩) (by decide)]; rfl
  have hd31 : ∃ v, m.mem (base g.n y + 31) = .data v := by
    rw [h.fetch hy (by omega) (Or.inl ⟨by omega, by omega⟩)]
    unfold blk
    by_cases hs : s.set y = g.n <;> simp [hs]
  have hd0 : ∃ v, m.mem (base g.n y) = .data v := by
    have := h.fetch hy (i := 0) (by omega) (Or.inl ⟨by omega, by omega⟩)
    rw [Nat.add_zero] at this
    rw [this]
    unfold blk
    cases s.ent y <;> simp
  obtain ⟨v31, hv31⟩ := hd31
  obtain ⟨v0, hv0⟩ := hd0
  obtain ⟨m1, R1, st1, mem1, pc1, reg1, stk1, sol1⟩ := eff_pop (g := g) (m := m) h.st (by rw [hpc]; exact f23) hmstk
  have p1 : m1.pc = base g.n w + 24 := by rw [pc1, hpc]
  obtain ⟨m2, R2, st2, mem2, pc2, reg2, stk2, sol2⟩ :=
    eff_modinst (g := g) (m := m1) st1 (by rw [mem1, p1]; exact f24) (a := T)
      (by simp [MAddr.eval, dataAt, mem1, hn1])
  have hj : Mk.build m1 (.jmpRegPlus 15) = .jmp (.at (base g.n y + 31)) := by
    have : ((base g.n y + 16 : Nat) + 15 : Int).toNat = base g.n y + 31 := by omega
    simp only [Mk.build, reg1, this]
  rw [hj, mem1] at mem2
  have p2 : m2.pc = base g.n w + 25 := by rw [pc2, p1]
  have hr2 : m2.reg = ((base g.n y + 16 : Nat) : Int) := by rw [reg2, reg1]
  have e3 : Dst.eval m2.reg (.rp 15) = base g.n y + 31 := by simp [Dst.eval, hr2]; omega
  obtain ⟨m3, R3, st3, mem3, pc3, reg3, stk3, sol3⟩ :=
    eff_store (g := g) (m := m2) st2
      (by rw [mem2, p2, memUpd_ne _ _ (Ne.symm hT5)]; exact f25)
      (v := v31)
      (by rw [e3, mem2, memUpd_ne _ _ (Ne.symm hT1)]; exact hv31)
  simp only [e3, Src.eval, mem2] at mem3
  have p3 : m3.pc = base g.n w + 26 := by rw [pc3, p2]
  have hr3 : m3.reg = ((base g.n y + 16 : Nat) : Int) := by rw [reg3, hr2]
  obtain ⟨m4, R4, st4, mem4, pc4, reg4, stk4, sol4⟩ :=
    eff_store (g := g) (m := m3) st3
      (by rw [mem3, p3, memUpd_ne _ _ (by omega : base g.n w + 26 ≠ base g.n y + 31), memUpd_ne _ _ (Ne.symm hT6)]
          exact f26)
      (v := (T : Nat))
      (by
        simp only [Dst.eval]
        rw [mem3, memUpd_ne _ _ (by omega : g.n + 1 ≠ base g.n y + 31), memUpd_ne _ _ (Ne.symm hT3)]
        exact hn1)
  simp only [Dst.eval, Src.eval, mem3, hr3] at mem4
  have p4 : m4.pc = base g.n w + 27 := by rw [pc4, p3]
  have hr4 : m4.reg = ((base g.n y + 16 : Nat) : Int) := by rw [reg4, hr3]
  have e5 : Dst.eval m4.reg (.rp (-16)) = base g.n y := by simp only [Dst.eval, hr4]; omega
  obtain ⟨m5, R5, st5, mem5, pc5, reg5, stk5, sol5⟩ :=
    eff_store (g := g) (m := m4) st4
      (by rw [mem4, p4, memUpd_ne _ _ (by omega : base g.n w + 27 ≠ g.n + 1),
        memUpd_ne _ _ (by omega : base g.n w + 27 ≠ base g.n y + 31), memUpd_ne _ _ (Ne.symm hT7)]; exact f27)
      (v := v0)
      (by
        rw [e5, mem4, memUpd_ne _ _ (by omega : base g.n y ≠ g.n + 1),
          memUpd_ne _ _ (by omega : base g.n y ≠ base g.n y + 31), memUpd_ne _ _ (Ne.symm hT2)]
        exact hv0)
  simp only [e5, Src.eval, mem4] at mem5
  refine ⟨m5, R1.trans (R2.trans (R3.trans (R4.trans R5))), st5, by rw [pc5, p4], by rw [reg5, hr4], ?_,
    by rw [sol5, sol4, sol3, sol2, sol1], mem5⟩
  rw [stk5, stk4, stk3, stk2, stk1]

/-- Popping one cell of the component: the cell of `y` joins the topological chain (the jump slot at the chain's end is
patched to the set cell of `y`), `y` gets the component `w` and the finished marker. -/
theorem vm_extract_step {g : Digraph} {s : SState} {oc : Nat} {m : VM} {w y : Nat} {rest : List (Option Nat)}
    (h : VR g s oc m) (hw : w < g.n) (hy : y < g.n) (hyc : y ∉ s.chain) (hye : s.ent y ≠ none)
    (hlt : ∀ u ∈ s.chain, u < g.n) (hpc : m.pc = base g.n w + 23) (hstk : s.stk = some y :: rest) :
    ∃ m', Rn g m m' ∧ m'.pc = (if y = w then base g.n w + 29 else base g.n w + 23) ∧
      VR g { s with stk := rest, chain := s.chain ++ [y], set := fupd s.set y w, ent := fupd s.ent y (some g.n) } oc m' ∧
      (∀ a, FreeC g s a → m'.mem a = m.mem a) := by
  have hbw := base_eq g.n w
  have hby := base_eq g.n y
  have hn1 : m.mem (g.n + 1) = .data (tailSlot g.n s.chain : Nat) := h.mem_n1
  obtain ⟨T, hTdef⟩ : ∃ T, T = tailSlot g.n s.chain := ⟨_, rfl⟩
  rw [← hTdef] at hn1
  have hT : (s.chain = [] ∧ T = g.n + 2) ∨ ∃ u, s.chain.getLast? = some u ∧ T = base g.n u + 35 := by
    rw [hTdef]; exact tailSlot_cases g.n s.chain
  have hTne : T ≠ base g.n y + 31 ∧ T ≠ base g.n y ∧ T ≠ g.n + 1 ∧ T ≠ base g.n w + 25 ∧ T ≠ base g.n w + 26 ∧
      T ≠ base g.n w + 27 ∧ T ≠ base g.n w + 28 ∧ T ≠ base g.n w + 29 := by
    rcases hT with ⟨_, hT⟩ | ⟨u, _, hT⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
    · have hbu := base_eq g.n u
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
  obtain ⟨hT1, hT2, hT3, hT5, hT6, hT7, hT8, hT9⟩ := hTne
  obtain ⟨m5, R5, st5, pc5, reg5, stk5, sol5, mem5⟩ :=
    extract_exec h hw hy hpc hstk hn1 hT1 hT2 hT3 hT5 hT6 hT7 hT8 hbw hby
  have f28 : m5.mem (base g.n w + 28) = .jc (.regNe (base g.n w + 16)) (-5) := by
    rw [mem5, memUpd_ne _ _ (by omega : base g.n w + 28 ≠ base g.n y),
      memUpd_ne _ _ (by omega : base g.n w + 28 ≠ g.n + 1),
      memUpd_ne _ _ (by omega : base g.n w + 28 ≠ base g.n y + 31), memUpd_ne _ _ (Ne.symm hT8)]
    rw [h.fetch_bp hw (by omega) (Or.inl ⟨by omega, by omega⟩) (by decide)]; rfl
  obtain ⟨m6, R6, st6, mem6, pc6, reg6, stk6, sol6⟩ : ∃ m6, Rn g m5 m6 ∧ m6.st = .run ∧ m6.mem = m5.mem ∧
      m6.pc = (if y = w then base g.n w + 29 else base g.n w + 23) ∧ m6.reg = m5.reg ∧ m6.stk = m5.stk ∧
      m6.sol = m5.sol := by
    have hm28 : m5.mem m5.pc = .jc (.regNe (base g.n w + 16)) (-5) := by rw [pc5]; exact f28
    by_cases hyw : y = w
    · subst hyw
      obtain ⟨m6, R6, st6, mem6, pc6, reg6, stk6, sol6⟩ :=
        eff_jc_false (g := g) (m := m5) st5 hm28 (by simp [Cnd.eval, reg5])
      exact ⟨m6, R6, st6, mem6, by rw [pc6, pc5]; simp, reg6, stk6, sol6⟩
    · obtain ⟨m6, R6, st6, mem6, pc6, reg6, stk6, sol6⟩ :=
        eff_jc_true (g := g) (m := m5) st5 hm28
          (by
            have : base g.n w + 16 ≠ base g.n y + 16 := by omega
            simp [Cnd.eval, reg5]; omega)
      exact ⟨m6, R6, st6, mem6, by rw [pc6, pc5]; simp [hyw]; omega, reg6, stk6, sol6⟩
  have hnodup : (s.chain ++ [y]).Nodup := by
    rw [List.nodup_append]
    exact ⟨h.nodup, List.nodup_cons.2 ⟨by simp, List.nodup_nil⟩, fun a ha b hb hab => by
      have hb' : b = y := by simpa using hb
      exact hyc (hb' ▸ hab ▸ ha)⟩
  have hM_T : m6.mem T = .jmp (.at (base g.n y + 31)) := by
    rw [mem6, mem5, memUpd_ne _ _ hT2, memUpd_ne _ _ hT3, memUpd_ne _ _ hT1, memUpd_same]
  have hM_31 : m6.mem (base g.n y + 31) = .data ((base g.n w : Nat) : Int) := by
    rw [mem6, mem5, memUpd_ne _ _ (by omega : base g.n y + 31 ≠ base g.n y),
      memUpd_ne _ _ (by omega : base g.n y + 31 ≠ g.n + 1), memUpd_same]
  have hM_n1 : m6.mem (g.n + 1) = .data (((base g.n y + 16 : Nat) : Int) + 19) := by
    rw [mem6, mem5, memUpd_ne _ _ (by omega : g.n + 1 ≠ base g.n y), memUpd_same]
  have hM_0 : m6.mem (base g.n y) = .data ((g.n : Nat) : Int) := by
    rw [mem6, mem5, memUpd_same]
  have hother : ∀ a, a ≠ T → a ≠ base g.n y + 31 → a ≠ g.n + 1 → a ≠ base g.n y → m6.mem a = m.mem a := by
    intro a n1 n2 n3 n4
    rw [mem6, mem5, memUpd_ne _ _ n4, memUpd_ne _ _ n3, memUpd_ne _ _ n2, memUpd_ne _ _ n1]
  refine ⟨m6, R5.trans R6, pc6, ⟨st6, ?_, ?_, ?_, hnodup⟩, ?_⟩
  · rw [sol6, sol5, h.sol]
  · show m6.stk = rest.map (enc g.n oc)
    rw [stk6, stk5]
  · exact extract_mem m.mem m6.mem hw hy hyc hye hlt hnodup hT h.mem hM_T hM_31 hM_n1 hM_0 hother
  · intro a ha
    obtain ⟨x, i, hx, e, hi, hne⟩ := ha
    have hbx := base_eq g.n x
    rcases hT with ⟨_, hT⟩ | ⟨u, _, hT⟩
    · apply hother <;> omega
    · have hbu := base_eq g.n u
      apply hother <;> omega

end SmcIrred.Vm
