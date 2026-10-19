module

public import SmcIrred.Smc.VmSim

public section

namespace SmcIrred

open Vm

theorem fetch_of_mem {g : Digraph} {s : SState} {m : VM} (hmem : ∀ a, m.mem a = img g s a ∨ FreeC g s a) {x i : Nat}
    (hx : x < g.n) (hi : i < 36) (hf : (i ≠ 10 ∧ i ≠ 30) ∨ s.ent x = none) :
    m.mem (base g.n x + i) = blk g s x i := by
  rcases hmem (base g.n x + i) with h1 | ⟨x', i', hx', e, hi', hne⟩
  · rw [h1, img_blk g s hx hi]
  · exfalso
    have hxi : x' = x ∧ i' = i := by unfold base at e; omega
    obtain ⟨rfl, rfl⟩ := hxi
    rcases hf with ⟨a1, a2⟩ | hn
    · omega
    · exact hne hn

theorem lnk_cons_ne (n a x : Nat) (l : List Nat) (hx : x ≠ a) : lnk n (a :: l) x = lnk n l x := by
  cases l with
  | nil => simp [lnk]
  | cons b t => simp [lnk, hx]

theorem lnk_mid (n x y : Nat) : ∀ (pre post : List Nat), (pre ++ x :: y :: post).Nodup →
    lnk n (pre ++ x :: y :: post) x = .at (base n y + 31) := by
  intro pre
  induction pre with
  | nil => intro post _; simp [lnk]
  | cons a pre ih =>
    intro post hnd
    have hxa : x ≠ a := by
      intro e
      subst e
      have := (List.nodup_cons.1 hnd).1
      exact this (by simp)
    rw [List.cons_append, lnk_cons_ne _ _ _ _ hxa]
    exact ih post (List.nodup_cons.1 hnd).2

theorem lnk_last (n x : Nat) : ∀ (pre : List Nat), (pre ++ [x]).Nodup → lnk n (pre ++ [x]) x = .sat := by
  intro pre
  induction pre with
  | nil => intro _; simp [lnk]
  | cons a pre ih =>
    intro hnd
    have hxa : x ≠ a := by
      intro e
      subst e
      have := (List.nodup_cons.1 hnd).1
      exact this (by simp)
    rw [List.cons_append, lnk_cons_ne _ _ _ _ hxa]
    exact ih (List.nodup_cons.1 hnd).2

theorem walk_step {g : Digraph} (hneg : ∀ x, x < g.n → nneg x < g.n) {s : SState} {x : Nat} (hxn : x < g.n)
    (hsx : s.set x ≠ g.n) {m : VM} (hst : m.st = .run) (hmem : ∀ a, m.mem a = img g s a ∨ FreeC g s a)
    (hpc : m.pc = base g.n x + 31) :
    (s.set x = s.set (nneg x) → ∃ m', Rn g m m' ∧ m'.st = .unsat ∧ m'.mem = m.mem) ∧
    (s.set x ≠ s.set (nneg x) → ∃ m', Rn g m m' ∧ m'.st = .run ∧ m'.mem = m.mem ∧ m'.pc = base g.n x + 35 ∧
      m'.sol = (if nneg x ∈ m.sol then m.sol else x :: m.sol)) := by
  have hnx : nneg x < g.n := hneg x hxn
  have f31 : m.mem (base g.n x + 31) = .data ((base g.n (s.set x) : Nat) : Int) := by
    rw [fetch_of_mem hmem hxn (by omega) (Or.inl ⟨by omega, by omega⟩)]
    simp [blk, hsx]
  have f32 : m.mem (base g.n x + 32) = .jc (.regNeSet x) 2 := by
    rw [fetch_of_mem hmem hxn (by omega) (Or.inl ⟨by omega, by omega⟩), blk_other s (by decide)]; rfl
  have f33 : m.mem (base g.n x + 33) = .jmp .unsat := by
    rw [fetch_of_mem hmem hxn (by omega) (Or.inl ⟨by omega, by omega⟩), blk_other s (by decide)]; rfl
  have f34 : m.mem (base g.n x + 34) = .func x := by
    rw [fetch_of_mem hmem hxn (by omega) (Or.inl ⟨by omega, by omega⟩), blk_other s (by decide)]; rfl
  have fN : m.mem (base g.n (nneg x) + 31) =
      (if s.set (nneg x) = g.n then .data (-1) else .data ((base g.n (s.set (nneg x)) : Nat) : Int)) := by
    rw [fetch_of_mem hmem hnx (by omega) (Or.inl ⟨by omega, by omega⟩)]
    simp [blk]
  obtain ⟨m1, R1, st1, mem1, pc1, reg1, stk1, sol1⟩ := eff_data (g := g) (m := m) hst (by rw [hpc]; exact f31)
  have p1 : m1.pc = base g.n x + 32 := by omega
  constructor
  · intro hq
    have hsn : s.set (nneg x) ≠ g.n := by rw [← hq]; exact hsx
    have hev : (Cnd.regNeSet x).eval g m1 = some false := by
      simp only [Cnd.eval, dataAt, mem1, fN, if_neg hsn, reg1, Option.map]
      simp [hq]
    obtain ⟨m2, R2, st2, mem2, pc2, reg2, stk2, sol2⟩ :=
      eff_jc_false (g := g) (m := m1) st1 (by rw [mem1, p1]; exact f32) hev
    have p2 : m2.pc = base g.n x + 33 := by omega
    have hj : m2.mem m2.pc = .jmp .unsat := by rw [mem2, mem1, p2]; exact f33
    exact ⟨_, R1.trans (R2.trans (Rn.of_step (step_unsat st2 hj))), rfl, by simp [step_unsat st2 hj, mem2, mem1]⟩
  · intro hq
    have hev : (Cnd.regNeSet x).eval g m1 = some true := by
      simp only [Cnd.eval, dataAt, mem1, fN, reg1, Option.map]
      by_cases hsn : s.set (nneg x) = g.n
      · have hne : ((base g.n (s.set x) : Nat) : Int) ≠ -1 := by
          simp only [base_eq]
          omega
        simp only [hsn, if_true]
        simp [hne]
      · simp only [if_neg hsn]
        simp only [base_eq]
        simp
        omega
    obtain ⟨m2, R2, st2, mem2, pc2, reg2, stk2, sol2⟩ :=
      eff_jc_true (g := g) (m := m1) st1 (by rw [mem1, p1]; exact f32) hev
    have p2 : m2.pc = base g.n x + 34 := by omega
    obtain ⟨m3, R3, st3, mem3, pc3, reg3, stk3, sol3⟩ :=
      eff_func (g := g) (m := m2) st2 (by rw [mem2, mem1, p2]; exact f34)
    refine ⟨m3, R1.trans (R2.trans R3), st3, by rw [mem3, mem2, mem1], by omega, ?_⟩
    rw [sol3, sol2, sol1]

/-- The solution phase: walk the chain from a node, comparing the component of the node with the one of its negation. -/
theorem vm_walk {g : Digraph} (hneg : ∀ x, x < g.n → nneg x < g.n) {s : SState} (hnd : s.chain.Nodup)
    (hlt : ∀ u ∈ s.chain, u < g.n) (hset : ∀ u ∈ s.chain, s.set u ≠ g.n) :
    ∀ (xs pre : List Nat) (x : Nat) (m : VM) (sol : List Nat), s.chain = pre ++ x :: xs → m.st = .run →
      (∀ a, m.mem a = img g s a ∨ FreeC g s a) → m.pc = base g.n x + 31 → m.sol = sol →
      ∃ m', Rn g m m' ∧ (sSolFold s.set (x :: xs) sol = none → m'.st = .unsat) ∧
        (∀ r, sSolFold s.set (x :: xs) sol = some r → m'.st = .sat ∧ m'.sol = r) ∧ m'.mem = m.mem := by
  intro xs
  induction xs with
  | nil =>
    intro pre x m sol hc hst hmem hpc hsol
    have hx : x ∈ s.chain := by rw [hc]; simp
    have hxn := hlt x hx
    obtain ⟨hA, hB⟩ := walk_step hneg hxn (hset x hx) hst hmem hpc
    by_cases hq : s.set x = s.set (nneg x)
    · obtain ⟨m', R, st, mm⟩ := hA hq
      refine ⟨m', R, fun _ => st, ?_, mm⟩
      intro r hr
      simp [sSolFold, hq] at hr
    · obtain ⟨m3, R3, st3, mem3, pc3, sol3⟩ := hB hq
      have f35 : m3.mem (base g.n x + 35) = .jmp .sat := by
        rw [mem3, fetch_of_mem hmem hxn (by omega) (Or.inl ⟨by omega, by omega⟩)]
        simp only [blk]
        simp only [show ¬ (35 = 0) from by omega, show ¬ (35 = 1) from by omega, show ¬ (35 = 5) from by omega,
          show ¬ (35 = 13 ∨ 35 = 20) from by omega, show ¬ (35 = 22) from by omega, show ¬ (35 = 29) from by omega,
          show ¬ (35 = 31) from by omega, if_false, if_true]
        rw [hc]
        rw [lnk_last g.n x pre (by rw [← hc]; exact hnd)]
      have hj : m3.mem m3.pc = .jmp .sat := by rw [pc3]; exact f35
      refine ⟨_, R3.trans (Rn.of_step (step_sat st3 hj)), fun h => by simp [sSolFold, hq] at h, ?_, ?_⟩
      · intro r hr
        simp only [sSolFold, hq, if_false] at hr
        simp only [sSolFold, Option.some.injEq] at hr
        refine ⟨rfl, ?_⟩
        show m3.sol = r
        rw [sol3, hsol, hr]
      · show m3.mem = m.mem
        exact mem3
  | cons y xs ih =>
    intro pre x m sol hc hst hmem hpc hsol
    have hx : x ∈ s.chain := by rw [hc]; simp
    have hxn := hlt x hx
    obtain ⟨hA, hB⟩ := walk_step hneg hxn (hset x hx) hst hmem hpc
    by_cases hq : s.set x = s.set (nneg x)
    · obtain ⟨m', R, st, mm⟩ := hA hq
      refine ⟨m', R, fun _ => st, ?_, mm⟩
      intro r hr
      simp [sSolFold, hq] at hr
    · obtain ⟨m3, R3, st3, mem3, pc3, sol3⟩ := hB hq
      have f35 : m3.mem (base g.n x + 35) = .jmp (.at (base g.n y + 31)) := by
        rw [mem3, fetch_of_mem hmem hxn (by omega) (Or.inl ⟨by omega, by omega⟩)]
        simp only [blk]
        simp only [show ¬ (35 = 0) from by omega, show ¬ (35 = 1) from by omega, show ¬ (35 = 5) from by omega,
          show ¬ (35 = 13 ∨ 35 = 20) from by omega, show ¬ (35 = 22) from by omega, show ¬ (35 = 29) from by omega,
          show ¬ (35 = 31) from by omega, if_false, if_true]
        rw [hc]
        rw [lnk_mid g.n x y pre xs (by rw [← hc]; exact hnd)]
      have hj : m3.mem m3.pc = .jmp (.at (base g.n y + 31)) := by rw [pc3]; exact f35
      obtain ⟨m4, R4, st4, mem4, pc4, reg4, stk4, sol4⟩ := eff_jmp (g := g) (m := m3) st3 hj
      have hc' : s.chain = (pre ++ [x]) ++ y :: xs := by rw [hc]; simp
      obtain ⟨m5, R5, hu, hs, mm5⟩ := ih (pre ++ [x]) y m4 (if nneg x ∈ sol then sol else x :: sol) hc' st4
        (fun a => by rw [mem4, mem3]; exact hmem a) pc4 (by rw [sol4, sol3, hsol])
      refine ⟨m5, R3.trans (R4.trans R5), ?_, ?_, ?_⟩
      · intro h
        apply hu
        simpa [sSolFold, hq] using h
      · intro r hr
        apply hs
        simpa [sSolFold, hq] using hr
      · rw [mm5, mem4, mem3]


theorem Vm.VR.oc {g : Digraph} {s : SState} {oc : Nat} {m : VM} (h : VR g s oc m) (hs : ∀ c ∈ s.stk, c ≠ none) (oc' : Nat) :
    VR g s oc' m := by
  refine ⟨h.st, h.sol, ?_, h.mem, h.nodup⟩
  rw [h.stk]
  apply List.map_congr_left
  intro c hc
  cases c with
  | none => exact absurd rfl (hs _ hc)
  | some x => rfl

theorem Vm.VR.mem_call {g : Digraph} {s : SState} {oc : Nat} {m : VM} (h : VR g s oc m) {a : Nat} (h1 : 1 ≤ a)
    (h2 : a ≤ g.n) : m.mem a = .call (base g.n (a - 1)) := by
  rcases h.mem a with h3 | ⟨x, i, hx, e, hi, hne⟩
  · rw [h3, img_call g s h1 h2]
  · exfalso; unfold base at e; omega

/-- The outer call of the node `v` (the `v+1`-st cell): the return cell `none` is pushed, the block of `v` is entered. -/
theorem vm_call_top {g : Digraph} {s : SState} {m : VM} {v : Nat} (h : VR g s (v + 1) m) (hv : v < g.n)
    (hpc : m.pc = v + 1) :
    ∃ m1, Rn g m m1 ∧ m1.pc = base g.n v ∧ VR g { s with stk := none :: s.stk } (v + 1) m1 := by
  have hc : m.mem m.pc = .call (base g.n v) := by
    rw [hpc, h.mem_call (by omega) (by omega)]
    simp
  obtain ⟨m1, R1, st1, mem1, pc1, reg1, stk1, sol1⟩ := eff_call (g := g) (m := m) h.st hc
  refine ⟨m1, R1, pc1, st1, by rw [sol1, h.sol], ?_, fun a => by rw [mem1]; exact h.mem a, h.nodup⟩
  show m1.stk = (none :: s.stk).map (enc g.n (v + 1))
  rw [stk1, h.stk, hpc]
  simp [enc]


theorem srel_none_stk {g : Digraph} {t : TState} {s : SState} (h : SRel g t s none) : ∀ c ∈ s.stk, c ≠ none := by
  have hs : s.stk = t.stk.map some := h.stk
  intro c hc
  rw [hs] at hc
  obtain ⟨u, _, e⟩ := List.mem_map.1 hc
  rw [← e]
  simp

/-- The outer call of an unvisited node. -/
theorem vm_top {g : Digraph} {f : Nat} (hF : CallSpec g f) (hG : ∀ x w, w ∈ g.succ x → w < g.n) (hf : g.n = f + 1)
    {t : TState} {s : SState} (h : SRel g t s none) {v oc : Nat} {m : VM} (hvn : v < g.n) (hw0 : t.num v = 0)
    (hv : VR g s oc m) (hpc : m.pc = v + 1) :
    ∃ m', Rn g m m' ∧ m'.pc = v + 2 ∧ VR g (sBody g (sCall g f) v { s with stk := none :: s.stk }).2 oc m' := by
  have hS := srel_none_stk h
  obtain ⟨m1, R1, p1, hv2⟩ := vm_call_top (hv.oc hS (v + 1)) hvn hpc
  have hent : ({ s with stk := none :: s.stk } : SState).ent v = none := (h.none_iff v).2 hw0
  obtain ⟨m2, R2, p2, hv3, cell2, jmp2, fr2⟩ :=
    vm_enter (g := g) (s := { s with stk := none :: s.stk }) hv2 hvn hent p1 (c0 := none) (rest := s.stk) rfl
  obtain ⟨hq1, hun1⟩ := top_enter_q g f hf h hw0 hvn
  have hlen : (g.succ v).take (g.succ v).length = g.succ v := List.take_length
  obtain ⟨m3, pend2, R3, p3, cell3, jmp3, hv4, hq2, hp2, fr3⟩ :=
    vm_scan hF hG hvn (g.succ v).length (Nat.le_refl _) _ _ _ (v + 1) m2 (enc g.n (v + 1) none) hq1 hun1 hv3 p2 cell2
      jmp2
  rw [hlen] at hv4 hq2 hp2
  have e1 : tsuccs (revG g) v = (g.succ v).reverse := tsuccs_rev hG v
  have hb : sBody g (sCall g f) v { s with stk := none :: s.stk } =
      ((sLeave g.n v (sLoop (sCall g f) v (tsuccs (revG g) v) (sEnter v { s with stk := none :: s.stk }))).low v,
        sLeave g.n v (sLoop (sCall g f) v (tsuccs (revG g) v) (sEnter v { s with stk := none :: s.stk }))) := rfl
  rw [hb, e1]
  obtain ⟨N, tl, hs5, hnd, hlt, hentu, hch, hchlt, hwe⟩ := scanq_leave hq2
  obtain ⟨m4, R4, p4, r4, hv5, fr4⟩ := vm_leave hv4 hvn hwe p3 cell3 jmp3 hs5 hnd hlt hentu hch hchlt
  have hres := ssim_top g f hf h hw0 hvn
  have hb2 := hres.stk
  rw [hb, e1] at hb2
  refine ⟨m4, R1.trans (R2.trans (R3.trans R4)), by rw [p4]; simp [enc], ?_⟩
  refine hv5.oc ?_ oc
  have hs : (sLeave g.n v (sLoop (sCall g f) v (g.succ v).reverse (sEnter v { s with stk := none :: s.stk }))).stk =
      _ := hb2
  intro c hc
  rw [hs] at hc
  obtain ⟨u, _, e⟩ := List.mem_map.1 hc
  rw [← e]
  simp

/-- The outer call of a visited node changes nothing. -/
theorem vm_top_visited {g : Digraph} {t : TState} {s : SState} (h : SRel g t s none) {v oc k : Nat} {m : VM}
    (hvn : v < g.n) (hk : s.ent v = some k) (hv : VR g s oc m) (hpc : m.pc = v + 1) :
    ∃ m', Rn g m m' ∧ m'.pc = v + 2 ∧ VR g s oc m' := by
  have hS := srel_none_stk h
  obtain ⟨m1, R1, p1, hv2⟩ := vm_call_top (hv.oc hS (v + 1)) hvn hpc
  obtain ⟨m2, R2, p2, r2, hv3, mem2⟩ := vm_visited (g := g) (s1 := { s with stk := none :: s.stk }) hv2 hvn hk p1
    (c0 := none) (rest := s.stk) rfl
  have hv4 : VR g s (v + 1) m2 := hv3
  exact ⟨m2, R1.trans R2, by rw [p2]; simp [enc], hv4.oc hS oc⟩

/-- The outer loop over the nodes `v, v+1, …, v+k-1`. -/
theorem vm_outer {g : Digraph} {f : Nat} (hF : CallSpec g f) (hG : ∀ x w, w ∈ g.succ x → w < g.n) (hf : f = g.n - 1) :
    ∀ (k v : Nat) (t : TState) (s : SState) (oc : Nat) (m : VM), v + k ≤ g.n → SRel g t s none → VR g s oc m →
      m.pc = v + 1 → ∃ m', Rn g m m' ∧ m'.pc = v + k + 1 ∧ VR g (sRun g f (List.range' v k) s) oc m' := by
  intro k
  induction k with
  | zero =>
    intro v t s oc m _ _ hv hpc
    exact ⟨m, Rn.refl _ _, by omega, hv⟩
  | succ k ih =>
    intro v t s oc m hk h hv hpc
    have hvn : v < g.n := by omega
    have hf1 : g.n = f + 1 := by omega
    have er : List.range' v (k + 1) = v :: List.range' (v + 1) k := by simp [List.range'_succ]
    rw [er]
    by_cases h0 : t.num v = 0
    · have he : s.ent v = none := (h.none_iff v).2 h0
      obtain ⟨m1, R1, p1, hv1⟩ := vm_top hF hG hf1 h hvn h0 hv hpc
      have e : sRun g f (v :: List.range' (v + 1) k) s =
          sRun g f (List.range' (v + 1) k) (sBody g (sCall g f) v { s with stk := none :: s.stk }).2 := by
        simp only [sRun, he]
      rw [e]
      obtain ⟨m2, R2, p2, hv2⟩ := ih (v + 1) (tVisit (revG g) (f + 1) v none t) _ oc m1 (by omega)
        (ssim_top g f hf1 h h0 hvn) hv1 (by omega)
      exact ⟨m2, R1.trans R2, by omega, hv2⟩
    · have hne : s.ent v ≠ none := fun e => h0 ((h.none_iff v).1 e)
      obtain ⟨k0, hk0⟩ : ∃ k0, s.ent v = some k0 := by
        cases hh : s.ent v
        · exact absurd hh hne
        · exact ⟨_, rfl⟩
      obtain ⟨m1, R1, p1, hv1⟩ := vm_top_visited h hvn hk0 hv hpc
      have e : sRun g f (v :: List.range' (v + 1) k) s = sRun g f (List.range' (v + 1) k) s := by
        simp only [sRun, hk0]
      rw [e]
      obtain ⟨m2, R2, p2, hv2⟩ := ih (v + 1) t s oc m1 (by omega) h hv1 (by omega)
      exact ⟨m2, R1.trans R2, by omega, hv2⟩

end SmcIrred
