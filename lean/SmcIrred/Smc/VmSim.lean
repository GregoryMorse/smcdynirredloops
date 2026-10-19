module

public import SmcIrred.Smc.VmLeave
public import SmcIrred.Smc.Visit

public section

namespace SmcIrred

open Vm

/-- What `vm_leave` needs about the state at the end of the scan of `w`, from the invariant of the scan. -/
theorem scanq_leave {g : Digraph} {w : Nat} {t : TState} {s : SState} {pend : Option Nat} (h : ScanQ g w t s pend) :
    ∃ N tl : List Nat, leave5 w s = { s with stk := (N ++ w :: tl).map some } ∧ (N ++ w :: tl).Nodup ∧
      (∀ u ∈ N ++ [w], u < g.n) ∧ (∀ u ∈ N ++ [w], s.ent u ≠ none ∧ s.ent u ≠ some g.n) ∧
      (∀ u ∈ s.chain, s.ent u = some g.n) ∧ (∀ u ∈ s.chain, u < g.n) ∧ s.ent w ≠ none := by
  obtain ⟨N, tl, e1, e2, e3⟩ := h.shape
  have hmem : ∀ u ∈ N ++ [w], u ∈ t.stk := by
    intro u hu
    rw [e1]
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hu ⊢
    rcases hu with hu | hu
    · exact Or.inl hu
    · exact Or.inr (Or.inl hu)
  have hne : ∀ u ∈ N ++ [w], s.ent u ≠ none := by
    intro u hu hn
    have := h.rel.stk_ent u (hmem u hu)
    rw [hn] at this
    simp at this
  have hch : ∀ u ∈ s.chain, s.ent u = some g.n := by
    intro u hu
    rw [h.rel.chain] at hu
    obtain ⟨C, hC, huC⟩ := List.mem_flatten.1 hu
    exact h.rel.done_ent u ⟨C, hC, huC⟩
  refine ⟨N, tl, leave5_eq h.rel h.hp e1 e2 e3, by rw [← e1]; exact h.rel.nodup,
    fun u hu => h.rel.lt (hne u hu), fun u hu => ⟨hne u hu, h.rel.stk_ne_n (hmem u hu)⟩, hch,
    fun u hu => h.rel.lt (by rw [hch u hu]; simp), hne w (by simp)⟩

theorem tsuccs_rev {g : Digraph} (hG : ∀ x w, w ∈ g.succ x → w < g.n) (v : Nat) :
    tsuccs (revG g) v = (g.succ v).reverse := by
  unfold tsuccs
  show (g.succ v).reverse.filter _ = _
  rw [List.filter_eq_self.2]
  intro a ha
  exact decide_eq_true (hG v a (List.mem_reverse.1 ha))

theorem take_succ_rev (l : List Nat) (c : Nat) (h : c < l.length) :
    (l.take (c + 1)).reverse = l.getD c 0 :: (l.take c).reverse := by
  rw [List.take_add_one, List.getElem?_eq_getElem h]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]


theorem sStep_ent (x : Nat) (rs : Nat × SState) : (sStep x rs).ent = rs.2.ent := by
  unfold sStep
  by_cases h : rs.1 < rs.2.low x <;> simp [h]

theorem FreeC.ne_blk {g : Digraph} {s : SState} {a w : Nat} (ha : FreeC g s a) (hw : s.ent w = none) :
    a ≠ base g.n w + 10 ∧ a ≠ base g.n w + 30 := by
  obtain ⟨y, i, hy, e, hi, hne⟩ := ha
  have hyw : y ≠ w := by
    intro e'
    subst e'
    exact hne hw
  rw [e, base_eq g.n y, base_eq g.n w]
  rcases hi with hi | hi
  · subst hi
    constructor <;> intro h <;> omega
  · subst hi
    constructor <;> intro h <;> omega

/-- The call of an unvisited node, at the level of the machine. -/
def CallSpec (g : Digraph) (F : Nat) : Prop :=
  ∀ (x w : Nat) (t : TState) (s : SState) (pend : Option Nat) (oc : Nat) (m : VM) (c : Nat),
    ScanQ g x t s pend → t.num w = 0 → w < g.n → tUn t.num g.n ≤ F → VR g s oc m → m.pc = base g.n x + 13 →
    m.reg = (c : Int) → 1 ≤ c → (g.succ x).getD (c - 1) 0 = w → x < g.n →
    ∃ m', Rn g m m' ∧ m'.pc = base g.n x + 16 ∧ m'.reg = (((sCall g F x w s).1 : Nat) : Int) ∧
      VR g (sCall g F x w s).2 oc m' ∧ (∀ a, FreeC g s a → m'.mem a = m.mem a)

/-- One call of the successor loop of `x` (visited or not), from the patched peek to the return into `x`. -/
theorem vm_call {g : Digraph} {f : Nat} (hF : CallSpec g f) {x w : Nat} {t : TState} {s : SState} {pend : Option Nat}
    {oc : Nat} {m : VM} {c : Nat} (h : ScanQ g x t s pend) (hx : x < g.n) (hwn : w < g.n) (hun : tUn t.num g.n ≤ f)
    (hv : VR g s oc m) (hpc : m.pc = base g.n x + 13) (hreg : m.reg = (c : Int)) (hc : 1 ≤ c)
    (hwc : (g.succ x).getD (c - 1) 0 = w) :
    ∃ m', Rn g m m' ∧ m'.pc = base g.n x + 16 ∧ m'.reg = (((sCall g f x w s).1 : Nat) : Int) ∧
      VR g (sCall g f x w s).2 oc m' ∧ (∀ a, FreeC g s a → m'.mem a = m.mem a) := by
  by_cases h1 : t.num w = 0
  · exact hF x w t s pend oc m c h h1 hwn hun hv hpc hreg hc hwc hx
  · have hent : s.ent w ≠ none := fun e => h1 ((h.rel.none_iff w).1 e)
    obtain ⟨k, hk⟩ : ∃ k, s.ent w = some k := by
      cases hh : s.ent w
      · exact absurd hh hent
      · exact ⟨_, rfl⟩
    have hxe : s.ent x ≠ none := fun e => h.vis ((h.rel.none_iff x).1 e)
    obtain ⟨m1, R1, p1, hv1, fr1⟩ := vm_pre hv hx hxe hwn hpc hreg hc hwc
    have hk1 : (sPre x w s).ent w = some k := by rw [sPre_ent]; exact hk
    have hstk := (sPre_fields x w s).2.2.2.2.2.1
    obtain ⟨m2, R2, p2, r2, hv2, mem2⟩ := vm_visited hv1 hwn hk1 p1 hstk
    have e2 : ({ sPre x w s with stk := s.stk } : SState) = { s with pk := (sPre x w s).pk } := by
      have := sPre_pop x w s
      rw [hstk] at this
      exact this
    rw [sCall_visited f x w k s hk, ← e2]
    refine ⟨m2, R1.trans R2, by rw [p2]; rfl, r2, hv2, ?_⟩
    intro a ha
    rw [mem2]
    exact fr1 a ha


/-- The successor loop of `v`, `c` iterations from the counter `c`. -/
theorem vm_scan {g : Digraph} {f : Nat} (hF : CallSpec g f) (hG : ∀ x w, w ∈ g.succ x → w < g.n) {v : Nat}
    (hv : v < g.n) : ∀ (c : Nat), c ≤ (g.succ v).length → ∀ (t : TState) (s : SState) (pend : Option Nat) (oc : Nat)
      (m : VM) (ra : Nat), ScanQ g v t s pend → tUn t.num g.n ≤ f → VR g s oc m → m.pc = base g.n v + 10 →
      m.mem (base g.n v + 10) = .data (c : Int) → m.mem (base g.n v + 30) = .jmp (.at ra) →
      ∃ m' pend', Rn g m m' ∧ m'.pc = base g.n v + 10 ∧ m'.mem (base g.n v + 10) = .data 0 ∧
        m'.mem (base g.n v + 30) = .jmp (.at ra) ∧
        VR g (sLoop (sCall g f) v ((g.succ v).take c).reverse s) oc m' ∧
        ScanQ g v (tScan (fun w p t => tVisit (revG g) f w (some p) t) v ((g.succ v).take c).reverse t)
          (sLoop (sCall g f) v ((g.succ v).take c).reverse s) pend' ∧
        VPost t (tScan (fun w p t => tVisit (revG g) f w (some p) t) v ((g.succ v).take c).reverse t) s
          (sLoop (sCall g f) v ((g.succ v).take c).reverse s) ∧
        (∀ a, FreeC g s a → a ≠ base g.n v + 10 → a ≠ base g.n v + 30 → m'.mem a = m.mem a) := by
  intro c
  induction c with
  | zero =>
    intro _ t s pend oc m ra h hun hr hpc hcell hj
    exact ⟨m, pend, Rn.refl _ _, hpc, hcell, hj, hr, h, VPost.refl _ _, fun _ _ _ _ => rfl⟩
  | succ c ih =>
    intro hc t s pend oc m ra h hun hr hpc hcell hj
    have hcl : c < (g.succ v).length := hc
    rw [take_succ_rev _ c hcl]
    have hxe : s.ent v ≠ none := fun e => h.vis ((h.rel.none_iff v).1 e)
    obtain ⟨m1, R1, p1, r1, hr1, c1, fr1⟩ := vm_iter_head hr hv hxe hpc hcell (by omega)
    have hwn : (g.succ v).getD c 0 < g.n := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hcl]
      exact hG v _ (List.getElem_mem hcl)
    obtain ⟨m2, R2, p2, r2, hr2, fr2⟩ := vm_call hF h hv hwn hun hr1 p1 r1 (by omega) (by simp)
    obtain ⟨pend1, hq1, hp1⟩ := ssim_edge g v f
      (fun w t s pend hq hz hn hu => ssim_visit g f w t s pend v hq hz hn hu) h hwn hun
    have hun1 : tUn (tEdge (fun w p t => tVisit (revG g) f w (some p) t) v ((g.succ v).getD c 0) t).num g.n ≤ f :=
      Nat.le_trans (tUn_mono (s := t) (fun u hu => hp1.mono u hu) g.n) hun
    have hmono : ∀ u, s.ent u ≠ none → (sStep v (sCall g f v ((g.succ v).getD c 0) s)).ent u ≠ none :=
      SRel.ent_mono h.rel hq1.rel hp1.mono
    have hmono2 : ∀ u, s.ent u ≠ none → (sCall g f v ((g.succ v).getD c 0) s).2.ent u ≠ none := by
      intro u hu
      have := hmono u hu
      rwa [sStep_ent] at this
    have hxe2 : (sCall g f v ((g.succ v).getD c 0) s).2.ent v ≠ none := hmono2 v hxe
    obtain ⟨m3, R3, p3, hr3, fr3⟩ := vm_after_call hr2 hv hxe2 p2 r2
    have fv : ∀ a i, i = 10 ∨ i = 30 → a = base g.n v + i → FreeC g s a := fun a i hi e => ⟨v, i, hv, e, hi, hxe⟩
    have cell3 : m3.mem (base g.n v + 10) = .data (c : Int) := by
      rw [fr3 _ (FreeC.mono hmono2 (fv _ 10 (Or.inl rfl) rfl)), fr2 _ (fv _ 10 (Or.inl rfl) rfl), c1]
      simp
    have j3 : m3.mem (base g.n v + 30) = .jmp (.at ra) := by
      rw [fr3 _ (FreeC.mono hmono2 (fv _ 30 (Or.inr rfl) rfl)), fr2 _ (fv _ 30 (Or.inr rfl) rfl),
        fr1 _ (by omega)]
      exact hj
    obtain ⟨m4, pend2, R4, p4, c4, j4, hr4, hq4, hp4, fr4⟩ := ih (by omega) _ _ pend1 oc m3 ra hq1 hun1 hr3 p3 cell3 j3
    refine ⟨m4, pend2, R1.trans (R2.trans (R3.trans R4)), p4, c4, j4, hr4, hq4, hp1.trans hp4, ?_⟩
    intro a ha h10 h30
    have ha1 : FreeC g (sStep v (sCall g f v ((g.succ v).getD c 0) s)) a := FreeC.mono hmono ha
    have ha2 : FreeC g (sCall g f v ((g.succ v).getD c 0) s).2 a := FreeC.mono hmono2 ha
    rw [fr4 a ha1 h10 h30, fr3 a ha2, fr2 a ha, fr1 a h10]


/-- The call of an unvisited node, given the call specification of the callees (one fuel step less). -/
theorem vm_body {g : Digraph} {f : Nat} (hF : CallSpec g f) (hG : ∀ x w, w ∈ g.succ x → w < g.n) :
    CallSpec g (f + 1) := by
  intro x w t s pend oc m c h hw0 hwn hun hv hpc hreg hc hwc hx
  have hent : (sPre x w s).ent w = none := by rw [sPre_ent]; exact (h.rel.none_iff w).2 hw0
  have hsw : s.ent w = none := (h.rel.none_iff w).2 hw0
  have hxe : s.ent x ≠ none := fun e => h.vis ((h.rel.none_iff x).1 e)
  rw [sCall_unvisited f x w s hent]
  have hb : sBody g (sCall g f) w (sPre x w s) =
      ((sLeave g.n w (sLoop (sCall g f) w (tsuccs (revG g) w) (sEnter w (sPre x w s)))).low w,
        sLeave g.n w (sLoop (sCall g f) w (tsuccs (revG g) w) (sEnter w (sPre x w s)))) := rfl
  rw [hb]
  obtain ⟨m1, R1, p1, hv1, fr1⟩ := vm_pre hv hx hxe hwn hpc hreg hc hwc
  obtain ⟨m2, R2, p2, hv2, cell2, jmp2, fr2⟩ :=
    vm_enter (g := g) (s := sPre x w s) hv1 hwn hent p1 (c0 := some x) (rest := s.stk)
      (sPre_fields x w s).2.2.2.2.2.1
  obtain ⟨hq1, hun1, hdep1, hs1dep'⟩ := visit_enter_q g h hw0 hwn hun
  have hlen : (g.succ w).take (g.succ w).length = g.succ w := List.take_length
  obtain ⟨m3, pend2, R3, p3, cell3, jmp3, hv3, hq2, hp2, fr3⟩ :=
    vm_scan hF hG hwn (g.succ w).length (Nat.le_refl _) _ _ _ oc m2 (base g.n x + 16) hq1 hun1 hv2 p2 cell2 jmp2
  rw [hlen] at hv3 hq2 hp2
  have e1 : tsuccs (revG g) w = (g.succ w).reverse := tsuccs_rev hG w
  rw [e1]
  obtain ⟨N, tl, hs5, hnd, hlt, hentu, hch, hchlt, hwe⟩ := scanq_leave hq2
  obtain ⟨m4, R4, p4, r4, hv4, fr4⟩ :=
    vm_leave hv3 hwn hwe p3 cell3 jmp3 hs5 hnd hlt hentu hch hchlt
  refine ⟨m4, R1.trans (R2.trans (R3.trans R4)), p4, r4, hv4, ?_⟩
  intro a ha
  have mono1 : ∀ u, s.ent u ≠ none → (sEnter w (sPre x w s)).ent u ≠ none := by
    intro u hu
    show fupd (sPre x w s).ent w (some (sPre x w s).idx) u ≠ none
    rw [sPre_ent]
    by_cases e : u = w
    · subst e; simp [fupd]
    · rw [fupd_ne _ _ e]; exact hu
  have mono2 := SRel.ent_mono hq1.rel hq2.rel hp2.mono
  have ha1 : FreeC g (sPre x w s) a := FreeC.mono (fun u hu => by rw [sPre_ent]; exact hu) ha
  have ha2 : FreeC g (sEnter w (sPre x w s)) a := FreeC.mono mono1 ha
  have ha3 : FreeC g (sLoop (sCall g f) w (g.succ w).reverse (sEnter w (sPre x w s))) a := FreeC.mono mono2 ha2
  have hne := FreeC.ne_blk ha hsw
  rw [fr4 a ha3, fr3 a ha2 hne.1 hne.2, fr2 a ha1, fr1 a ha]

theorem callSpec_all {g : Digraph} (hG : ∀ x w, w ∈ g.succ x → w < g.n) : ∀ F, CallSpec g F := by
  intro F
  induction F with
  | zero =>
    intro x w t s pend oc m c h hw0 hwn hun
    have := tUn_pos (s := t) hwn hw0
    omega
  | succ f ih => exact vm_body ih hG

end SmcIrred
