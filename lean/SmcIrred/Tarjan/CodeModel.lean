module

public import SmcIrred.Tarjan.CodeSim
public import SmcIrred.Tarjan.TwoSatCode

public section

namespace SmcIrred

variable {g : Digraph} {m0 : TState} {c0 : CState}

theorem sim_visit (g : Digraph) : ∀ (f : Nat) (m : TState) (c : CState) (v : Nat) (par : Option Nat),
    CSim m0 c0 m c → m.num v = 0 → CPost m0 c0 m (tVisit g f v par m) (cVisit g f v par c) := by
  intro f
  induction f with
  | zero => intro m c v par h _; exact CPost.refl h
  | succ f ih =>
    intro m c v par h hn
    obtain ⟨m1, hm1⟩ : ∃ m1 : TState, m1 = { m with cnt := m.cnt + 1, num := tupd m.num v (m.cnt + 1), low := tupd m.low v (m.cnt + 1), stk := v :: m.stk, ticks := m.ticks + 1 } := ⟨_, rfl⟩
    have hT : tVisit g (f + 1) v par m =
        tFinish v par (tScan (fun w p t => tVisit g f w (some p) t) v (tsuccs g v) m1) := by
      rw [hm1]; rfl
    have hC : cVisit g (f + 1) v par c =
        cFinish v par (cScan (fun w p t => cVisit g f w (some p) t) v (tsuccs g v) (cEnter v c)) := rfl
    have hs1 : CSim m0 c0 m1 (cEnter v c) := by rw [hm1]; exact sim_enter h hn
    have hscan := sim_scan (m0 := m0) (c0 := c0) (F := fun w p t => tVisit g f w (some p) t)
      (F' := fun w p t => cVisit g f w (some p) t) v (fun w p m c hs hw => ih m c w (some p) hs hw)
      (tsuccs g v) m1 _ hs1
    have hnz : m1.num v ≠ 0 := by
      rw [hm1]; show tupd m.num v (m.cnt + 1) v ≠ 0; rw [tupd_same]; omega
    have hm1stk : m1.stk = v :: m.stk := by rw [hm1]
    have hm1num : ∀ x, x ≠ v → m1.num x = m.num x := by
      intro x hx; rw [hm1]; show tupd m.num v (m.cnt + 1) x = m.num x; rw [tupd_ne _ _ hx]
    obtain ⟨N0, nd0, e0, f0⟩ := hscan.stk
    have hv0 : v ∉ N0 := fun hv => hnz (by have := f0 v hv; exact absurd this hnz)
    have hstk2 : (tScan (fun w p t => tVisit g f w (some p) t) v (tsuccs g v) m1).stk = N0 ++ v :: m.stk := by
      rw [e0, hm1stk]
    obtain ⟨hfin, hstkf, hnumf⟩ := sim_finish hscan.sim hv0 hstk2 par
    rw [hT, hC]
    refine ⟨hfin, ?_, ?_⟩
    · rcases hstkf with h1 | h1
      · exact ⟨[], List.nodup_nil, by rw [h1]; simp, by simp⟩
      · refine ⟨N0 ++ [v], ?_, by rw [h1, hstk2]; simp, ?_⟩
        · rw [List.nodup_append]
          refine ⟨nd0, List.nodup_cons.2 ⟨by simp, List.nodup_nil⟩, ?_⟩
          intro x hx y hy hxy
          rw [List.mem_singleton] at hy
          subst hy; subst hxy
          exact hv0 hx
        · intro x hx
          rcases List.mem_append.1 hx with hx | hx
          · have hxv : x ≠ v := fun e => hv0 (e ▸ hx)
            have := f0 x hx
            rw [hm1num x hxv] at this
            exact this
          · rw [List.mem_singleton] at hx; subst hx; exact hn
    · intro x hx
      rw [hnumf]
      refine hscan.mono x ?_
      by_cases e : x = v
      · subst e; exact absurd hn hx
      · rw [hm1num x e]; exact hx

/-- The invariant between the clean run and the legacy run **between** two iterations of the outer loop: both stacks
are empty (up to leftover entries of the legacy stack that its flags ignore), all flags are off, and the legacy output
is the clean output with duplicate singletons. -/
structure OSim (g : Digraph) (m : TState) (c : CState) : Prop where
  inv : TInv g [] m
  cnt : c.cnt = m.cnt
  num : c.num = m.num
  low : c.low = m.low
  stk0 : m.stk = []
  off : ∀ w, c.on w = false
  dup : DupOf m.out c.out

theorem DupOf.append {l l' : List (List Nat)} (h : DupOf l l') : ∀ R : List (List Nat), DupOf (l ++ R) (l' ++ R) := by
  intro R
  induction R generalizing l l' with
  | nil => simpa using h
  | cons C R ih =>
    have := ih (DupOf.keep C h)
    simpa using this

theorem TInv.bump {P : List Nat} {s : TState} (h : TInv g P s) (k : Nat) (hk : s.cnt ≤ k) :
    TInv g P { s with cnt := k } :=
  ⟨h.stk_lt, h.done_lt, h.vis_iff, h.disj, h.stk_nodup, h.out_nodup, fun w => Nat.le_trans (h.num_le w) hk, h.P_sub,
    h.P_sorted, h.reach_P, h.closed_out, h.scc_out, h.low_le, h.low_wit, h.fin_low, h.low_min, h.fin_edge, h.fin_vis⟩

theorem cScan_idle (F' : Nat → Nat → CState → CState) (v : Nat) (s : CState) :
    ∀ ws : List Nat, (∀ w ∈ ws, s.num w ≠ 0 ∧ s.on w = false) → cScan F' v ws s = s := by
  intro ws
  induction ws with
  | nil => intro _; rfl
  | cons w ws ih =>
    intro h
    obtain ⟨h1, h2⟩ := h w List.mem_cons_self
    have : cEdge F' v w s = s := by
      unfold cEdge
      simp [h1, h2]
    show cScan F' v ws (cEdge F' v w s) = s
    rw [this]
    exact ih (fun x hx => h x (List.mem_cons_of_mem _ hx))

theorem OSim.csim {m : TState} {c : CState} (h : OSim g m c) : CSim m c m c :=
  ⟨h.cnt, h.num, h.low, ⟨c.stk, by rw [h.stk0]; simp⟩,
    fun w => by rw [h.off w, h.stk0]; simp, ⟨[], by simp, by simp⟩, by rw [h.stk0]; exact List.nodup_nil,
    by rw [h.stk0]; simp⟩

theorem osim_step (g : Digraph) {m : TState} {c : CState} (h : OSim g m c) {v : Nat} (hv : v < g.n) :
    ∃ m1 : TState, OSim g m1 (cVisit g g.n v none c) ∧ (∀ w, m.num w ≠ 0 → m1.num w ≠ 0) ∧ m1.num v ≠ 0 := by
  by_cases hn : m.num v = 0
  · have key := visit_spec g g.n m v none [] h.inv hv hn (tUn_le m g.n) rfl
    have hp := sim_visit (m0 := m) (c0 := c) g g.n m c v none h.csim hn
    have hI : TInv g [] (tVisit g g.n v none m) := key.1
    have hs0 : (tVisit g g.n v none m).stk = [] := hI.stk_nil
    refine ⟨tVisit g g.n v none m, ⟨hI, hp.sim.cnt, hp.sim.num, hp.sim.low, hs0, ?_, ?_⟩, hp.mono, key.2.1⟩
    · intro w
      cases hw : (cVisit g g.n v none c).on w
      · rfl
      · have := (hp.sim.on w).1 hw
        rw [hs0] at this; simp at this
    · obtain ⟨R, hR1, hR2⟩ := hp.sim.out
      rw [hR1, hR2]
      exact h.dup.append R
  · obtain ⟨f, hf⟩ : ∃ f, g.n = f + 1 := ⟨g.n - 1, by omega⟩
    have hcn : c.num v ≠ 0 := by rw [h.num]; exact hn
    have hfv : ∀ w ∈ tsuccs g v, c.num w ≠ 0 := by
      intro w hw
      simp only [tsuccs, List.mem_filter, decide_eq_true_eq] at hw
      rw [h.num]
      exact h.inv.fin_vis v hn (by simp) w ⟨hv, hw.2, hw.1⟩
    have hE : cEnter v c = { c with cnt := c.cnt + 1, stk := v :: c.stk } := by
      unfold cEnter; simp [hcn]
    have hC : cVisit g g.n v none c = cFinish v none
        (cScan (fun w p t => cVisit g f w (some p) t) v (tsuccs g v) { c with cnt := c.cnt + 1, stk := v :: c.stk }) := by
      rw [hf]; show cFinish v none (cScan _ v (tsuccs g v) (cEnter v c)) = _; rw [hE]
    have hid : cScan (fun w p t => cVisit g f w (some p) t) v (tsuccs g v)
        ({ c with cnt := c.cnt + 1, stk := v :: c.stk } : CState) = { c with cnt := c.cnt + 1, stk := v :: c.stk } :=
      cScan_idle _ v _ _ (fun w hw => ⟨hfv w hw, h.off w⟩)
    rw [hC, hid]
    have hI' := h.inv.bump (m.cnt + 1) (Nat.le_succ _)
    refine ⟨{ m with cnt := m.cnt + 1 }, ?_, fun w hw => hw, hn⟩
    by_cases hl : c.low v = c.num v
    · have hdone : ∃ C ∈ m.out, v ∈ C := by
        rcases (h.inv.vis_iff v).1 hn with hs | hd
        · rw [h.stk0] at hs; simp at hs
        · exact hd
      obtain ⟨C, hC1, hC2⟩ := hdone
      unfold cFinish
      simp only [hl, ↓reduceIte, popTo, List.mem_singleton]
      refine ⟨hI', by simp [h.cnt], h.num, h.low, h.stk0, ?_, ?_⟩
      · intro w; simp [h.off w]
      · exact DupOf.dup v C h.dup hC1 hC2
    · unfold cFinish
      simp only [hl, ↓reduceIte]
      exact ⟨hI', by simp [h.cnt], h.num, h.low, h.stk0, h.off, h.dup⟩

theorem cRun_sim (g : Digraph) : ∀ (vs : List Nat) (m : TState) (c : CState), OSim g m c → (∀ v ∈ vs, v < g.n) →
    ∃ m' : TState, OSim g m' (cRun g vs c) ∧ (∀ w, m.num w ≠ 0 → m'.num w ≠ 0) ∧ ∀ v ∈ vs, m'.num v ≠ 0 := by
  intro vs
  induction vs with
  | nil => intro m c h _; exact ⟨m, h, fun w hw => hw, by simp⟩
  | cons v vs ih =>
    intro m c h hv
    obtain ⟨m1, h1, hm1, hv1⟩ := osim_step g h (hv v List.mem_cons_self)
    obtain ⟨m', h', hm', hvs⟩ := ih m1 _ h1 (fun w hw => hv w (List.mem_cons_of_mem _ hw))
    refine ⟨m', h', fun w hw => hm' w (hm1 w hw), ?_⟩
    intro w hw
    rcases List.mem_cons.1 hw with rfl | hw
    · exact hm' w hv1
    · exact hvs w hw

/-- **The legacy `tarjan_scc` (L01) and `twosat`.** The component vector of the legacy outer loop (which re-enters visited
vertices) is a correct Tarjan emission order with extra singleton components `[r]` inserted, each after a component that
contains `r`; the correct emission order consists of the strongly connected components of the graph, each once, in
reverse topological order; and the loop of `twosat` ends in the same state (same `unsat` flag, same set `sol`) on both
lists. -/
theorem ctarjan_spec (g : Digraph) : ∃ comps : List (List Nat), DupOf comps (ctarjanSccs g) ∧
    (∀ C ∈ comps, ∀ u ∈ C, ∀ w, (w ∈ C ↔ g.SameSCC u w)) ∧ (∀ v, v < g.n → ∃ C ∈ comps, v ∈ C) ∧
    comps.flatten.Nodup ∧ (∀ C ∈ comps, ∀ w ∈ C, w < g.n) ∧
    (∀ L C R, comps = L ++ C :: R → ∀ u ∈ C, ∀ w, g.edge u w → w ∈ C ∨ ∃ C' ∈ L, w ∈ C') ∧
    TsE (tsFold comps) (tsFold (ctarjanSccs g)) := by
  have h0 : OSim g TState.init CState.init :=
    ⟨TInv.init g, rfl, rfl, rfl, rfl, fun _ => rfl, DupOf.nil⟩
  obtain ⟨m', h', -, hvis⟩ := cRun_sim g (List.range g.n) _ _ h0 (by intro v hv; simpa using hv)
  refine ⟨m'.out, h'.dup, h'.inv.scc_out, ?_, h'.inv.out_nodup, h'.inv.done_lt, h'.inv.closed_out,
    (tsFold_dup h'.dup).1⟩
  intro v hv
  have hn : m'.num v ≠ 0 := hvis v (List.mem_range.2 hv)
  rcases (h'.inv.vis_iff v).1 hn with hs | hd
  · rw [h'.stk0] at hs; simp at hs
  · exact hd

end SmcIrred
