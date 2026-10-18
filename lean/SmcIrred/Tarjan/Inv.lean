module

public import SmcIrred.Spec.Tarjan
public import SmcIrred.TwoSat.Reach

public section

namespace SmcIrred

variable {g : Digraph}

/-- The vertex lies in an emitted component. -/
@[expose] def TState.Done (s : TState) (w : Nat) : Prop := ∃ C ∈ s.out, w ∈ C

/-- Emitted components end with their root (`lowlink = index`); the other members have `lowlink < index`. -/
@[expose] def DoneLow (s : TState) : Prop :=
  ∀ C ∈ s.out, ∃ r, C.getLast? = some r ∧ s.low r = s.num r ∧ ∀ u ∈ C, u ≠ r → s.low u < s.num u

theorem mem_of_getLast' {C : List Nat} {r : Nat} (h : C.getLast? = some r) : r ∈ C := by
  obtain ⟨ys, e⟩ := List.getLast?_eq_some_iff.1 h
  rw [e]; simp

theorem DoneLow.congr {s t : TState} (h : DoneLow s) (hout : t.out = s.out) (hnum : ∀ w, (∃ C ∈ s.out, w ∈ C) → t.num w = s.num w)
    (hlow : ∀ w, (∃ C ∈ s.out, w ∈ C) → t.low w = s.low w) : DoneLow t := by
  intro C hC
  rw [hout] at hC
  obtain ⟨r, h1, h2, h3⟩ := h C hC
  have hr : ∃ C' ∈ s.out, r ∈ C' := ⟨C, hC, mem_of_getLast' h1⟩
  refine ⟨r, h1, by rw [hnum r hr, hlow r hr]; exact h2, fun u hu hne => ?_⟩
  have hu' : ∃ C' ∈ s.out, u ∈ C' := ⟨C, hC, hu⟩
  rw [hnum u hu', hlow u hu']; exact h3 u hu hne

/-- The invariant of Tarjan's algorithm along the active call path `P` (head = the vertex being scanned): the stack and
the emitted components partition the visited vertices; emitted components are complete strongly connected components
whose successors lie in themselves or in earlier components; the lowlinks of stacked vertices witness a path to a
stacked vertex of that index; finished vertices have lowlink below their index, bounded by their examined edges. -/
structure TInv (g : Digraph) (P : List Nat) (s : TState) : Prop where
  stk_lt : ∀ w ∈ s.stk, w < g.n
  done_lt : ∀ C ∈ s.out, ∀ w ∈ C, w < g.n
  vis_iff : ∀ w, s.num w ≠ 0 ↔ (w ∈ s.stk ∨ s.Done w)
  disj : ∀ w ∈ s.stk, ¬ s.Done w
  stk_nodup : s.stk.Nodup
  out_nodup : s.out.flatten.Nodup
  num_le : ∀ w, s.num w ≤ s.cnt
  P_sub : ∀ p ∈ P, p ∈ s.stk
  P_sorted : P.Pairwise (fun a b => s.num b < s.num a)
  reach_P : ∀ p ∈ P, ∀ w, s.num w ≠ 0 → s.num p ≤ s.num w → g.Reach p w
  closed_out : ∀ L C R, s.out = L ++ C :: R → ∀ u ∈ C, ∀ w, g.edge u w → w ∈ C ∨ ∃ C' ∈ L, w ∈ C'
  scc_out : ∀ C ∈ s.out, ∀ u ∈ C, ∀ w, (w ∈ C ↔ g.SameSCC u w)
  low_le : ∀ w ∈ s.stk, 1 ≤ s.low w ∧ s.low w ≤ s.num w
  low_wit : ∀ w ∈ s.stk, s.low w < s.num w → ∃ y ∈ s.stk, s.num y = s.low w ∧ g.Reach w y
  fin_low : ∀ w ∈ s.stk, w ∉ P → s.low w < s.num w
  low_min : ∀ p ∈ P, ∀ w ∈ s.stk, w ∉ P → s.num p < s.num w →
    (∀ q ∈ P, s.num q < s.num w → s.num q ≤ s.num p) → s.low p ≤ s.low w
  fin_edge : ∀ x ∈ s.stk, x ∉ P → ∀ y, g.edge x y → s.Done y ∨ (y ∈ s.stk ∧ s.low x ≤ s.num y)
  fin_vis : ∀ x, s.num x ≠ 0 → x ∉ P → ∀ y, g.edge x y → s.num y ≠ 0
  done_low : DoneLow s

theorem tupd_same (f : Nat → Nat) (k x : Nat) : tupd f k x k = x := by simp [tupd]

theorem tupd_ne (f : Nat → Nat) {k j : Nat} (x : Nat) (h : j ≠ k) : tupd f k x j = f j := by simp [tupd, h]

theorem TInv.init (g : Digraph) : TInv g [] TState.init where
  stk_lt := by simp [TState.init]
  done_lt := by simp [TState.init]
  vis_iff := by simp [TState.init, TState.Done]
  disj := by simp [TState.init]
  stk_nodup := by simp [TState.init]
  out_nodup := by simp [TState.init]
  num_le := by simp [TState.init]
  P_sub := by simp
  P_sorted := by simp
  reach_P := by simp
  closed_out := by
    intro L C R h
    simp [TState.init] at h
  scc_out := by simp [TState.init]
  low_le := by simp [TState.init]
  low_wit := by simp [TState.init]
  fin_low := by simp [TState.init]
  low_min := by simp
  fin_edge := by simp [TState.init]
  fin_vis := by simp [TState.init]
  done_low := by simp [TState.init, DoneLow]

theorem TInv.vis_of_stk {P : List Nat} {s : TState} (h : TInv g P s) {w : Nat} (hw : w ∈ s.stk) : s.num w ≠ 0 :=
  (h.vis_iff w).2 (Or.inl hw)

theorem TInv.vis_of_done {P : List Nat} {s : TState} (h : TInv g P s) {w : Nat} (hw : s.Done w) : s.num w ≠ 0 :=
  (h.vis_iff w).2 (Or.inr hw)

theorem TInv.head_lt {P : List Nat} {s : TState} (h : TInv g P s) {p : Nat} {P0 : List Nat} (hP : P = p :: P0) :
    p < g.n := h.stk_lt p (h.P_sub p (hP ▸ List.mem_cons_self))

/-- The head of the path has the largest index of the path. -/
theorem TInv.head_max {P : List Nat} {s : TState} (h : TInv g P s) {p : Nat} {P0 : List Nat} (hP : P = p :: P0)
    {q : Nat} (hq : q ∈ P) : s.num q ≤ s.num p := by
  subst hP
  rcases List.mem_cons.1 hq with rfl | hq
  · exact Nat.le_refl _
  · exact Nat.le_of_lt ((List.pairwise_cons.1 h.P_sorted).1 q hq)

/-- Entering a fresh vertex `v` reachable from every vertex of the path. -/
theorem TInv.enter {P : List Nat} {s : TState} (h : TInv g P s) {v : Nat} (hv : v < g.n) (hn : s.num v = 0)
    (hP : ∀ p ∈ P, g.Reach p v) :
    TInv g (v :: P) { s with cnt := s.cnt + 1, num := tupd s.num v (s.cnt + 1), low := tupd s.low v (s.cnt + 1),
                             stk := v :: s.stk, ticks := s.ticks + 1 } := by
  have hvs : v ∉ s.stk := fun hm => h.vis_of_stk hm hn
  have hvd : ¬ s.Done v := fun hm => h.vis_of_done hm hn
  have hne : ∀ w ∈ s.stk, w ≠ v := fun w hw e => hvs (e ▸ hw)
  have hnum : ∀ w, w ≠ v → tupd s.num v (s.cnt + 1) w = s.num w := fun w hw => tupd_ne _ _ hw
  have hlow : ∀ w, w ≠ v → tupd s.low v (s.cnt + 1) w = s.low w := fun w hw => tupd_ne _ _ hw
  have hnv : tupd s.num v (s.cnt + 1) v = s.cnt + 1 := tupd_same _ _ _
  have hlv : tupd s.low v (s.cnt + 1) v = s.cnt + 1 := tupd_same _ _ _
  have hlt : ∀ w, w ≠ v → s.num w < s.cnt + 1 := fun w _ => Nat.lt_succ_of_le (h.num_le w)
  refine ⟨?_, h.done_lt, ?_, ?_, ?_, h.out_nodup, ?_, ?_, ?_, ?_, h.closed_out, h.scc_out, ?_, ?_, ?_, ?_, ?_, ?_,
    h.done_low.congr rfl (fun w hw => hnum w (fun e => hvd (e ▸ hw))) (fun w hw => hlow w (fun e => hvd (e ▸ hw)))⟩
  · intro w hw
    rcases List.mem_cons.1 hw with rfl | hw
    · exact hv
    · exact h.stk_lt w hw
  · intro w
    show tupd s.num v (s.cnt + 1) w ≠ 0 ↔ w ∈ v :: s.stk ∨ s.Done w
    by_cases e : w = v
    · subst e; simp [hnv]
    · rw [hnum w e]
      rw [h.vis_iff w]
      simp [List.mem_cons, e]
  · intro w hw
    rcases List.mem_cons.1 hw with rfl | hw
    · exact hvd
    · exact h.disj w hw
  · exact List.nodup_cons.2 ⟨hvs, h.stk_nodup⟩
  · intro w
    show tupd s.num v (s.cnt + 1) w ≤ s.cnt + 1
    by_cases e : w = v
    · subst e; simp [hnv]
    · rw [hnum w e]; exact Nat.le_succ_of_le (h.num_le w)
  · intro p hp
    rcases List.mem_cons.1 hp with rfl | hp
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (h.P_sub p hp)
  · show List.Pairwise _ (v :: P)
    rw [List.pairwise_cons]
    refine ⟨fun b hb => ?_, ?_⟩
    · have hb' : b ≠ v := fun e => hvs (e ▸ h.P_sub b hb)
      show tupd s.num v (s.cnt + 1) b < tupd s.num v (s.cnt + 1) v
      rw [hnum b hb', hnv]; exact hlt b hb'
    · refine List.Pairwise.imp_of_mem ?_ h.P_sorted
      intro a b ha hb hab
      have ha' : a ≠ v := fun e => hvs (e ▸ h.P_sub a ha)
      have hb' : b ≠ v := fun e => hvs (e ▸ h.P_sub b hb)
      show tupd s.num v (s.cnt + 1) b < tupd s.num v (s.cnt + 1) a
      rw [hnum a ha', hnum b hb']; exact hab
  · intro p hp w hw hpw
    show g.Reach p w
    rcases List.mem_cons.1 hp with rfl | hp
    · by_cases e : w = p
      · subst e; exact .refl _
      · exfalso
        have h1 : tupd s.num p (s.cnt + 1) w = s.num w := hnum w e
        have h2 : tupd s.num p (s.cnt + 1) p = s.cnt + 1 := hnv
        have h3 := h.num_le w
        have : tupd s.num p (s.cnt + 1) p ≤ tupd s.num p (s.cnt + 1) w := hpw
        omega
    · have hp' : p ≠ v := fun e => hvs (e ▸ h.P_sub p hp)
      have hpp : tupd s.num v (s.cnt + 1) p = s.num p := hnum p hp'
      have hpv := hP p hp
      by_cases e : w = v
      · rw [e]; exact hpv
      · have hww : tupd s.num v (s.cnt + 1) w = s.num w := hnum w e
        exact h.reach_P p hp w (by rw [← hww]; exact hw) (by
          have : tupd s.num v (s.cnt + 1) p ≤ tupd s.num v (s.cnt + 1) w := hpw
          rw [hpp, hww] at this; exact this)
  · intro w hw
    rcases List.mem_cons.1 hw with rfl | hw
    · show 1 ≤ tupd s.low w (s.cnt + 1) w ∧ tupd s.low w (s.cnt + 1) w ≤ tupd s.num w (s.cnt + 1) w
      rw [hlv, hnv]; omega
    · have e := hne w hw
      show 1 ≤ tupd s.low v (s.cnt + 1) w ∧ tupd s.low v (s.cnt + 1) w ≤ tupd s.num v (s.cnt + 1) w
      rw [hlow w e, hnum w e]; exact h.low_le w hw
  · intro w hw hlw
    rcases List.mem_cons.1 hw with rfl | hw
    · exfalso
      have : tupd s.low w (s.cnt + 1) w < tupd s.num w (s.cnt + 1) w := hlw
      rw [hlv, hnv] at this; omega
    · have e := hne w hw
      have hlw' : s.low w < s.num w := by
        have : tupd s.low v (s.cnt + 1) w < tupd s.num v (s.cnt + 1) w := hlw
        rwa [hlow w e, hnum w e] at this
      obtain ⟨y, hy, hny, hry⟩ := h.low_wit w hw hlw'
      have ey := hne y hy
      refine ⟨y, List.mem_cons_of_mem _ hy, ?_, hry⟩
      show tupd s.num v (s.cnt + 1) y = tupd s.low v (s.cnt + 1) w
      rw [hnum y ey, hlow w e, hny]
  · intro w hw hwP
    have e : w ≠ v := fun e => hwP (e ▸ List.mem_cons_self)
    have hw' : w ∈ s.stk := by
      rcases List.mem_cons.1 hw with h' | h'
      · exact absurd h' e
      · exact h'
    have hwP' : w ∉ P := fun hm => hwP (List.mem_cons_of_mem _ hm)
    show tupd s.low v (s.cnt + 1) w < tupd s.num v (s.cnt + 1) w
    rw [hlow w e, hnum w e]; exact h.fin_low w hw' hwP'
  · intro p hp w hw hwP hpw hmin
    have e : w ≠ v := fun e => hwP (e ▸ List.mem_cons_self)
    have hw' : w ∈ s.stk := by
      rcases List.mem_cons.1 hw with h' | h'
      · exact absurd h' e
      · exact h'
    have hwP' : w ∉ P := fun hm => hwP (List.mem_cons_of_mem _ hm)
    rcases List.mem_cons.1 hp with rfl | hp
    · exfalso
      have h1 : tupd s.num p (s.cnt + 1) p < tupd s.num p (s.cnt + 1) w := hpw
      rw [hnv, hnum w e] at h1
      have := h.num_le w
      omega
    · have hp' : p ≠ v := fun e => hvs (e ▸ h.P_sub p hp)
      show tupd s.low v (s.cnt + 1) p ≤ tupd s.low v (s.cnt + 1) w
      rw [hlow p hp', hlow w e]
      refine h.low_min p hp w hw' hwP' ?_ ?_
      · have h1 : tupd s.num v (s.cnt + 1) p < tupd s.num v (s.cnt + 1) w := hpw
        rwa [hnum p hp', hnum w e] at h1
      · intro q hq hqw
        have hq' : q ≠ v := fun e => hvs (e ▸ h.P_sub q hq)
        have h2 := hmin q (List.mem_cons_of_mem _ hq) (by
          show tupd s.num v (s.cnt + 1) q < tupd s.num v (s.cnt + 1) w
          rw [hnum q hq', hnum w e]; exact hqw)
        have h3 : tupd s.num v (s.cnt + 1) q ≤ tupd s.num v (s.cnt + 1) p := h2
        rwa [hnum q hq', hnum p hp'] at h3
  · intro x hx hxP y hy
    have e : x ≠ v := fun e => hxP (e ▸ List.mem_cons_self)
    have hx' : x ∈ s.stk := by
      rcases List.mem_cons.1 hx with h' | h'
      · exact absurd h' e
      · exact h'
    have hxP' : x ∉ P := fun hm => hxP (List.mem_cons_of_mem _ hm)
    rcases h.fin_edge x hx' hxP' y hy with hd | ⟨hys, hl⟩
    · exact Or.inl hd
    · have ey := hne y hys
      refine Or.inr ⟨List.mem_cons_of_mem _ hys, ?_⟩
      show tupd s.low v (s.cnt + 1) x ≤ tupd s.num v (s.cnt + 1) y
      rw [hlow x e, hnum y ey]; exact hl
  · intro x hx hxP y hy
    have e : x ≠ v := fun e => hxP (e ▸ List.mem_cons_self)
    have hxP' : x ∉ P := fun hm => hxP (List.mem_cons_of_mem _ hm)
    have hx' : s.num x ≠ 0 := by
      have : tupd s.num v (s.cnt + 1) x ≠ 0 := hx
      rwa [hnum x e] at this
    have := h.fin_vis x hx' hxP' y hy
    show tupd s.num v (s.cnt + 1) y ≠ 0
    by_cases ey : y = v
    · subst ey; rw [hnv]; omega
    · rw [hnum y ey]; exact this

/-- A back/cross edge from the scanned vertex `v` to a stacked vertex `w` lowers the lowlink of `v` to the index of `w`. -/
theorem TInv.lowStep {P : List Nat} {s : TState} {v : Nat} (h : TInv g (v :: P) s) {w : Nat} (hw : w ∈ s.stk)
    (he : g.edge v w) :
    TInv g (v :: P) { s with low := tupd s.low v (min (s.low v) (s.num w)) } := by
  have hv : v ∈ s.stk := h.P_sub v List.mem_cons_self
  have hlv : tupd s.low v (min (s.low v) (s.num w)) v = min (s.low v) (s.num w) := tupd_same _ _ _
  have hl : ∀ j, j ≠ v → tupd s.low v (min (s.low v) (s.num w)) j = s.low j := fun j hj => tupd_ne _ _ hj
  have hwn := h.vis_of_stk hw
  refine ⟨h.stk_lt, h.done_lt, h.vis_iff, h.disj, h.stk_nodup, h.out_nodup, h.num_le, h.P_sub, h.P_sorted,
    h.reach_P, h.closed_out, h.scc_out, ?_, ?_, ?_, ?_, ?_, h.fin_vis,
    h.done_low.congr rfl (fun _ _ => rfl) (fun w hw => hl w (fun e => h.disj w (e ▸ hv) hw))⟩
  · intro x hx
    show 1 ≤ tupd s.low v (min (s.low v) (s.num w)) x ∧ tupd s.low v (min (s.low v) (s.num w)) x ≤ s.num x
    by_cases e : x = v
    · subst e
      rw [hlv]
      have := h.low_le x hx
      omega
    · rw [hl x e]; exact h.low_le x hx
  · intro x hx hlx
    by_cases e : x = v
    · subst e
      have hlx' : min (s.low x) (s.num w) < s.num x := by rw [← hlv]; exact hlx
      by_cases c : s.num w < s.low x
      · refine ⟨w, hw, ?_, .step he (.refl _)⟩
        show s.num w = tupd s.low x (min (s.low x) (s.num w)) x
        rw [hlv]; omega
      · have c' : s.low x < s.num x := by omega
        obtain ⟨y, hy, hny, hry⟩ := h.low_wit x hx c'
        refine ⟨y, hy, ?_, hry⟩
        show s.num y = tupd s.low x (min (s.low x) (s.num w)) x
        rw [hlv, hny]; omega
    · have hlx' : s.low x < s.num x := by rw [← hl x e]; exact hlx
      obtain ⟨y, hy, hny, hry⟩ := h.low_wit x hx hlx'
      exact ⟨y, hy, by show s.num y = tupd s.low v _ x; rw [hl x e]; exact hny, hry⟩
  · intro x hx hxP
    have e : x ≠ v := fun e => hxP (e ▸ List.mem_cons_self)
    show tupd s.low v (min (s.low v) (s.num w)) x < s.num x
    rw [hl x e]; exact h.fin_low x hx hxP
  · intro p hp x hx hxP hpx hmin
    have e : x ≠ v := fun e => hxP (e ▸ List.mem_cons_self)
    show tupd s.low v (min (s.low v) (s.num w)) p ≤ tupd s.low v (min (s.low v) (s.num w)) x
    rw [hl x e]
    have := h.low_min p hp x hx hxP hpx hmin
    by_cases ep : p = v
    · subst ep; rw [hlv]; omega
    · rw [hl p ep]; exact this
  · intro x hx hxP y hy
    have e : x ≠ v := fun e => hxP (e ▸ List.mem_cons_self)
    show s.Done y ∨ (y ∈ s.stk ∧ tupd s.low v (min (s.low v) (s.num w)) x ≤ s.num y)
    rw [hl x e]; exact h.fin_edge x hx hxP y hy

end SmcIrred
