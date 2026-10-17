module

public import SmcIrred.Tarjan.Inv

public section

namespace SmcIrred

variable {g : Digraph}

theorem popTo_split {v : Nat} {N b : List Nat} (hv : v ∉ N) : popTo v (N ++ v :: b) = (N ++ [v], b) := by
  induction N with
  | nil => simp [popTo]
  | cons x N ih =>
    have hx : x ≠ v := fun e => hv (e ▸ List.mem_cons_self)
    have hv' : v ∉ N := fun hm => hv (List.mem_cons_of_mem _ hm)
    simp [popTo, hx, ih hv']

/-- Everything reachable from an emitted vertex is emitted. -/
theorem TInv.done_reach {P : List Nat} {s : TState} (h : TInv g P s) {x y : Nat} (hxy : g.Reach x y) (hx : s.Done x) :
    s.Done y := by
  induction hxy with
  | refl _ => exact hx
  | @step a b c he _ ih =>
    refine ih ?_
    obtain ⟨C, hC, hxC⟩ := hx
    obtain ⟨L, R, hLR⟩ := List.append_of_mem hC
    rcases h.closed_out L C R hLR a hxC b he with hb | ⟨C', hC', hb⟩
    · exact ⟨C, hC, hb⟩
    · exact ⟨C', by rw [hLR]; simp [hC'], hb⟩

/-- The component `N ++ [v]` popped at a root `v` is a complete strongly connected component, closed under successors up
to earlier components. -/
theorem TInv.pop {P : List Nat} {s : TState} {v : Nat} {N b : List Nat} (h : TInv g (v :: P) s)
    (hstk : s.stk = N ++ v :: b) (hN : ∀ u ∈ N, s.num v < s.num u) (hb : ∀ y ∈ b, s.num y < s.num v)
    (hlow : s.low v = s.num v) (hex : ∀ y, g.edge v y → s.Done y ∨ (y ∈ s.stk ∧ s.low v ≤ s.num y)) (t : Nat) :
    TInv g P { s with stk := b, out := s.out ++ [N ++ [v]], ticks := t } := by
  have hvN : v ∉ N := fun hm => absurd (hN v hm) (Nat.lt_irrefl _)
  have hnd : (N ++ v :: b).Nodup := hstk ▸ h.stk_nodup
  rw [List.nodup_append] at hnd
  obtain ⟨hNnd, hvbnd, hdisj⟩ := hnd
  have hvb : v ∉ b := (List.nodup_cons.1 hvbnd).1
  have hbnd : b.Nodup := (List.nodup_cons.1 hvbnd).2
  have hNb : ∀ u ∈ N, u ∉ b := fun u hu hub => hdisj u hu u (List.mem_cons_of_mem _ hub) rfl
  have hmemstk : ∀ u, u ∈ s.stk ↔ u ∈ N ∨ u = v ∨ u ∈ b := by
    intro u; rw [hstk]; simp [List.mem_append, List.mem_cons]
  have hvstk : v ∈ s.stk := (hmemstk v).2 (Or.inr (Or.inl rfl))
  have hPlt : ∀ p ∈ P, s.num p < s.num v := (List.pairwise_cons.1 h.P_sorted).1
  have hPb : ∀ p ∈ P, p ∈ b := by
    intro p hp
    have hps := h.P_sub p (List.mem_cons_of_mem _ hp)
    rcases (hmemstk p).1 hps with hpN | rfl | hpb
    · have := hN p hpN; have := hPlt p hp; omega
    · have := hPlt p hp; omega
    · exact hpb
  have hnotP : ∀ x ∈ N, x ∉ v :: P := by
    intro x hx hxm
    rcases List.mem_cons.1 hxm with rfl | hxP
    · exact hvN hx
    · exact hNb x hx (hPb x hxP)
  have hnum_stk : ∀ y ∈ s.stk, y ∈ N ∨ y = v ∨ s.num y < s.num v := by
    intro y hy
    rcases (hmemstk y).1 hy with hyN | hyv | hyb
    · exact Or.inl hyN
    · exact Or.inr (Or.inl hyv)
    · exact Or.inr (Or.inr (hb y hyb))
  -- every vertex of the component is reachable from `v`
  have reachFrom : ∀ x, (x ∈ N ∨ x = v) → g.Reach v x := by
    intro x hx
    rcases hx with hx | rfl
    · exact h.reach_P v List.mem_cons_self x (h.vis_of_stk ((hmemstk x).2 (Or.inl hx))) (Nat.le_of_lt (hN x hx))
    · exact .refl _
  -- the lowlink of every member is at least the index of `v`
  have lowge : ∀ x ∈ N, s.num v ≤ s.low x := by
    intro x hx
    have := h.low_min v List.mem_cons_self x ((hmemstk x).2 (Or.inl hx)) (hnotP x hx) (hN x hx) (by
      intro q hq hqx
      rcases List.mem_cons.1 hq with rfl | hqP
      · exact Nat.le_refl _
      · exact Nat.le_of_lt (hPlt q hqP))
    omega
  -- every vertex of the component reaches `v`
  have reachTo : ∀ m, ∀ x ∈ N, s.num x = m → g.Reach x v := by
    intro m
    induction m using Nat.strongRecOn with
    | _ m ih =>
      intro x hx hxm
      have hxs : x ∈ s.stk := (hmemstk x).2 (Or.inl hx)
      have hl := h.fin_low x hxs (hnotP x hx)
      obtain ⟨y, hy, hny, hry⟩ := h.low_wit x hxs hl
      have hge := lowge x hx
      rcases hnum_stk y hy with hyN | rfl | hyl
      · exact hry.trans (ih (s.num y) (by omega) y hyN rfl)
      · exact hry
      · omega
  -- successors of the component
  have reachTo' : ∀ x, (x ∈ N ∨ x = v) → g.Reach x v := by
    intro x hx
    rcases hx with hx | rfl
    · exact reachTo _ x hx rfl
    · exact .refl _
  have hclos : ∀ u, (u ∈ N ∨ u = v) → ∀ y, g.edge u y → (y ∈ N ∨ y = v) ∨ s.Done y := by
    intro u hu y hy
    rcases hu with hu | rfl
    · have hus := (hmemstk u).2 (Or.inl hu)
      have hl := lowge u hu
      rcases h.fin_edge u hus (hnotP u hu) y hy with hd | ⟨hys, hly⟩
      · exact Or.inr hd
      · rcases hnum_stk y hys with hyN | hyv | hyl
        · exact Or.inl (Or.inl hyN)
        · exact Or.inl (Or.inr hyv)
        · omega
    · rcases hex y hy with hd | ⟨hys, hly⟩
      · exact Or.inr hd
      · rcases hnum_stk y hys with hyN | hyv | hyl
        · exact Or.inl (Or.inl hyN)
        · exact Or.inl (Or.inr hyv)
        · omega
  have hpath : ∀ x w, g.Reach x w → ((x ∈ N ∨ x = v) ∨ s.Done x) → ((w ∈ N ∨ w = v) ∨ s.Done w) := by
    intro x w hxw
    induction hxw with
    | refl _ => exact id
    | @step a b c he _ ih =>
      intro ha
      refine ih ?_
      rcases ha with ha | ha
      · exact hclos a ha b he
      · exact Or.inr (h.done_reach (.step he (.refl _)) ha)
  have hDone : ∀ y, ({ s with stk := b, out := s.out ++ [N ++ [v]], ticks := t } : TState).Done y ↔
      (s.Done y ∨ y ∈ N ∨ y = v) := by
    intro y
    constructor
    · rintro ⟨C, hC, hyC⟩
      rcases List.mem_append.1 hC with hC | hC
      · exact Or.inl ⟨C, hC, hyC⟩
      · have : C = N ++ [v] := by simpa using hC
        subst this
        right; simpa [List.mem_append] using hyC
    · rintro (⟨C, hC, hyC⟩ | hy)
      · exact ⟨C, List.mem_append_left _ hC, hyC⟩
      · exact ⟨N ++ [v], List.mem_append_right _ (List.mem_singleton_self _), by simpa [List.mem_append] using hy⟩
  have hCv : ∀ x, (x ∈ N ∨ x = v) → x ∈ s.stk := fun x hx => by
    rcases hx with hx | rfl
    · exact (hmemstk x).2 (Or.inl hx)
    · exact hvstk
  refine ⟨?_, ?_, ?_, ?_, hbnd, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w hw
    exact h.stk_lt w ((hmemstk w).2 (Or.inr (Or.inr hw)))
  · intro C hC w hw
    rcases List.mem_append.1 hC with hC | hC
    · exact h.done_lt C hC w hw
    · have : C = N ++ [v] := by simpa using hC
      subst this
      exact h.stk_lt w (hCv w (by simpa [List.mem_append] using hw))
  · intro w
    show s.num w ≠ 0 ↔ w ∈ b ∨ ({ s with stk := b, out := s.out ++ [N ++ [v]], ticks := t } : TState).Done w
    rw [h.vis_iff w, hDone w, hmemstk w]
    constructor
    · rintro ((hwN | rfl | hwb) | hd)
      · exact Or.inr (Or.inr (Or.inl hwN))
      · exact Or.inr (Or.inr (Or.inr rfl))
      · exact Or.inl hwb
      · exact Or.inr (Or.inl hd)
    · rintro (hwb | hd | hwN | rfl)
      · exact Or.inl (Or.inr (Or.inr hwb))
      · exact Or.inr hd
      · exact Or.inl (Or.inl hwN)
      · exact Or.inl (Or.inr (Or.inl rfl))
  · intro w hw hwd
    have hws := (hmemstk w).2 (Or.inr (Or.inr hw))
    rcases (hDone w).1 hwd with hd | hwN | rfl
    · exact h.disj w hws hd
    · exact hNb w hwN hw
    · exact hvb hw
  · show (s.out ++ [N ++ [v]]).flatten.Nodup
    rw [List.flatten_append, List.nodup_append]
    refine ⟨h.out_nodup, ?_, ?_⟩
    · simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
      rw [List.nodup_append]
      exact ⟨hNnd, List.nodup_cons.2 ⟨by simp, List.nodup_nil⟩, fun a ha c hc => by
        rw [List.mem_singleton] at hc; subst hc; exact fun e => hvN (e ▸ ha)⟩
    · intro a ha c hc
      simp only [List.flatten_cons, List.flatten_nil, List.append_nil] at hc
      intro e
      subst e
      have hcs : a ∈ s.stk := hCv a (by simpa [List.mem_append] using hc)
      obtain ⟨C, hC, hac⟩ := List.mem_flatten.1 ha
      exact h.disj a hcs ⟨C, hC, hac⟩
  · exact h.num_le
  · intro p hp
    exact hPb p hp
  · exact (List.pairwise_cons.1 h.P_sorted).2
  · intro p hp w hw hpw
    exact h.reach_P p (List.mem_cons_of_mem _ hp) w hw hpw
  · intro L C R hLCR u hu w hw
    rcases List.append_eq_append_iff.1 hLCR with ⟨a', hL, hca⟩ | ⟨c', hout, hc'⟩
    · cases a' with
      | nil =>
        simp at hca
        obtain ⟨rfl, rfl⟩ := hca
        simp at hL
        subst hL
        rcases hclos u (by simpa [List.mem_append] using hu) w hw with hwC | ⟨C', hC', hwC'⟩
        · exact Or.inl (by simpa [List.mem_append] using hwC)
        · exact Or.inr ⟨C', hC', hwC'⟩
      | cons x a'' =>
        simp at hca
    · cases c' with
      | nil =>
        simp at hc'
        obtain ⟨rfl, rfl⟩ := hc'
        simp at hout
        subst hout
        rcases hclos u (by simpa [List.mem_append] using hu) w hw with hwC | ⟨C', hC', hwC'⟩
        · exact Or.inl (by simpa [List.mem_append] using hwC)
        · exact Or.inr ⟨C', hC', hwC'⟩
      | cons x c'' =>
        simp at hc'
        obtain ⟨rfl, hR⟩ := hc'
        exact h.closed_out L C c'' hout u hu w hw
  · intro C hC u hu w
    rcases List.mem_append.1 hC with hC | hC
    · exact h.scc_out C hC u hu w
    · have : C = N ++ [v] := by simpa using hC
      subst this
      have hu' : u ∈ N ∨ u = v := by simpa [List.mem_append] using hu
      constructor
      · intro hw
        have hw' : w ∈ N ∨ w = v := by simpa [List.mem_append] using hw
        exact ⟨(reachTo' u hu').trans (reachFrom w hw'), (reachTo' w hw').trans (reachFrom u hu')⟩
      · intro hs
        have hvw : g.Reach v w := (reachFrom u hu').trans hs.1
        rcases hpath v w hvw (Or.inl (Or.inr rfl)) with hwC | hd
        · simpa [List.mem_append] using hwC
        · exfalso
          have hwv : g.Reach w v := hs.2.trans (reachTo' u hu')
          exact h.disj v hvstk (h.done_reach hwv hd)
  · intro w hw
    exact h.low_le w ((hmemstk w).2 (Or.inr (Or.inr hw)))
  · intro w hw hlw
    have hws := (hmemstk w).2 (Or.inr (Or.inr hw))
    obtain ⟨y, hy, hny, hry⟩ := h.low_wit w hws hlw
    have hle := (h.low_le w hws).2
    have hwv := hb w hw
    rcases (hmemstk y).1 hy with hyN | rfl | hyb
    · have := hN y hyN; omega
    · omega
    · exact ⟨y, hyb, hny, hry⟩
  · intro w hw hwP
    have hws := (hmemstk w).2 (Or.inr (Or.inr hw))
    refine h.fin_low w hws ?_
    intro hm
    rcases List.mem_cons.1 hm with rfl | hwP'
    · exact hvb hw
    · exact hwP hwP'
  · intro p hp w hw hwP hpw hmin
    have hws := (hmemstk w).2 (Or.inr (Or.inr hw))
    have hnw : w ∉ v :: P := by
      intro hm
      rcases List.mem_cons.1 hm with rfl | hwP'
      · exact hvb hw
      · exact hwP hwP'
    refine h.low_min p (List.mem_cons_of_mem _ hp) w hws hnw hpw ?_
    intro q hq hqw
    rcases List.mem_cons.1 hq with rfl | hqP
    · have := hb w hw; omega
    · exact hmin q hqP hqw
  · intro x hx hxP y hy
    have hxs := (hmemstk x).2 (Or.inr (Or.inr hx))
    have hnx : x ∉ v :: P := by
      intro hm
      rcases List.mem_cons.1 hm with rfl | hxP'
      · exact hvb hx
      · exact hxP hxP'
    rcases h.fin_edge x hxs hnx y hy with hd | ⟨hys, hl⟩
    · exact Or.inl ((hDone y).2 (Or.inl hd))
    · rcases (hmemstk y).1 hys with hyN | rfl | hyb
      · exact Or.inl ((hDone y).2 (Or.inr (Or.inl hyN)))
      · exact Or.inl ((hDone y).2 (Or.inr (Or.inr rfl)))
      · exact Or.inr ⟨hyb, hl⟩
  · intro x hx hxP y hy
    by_cases e : x = v
    · subst e
      rcases hex y hy with hd | ⟨hys, -⟩
      · exact h.vis_of_done hd
      · exact h.vis_of_stk hys
    · refine h.fin_vis x hx ?_ y hy
      intro hm
      rcases List.mem_cons.1 hm with h' | hxP'
      · exact e h'
      · exact hxP hxP'

theorem tupd_self (f : Nat → Nat) (k : Nat) : tupd f k (f k) = f := by
  funext j
  by_cases e : j = k
  · subst e; simp [tupd]
  · simp [tupd, e]

/-- A finished non-root vertex stays on the stack; the parent takes the minimum of its lowlink and the child's. -/
theorem TInv.keep {P : List Nat} {s : TState} {v p : Nat} {P0 : List Nat} (h : TInv g (v :: P) s) (hP : P = p :: P0)
    (hpv : g.Reach p v) (hlow : s.low v ≠ s.num v)
    (hex : ∀ y, g.edge v y → s.Done y ∨ (y ∈ s.stk ∧ s.low v ≤ s.num y)) (t : Nat) :
    TInv g P { s with low := tupd s.low p (min (s.low p) (s.low v)), ticks := t } := by
  subst hP
  have hvs : v ∈ s.stk := h.P_sub v List.mem_cons_self
  have hps : p ∈ s.stk := h.P_sub p (List.mem_cons_of_mem _ List.mem_cons_self)
  have hpl : s.num p < s.num v := (List.pairwise_cons.1 h.P_sorted).1 p List.mem_cons_self
  have hPh : ∀ q ∈ p :: P0, s.num q ≤ s.num p := fun q hq => h.head_max (P := v :: p :: P0) (p := v) rfl (List.mem_cons_of_mem _ hq) |> fun _ => by
    rcases List.mem_cons.1 hq with rfl | hq
    · exact Nat.le_refl _
    · exact Nat.le_of_lt ((List.pairwise_cons.1 (List.pairwise_cons.1 h.P_sorted).2).1 q hq)
  have hvp : v ≠ p := fun e => by subst e; omega
  have hlvl : s.low v < s.num v := by
    have := (h.low_le v hvs).2; omega
  have hL : tupd s.low p (min (s.low p) (s.low v)) p = min (s.low p) (s.low v) := tupd_same _ _ _
  have hLn : ∀ j, j ≠ p → tupd s.low p (min (s.low p) (s.low v)) j = s.low j := fun j hj => tupd_ne _ _ hj
  have hLle : ∀ j, tupd s.low p (min (s.low p) (s.low v)) j ≤ s.low j := by
    intro j
    by_cases e : j = p
    · subst e; rw [hL]; omega
    · rw [hLn j e]; exact Nat.le_refl _
  have hnP : ∀ x, x ∉ v :: p :: P0 → x ≠ p := fun x hx e => hx (e ▸ List.mem_cons_of_mem _ List.mem_cons_self)
  refine ⟨h.stk_lt, h.done_lt, h.vis_iff, h.disj, h.stk_nodup, h.out_nodup, h.num_le, ?_, ?_, ?_, h.closed_out,
    h.scc_out, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q hq; exact h.P_sub q (List.mem_cons_of_mem _ hq)
  · exact (List.pairwise_cons.1 h.P_sorted).2
  · intro q hq w hw hqw; exact h.reach_P q (List.mem_cons_of_mem _ hq) w hw hqw
  · intro w hw
    show 1 ≤ tupd s.low p (min (s.low p) (s.low v)) w ∧ tupd s.low p (min (s.low p) (s.low v)) w ≤ s.num w
    by_cases e : w = p
    · subst e
      rw [hL]
      have := h.low_le w hps
      have := h.low_le v hvs
      omega
    · rw [hLn w e]; exact h.low_le w hw
  · intro w hw hlw
    by_cases e : w = p
    · subst e
      have hlw' : min (s.low w) (s.low v) < s.num w := by rw [← hL]; exact hlw
      by_cases c : s.low v < s.low w
      · obtain ⟨y, hy, hny, hry⟩ := h.low_wit v hvs hlvl
        refine ⟨y, hy, ?_, hpv.trans hry⟩
        show s.num y = tupd s.low w (min (s.low w) (s.low v)) w
        rw [hL, hny]; omega
      · have c' : s.low w < s.num w := by omega
        obtain ⟨y, hy, hny, hry⟩ := h.low_wit w hw c'
        refine ⟨y, hy, ?_, hry⟩
        show s.num y = tupd s.low w (min (s.low w) (s.low v)) w
        rw [hL, hny]; omega
    · have hlw' : s.low w < s.num w := by rw [← hLn w e]; exact hlw
      obtain ⟨y, hy, hny, hry⟩ := h.low_wit w hw hlw'
      exact ⟨y, hy, by show s.num y = tupd s.low p _ w; rw [hLn w e]; exact hny, hry⟩
  · intro w hw hwP
    show tupd s.low p (min (s.low p) (s.low v)) w < s.num w
    by_cases e : w = v
    · subst e
      rw [hLn w hvp]; exact hlvl
    · have hn : w ∉ v :: p :: P0 := by
        intro hm
        rcases List.mem_cons.1 hm with h' | h'
        · exact e h'
        · exact hwP h'
      rw [hLn w (hnP w hn)]; exact h.fin_low w hw hn
  · intro q hq w hw hwP hqw hmin
    have hqw : s.num q < s.num w := hqw
    have hmin : ∀ r ∈ p :: P0, s.num r < s.num w → s.num r ≤ s.num q := hmin
    show tupd s.low p (min (s.low p) (s.low v)) q ≤ tupd s.low p (min (s.low p) (s.low v)) w
    by_cases e : w = v
    · subst e
      rw [hLn w hvp]
      have hqp : q = p := by
        rcases List.mem_cons.1 hq with rfl | hq0
        · rfl
        · have h1 := hmin p List.mem_cons_self hpl
          have h2 := (List.pairwise_cons.1 (List.pairwise_cons.1 h.P_sorted).2).1 q hq0
          exact absurd (Nat.lt_of_le_of_lt h1 h2) (Nat.lt_irrefl _)
      subst hqp
      rw [hL]; omega
    · have hn : w ∉ v :: p :: P0 := by
        intro hm
        rcases List.mem_cons.1 hm with h' | h'
        · exact e h'
        · exact hwP h'
      rw [hLn w (hnP w hn)]
      by_cases c : s.num v < s.num w
      · have hqp : q = p := by
          rcases List.mem_cons.1 hq with rfl | hq0
          · rfl
          · have h1 := hmin p List.mem_cons_self (Nat.lt_trans hpl c)
            have h2 := (List.pairwise_cons.1 (List.pairwise_cons.1 h.P_sorted).2).1 q hq0
            exact absurd (Nat.lt_of_le_of_lt h1 h2) (Nat.lt_irrefl _)
        subst hqp
        have h3 := h.low_min v List.mem_cons_self w hw hn c (fun r hr hrw => by
          rcases List.mem_cons.1 hr with rfl | hr0
          · exact Nat.le_refl _
          · have := (List.pairwise_cons.1 h.P_sorted).1 r hr0; omega)
        rw [hL]; omega
      · have h3 := h.low_min q (List.mem_cons_of_mem _ hq) w hw hn hqw (fun r hr hrw => by
          rcases List.mem_cons.1 hr with rfl | hr0
          · omega
          · exact hmin r hr0 hrw)
        exact Nat.le_trans (hLle q) h3
  · intro x hx hxP y hy
    show s.Done y ∨ (y ∈ s.stk ∧ tupd s.low p (min (s.low p) (s.low v)) x ≤ s.num y)
    by_cases e : x = v
    · subst e
      rw [hLn x hvp]; exact hex y hy
    · have hn : x ∉ v :: p :: P0 := by
        intro hm
        rcases List.mem_cons.1 hm with h' | h'
        · exact e h'
        · exact hxP h'
      rw [hLn x (hnP x hn)]; exact h.fin_edge x hx hn y hy
  · intro x hx hxP y hy
    by_cases e : x = v
    · subst e
      rcases hex y hy with hd | ⟨hys, -⟩
      · exact h.vis_of_done hd
      · exact h.vis_of_stk hys
    · refine h.fin_vis x hx ?_ y hy
      intro hm
      rcases List.mem_cons.1 hm with h' | h'
      · exact e h'
      · exact hxP h'

theorem tstate_eq_of_low {s : TState} {L : Nat → Nat} (hL : L = s.low) : ({ s with low := L } : TState) = s := by
  subst hL; rfl

/-- What the end of a visit of `v` needs about its parent: a root visit starts with an empty path and stack, a child
visit has the parent at the head of the path and a path to `v`. -/
abbrev FPar (g : Digraph) (P : List Nat) (v : Nat) (b : List Nat) : Option Nat → Prop
  | none => P = [] ∧ b = []
  | some p => (∃ P0, P = p :: P0) ∧ g.Reach p v

/-- The end of `strongconnect`: pop the component if `v` is a root, otherwise return the lowlink to the parent. -/
theorem tFinish_spec {P : List Nat} {s2 : TState} {v : Nat} {N b : List Nat} {par : Option Nat}
    (h : TInv g (v :: P) s2) (hstk : s2.stk = N ++ v :: b) (hN : ∀ u ∈ N, s2.num v < s2.num u)
    (hb : ∀ y ∈ b, s2.num y < s2.num v)
    (hex : ∀ y, g.edge v y → s2.Done y ∨ (y ∈ s2.stk ∧ s2.low v ≤ s2.num y))
    (hpar : FPar g P v b par) :
    TInv g P (tFinish v par s2) ∧ (tFinish v par s2).num = s2.num ∧ (tFinish v par s2).cnt = s2.cnt ∧
    (∃ R, (tFinish v par s2).out = s2.out ++ R) ∧
    ((tFinish v par s2).stk = b ∨ (tFinish v par s2).stk = N ++ v :: b) ∧
    (∀ w, par ≠ some w → (tFinish v par s2).low w = s2.low w) ∧
    (∀ p, par = some p → (tFinish v par s2).low p ≤ s2.low p ∧
      ((tFinish v par s2).Done v ∨
        (v ∈ (tFinish v par s2).stk ∧ (tFinish v par s2).low p ≤ (tFinish v par s2).num v))) := by
  have hvN : v ∉ N := fun hm => absurd (hN v hm) (Nat.lt_irrefl _)
  have hvstk : v ∈ s2.stk := h.P_sub v List.mem_cons_self
  have hlowle := (h.low_le v hvstk).2
  by_cases hl : s2.low v = s2.num v
  · have hpop := h.pop hstk hN hb hl hex
    cases par with
    | none =>
      have e : tFinish v none s2 = { s2 with stk := b, out := s2.out ++ [N ++ [v]], ticks := s2.ticks + (N ++ [v]).length } := by
        simp only [tFinish, hl, ↓reduceIte, hstk, popTo_split hvN]
      rw [e]
      exact ⟨hpop _, rfl, rfl, ⟨_, rfl⟩, Or.inl rfl, fun _ _ => rfl, fun p hp => absurd hp (by simp)⟩
    | some p0 =>
      obtain ⟨⟨P0, hP⟩, hpv⟩ := hpar
      have hp0 : p0 ∈ s2.stk := h.P_sub p0 (by rw [hP]; exact List.mem_cons_of_mem _ List.mem_cons_self)
      have h1 := (h.low_le p0 hp0).2
      have h2 : s2.num p0 < s2.num v := by
        have := (List.pairwise_cons.1 h.P_sorted).1 p0 (by rw [hP]; exact List.mem_cons_self)
        exact this
      have hs : tupd s2.low p0 (min (s2.low p0) (s2.num v)) = s2.low := by
        rw [Nat.min_eq_left (by omega)]; exact tupd_self _ _
      have e : tFinish v (some p0) s2 = { s2 with stk := b, out := s2.out ++ [N ++ [v]], ticks := s2.ticks + (N ++ [v]).length } := by
        simp only [tFinish, hl, ↓reduceIte, hstk, popTo_split hvN, hs]
      rw [e]
      refine ⟨hpop _, rfl, rfl, ⟨_, rfl⟩, Or.inl rfl, fun _ _ => rfl, ?_⟩
      intro p hp
      exact ⟨Nat.le_refl _, Or.inl ⟨N ++ [v], List.mem_append_right _ (List.mem_singleton_self _),
        List.mem_append_right _ (List.mem_singleton_self _)⟩⟩
  · have hlt : s2.low v < s2.num v := by omega
    cases par with
    | none =>
      exfalso
      obtain ⟨hP0, hb0⟩ := hpar
      obtain ⟨y, hy, hny, -⟩ := h.low_wit v hvstk hlt
      rcases (show y ∈ N ∨ y = v ∨ y ∈ b by
        rw [hstk] at hy; simpa [List.mem_append, List.mem_cons] using hy) with hyN | rfl | hyb
      · have := hN y hyN; omega
      · omega
      · rw [hb0] at hyb; simp at hyb
    | some p0 =>
      obtain ⟨⟨P0, hP⟩, hpv⟩ := hpar
      have hk := h.keep hP hpv hl hex s2.ticks
      have e : tFinish v (some p0) s2 = { s2 with low := tupd s2.low p0 (min (s2.low p0) (s2.low v)) } := by
        simp only [tFinish, hl, ↓reduceIte]
      rw [e]
      refine ⟨hk, rfl, rfl, ⟨[], by simp⟩, Or.inr hstk, ?_, ?_⟩
      · intro w hw
        show tupd s2.low p0 (min (s2.low p0) (s2.low v)) w = s2.low w
        exact tupd_ne _ _ (fun e => hw (by rw [e]))
      intro p hp
      have e : p = p0 := by injection hp with hp; exact hp.symm
      subst e
      refine ⟨?_, Or.inr ⟨hvstk, ?_⟩⟩
      · show tupd s2.low p (min (s2.low p) (s2.low v)) p ≤ s2.low p
        rw [tupd_same]; exact Nat.min_le_left _ _
      · show tupd s2.low p (min (s2.low p) (s2.low v)) p ≤ s2.num v
        rw [tupd_same]; exact Nat.le_trans (Nat.min_le_right _ _) (Nat.le_of_lt hlt)

end SmcIrred
