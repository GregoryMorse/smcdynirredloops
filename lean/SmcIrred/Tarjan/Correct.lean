module

public import SmcIrred.Tarjan.Mono

public section

namespace SmcIrred

variable {g : Digraph}

/-- The successors `ex` of `v` examined so far are visited, and lead to an emitted vertex or to a stacked vertex whose
index is at least the lowlink of `v`. -/
@[expose] def TExam (v : Nat) (s : TState) (ex : List Nat) : Prop :=
  ∀ w ∈ ex, s.num w ≠ 0 ∧ (s.Done w ∨ (w ∈ s.stk ∧ s.low v ≤ s.num w))

theorem TExam.ext {v : Nat} {s t : TState} {ex : List Nat} (h : TExam v s ex) (hm : TMono s t)
    (hl : t.low v ≤ s.low v) : TExam v t ex := by
  intro w hw
  obtain ⟨hn, hd⟩ := h w hw
  refine ⟨by rw [hm.num_eq w hn]; exact hn, ?_⟩
  rcases hd with hd | ⟨hs, hle⟩
  · obtain ⟨R, hR⟩ := hm.out_ext
    obtain ⟨C, hC, hwC⟩ := hd
    exact Or.inl ⟨C, by rw [hR]; exact List.mem_append_left _ hC, hwC⟩
  · obtain ⟨N, hN⟩ := hm.stk_ext
    refine Or.inr ⟨by rw [hN]; exact List.mem_append_right _ hs, ?_⟩
    rw [hm.num_eq w hn]; omega

/-- The specification of a visit with fuel `f`. -/
@[expose] def VSpec (g : Digraph) (f : Nat) : Prop :=
  ∀ (s : TState) (v : Nat) (par : Option Nat) (P : List Nat),
    TInv g P s → v < g.n → s.num v = 0 → tUn s.num g.n ≤ f →
    (match par with | none => P = [] | some p => (∃ P0, P = p :: P0) ∧ g.edge p v) →
    TInv g P (tVisit g f v par s) ∧ (tVisit g f v par s).num v ≠ 0 ∧ TMono s (tVisit g f v par s) ∧
    (∀ w, s.num w ≠ 0 → par ≠ some w → (tVisit g f v par s).low w = s.low w) ∧
    (∀ p, par = some p → (tVisit g f v par s).low p ≤ s.low p ∧
      ((tVisit g f v par s).Done v ∨
        (v ∈ (tVisit g f v par s).stk ∧ (tVisit g f v par s).low p ≤ (tVisit g f v par s).num v)))

theorem scan_spec {f : Nat} (ih : VSpec g f) {v : Nat} {P : List Nat} (ws : List Nat) :
    ∀ (ex : List Nat) (s : TState), TInv g (v :: P) s → tUn s.num g.n ≤ f → (∀ w ∈ ex ++ ws, g.edge v w) →
      TExam v s ex →
      TInv g (v :: P) (tScan (fun w p t => tVisit g f w (some p) t) v ws s) ∧
      TMono s (tScan (fun w p t => tVisit g f w (some p) t) v ws s) ∧
      (tScan (fun w p t => tVisit g f w (some p) t) v ws s).low v ≤ s.low v ∧
      (∀ w, s.num w ≠ 0 → w ≠ v → (tScan (fun w p t => tVisit g f w (some p) t) v ws s).low w = s.low w) ∧
      TExam v (tScan (fun w p t => tVisit g f w (some p) t) v ws s) (ex ++ ws) := by
  induction ws with
  | nil =>
    intro ex s h _ _ hex
    refine ⟨h, TMono.refl s, Nat.le_refl _, fun _ _ _ => rfl, ?_⟩
    rw [List.append_nil]; exact hex
  | cons w ws ihw =>
    intro ex s h hun hed hex
    have hw : g.edge v w := hed w (by simp)
    have hed' : ∀ w' ∈ (ex ++ [w]) ++ ws, g.edge v w' := by
      have : (ex ++ [w]) ++ ws = ex ++ w :: ws := by simp
      rw [this]; exact hed
    obtain ⟨s', hse, hI', hM', hl', hlow', hnew⟩ : ∃ s' : TState,
        tEdge (fun w p t => tVisit g f w (some p) t) v w s = s' ∧ TInv g (v :: P) s' ∧ TMono s s' ∧
        s'.low v ≤ s.low v ∧ (∀ w', s.num w' ≠ 0 → w' ≠ v → s'.low w' = s.low w') ∧
        (s'.num w ≠ 0 ∧ (s'.Done w ∨ (w ∈ s'.stk ∧ s'.low v ≤ s'.num w))) := by
      by_cases h1 : s.num w = 0
      · have e : tEdge (fun w p t => tVisit g f w (some p) t) v w s =
            tVisit g f w (some v) { s with ticks := s.ticks + 1 } := by
          simp only [tEdge, h1, ↓reduceIte]
        have key := ih { s with ticks := s.ticks + 1 } w (some v) (v :: P) (h.tick _) hw.2.1 h1 hun ⟨⟨P, rfl⟩, hw⟩
        obtain ⟨hI, hnv, hM, hlo, hpar⟩ := key
        have hM0 : TMono s { s with ticks := s.ticks + 1 } := TMono.of_fields rfl rfl rfl rfl
        refine ⟨_, e, hI, hM0.trans hM, (hpar v rfl).1, ?_, hnv, (hpar v rfl).2⟩
        intro w' hw' hne
        exact hlo w' hw' (by intro e'; injection e' with e'; exact hne e'.symm)
      · by_cases h2 : w ∈ s.stk
        · have e : tEdge (fun w p t => tVisit g f w (some p) t) v w s =
              { { s with ticks := s.ticks + 1 } with
                low := tupd s.low v (min (s.low v) (s.num w)) } := by
            simp only [tEdge, h1, h2, ↓reduceIte]
          refine ⟨_, e, (h.tick (s.ticks + 1)).lowStep h2 hw, TMono.of_fields rfl rfl rfl rfl, ?_, ?_, ?_⟩
          · show tupd s.low v (min (s.low v) (s.num w)) v ≤ s.low v
            rw [tupd_same]; exact Nat.min_le_left _ _
          · intro w' _ hne
            exact tupd_ne _ _ hne
          · refine ⟨h1, Or.inr ⟨h2, ?_⟩⟩
            show tupd s.low v (min (s.low v) (s.num w)) v ≤ s.num w
            rw [tupd_same]; exact Nat.min_le_right _ _
        · have e : tEdge (fun w p t => tVisit g f w (some p) t) v w s = { s with ticks := s.ticks + 1 } := by
            simp only [tEdge, h1, h2, ↓reduceIte]
          have hd : s.Done w := by
            rcases (h.vis_iff w).1 h1 with hs | hd
            · exact absurd hs h2
            · exact hd
          exact ⟨_, e, h.tick _, TMono.of_fields rfl rfl rfl rfl, Nat.le_refl _, fun _ _ _ => rfl, h1, Or.inl hd⟩
    rw [show tScan (fun w p t => tVisit g f w (some p) t) v (w :: ws) s =
        tScan (fun w p t => tVisit g f w (some p) t) v ws (tEdge (fun w p t => tVisit g f w (some p) t) v w s) from rfl,
      hse]
    have hun' : tUn s'.num g.n ≤ f :=
      Nat.le_trans (tUn_mono (fun w' hw' => by rw [hM'.num_eq w' hw']; exact hw') g.n) hun
    have hex' : TExam v s' (ex ++ [w]) := by
      intro w' hw'
      rcases List.mem_append.1 hw' with hw' | hw'
      · exact hex.ext hM' hl' w' hw'
      · rw [List.mem_singleton] at hw'; subst hw'; exact hnew
    obtain ⟨hI2, hM2, hl2, hlow2, hE2⟩ := ihw (ex ++ [w]) s' hI' hun' hed' hex'
    refine ⟨hI2, hM'.trans hM2, Nat.le_trans hl2 hl', ?_, ?_⟩
    · intro w' hw' hne
      rw [hlow2 w' (by rw [hM'.num_eq w' hw']; exact hw') hne]
      exact hlow' w' hw' hne
    · have : (ex ++ [w]) ++ ws = ex ++ w :: ws := by simp
      rw [this] at hE2; exact hE2

theorem visit_spec (g : Digraph) : ∀ f, VSpec g f := by
  intro f
  induction f with
  | zero =>
    intro s v par P h hv hn hun _
    exfalso
    have := tUn_pos (s := s) hv hn
    have : tUn s.num g.n ≤ 0 := hun
    omega
  | succ f ih =>
    intro s v par P h hv hn hun hpar
    have hreach : ∀ p ∈ P, g.Reach p v := by
      cases par with
      | none =>
        have hP : P = [] := hpar
        intro p hp; rw [hP] at hp; simp at hp
      | some p0 =>
        obtain ⟨⟨P0, hP⟩, hed⟩ := hpar
        intro q hq
        have hp0 : s.num p0 ≠ 0 := h.vis_of_stk (h.P_sub p0 (by rw [hP]; exact List.mem_cons_self))
        exact (h.reach_P q hq p0 hp0 (h.head_max hP hq)).trans (.step hed (.refl v))
    obtain ⟨s1, hs1⟩ : ∃ s1 : TState, s1 = { s with cnt := s.cnt + 1, num := tupd s.num v (s.cnt + 1), low := tupd s.low v (s.cnt + 1), stk := v :: s.stk, ticks := s.ticks + 1 } := ⟨_, rfl⟩
    have h1 : TInv g (v :: P) s1 := by rw [hs1]; exact h.enter hv hn hreach
    have hs1num : ∀ w, w ≠ v → s1.num w = s.num w := by intro w hw; rw [hs1]; exact tupd_ne _ _ hw
    have hs1low : ∀ w, w ≠ v → s1.low w = s.low w := by intro w hw; rw [hs1]; exact tupd_ne _ _ hw
    have hs1v : s1.num v = s.cnt + 1 := by rw [hs1]; exact tupd_same _ _ _
    have hs1cnt : s1.cnt = s.cnt + 1 := by rw [hs1]
    have hs1stk : s1.stk = v :: s.stk := by rw [hs1]
    have hs1out : s1.out = s.out := by rw [hs1]
    have hvs : ∀ w, s.num w ≠ 0 → w ≠ v := fun w hw e => hw (by rw [e]; exact hn)
    have hmono1 : ∀ w, s.num w ≠ 0 → s1.num w ≠ 0 := by
      intro w hw; rw [hs1num w (hvs w hw)]; exact hw
    have hun1 : tUn s1.num g.n ≤ f := by
      have := tUn_lt hmono1 hn (by rw [hs1v]; omega) g.n hv
      omega
    have hM01 : TMono s s1 := by
      refine ⟨⟨fun w hw => hs1num w (hvs w hw), ⟨[], by simp [hs1out]⟩, by rw [hs1cnt]; omega, ?_⟩,
        ⟨[v], by simp [hs1stk]⟩⟩
      intro w h0 h1'
      by_cases e : w = v
      · subst e; rw [hs1v]; omega
      · rw [hs1num w e] at h1'; exact absurd h0 h1'
    have hedges : ∀ w ∈ [] ++ tsuccs g v, g.edge v w := by
      intro w hw
      simp [tsuccs, List.mem_filter] at hw
      exact ⟨hv, hw.2, hw.1⟩
    obtain ⟨hI2, hM12, hl2, hlow2, hE2⟩ :=
      scan_spec ih (tsuccs g v) [] s1 h1 hun1 hedges (by intro w hw; simp at hw)
    obtain ⟨s2, hs2⟩ : ∃ s2, s2 = tScan (fun w p t => tVisit g f w (some p) t) v (tsuccs g v) s1 := ⟨_, rfl⟩
    rw [← hs2] at hI2 hM12 hl2 hlow2 hE2
    have hT : tVisit g (f + 1) v par s = tFinish v par s2 := by rw [hs2, hs1]; rfl
    rw [hT]
    obtain ⟨N, hNeq⟩ := hM12.stk_ext
    have hstk : s2.stk = N ++ v :: s.stk := by rw [hNeq, hs1stk]
    have hnd := hI2.stk_nodup
    rw [hNeq, List.nodup_append] at hnd
    obtain ⟨-, -, hdisjN⟩ := hnd
    have hv2 : s2.num v = s.cnt + 1 := by
      rw [hM12.num_eq v (by rw [hs1v]; omega), hs1v]
    have hN : ∀ u ∈ N, s2.num v < s2.num u := by
      intro u hu
      have hus : u ∈ s2.stk := by rw [hNeq]; exact List.mem_append_left _ hu
      have hn2 : s2.num u ≠ 0 := hI2.vis_of_stk hus
      have hs1u : s1.num u = 0 := by
        refine Classical.byContradiction fun hne => ?_
        rcases (h1.vis_iff u).1 hne with hst | hdn
        · exact hdisjN u hu u hst rfl
        · obtain ⟨R, hR⟩ := hM12.out_ext
          obtain ⟨C, hC, huC⟩ := hdn
          exact hI2.disj u hus ⟨C, by rw [hR]; exact List.mem_append_left _ hC, huC⟩
      have := hM12.num_new u hs1u hn2
      rw [hv2]; rw [hs1cnt] at this; exact this
    have hb : ∀ y ∈ s.stk, s2.num y < s2.num v := by
      intro y hy
      have hyv := hvs y (h.vis_of_stk hy)
      rw [hM12.num_eq y (hmono1 y (h.vis_of_stk hy)), hs1num y hyv, hv2]
      exact Nat.lt_succ_of_le (h.num_le y)
    have hex : ∀ y, g.edge v y → s2.Done y ∨ (y ∈ s2.stk ∧ s2.low v ≤ s2.num y) := by
      intro y hy
      have : y ∈ [] ++ tsuccs g v := by
        simp [tsuccs, List.mem_filter]; exact ⟨hy.2.2, hy.2.1⟩
      exact (hE2 y this).2
    have hpar' : FPar g P v s.stk par := by
      cases par with
      | none =>
        have hP : P = [] := hpar
        subst hP
        exact ⟨rfl, h.stk_nil⟩
      | some p0 =>
        obtain ⟨hP, hed⟩ := hpar
        exact ⟨hP, .step hed (.refl v)⟩
    obtain ⟨hIe, hne, hce, ⟨R, hRe⟩, hstke, hlowE, hlast⟩ := tFinish_spec hI2 hstk hN hb hex hpar'
    have hc01 := hM01.toTCore
    have hc12 := hM12.toTCore
    have hc2e : TCore s2 (tFinish v par s2) :=
      ⟨fun w _ => by rw [hne], ⟨R, hRe⟩, by rw [hce]; exact Nat.le_refl _,
        fun w h0 h1' => by rw [hne] at h1'; exact absurd h0 h1'⟩
    refine ⟨hIe, ?_, ⟨(hc01.trans hc12).trans hc2e, ?_⟩, ?_, ?_⟩
    · rw [hne, hv2]; omega
    · rcases hstke with e | e
      · exact ⟨[], by simp [e]⟩
      · exact ⟨N ++ [v], by simp [e]⟩
    · intro w hw hpw
      rw [hlowE w hpw, hlow2 w (hmono1 w hw) (hvs w hw), hs1low w (hvs w hw)]
    · intro p hp
      obtain ⟨hlp, hrest⟩ := hlast p hp
      subst hp
      obtain ⟨⟨P0, hP⟩, -⟩ := hpar
      have hpn : s.num p ≠ 0 := h.vis_of_stk (h.P_sub p (by rw [hP]; exact List.mem_cons_self))
      refine ⟨?_, hrest⟩
      rw [hlow2 p (hmono1 p hpn) (hvs p hpn), hs1low p (hvs p hpn)] at hlp
      exact hlp

theorem tRun_spec (g : Digraph) : ∀ (vs : List Nat) (s : TState), TInv g [] s → (∀ v ∈ vs, v < g.n) →
    TInv g [] (tRun g vs s) ∧ (∀ w, s.num w ≠ 0 → (tRun g vs s).num w ≠ 0) ∧
    (∀ v ∈ vs, (tRun g vs s).num v ≠ 0) := by
  intro vs
  induction vs with
  | nil => intro s h _; exact ⟨h, fun w hw => hw, by simp⟩
  | cons v vs ih =>
    intro s h hv
    have hv0 : v < g.n := hv v List.mem_cons_self
    have hvs : ∀ w ∈ vs, w < g.n := fun w hw => hv w (List.mem_cons_of_mem _ hw)
    obtain ⟨s', hs'e, hI', hmon, hvis⟩ : ∃ s' : TState,
        (if s.num v = 0 then tVisit g g.n v none s else s) = s' ∧ TInv g [] s' ∧
        (∀ w, s.num w ≠ 0 → s'.num w ≠ 0) ∧ s'.num v ≠ 0 := by
      by_cases h0 : s.num v = 0
      · have key := visit_spec g g.n s v none [] h hv0 h0 (tUn_le s g.n) rfl
        exact ⟨_, by simp [h0], key.1, fun w hw => by rw [key.2.2.1.num_eq w hw]; exact hw, key.2.1⟩
      · exact ⟨s, by simp [h0], h, fun w hw => hw, h0⟩
    show TInv g [] (tRun g vs (if s.num v = 0 then tVisit g g.n v none s else s)) ∧
      (∀ w, s.num w ≠ 0 → (tRun g vs (if s.num v = 0 then tVisit g g.n v none s else s)).num w ≠ 0) ∧
      (∀ v' ∈ v :: vs, (tRun g vs (if s.num v = 0 then tVisit g g.n v none s else s)).num v' ≠ 0)
    rw [hs'e]
    obtain ⟨hI2, hmon2, hvis2⟩ := ih s' hI' hvs
    refine ⟨hI2, fun w hw => hmon2 w (hmon w hw), ?_⟩
    intro w hw
    rcases List.mem_cons.1 hw with rfl | hw
    · exact hmon2 w hvis
    · exact hvis2 w hw

/-- **Tarjan's algorithm is correct** (C08, C21): the emitted lists are exactly the strongly connected components of the
graph, each exactly once, and a component is emitted only after every component it reaches (reverse topological
order). -/
theorem tarjan_spec (g : Digraph) :
    (∀ C ∈ tarjanSccs g, ∀ u ∈ C, ∀ w, (w ∈ C ↔ g.SameSCC u w)) ∧
    (∀ v, v < g.n → ∃ C ∈ tarjanSccs g, v ∈ C) ∧
    (tarjanSccs g).flatten.Nodup ∧
    (∀ C ∈ tarjanSccs g, ∀ w ∈ C, w < g.n) ∧
    (∀ L C R, tarjanSccs g = L ++ C :: R → ∀ u ∈ C, ∀ w, g.edge u w → w ∈ C ∨ ∃ C' ∈ L, w ∈ C') := by
  obtain ⟨hI, -, hvis⟩ := tRun_spec g (List.range g.n) TState.init (TInv.init g) (by intro v hv; simpa using hv)
  have hstk : (tarjan g).stk = [] := hI.stk_nil
  refine ⟨hI.scc_out, ?_, hI.out_nodup, hI.done_lt, hI.closed_out⟩
  intro v hv
  have hn : (tarjan g).num v ≠ 0 := hvis v (List.mem_range.2 hv)
  rcases (hI.vis_iff v).1 hn with hs | hd
  · have hs' : v ∈ (tarjan g).stk := hs
    rw [hstk] at hs'; simp at hs'
  · exact hd

end SmcIrred
