module

public import SmcIrred.Smc.Sim

public section

namespace SmcIrred

variable {g : Digraph}

theorem sEnter_dep (w : Nat) (s : SState) : (sEnter w s).dep w = (sEnter w s).stk.length := by
  simp [sEnter, fupd]

theorem sEnter_dep_ne (w u : Nat) (s : SState) (h : u ≠ w) : (sEnter w s).dep u = s.dep u := by
  simp [sEnter, fupd, h]

theorem sPre_dep (x w : Nat) (s : SState) : (sPre x w s).dep = s.dep := by
  unfold sPre; by_cases hc : s.stk.length = s.dep x <;> simp [hc]

theorem sStep_dep (x : Nat) (rs : Nat × SState) : (sStep x rs).dep = rs.2.dep := by
  unfold sStep; by_cases hc : rs.1 < rs.2.low x <;> simp [hc]

theorem tEnterSt_mono (t : TState) (w : Nat) (hw0 : t.num w = 0) : ∀ u, t.num u ≠ 0 → (tEnterSt t w).num u ≠ 0 := by
  intro u hu
  have e : u ≠ w := fun e => hu (e ▸ hw0)
  simpa [tEnterSt, tupd_ne _ _ e] using hu

/-- The end of a visit: the finish of `w` and the caller's lowlink update. -/
theorem visit_close (g : Digraph) {t tS : TState} {s s1 sL : SState} {pend pend2 : Option Nat} {x w : Nat}
    (h : ScanQ g x t s pend) (hw0 : t.num w = 0)
    (hs1dep : s1.dep w = t.stk.length) (hs1dep' : ∀ u, u ≠ w → s1.dep u = s.dep u)
    (hq2 : ScanQ g w tS sL pend2) (hp2 : VPost (tEnterSt t w) tS s1 sL) :
    ScanQ g x (tFinish w (some x) tS) (sStep x ((sLeave g.n w sL).low w, sLeave g.n w sL)) none ∧
    VPost t (tFinish w (some x) tS) s (sStep x ((sLeave g.n w sL).low w, sLeave g.n w sL)) := by
  have hm := tEnterSt_mono t w hw0
  have hxw : x ≠ w := fun e => h.vis (e ▸ hw0)
  have hx1 : (tEnterSt t w).num x ≠ 0 := hm x h.vis
  have hw1 : (tEnterSt t w).num w ≠ 0 := by simp [tEnterSt, tupd]
  obtain ⟨Nw, tlw, e1, e2, e3⟩ := hq2.shape
  obtain ⟨N', e4⟩ := hp2.stk
  have e4' : tS.stk = N' ++ w :: t.stk := e4
  have hdw : sL.dep w = s1.dep w := hp2.dep w hw1
  have hlen : tlw.length = t.stk.length := by rw [← e2, hdw, hs1dep]
  have hinj := List.append_inj' (e4'.symm.trans e1) (by simp [hlen])
  have htl : tlw = t.stk := (List.cons.inj hinj.2).2.symm
  obtain ⟨hl1, hl2, hl3, hl4, hl5, hl6⟩ := ssim_leave hq2.rel hq2.hp hq2.vis e1 e2 e3
  have hxS : tS.num x ≠ 0 := hp2.mono x hx1
  have hx3 : (tFinish w none tS).num x ≠ 0 := by rw [hl5]; exact hxS
  have hw3 : (tFinish w none tS).num w ≠ 0 := by rw [hl5]; exact hq2.vis
  have hpar := ssim_parent hl1 hx3 hw3
  have hdepu : ∀ u, t.num u ≠ 0 → (sStep x ((sLeave g.n w sL).low w, sLeave g.n w sL)).dep u = s.dep u := by
    intro u hu
    have hne : u ≠ w := fun e => hu (e ▸ hw0)
    rw [sStep_dep]
    show (sLeave g.n w sL).dep u = s.dep u
    rw [hl3, hp2.dep u (hm u hu), hs1dep' u hne]
  rw [tFinish_some]
  obtain ⟨N0, tl0, f1, f2, _⟩ := h.shape
  refine ⟨⟨hpar, Or.inl rfl, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rcases hl4 with hA | hB
    · refine ⟨N0, tl0, ?_, ?_, fun hh => absurd hh (by simp)⟩
      · show (tFinish w none tS).stk = _
        rw [hA, htl, f1]
      · rw [hdepu x h.vis, f2]
    · refine ⟨N' ++ w :: N0, tl0, ?_, ?_, fun hh => absurd hh (by simp)⟩
      · show (tFinish w none tS).stk = _
        rw [hB, e4', f1]; simp
      · rw [hdepu x h.vis, f2]
  · exact hx3
  · intro u hu
    show (tFinish w none tS).num u ≠ 0
    rw [hl5]
    exact hp2.mono u (hm u hu)
  · rcases hl4 with hA | hB
    · exact ⟨[], by show (tFinish w none tS).stk = _; rw [hA, htl]; simp⟩
    · exact ⟨N' ++ [w], by show (tFinish w none tS).stk = _; rw [hB, e4']; simp⟩
  · exact hdepu

theorem ssim_visit (g : Digraph) : ∀ (F : Nat) (w : Nat) (t : TState) (s : SState) (pend : Option Nat) (x : Nat),
    ScanQ g x t s pend → t.num w = 0 → w < g.n → tUn t.num g.n ≤ F →
    ScanQ g x (tVisit (revG g) F w (some x) t) (sStep x (sCall g F x w s)) none ∧
    VPost t (tVisit (revG g) F w (some x) t) s (sStep x (sCall g F x w s)) := by
  intro F
  induction F with
  | zero =>
    intro w t s pend x h hw0 hwn hun
    have := tUn_pos (s := t) hwn hw0
    omega
  | succ f ih =>
    intro w t s pend x h hw0 hwn hun
    have hent : (sPre x w s).ent w = none := by rw [sPre_ent]; exact (h.rel.none_iff w).2 hw0
    rw [sCall_unvisited f x w s hent, tVisit_succ]
    have hb : sBody g (sCall g f) w (sPre x w s) =
        ((sLeave g.n w (sLoop (sCall g f) w (tsuccs (revG g) w) (sEnter w (sPre x w s)))).low w,
          sLeave g.n w (sLoop (sCall g f) w (tsuccs (revG g) w) (sEnter w (sPre x w s)))) := rfl
    rw [hb]
    have hrel1 := ssim_enter_call h.rel hw0 hwn (scanQ_pend h) h.hp
    have hdep1 : (sEnter w (sPre x w s)).dep w = t.stk.length := by
      obtain ⟨tl, e1, e2⟩ := hrel1.stk
      have e1' : w :: t.stk = w :: tl := e1
      have htl : tl = t.stk := (List.cons.inj e1').2.symm
      rw [sEnter_dep, e2, htl]; simp
    have hq1 : ScanQ g w (tEnterSt t w) (sEnter w (sPre x w s)) (some w) :=
      ⟨hrel1, Or.inr rfl, ⟨[], t.stk, by simp [tEnterSt], hdep1, fun _ => rfl⟩, by simp [tEnterSt, tupd]⟩
    have hun1 : tUn (tEnterSt t w).num g.n ≤ f := by
      have := tUn_lt (s := t) (t := tEnterSt t w) (tEnterSt_mono t w hw0) hw0 (by simp [tEnterSt, tupd]) g.n hwn
      omega
    have hws : ∀ w' ∈ tsuccs (revG g) w, w' < g.n := by
      intro w' hm
      have := (List.mem_filter.1 hm).2
      exact of_decide_eq_true this
    obtain ⟨pend2, hq2, hp2⟩ := ssim_scan g w f
      (fun w' t' s' pend' hq hz hn hu => ih w' t' s' pend' w hq hz hn hu) _ _ _ _ hq1 hws hun1
    have hs1dep' : ∀ u, u ≠ w → (sEnter w (sPre x w s)).dep u = s.dep u := by
      intro u hne
      rw [sEnter_dep_ne _ _ _ hne, sPre_dep]
    exact visit_close g h hw0 hdep1 hs1dep' hq2 hp2

/-- A visit started by the outer loop (the call cell is `none`). -/
theorem ssim_top (g : Digraph) (f : Nat) (hf : g.n = f + 1) {t : TState} {s : SState} (h : SRel g t s none) {w : Nat}
    (hw0 : t.num w = 0) (hwn : w < g.n) :
    SRel g (tVisit (revG g) (f + 1) w none t) (sBody g (sCall g f) w { s with stk := none :: s.stk }).2 none := by
  rw [tVisit_succ]
  have hrel1 := ssim_enter_top h hw0 hwn
  have hdep1 : (sEnter w { s with stk := none :: s.stk }).dep w = t.stk.length := by
    obtain ⟨tl, e1, e2⟩ := hrel1.stk
    have e1' : w :: t.stk = w :: tl := e1
    have htl : tl = t.stk := (List.cons.inj e1').2.symm
    rw [sEnter_dep, e2, htl]; simp
  have hq1 : ScanQ g w (tEnterSt t w) (sEnter w { s with stk := none :: s.stk }) (some w) :=
    ⟨hrel1, Or.inr rfl, ⟨[], t.stk, by simp [tEnterSt], hdep1, fun _ => rfl⟩, by simp [tEnterSt, tupd]⟩
  have hun1 : tUn (tEnterSt t w).num g.n ≤ f := by
    have := tUn_lt (s := t) (t := tEnterSt t w) (tEnterSt_mono t w hw0) hw0 (by simp [tEnterSt, tupd]) g.n hwn
    have := tUn_le t g.n
    omega
  have hws : ∀ w' ∈ tsuccs (revG g) w, w' < g.n := by
    intro w' hm
    exact of_decide_eq_true (List.mem_filter.1 hm).2
  obtain ⟨pend2, hq2, hp2⟩ := ssim_scan g w f
    (fun w' t' s' pend' hq hz hn hu => ssim_visit g f w' t' s' pend' w hq hz hn hu) _ _ _ _ hq1 hws hun1
  have hl := (ssim_leave hq2.rel hq2.hp hq2.vis hq2.shape.choose_spec.choose_spec.1 hq2.shape.choose_spec.choose_spec.2.1
    hq2.shape.choose_spec.choose_spec.2.2).1
  exact hl

theorem sRun_sim (g : Digraph) (f : Nat) (hf : f = g.n - 1) : ∀ (vs : List Nat) (t : TState) (s : SState),
    SRel g t s none → (∀ v ∈ vs, v < g.n) → SRel g (tRun (revG g) vs t) (sRun g f vs s) none := by
  intro vs
  induction vs with
  | nil => intro t s h _; exact h
  | cons v vs ih =>
    intro t s h hv
    have hvn : v < g.n := hv v List.mem_cons_self
    have hvs : ∀ u ∈ vs, u < g.n := fun u hu => hv u (List.mem_cons_of_mem _ hu)
    have hf' : g.n = f + 1 := by omega
    show SRel g (tRun (revG g) vs (if t.num v = 0 then tVisit (revG g) (revG g).n v none t else t)) _ none
    by_cases h0 : t.num v = 0
    · have he : s.ent v = none := (h.none_iff v).2 h0
      have hn : (revG g).n = f + 1 := hf'
      simp only [h0, ↓reduceIte, hn]
      have e : sRun g f (v :: vs) s = sRun g f vs (sBody g (sCall g f) v { s with stk := none :: s.stk }).2 := by
        simp only [sRun, he]
      rw [e]
      exact ih _ _ (ssim_top g f hf' h h0 hvn) hvs
    · have hne : s.ent v ≠ none := fun e => h0 ((h.none_iff v).1 e)
      obtain ⟨k, hk⟩ : ∃ k, s.ent v = some k := by
        cases hh : s.ent v
        · exact absurd hh hne
        · exact ⟨_, rfl⟩
      simp only [h0, ↓reduceIte]
      have e : sRun g f (v :: vs) s = sRun g f vs s := by simp only [sRun, hk]
      rw [e]
      exact ih _ _ h hvs

end SmcIrred
