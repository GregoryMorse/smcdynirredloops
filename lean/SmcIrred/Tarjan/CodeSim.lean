module

public import SmcIrred.Tarjan.Cost
public import SmcIrred.Spec.TarjanCode

public section

namespace SmcIrred

/-- The simulation between a run of the literal C++ model `c` and the same run of the clean model `m`, relative to the
starting states `m0`, `c0`: same counter, indices and lowlinks; the C++ stack is the clean stack on top of leftover
entries; the `onstack` flags are membership in the clean stack; both output vectors grew by the same suffix. -/
structure CSim (m0 : TState) (c0 : CState) (m : TState) (c : CState) : Prop where
  cnt : c.cnt = m.cnt
  num : c.num = m.num
  low : c.low = m.low
  stk : ∃ G, c.stk = m.stk ++ G
  on : ∀ w, c.on w = true ↔ w ∈ m.stk
  out : ∃ R, m.out = m0.out ++ R ∧ c.out = c0.out ++ R
  nodup : m.stk.Nodup
  vis : ∀ x ∈ m.stk, m.num x ≠ 0

/-- What a visit does to the clean state: it simulates, and it only pushes fresh vertices on the stack. -/
structure CPost (m0 : TState) (c0 : CState) (m : TState) (m' : TState) (c' : CState) : Prop where
  sim : CSim m0 c0 m' c'
  stk : ∃ N, N.Nodup ∧ m'.stk = N ++ m.stk ∧ ∀ x ∈ N, m.num x = 0
  mono : ∀ x, m.num x ≠ 0 → m'.num x ≠ 0

variable {m0 : TState} {c0 : CState}

theorem CPost.refl {m : TState} {c : CState} (h : CSim m0 c0 m c) : CPost m0 c0 m m c :=
  ⟨h, ⟨[], List.nodup_nil, by simp, by simp⟩, fun _ h => h⟩

theorem CSim.tick {m : TState} {c : CState} (h : CSim m0 c0 m c) (t : Nat) : CSim m0 c0 { m with ticks := t } c :=
  ⟨h.cnt, h.num, h.low, h.stk, h.on, h.out, h.nodup, h.vis⟩

theorem CPost.tickL {m m' : TState} {c' : CState} (t : Nat) (h : CPost m0 c0 { m with ticks := t } m' c') :
    CPost m0 c0 m m' c' := ⟨h.sim, h.stk, h.mono⟩

theorem CPost.tickR {m : TState} {c : CState} (h : CSim m0 c0 m c) (t : Nat) :
    CPost m0 c0 m { m with ticks := t } c :=
  ⟨h.tick t, ⟨[], List.nodup_nil, by simp, by simp⟩, fun _ hx => hx⟩

theorem CPost.trans {m m1 m2 : TState} {c2 : CState} {c1 : CState} (h1 : CPost m0 c0 m m1 c1)
    (h2 : CPost m0 c0 m1 m2 c2) : CPost m0 c0 m m2 c2 where
  sim := h2.sim
  stk := by
    obtain ⟨N1, n1, e1, f1⟩ := h1.stk
    obtain ⟨N2, n2, e2, f2⟩ := h2.stk
    refine ⟨N2 ++ N1, ?_, by rw [e2, e1, List.append_assoc], ?_⟩
    · rw [List.nodup_append]
      refine ⟨n2, n1, ?_⟩
      intro x hx y hy hxy
      subst hxy
      have h3 := f2 x hx
      have h4 : x ∈ m1.stk := by rw [e1]; exact List.mem_append_left _ hy
      exact h1.sim.vis x h4 h3
    · intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · have := f2 x hx
        exact Classical.byContradiction fun hne => (h1.mono x hne) this
      · exact f1 x hx
  mono := fun x hx => h2.mono x (h1.mono x hx)

theorem sim_enter {m : TState} {c : CState} (h : CSim m0 c0 m c) {v : Nat} (hn : m.num v = 0) :
    CSim m0 c0 { m with cnt := m.cnt + 1, num := tupd m.num v (m.cnt + 1), low := tupd m.low v (m.cnt + 1),
                        stk := v :: m.stk, ticks := m.ticks + 1 } (cEnter v c) := by
  have hcn : c.num v = 0 := by rw [h.num]; exact hn
  have hvs : v ∉ m.stk := fun hv => h.vis v hv hn
  unfold cEnter
  simp only [hcn, ↓reduceIte]
  obtain ⟨G, hG⟩ := h.stk
  obtain ⟨R, hR1, hR2⟩ := h.out
  refine ⟨?_, ?_, ?_, ⟨G, ?_⟩, ?_, ⟨R, hR1, hR2⟩, ?_, ?_⟩
  · show c.cnt + 1 = m.cnt + 1; rw [h.cnt]
  · show tupd c.num v (c.cnt + 1) = tupd m.num v (m.cnt + 1); rw [h.num, h.cnt]
  · show tupd c.low v (c.cnt + 1) = tupd m.low v (m.cnt + 1); rw [h.low, h.cnt]
  · show v :: c.stk = (v :: m.stk) ++ G; rw [hG]; rfl
  · intro w
    show tupdB c.on v true w = true ↔ w ∈ v :: m.stk
    by_cases e : w = v
    · subst e; simp [tupdB]
    · simp [tupdB, e, h.on w]
  · exact List.nodup_cons.2 ⟨hvs, h.nodup⟩
  · intro x hx
    show tupd m.num v (m.cnt + 1) x ≠ 0
    by_cases e : x = v
    · subst e; rw [tupd_same]; omega
    · rw [tupd_ne _ _ e]; exact h.vis x (by simpa [e] using hx)

theorem sim_scan {F : Nat → Nat → TState → TState} {F' : Nat → Nat → CState → CState} (v : Nat)
    (hF : ∀ w p m c, CSim m0 c0 m c → m.num w = 0 → CPost m0 c0 m (F w p m) (F' w p c)) :
    ∀ (ws : List Nat) (m : TState) (c : CState), CSim m0 c0 m c →
      CPost m0 c0 m (tScan F v ws m) (cScan F' v ws c) := by
  intro ws
  induction ws with
  | nil => intro m c h; exact CPost.refl h
  | cons w ws ih =>
    intro m c h
    have hedge : CPost m0 c0 m (tEdge F v w m) (cEdge F' v w c) := by
      unfold tEdge cEdge
      have hcn : c.num w = m.num w := by rw [h.num]
      by_cases h1 : m.num w = 0
      · have hc1 : c.num w = 0 := by rw [hcn]; exact h1
        simp only [h1, hc1, ↓reduceIte]
        exact CPost.tickL _ (hF w v { m with ticks := m.ticks + 1 } c (h.tick _) h1)
      · have hc1 : ¬ c.num w = 0 := by rw [hcn]; exact h1
        simp only [h1, hc1, ↓reduceIte]
        by_cases h2 : w ∈ m.stk
        · have h3 : c.on w = true := (h.on w).2 h2
          simp only [h2, h3, ↓reduceIte]
          refine ⟨⟨h.cnt, h.num, ?_, h.stk, h.on, h.out, h.nodup, h.vis⟩, ⟨[], List.nodup_nil, by simp, by simp⟩,
            fun _ hx => hx⟩
          show tupd c.low v (min (c.low v) (c.num w)) = tupd m.low v (min (m.low v) (m.num w))
          rw [h.low, hcn]
        · have h3 : c.on w = false := by
            cases hc : c.on w
            · rfl
            · exact absurd ((h.on w).1 hc) h2
          simp only [h2, h3, Bool.false_eq_true, ↓reduceIte]
          exact CPost.tickR h _
    exact hedge.trans (ih _ _ hedge.sim)

theorem popTo_append {v : Nat} {N b G : List Nat} (hv : v ∉ N) :
    popTo v ((N ++ v :: b) ++ G) = (N ++ [v], b ++ G) := by
  have : (N ++ v :: b) ++ G = N ++ v :: (b ++ G) := by simp
  rw [this]; exact popTo_split hv

theorem sim_finish {m : TState} {c : CState} (h : CSim m0 c0 m c) {v : Nat} {N b : List Nat} (hv : v ∉ N)
    (hstk : m.stk = N ++ v :: b) (par : Option Nat) :
    CSim m0 c0 (tFinish v par m) (cFinish v par c) ∧
    ((tFinish v par m).stk = b ∨ (tFinish v par m).stk = m.stk) ∧ (tFinish v par m).num = m.num := by
  obtain ⟨G, hG⟩ := h.stk
  obtain ⟨R, hR1, hR2⟩ := h.out
  have hnd := h.nodup
  rw [hstk] at hnd
  have hb : b.Nodup := (List.nodup_cons.1 (List.nodup_append.1 hnd).2.1).2
  have hdisj := (List.nodup_append.1 hnd).2.2
  by_cases hl : m.low v = m.num v
  · have hpop : popTo v c.stk = (N ++ [v], b ++ G) := by rw [hG, hstk]; exact popTo_append hv
    have hpm : popTo v m.stk = (N ++ [v], b) := by rw [hstk]; exact popTo_split hv
    have hsim : CSim m0 c0 { m with stk := b, out := m.out ++ [N ++ [v]], ticks := m.ticks + (N ++ [v]).length }
        { c with stk := b ++ G, on := fun w => if w ∈ N ++ [v] then false else c.on w, out := c.out ++ [N ++ [v]] } := by
      refine ⟨h.cnt, h.num, h.low, ⟨G, rfl⟩, ?_, ⟨R ++ [N ++ [v]], ?_, ?_⟩, hb, ?_⟩
      · intro w
        show (if w ∈ N ++ [v] then false else c.on w) = true ↔ w ∈ b
        by_cases hw : w ∈ N ++ [v]
        · simp only [hw, ↓reduceIte]
          constructor
          · intro hh; simp at hh
          · intro hwb
            exfalso
            have hwv : w ∈ N ∨ w = v := by simpa using hw
            rcases hwv with hwN | rfl
            · exact hdisj w hwN w (List.mem_cons_of_mem _ hwb) rfl
            · exact (List.nodup_cons.1 (List.nodup_append.1 hnd).2.1).1 hwb
        · simp only [hw, ↓reduceIte]
          rw [h.on w, hstk]
          constructor
          · intro hh
            rcases List.mem_append.1 hh with hh | hh
            · exact absurd (List.mem_append_left _ hh) hw
            · rcases List.mem_cons.1 hh with rfl | hh
              · exact absurd (by simp) hw
              · exact hh
          · intro hh; exact List.mem_append_right _ (List.mem_cons_of_mem _ hh)
      · show m.out ++ [N ++ [v]] = m0.out ++ (R ++ [N ++ [v]]); rw [hR1]; simp
      · show c.out ++ [N ++ [v]] = c0.out ++ (R ++ [N ++ [v]]); rw [hR2]; simp
      · intro x hx
        exact h.vis x (by rw [hstk]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hx))
    have hlc : c.low v = c.num v := by rw [h.low, h.num]; exact hl
    refine ⟨?_, Or.inl (by cases par <;> simp [tFinish, hl, hpm]), by cases par <;> simp [tFinish, hl]⟩
    cases par with
    | none =>
      unfold tFinish cFinish
      simp only [hl, hlc, hpm, hpop, ↓reduceIte]
      exact hsim
    | some p =>
      unfold tFinish cFinish
      simp only [hl, hlc, hpm, hpop, ↓reduceIte]
      refine ⟨hsim.cnt, hsim.num, ?_, hsim.stk, hsim.on, hsim.out, hsim.nodup, hsim.vis⟩
      show tupd c.low p (min (c.low p) (c.num v)) = tupd m.low p (min (m.low p) (m.num v))
      rw [h.low, h.num]
  · have hlc : ¬ c.low v = c.num v := by rw [h.low, h.num]; exact hl
    refine ⟨?_, Or.inr (by cases par <;> simp [tFinish, hl]), by cases par <;> simp [tFinish, hl]⟩
    cases par with
    | none =>
      unfold tFinish cFinish
      simp only [hl, hlc, ↓reduceIte]
      exact h
    | some p =>
      unfold tFinish cFinish
      simp only [hl, hlc, ↓reduceIte]
      refine ⟨h.cnt, h.num, ?_, h.stk, h.on, h.out, h.nodup, h.vis⟩
      show tupd c.low p (min (c.low p) (c.low v)) = tupd m.low p (min (m.low p) (m.low v))
      rw [h.low]

end SmcIrred
