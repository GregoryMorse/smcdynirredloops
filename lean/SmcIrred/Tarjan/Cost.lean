module

public import SmcIrred.Tarjan.Correct

public section

namespace SmcIrred

variable {g : Digraph}

/-- The potential of a state: the work charged so far (vertex entries, examined edges, popped vertices) plus the stack
size; popping moves work from the stack to the counter and leaves the potential unchanged. -/
@[expose] def tPsi (s : TState) : Nat := s.ticks + s.stk.length

/-- The work every visited vertex among `0 … k-1` is charged: entry, pop and one unit per successor. -/
@[expose] def tPot (g : Digraph) (num : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => tPot g num k + (if num k = 0 then 0 else 2 + (tsuccs g k).length)

theorem popTo_length (v : Nat) : ∀ l : List Nat, (popTo v l).1.length + (popTo v l).2.length = l.length := by
  intro l
  induction l with
  | nil => simp [popTo]
  | cons x xs ih =>
    by_cases h : x = v
    · simp [popTo, h]; omega
    · simp [popTo, h]; omega

theorem tFinish_num (v : Nat) (par : Option Nat) (s : TState) : (tFinish v par s).num = s.num := by
  unfold tFinish
  by_cases hl : s.low v = s.num v <;> cases par <;> simp [hl]

theorem tFinish_psi (v : Nat) (par : Option Nat) (s : TState) : tPsi (tFinish v par s) = tPsi s := by
  have := popTo_length v s.stk
  unfold tFinish
  by_cases hl : s.low v = s.num v <;> cases par <;> simp [hl, tPsi] <;> omega

theorem tPot_mono {num num' : Nat → Nat} (hm : ∀ w, num w ≠ 0 → num' w ≠ 0) :
    ∀ k, tPot g num k ≤ tPot g num' k := by
  intro k
  induction k with
  | zero => exact Nat.le_refl _
  | succ k ih =>
    show tPot g num k + (if num k = 0 then 0 else 2 + (tsuccs g k).length) ≤
      tPot g num' k + (if num' k = 0 then 0 else 2 + (tsuccs g k).length)
    by_cases h1 : num k = 0
    · by_cases h2 : num' k = 0 <;> simp [h1, h2] <;> omega
    · have h2 := hm k h1
      simp [h1, h2]; omega

theorem tPot_gain {num num' : Nat → Nat} (hm : ∀ w, num w ≠ 0 → num' w ≠ 0) {v : Nat} (hs : num v = 0)
    (ht : num' v ≠ 0) : ∀ k, v < k → tPot g num k + (2 + (tsuccs g v).length) ≤ tPot g num' k := by
  intro k
  induction k with
  | zero => intro h; omega
  | succ k ih =>
    intro hk
    show tPot g num k + (if num k = 0 then 0 else 2 + (tsuccs g k).length) + (2 + (tsuccs g v).length) ≤
      tPot g num' k + (if num' k = 0 then 0 else 2 + (tsuccs g k).length)
    by_cases e : v = k
    · subst e
      have := tPot_mono (g := g) hm v
      simp [hs, ht]; omega
    · have := ih (by omega)
      by_cases h1 : num k = 0
      · by_cases h2 : num' k = 0 <;> simp [h1, h2] <;> omega
      · have h2 := hm k h1
        simp [h1, h2]; omega

theorem tPot_le (num : Nat → Nat) : ∀ k, tPot g num k ≤ 2 * k + tEdges g k := by
  intro k
  induction k with
  | zero => exact Nat.le_refl _
  | succ k ih =>
    show tPot g num k + (if num k = 0 then 0 else 2 + (tsuccs g k).length) ≤ 2 * (k + 1) + (tEdges g k + (tsuccs g k).length)
    by_cases h : num k = 0 <;> simp [h] <;> omega

/-- Visited vertices stay visited. -/
@[expose] def VisMono (F : Nat → Nat → TState → TState) : Prop :=
  ∀ w p s x, s.num x ≠ 0 → (F w p s).num x ≠ 0

theorem tScan_vis {F : Nat → Nat → TState → TState} (hF : VisMono F) (v : Nat) :
    ∀ (ws : List Nat) (s : TState) (x : Nat), s.num x ≠ 0 → (tScan F v ws s).num x ≠ 0 := by
  intro ws
  induction ws with
  | nil => intro s x h; exact h
  | cons w ws ih =>
    intro s x h
    show (tScan F v ws (tEdge F v w s)).num x ≠ 0
    refine ih _ x ?_
    unfold tEdge
    by_cases h1 : s.num w = 0
    · simp only [h1, ↓reduceIte]; exact hF w v _ x h
    · by_cases h2 : w ∈ s.stk <;> simp [h1, h2] <;> exact h

theorem tVisit_vis (g : Digraph) : ∀ (f : Nat) (v : Nat) (par : Option Nat) (s : TState) (x : Nat),
    s.num x ≠ 0 → (tVisit g f v par s).num x ≠ 0 := by
  intro f
  induction f with
  | zero => intro v par s x h; exact h
  | succ f ih =>
    intro v par s x h
    show (tFinish v par (tScan (fun w p t => tVisit g f w (some p) t) v (tsuccs g v) _)).num x ≠ 0
    rw [tFinish_num]
    refine tScan_vis (fun w p s x hx => ih w (some p) s x hx) v _ _ x ?_
    show tupd s.num v (s.cnt + 1) x ≠ 0
    by_cases e : x = v
    · subst e; rw [tupd_same]; omega
    · rw [tupd_ne _ _ e]; exact h

theorem tScan_cost {F : Nat → Nat → TState → TState} (hV : VisMono F)
    (hF : ∀ w p s, s.num w = 0 → w < g.n → tPsi (F w p s) + tPot g s.num g.n ≤ tPsi s + tPot g (F w p s).num g.n)
    (v : Nat) :
    ∀ (ws : List Nat) (s : TState), (∀ w ∈ ws, w < g.n) →
      tPsi (tScan F v ws s) + tPot g s.num g.n ≤ tPsi s + ws.length + tPot g (tScan F v ws s).num g.n := by
  intro ws
  induction ws with
  | nil => intro s _; show tPsi s + tPot g s.num g.n ≤ tPsi s + ([] : List Nat).length + tPot g s.num g.n; simp
  | cons w ws ih =>
    intro s hw
    have hwn : w < g.n := hw w List.mem_cons_self
    have hws : ∀ x ∈ ws, x < g.n := fun x hx => hw x (List.mem_cons_of_mem _ hx)
    show tPsi (tScan F v ws (tEdge F v w s)) + tPot g s.num g.n ≤ tPsi s + (ws.length + 1) +
      tPot g (tScan F v ws (tEdge F v w s)).num g.n
    have key : tPsi (tEdge F v w s) + tPot g s.num g.n ≤ tPsi s + 1 + tPot g (tEdge F v w s).num g.n := by
      unfold tEdge
      by_cases h1 : s.num w = 0
      · simp only [h1, ↓reduceIte]
        have := hF w v { s with ticks := s.ticks + 1 } h1 hwn
        have e : tPsi { s with ticks := s.ticks + 1 } = tPsi s + 1 := by simp [tPsi]; omega
        have e2 : tPot g ({ s with ticks := s.ticks + 1 } : TState).num g.n = tPot g s.num g.n := rfl
        omega
      · by_cases h2 : w ∈ s.stk <;> simp [h1, h2, tPsi] <;> omega
    have := ih (tEdge F v w s) hws
    omega

theorem tVisit_cost (g : Digraph) : ∀ (f : Nat) (s : TState) (v : Nat) (par : Option Nat), s.num v = 0 → v < g.n →
    tPsi (tVisit g f v par s) + tPot g s.num g.n ≤ tPsi s + tPot g (tVisit g f v par s).num g.n := by
  intro f
  induction f with
  | zero => intro s v par _ _; exact Nat.le_refl _
  | succ f ih =>
    intro s v par hn hv
    obtain ⟨s1, hs1⟩ : ∃ s1 : TState, s1 = { s with cnt := s.cnt + 1, num := tupd s.num v (s.cnt + 1), low := tupd s.low v (s.cnt + 1), stk := v :: s.stk, ticks := s.ticks + 1 } := ⟨_, rfl⟩
    have hT : tVisit g (f + 1) v par s = tFinish v par (tScan (fun w p t => tVisit g f w (some p) t) v (tsuccs g v) s1) := by
      rw [hs1]; rfl
    rw [hT, tFinish_psi, tFinish_num]
    have hscan := tScan_cost (g := g) (F := fun w p t => tVisit g f w (some p) t)
      (fun w p s x hx => tVisit_vis g f w (some p) s x hx)
      (fun w p s hs hw => ih s w (some p) hs hw) v (tsuccs g v) s1
      (by intro w hw; simp [tsuccs, List.mem_filter] at hw; exact hw.2)
    have hnum : s1.num = tupd s.num v (s.cnt + 1) := by rw [hs1]
    have hgain := tPot_gain (g := g) (num := s.num) (num' := tupd s.num v (s.cnt + 1))
      (fun w hw => by
        by_cases e : w = v
        · subst e; rw [tupd_same]; omega
        · rw [tupd_ne _ _ e]; exact hw) hn (by rw [tupd_same]; omega) g.n hv
    have hpsi : tPsi s1 = tPsi s + 2 := by rw [hs1]; simp [tPsi]; omega
    rw [hnum] at hscan
    omega

theorem tRun_cost (g : Digraph) : ∀ (vs : List Nat) (s : TState), (∀ v ∈ vs, v < g.n) →
    tPsi (tRun g vs s) + tPot g s.num g.n ≤ tPsi s + tPot g (tRun g vs s).num g.n := by
  intro vs
  induction vs with
  | nil => intro s _; exact Nat.le_refl _
  | cons v vs ih =>
    intro s hv
    have hv0 : v < g.n := hv v List.mem_cons_self
    have hvs : ∀ w ∈ vs, w < g.n := fun w hw => hv w (List.mem_cons_of_mem _ hw)
    show tPsi (tRun g vs (if s.num v = 0 then tVisit g g.n v none s else s)) + tPot g s.num g.n ≤ _ +
      tPot g (tRun g vs (if s.num v = 0 then tVisit g g.n v none s else s)).num g.n
    have h2 := ih (if s.num v = 0 then tVisit g g.n v none s else s) hvs
    by_cases h0 : s.num v = 0
    · have h1 := tVisit_cost g g.n s v none h0 hv0
      simp only [h0, ↓reduceIte] at h2 ⊢
      omega
    · simp only [h0, ↓reduceIte] at h2 ⊢
      exact h2

/-- **Linear cost** (C21): Tarjan's algorithm charges at most `2n + m` units, where `m` is the number of (in-range)
edges: one unit per vertex entry, per examined edge and per popped vertex. -/
theorem tarjan_cost (g : Digraph) : (tarjan g).ticks ≤ 2 * g.n + tEdges g g.n := by
  have h := tRun_cost g (List.range g.n) TState.init (by intro v hv; simpa using hv)
  obtain ⟨hI, -, -⟩ := tRun_spec g (List.range g.n) TState.init (TInv.init g) (by intro v hv; simpa using hv)
  have hstk : (tarjan g).stk = [] := hI.stk_nil
  have hp := tPot_le (g := g) (tarjan g).num g.n
  have h0 : tPot g TState.init.num g.n = 0 := by
    have : ∀ k, tPot g TState.init.num k = 0 := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih => show tPot g TState.init.num k + (if TState.init.num k = 0 then 0 else _) = 0; simp [TState.init] at ih ⊢; exact ih
    exact this _
  have hs : tPsi (tarjan g) = (tarjan g).ticks := by simp [tPsi, hstk]
  have hi : tPsi TState.init = 0 := by simp [tPsi, TState.init]
  show (tarjan g).ticks ≤ _
  have h' : tPsi (tarjan g) + tPot g TState.init.num g.n ≤ tPsi TState.init + tPot g (tarjan g).num g.n := h
  omega

end SmcIrred
