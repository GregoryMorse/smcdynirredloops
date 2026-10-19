module

public import SmcIrred.Smc.Finish
public import SmcIrred.Tarjan.Mono

public section

namespace SmcIrred

variable {g : Digraph}

/-- The scan of the node `v` is in progress: the machine simulates Tarjan's state, the stack of the simulated state has
`v` on it with the recorded depth, and `v` is the pending node (not pushed yet) exactly when nothing was pushed since
its entry. -/
structure ScanQ (g : Digraph) (v : Nat) (t : TState) (s : SState) (pend : Option Nat) : Prop where
  rel : SRel g t s pend
  hp : pend = none ∨ pend = some v
  shape : ∃ N tl, t.stk = N ++ v :: tl ∧ s.dep v = tl.length ∧ (pend = some v → N = [])
  vis : t.num v ≠ 0

/-- What a visit or an edge does to the states: visited vertices stay visited, the stack only grows on top, the depths of
visited nodes are untouched. -/
structure VPost (t t' : TState) (s s' : SState) : Prop where
  mono : ∀ u, t.num u ≠ 0 → t'.num u ≠ 0
  stk : ∃ N, t'.stk = N ++ t.stk
  dep : ∀ u, t.num u ≠ 0 → s'.dep u = s.dep u

theorem VPost.refl (t : TState) (s : SState) : VPost t t s s := ⟨fun _ h => h, ⟨[], by simp⟩, fun _ _ => rfl⟩

theorem VPost.trans {t1 t2 t3 : TState} {s1 s2 s3 : SState} (h1 : VPost t1 t2 s1 s2) (h2 : VPost t2 t3 s2 s3) :
    VPost t1 t3 s1 s3 where
  mono u hu := h2.mono u (h1.mono u hu)
  stk := by
    obtain ⟨N1, e1⟩ := h1.stk
    obtain ⟨N2, e2⟩ := h2.stk
    exact ⟨N2 ++ N1, by rw [e2, e1, List.append_assoc]⟩
  dep u hu := by rw [h2.dep u (h1.mono u hu), h1.dep u hu]

theorem scanQ_pend {v : Nat} {t : TState} {s : SState} {pend : Option Nat} (h : ScanQ g v t s pend) :
    pend = some v ↔ s.stk.length = s.dep v := by
  obtain ⟨N, tl, e1, e2, e3⟩ := h.shape
  constructor
  · intro hp
    have hN := e3 hp
    subst hN
    subst hp
    obtain ⟨tl', f1, f2⟩ := h.rel.stk
    have : tl' = tl := by rw [e1] at f1; exact (List.cons.inj f1).2.symm
    subst this
    rw [f2, e2]; simp
  · intro hl
    rcases h.hp with hp | hp
    · exfalso
      subst hp
      have hs : s.stk = t.stk.map some := h.rel.stk
      rw [hs, e1, e2] at hl
      simp at hl
      omega
    · exact hp

theorem tFinish_some (v x : Nat) (t : TState) :
    tFinish v (some x) t = { tFinish v none t with low := tupd (tFinish v none t).low x (min ((tFinish v none t).low x) ((tFinish v none t).low v)) } := by
  unfold tFinish
  by_cases hl : t.low v = t.num v <;> simp [hl]

/-- The caller's lowlink update after a call returned. -/
theorem ssim_parent {t : TState} {s : SState} {pend : Option Nat} (h : SRel g t s pend) {x v : Nat}
    (hx : t.num x ≠ 0) (hv : t.num v ≠ 0) :
    SRel g { t with low := tupd t.low x (min (t.low x) (t.low v)) } (sStep x (s.low v, s)) pend := by
  have hlx := h.low x hx
  have hlv := h.low v hv
  have hlex := h.low_le x hx
  unfold sStep
  by_cases hlt : s.low v < s.low x
  · have hmin : min (t.low x) (t.low v) = t.low v := by omega
    simp only [hlt, ↓reduceIte, hmin]
    refine ⟨h.stk, h.idx, h.none_iff, h.stk_ent, h.done_ent, h.vis, h.disj, h.nodup, h.num_le, ?_, ?_, ?_, h.chain, h.set,
      h.bound, h.pk⟩
    · intro u hu
      by_cases e : u = x
      · subst e; simp [fupd, tupd]; omega
      · simp only [fupd_ne _ _ e, tupd_ne _ _ e]; exact h.low u hu
    · intro u hu
      by_cases e : u = x
      · subst e; simp [tupd]; omega
      · simp only [tupd_ne _ _ e]; exact h.low_le u hu
    · intro u hu
      by_cases e : u = x
      · subst e; simp [fupd, tupd]; omega
      · simp only [fupd_ne _ _ e, tupd_ne _ _ e]; exact h.chk u hu
  · have hmin : min (t.low x) (t.low v) = t.low x := by omega
    simp only [hlt, ↓reduceIte, hmin, tupd_self]
    exact h

theorem sCall_visited_dep (f x w : Nat) (s : SState) (hw : s.ent w ≠ none) :
    (sStep x (sCall g f x w s)).dep = s.dep := by
  obtain ⟨k, hk⟩ : ∃ k, s.ent w = some k := by
    cases hh : s.ent w
    · exact absurd hh hw
    · exact ⟨_, rfl⟩
  rw [sCall_visited f x w k s hk]
  unfold sStep
  by_cases hlt : k < s.low x <;> simp [hlt]

theorem ScanQ.tick {v : Nat} {t : TState} {s : SState} {pend : Option Nat} (h : ScanQ g v t s pend) (k : Nat) :
    ScanQ g v { t with ticks := k } s pend :=
  ⟨h.rel.tick k, h.hp, h.shape, h.vis⟩

theorem VPost.tickL {t t' : TState} {s s' : SState} (k : Nat) (h : VPost { t with ticks := k } t' s s') :
    VPost t t' s s' := ⟨h.mono, h.stk, h.dep⟩

theorem tEdge_visited (F : Nat → Nat → TState → TState) (v w : Nat) (t : TState) (hw : t.num w ≠ 0) :
    (tEdge F v w t).stk = t.stk ∧ (tEdge F v w t).num = t.num := by
  unfold tEdge
  simp only [hw, ↓reduceIte]
  by_cases h2 : w ∈ t.stk <;> simp [h2]

/-- One edge of the successor loop: a visit of an unvisited successor or the stub of a visited one. -/
theorem ssim_edge (g : Digraph) (v f : Nat)
    (hF : ∀ (w : Nat) (t : TState) (s : SState) (pend : Option Nat), ScanQ g v t s pend → t.num w = 0 → w < g.n →
      tUn t.num g.n ≤ f →
      ScanQ g v (tVisit (revG g) f w (some v) t) (sStep v (sCall g f v w s)) none ∧
      VPost t (tVisit (revG g) f w (some v) t) s (sStep v (sCall g f v w s)))
    {t : TState} {s : SState} {pend : Option Nat} (h : ScanQ g v t s pend) {w : Nat} (hwn : w < g.n)
    (hun : tUn t.num g.n ≤ f) :
    ∃ pend1, ScanQ g v (tEdge (fun w p t => tVisit (revG g) f w (some p) t) v w t)
          (sStep v (sCall g f v w s)) pend1 ∧
        VPost t (tEdge (fun w p t => tVisit (revG g) f w (some p) t) v w t) s (sStep v (sCall g f v w s)) := by
  by_cases h1 : t.num w = 0
  · have hu : tEdge (fun w p t => tVisit (revG g) f w (some p) t) v w t =
        tVisit (revG g) f w (some v) { t with ticks := t.ticks + 1 } := by
      unfold tEdge; simp only [h1, ↓reduceIte]
    rw [hu]
    have := hF w { t with ticks := t.ticks + 1 } s pend (h.tick _) h1 hwn hun
    exact ⟨none, this.1, this.2.tickL _⟩
  · have hvis := h.vis
    obtain ⟨hs1, hs2⟩ := tEdge_visited (fun w p t => tVisit (revG g) f w (some p) t) v w t h1
    have hent : s.ent w ≠ none := fun e => h1 ((h.rel.none_iff w).1 e)
    have hrel := ssim_visited_edge (g := g) (fun w p t => tVisit (revG g) f w (some p) t) f h.rel hvis h1
    have hdep := sCall_visited_dep (g := g) f v w s hent
    refine ⟨pend, ⟨hrel, h.hp, ?_, ?_⟩, ⟨?_, ⟨[], by simp [hs1]⟩, ?_⟩⟩
    · obtain ⟨N, tl, e1, e2, e3⟩ := h.shape
      exact ⟨N, tl, by rw [hs1]; exact e1, by rw [hdep]; exact e2, e3⟩
    · rw [hs2]; exact h.vis
    · intro u hu; rw [hs2]; exact hu
    · intro u _; rw [hdep]

theorem ssim_scan (g : Digraph) (v f : Nat)
    (hF : ∀ (w : Nat) (t : TState) (s : SState) (pend : Option Nat), ScanQ g v t s pend → t.num w = 0 → w < g.n →
      tUn t.num g.n ≤ f →
      ScanQ g v (tVisit (revG g) f w (some v) t) (sStep v (sCall g f v w s)) none ∧
      VPost t (tVisit (revG g) f w (some v) t) s (sStep v (sCall g f v w s))) :
    ∀ (ws : List Nat) (t : TState) (s : SState) (pend : Option Nat), ScanQ g v t s pend → (∀ w ∈ ws, w < g.n) →
      tUn t.num g.n ≤ f →
      ∃ pend', ScanQ g v (tScan (fun w p t => tVisit (revG g) f w (some p) t) v ws t) (sLoop (sCall g f) v ws s) pend' ∧
        VPost t (tScan (fun w p t => tVisit (revG g) f w (some p) t) v ws t) s (sLoop (sCall g f) v ws s) := by
  intro ws
  induction ws with
  | nil => intro t s pend h _ _; exact ⟨pend, h, VPost.refl _ _⟩
  | cons w ws ih =>
    intro t s pend h hw hun
    have hwn : w < g.n := hw w List.mem_cons_self
    have hws : ∀ x ∈ ws, x < g.n := fun x hx => hw x (List.mem_cons_of_mem _ hx)
    obtain ⟨pend1, hq1, hp1⟩ := ssim_edge g v f hF h hwn hun
    have hun1 : tUn (tEdge (fun w p t => tVisit (revG g) f w (some p) t) v w t).num g.n ≤ f :=
      Nat.le_trans (tUn_mono (s := t) (fun u hu => hp1.mono u hu) g.n) hun
    obtain ⟨pend2, hq2, hp2⟩ := ih _ _ pend1 hq1 hws hun1
    exact ⟨pend2, hq2, hp1.trans hp2⟩

theorem sCall_unvisited (f x w : Nat) (s : SState) (h : (sPre x w s).ent w = none) :
    sCall g (f + 1) x w s = sBody g (sCall g f) w (sPre x w s) := by
  unfold sCall
  split <;> simp_all

end SmcIrred
