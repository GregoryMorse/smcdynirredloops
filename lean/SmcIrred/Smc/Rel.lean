module

public import SmcIrred.Tarjan.Cost
public import SmcIrred.Spec.SmcMachine

public section

namespace SmcIrred

variable {g : Digraph}

/-- The machine stack against the Tarjan stack: equal (`none`), or the Tarjan stack has the node `p` on top that the
machine has not pushed yet. -/
@[expose] def StkRel (tstk : List Nat) (sstk : List (Option Nat)) : Option Nat → Prop
  | none => sstk = tstk.map some
  | some p => ∃ tl, tstk = p :: tl ∧ sstk = tl.map some

/-- The state of the machine simulates the state of Tarjan's algorithm on the reversed graph. -/
structure SRel (g : Digraph) (t : TState) (s : SState) (pend : Option Nat) : Prop where
  stk : StkRel t.stk s.stk pend
  idx : s.idx = t.cnt
  none_iff : ∀ w, s.ent w = none ↔ t.num w = 0
  stk_ent : ∀ w ∈ t.stk, s.ent w = some (t.num w - 1)
  done_ent : ∀ w, t.Done w → s.ent w = some g.n
  vis : ∀ w, t.num w ≠ 0 → (w ∈ t.stk ∨ t.Done w)
  disj : ∀ w ∈ t.stk, ¬ t.Done w
  nodup : t.stk.Nodup
  num_le : ∀ w, t.num w ≤ t.cnt
  low : ∀ w, t.num w ≠ 0 → s.low w + 1 = t.low w
  low_le : ∀ w, t.num w ≠ 0 → t.low w ≤ t.num w
  chk : ∀ w, t.num w ≠ 0 → (s.chk w = true ↔ t.low w < t.num w)
  chain : s.chain = t.out.flatten
  set : ∀ C ∈ t.out, ∃ r ∈ C, ∀ u ∈ C, s.set u = r
  bound : ∃ L : List Nat, L.Nodup ∧ (∀ w, w ∈ L ↔ s.ent w ≠ none) ∧ L.length = s.idx ∧ ∀ w ∈ L, w < g.n
  pk : ∀ w, s.ent w = none → s.pk w = false

theorem SRel.init (g : Digraph) : SRel g TState.init (SState.init g.n) none where
  stk := rfl
  idx := rfl
  none_iff := by intro w; simp [SState.init, TState.init]
  stk_ent := by simp [TState.init]
  done_ent := by simp [TState.init, TState.Done]
  vis := by simp [TState.init]
  disj := by simp [TState.init]
  nodup := by simp [TState.init]
  num_le := by simp [TState.init]
  low := by simp [TState.init]
  low_le := by simp [TState.init]
  chk := by simp [TState.init]
  chain := rfl
  set := by simp [TState.init]
  bound := ⟨[], List.nodup_nil, by simp [SState.init], rfl, by simp⟩
  pk := by simp [SState.init]

/-- The start of `strongconnect` in the clean model. -/
@[expose] def tEnterSt (t : TState) (v : Nat) : TState :=
  { t with cnt := t.cnt + 1, num := tupd t.num v (t.cnt + 1), low := tupd t.low v (t.cnt + 1), stk := v :: t.stk,
           ticks := t.ticks + 1 }

theorem tVisit_succ (g : Digraph) (f v : Nat) (par : Option Nat) (t : TState) :
    tVisit g (f + 1) v par t =
      tFinish v par (tScan (fun w p t => tVisit g f w (some p) t) v (tsuccs g v) (tEnterSt t v)) := rfl

theorem fupd_same {α : Type} (f : Nat → α) (k : Nat) (x : α) : fupd f k x k = x := by simp [fupd]

theorem fupd_ne {α : Type} (f : Nat → α) {k j : Nat} (x : α) (h : j ≠ k) : fupd f k x j = f j := by simp [fupd, h]

/-- Entering an unvisited node: the call cell `c` was pushed and the entry peeks (`b`) or pops it. -/
theorem ssim_enter {t : TState} {s : SState} {pend : Option Nat} (h : SRel g t s pend) {w : Nat}
    (hw0 : t.num w = 0) (hwn : w < g.n) (c : Option Nat) (b : Bool)
    (hb : (b = true → ∃ x, pend = some x ∧ c = some x) ∧ (b = false → pend = none)) :
    SRel g (tEnterSt t w) (sEnter w { s with pk := fupd s.pk w b, stk := c :: s.stk }) (some w) := by
  have hwe : s.ent w = none := (h.none_iff w).2 hw0
  have hwstk : w ∉ t.stk := fun hm => by have := h.stk_ent w hm; rw [hwe] at this; simp at this
  have hwdone : ¬ t.Done w := fun hd => by have := h.done_ent w hd; rw [hwe] at this; simp at this
  have hnum : ∀ u, u ≠ w → tupd t.num w (t.cnt + 1) u = t.num u := fun u hu => tupd_ne _ _ hu
  have hne : ∀ u, t.num u ≠ 0 → u ≠ w := fun u hu e => hu (e ▸ hw0)
  unfold sEnter
  simp only [fupd_same]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- stk
    cases hbb : b
    · have hp := hb.2 hbb
      subst hp
      refine ⟨t.stk, rfl, ?_⟩
      have := h.stk
      simp only [StkRel] at this
      simp [this]
    · obtain ⟨x, hp, hc⟩ := hb.1 hbb
      subst hp
      obtain ⟨tl, e1, e2⟩ := h.stk
      refine ⟨x :: tl, by simp [tEnterSt, e1], ?_⟩
      simp [hc, e2]
  · simp [h.idx, tEnterSt]
  · intro u
    by_cases e : u = w
    · subst e; simp [fupd, tEnterSt, tupd, hwe]
    · simp only [fupd_ne _ _ e, tEnterSt, tupd_ne _ _ e]; exact h.none_iff u
  · intro u hu
    simp only [tEnterSt, List.mem_cons] at hu
    rcases hu with rfl | hu
    · simp [fupd, tEnterSt, tupd, h.idx]
    · have hu0 : t.num u ≠ 0 := fun h0 => by
        have := h.stk_ent u hu
        rw [(h.none_iff u).2 h0] at this; simp at this
      have e := hne u hu0
      simp only [fupd_ne _ _ e, tEnterSt, tupd_ne _ _ e]
      exact h.stk_ent u hu
  · intro u hu
    have hu' : t.Done u := hu
    have e : u ≠ w := fun e => hwdone (e ▸ hu')
    simp only [fupd_ne _ _ e]
    exact h.done_ent u hu'
  · intro u hu
    by_cases e : u = w
    · subst e; left; simp [tEnterSt]
    · have : t.num u ≠ 0 := by simpa [tEnterSt, tupd_ne _ _ e] using hu
      rcases h.vis u this with hs | hd
      · left; simp [tEnterSt, hs]
      · right; exact hd
  · intro u hu
    simp only [tEnterSt, List.mem_cons] at hu
    rcases hu with rfl | hu
    · exact hwdone
    · exact h.disj u hu
  · exact List.nodup_cons.2 ⟨hwstk, h.nodup⟩
  · intro u
    by_cases e : u = w
    · subst e; simp [tEnterSt, tupd]
    · simp only [tEnterSt, tupd_ne _ _ e]; exact Nat.le_succ_of_le (h.num_le u)
  · intro u hu
    by_cases e : u = w
    · subst e; simp [fupd, tEnterSt, tupd, h.idx]
    · have : t.num u ≠ 0 := by simpa [tEnterSt, tupd_ne _ _ e] using hu
      simp only [fupd_ne _ _ e, tEnterSt, tupd_ne _ _ e]; exact h.low u this
  · intro u hu
    by_cases e : u = w
    · subst e; simp [tEnterSt, tupd]
    · have : t.num u ≠ 0 := by simpa [tEnterSt, tupd_ne _ _ e] using hu
      simp only [tEnterSt, tupd_ne _ _ e]; exact h.low_le u this
  · intro u hu
    by_cases e : u = w
    · subst e; simp [fupd, tEnterSt, tupd]
    · have : t.num u ≠ 0 := by simpa [tEnterSt, tupd_ne _ _ e] using hu
      simp only [fupd_ne _ _ e, tEnterSt, tupd_ne _ _ e]; exact h.chk u this
  · exact h.chain
  · exact h.set
  · obtain ⟨L, h1, h2, h3, h4⟩ := h.bound
    have hwL : w ∉ L := fun hm => by have := (h2 w).1 hm; exact this hwe
    refine ⟨w :: L, List.nodup_cons.2 ⟨hwL, h1⟩, ?_, by simp [h3], ?_⟩
    · intro u
      by_cases e : u = w
      · subst e; simp [fupd]
      · simp only [List.mem_cons, e, false_or, fupd_ne _ _ e]; exact h2 u
    · intro u hu
      rcases List.mem_cons.1 hu with rfl | hu
      · exact hwn
      · exact h4 u hu
  · intro u hu
    by_cases e : u = w
    · subst e; simp [fupd] at hu
    · simp only [fupd_ne _ _ e] at hu ⊢
      exact h.pk u hu

theorem SRel.tick {t : TState} {s : SState} {pend : Option Nat} (h : SRel g t s pend) (k : Nat) :
    SRel g { t with ticks := k } s pend :=
  ⟨h.stk, h.idx, h.none_iff, h.stk_ent, h.done_ent, h.vis, h.disj, h.nodup, h.num_le, h.low, h.low_le, h.chk, h.chain,
    h.set, h.bound, h.pk⟩

theorem SRel.with_pk {t : TState} {s : SState} {pend : Option Nat} (h : SRel g t s pend) (P : Nat → Bool)
    (hP : ∀ u, s.ent u = none → P u = false) : SRel g t { s with pk := P } pend :=
  ⟨h.stk, h.idx, h.none_iff, h.stk_ent, h.done_ent, h.vis, h.disj, h.nodup, h.num_le, h.low, h.low_le, h.chk, h.chain,
    h.set, h.bound, hP⟩

theorem sPre_eq {t : TState} {s : SState} {pend : Option Nat} (h : SRel g t s pend) {x w : Nat} (hw0 : t.num w = 0) :
    sPre x w s = { s with pk := fupd s.pk w (decide (s.stk.length = s.dep x)), stk := some x :: s.stk } := by
  have hwe : s.ent w = none := (h.none_iff w).2 hw0
  have hpk : s.pk w = false := h.pk w hwe
  unfold sPre
  by_cases hc : s.stk.length = s.dep x
  · simp [hc]
  · simp only [hc, ↓reduceIte, decide_false]
    have : fupd s.pk w false = s.pk := by
      funext u
      by_cases e : u = w
      · subst e; simp [fupd, hpk]
      · simp [fupd, e]
    rw [this]

/-- The call of an unvisited node: the entry simulates `tEnterSt`. -/
theorem ssim_enter_call {t : TState} {s : SState} {pend : Option Nat} (h : SRel g t s pend) {x w : Nat}
    (hw0 : t.num w = 0) (hwn : w < g.n) (hpend : pend = some x ↔ s.stk.length = s.dep x)
    (hp : pend = none ∨ pend = some x) :
    SRel g (tEnterSt t w) (sEnter w (sPre x w s)) (some w) := by
  rw [sPre_eq h hw0]
  refine ssim_enter h hw0 hwn (some x) (decide (s.stk.length = s.dep x)) ⟨?_, ?_⟩
  · intro hb
    exact ⟨x, hpend.2 (of_decide_eq_true hb), rfl⟩
  · intro hb
    have : ¬ s.stk.length = s.dep x := of_decide_eq_false hb
    rcases hp with hp | hp
    · exact hp
    · exact absurd (hpend.1 hp) this

/-- The outer loop's call of an unvisited node (the cell is `none`, nothing is peeked). -/
theorem ssim_enter_top {t : TState} {s : SState} (h : SRel g t s none) {w : Nat} (hw0 : t.num w = 0) (hwn : w < g.n) :
    SRel g (tEnterSt t w) (sEnter w { s with stk := none :: s.stk }) (some w) := by
  have hwe : s.ent w = none := (h.none_iff w).2 hw0
  have hpk : s.pk w = false := h.pk w hwe
  have : ({ s with stk := none :: s.stk } : SState) = { s with pk := fupd s.pk w false, stk := none :: s.stk } := by
    have e : fupd s.pk w false = s.pk := by
      funext u
      by_cases e : u = w
      · subst e; simp [fupd, hpk]
      · simp [fupd, e]
    rw [e]
  rw [this]
  exact ssim_enter h hw0 hwn none false ⟨fun hb => absurd hb (by simp), fun _ => rfl⟩

theorem sPre_ent (x w : Nat) (s : SState) : (sPre x w s).ent = s.ent := by
  unfold sPre; by_cases hc : s.stk.length = s.dep x <;> simp [hc]

theorem sPre_pop (x w : Nat) (s : SState) :
    ({ sPre x w s with stk := (sPre x w s).stk.tail } : SState) = { s with pk := (sPre x w s).pk } := by
  unfold sPre; by_cases hc : s.stk.length = s.dep x <;> simp [hc]

theorem sCall_visited (f x w k : Nat) (s : SState) (hk : s.ent w = some k) :
    sCall g f x w s = (k, { s with pk := (sPre x w s).pk }) := by
  have h1 : (sPre x w s).ent w = some k := by rw [sPre_ent]; exact hk
  unfold sCall
  split <;> simp_all [sPre_pop]

theorem sPre_pk (x w : Nat) (s : SState) (hw : s.ent w ≠ none) (hpk : ∀ u, s.ent u = none → s.pk u = false) :
    ∀ u, s.ent u = none → (sPre x w s).pk u = false := by
  intro u hu
  have hne : u ≠ w := fun e => hw (e ▸ hu)
  unfold sPre
  by_cases hc : s.stk.length = s.dep x
  · simp [hc, fupd_ne _ _ hne, hpk u hu]
  · simp [hc, hpk u hu]

/-- An edge to a visited vertex: the stub returns its marker and the caller's lowlink is lowered when the marker is
smaller; this is Tarjan's `w ∈ stk` test (finished components return `n`, which never lowers a lowlink). -/
theorem ssim_visited_edge (F : Nat → Nat → TState → TState) (f : Nat) {t : TState} {s : SState} {pend : Option Nat}
    (h : SRel g t s pend) {x w : Nat} (hx : t.num x ≠ 0) (hw : t.num w ≠ 0) :
    SRel g (tEdge F x w t) (sStep x (sCall g f x w s)) pend := by
  have hwe : s.ent w ≠ none := fun e => hw ((h.none_iff w).1 e)
  obtain ⟨k, hk⟩ : ∃ k, s.ent w = some k := by
    cases hh : s.ent w
    · exact absurd hh hwe
    · exact ⟨_, rfl⟩
  have hbd : s.low x < g.n := by
    obtain ⟨L, h1, h2, h3, h4⟩ := h.bound
    have hsub : L ⊆ List.range g.n := fun u hu => List.mem_range.2 (h4 u hu)
    have hlen : L.length ≤ g.n := by
      have := List.Nodup.length_le_of_subset h1 hsub
      simpa using this
    have e1 := h.low x hx
    have e2 := h.low_le x hx
    have e3 := h.num_le x
    have e4 := h.idx
    omega
  rw [sCall_visited f x w k s hk]
  have hP := sPre_pk x w s hwe h.pk
  have hs' : SRel g t { s with pk := (sPre x w s).pk } pend := h.with_pk _ hP
  unfold tEdge sStep
  simp only [hw, ite_false]
  by_cases hst : w ∈ t.stk
  · have hkw : k = t.num w - 1 := by
      have := h.stk_ent w hst; rw [hk] at this; exact Option.some.inj this
    have hlx := h.low x hx
    have hlex := h.low_le x hx
    by_cases hlt : k < s.low x
    · have hmin : min (t.low x) (t.num w) = t.num w := by omega
      simp only [hst, hlt, ↓reduceIte, hmin]
      refine ⟨hs'.stk, hs'.idx, hs'.none_iff, hs'.stk_ent, hs'.done_ent, hs'.vis, hs'.disj, hs'.nodup, hs'.num_le, ?_, ?_, ?_, hs'.chain, hs'.set, hs'.bound, hs'.pk⟩
      · intro u hu
        by_cases e : u = x
        · subst e; simp [fupd, tupd]; omega
        · simp only [fupd_ne _ _ e, tupd_ne _ _ e]; exact hs'.low u hu
      · intro u hu
        by_cases e : u = x
        · subst e; simp [tupd]; omega
        · simp only [tupd_ne _ _ e]; exact hs'.low_le u hu
      · intro u hu
        by_cases e : u = x
        · subst e; simp [fupd, tupd]; omega
        · simp only [fupd_ne _ _ e, tupd_ne _ _ e]; exact hs'.chk u hu
    · have hmin : min (t.low x) (t.num w) = t.low x := by omega
      simp only [hst, hlt, ↓reduceIte, hmin, tupd_self]
      exact hs'.tick _
  · have hd : t.Done w := by
      rcases h.vis w hw with hh | hh
      · exact absurd hh hst
      · exact hh
    have hkn : k = g.n := by
      have := h.done_ent w hd; rw [hk] at this; exact Option.some.inj this
    have hlt : ¬ k < s.low x := by omega
    simp only [hst, hlt, ite_false]
    exact hs'.tick _

end SmcIrred
