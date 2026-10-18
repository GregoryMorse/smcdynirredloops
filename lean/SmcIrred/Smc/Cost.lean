module

public import SmcIrred.Smc.Solve

public section

namespace SmcIrred

/-! # Step count of the Level 2 machine (G27)

`cCall`, `cBody`, `cLoop`, `cLeave`, `cExtract`, `cntRun` mirror `sCall`, `sBody`, `sLoop`, `sLeave`, `sExtract`, `sRun` and
add the number of primitive machine operations: one per call (`sPre`, whether the callee is visited or not), one for the
entry code and one for the exit code of a node (`sEnter`, `sLeave`), one per successor-loop iteration (`sStep`), one per
cell popped by the component extraction, one per outer-loop iteration; the solution phase adds one per chain element.
The state component of each mirror is the original function (`cntRun_state`), so the count is the count of the machine that
`smcSolve_spec` proves correct. -/

variable {g : Digraph}

@[expose] def cExtract (n w : Nat) : Nat → SState → Nat × SState
  | 0, s => (0, s)
  | k + 1, s =>
    match s.stk with
    | [] => (0, s)
    | none :: rest => (0, { s with stk := rest })
    | some u :: rest =>
      let s' : SState := { s with stk := rest, chain := s.chain ++ [u], set := fupd s.set u w, ent := fupd s.ent u (some n) }
      if u = w then (1, s') else (1 + (cExtract n w k s').1, (cExtract n w k s').2)

@[expose] def cLeave (n w : Nat) (s4 : SState) : Nat × SState :=
  let s5 : SState := if s4.stk.length = s4.dep w then { s4 with stk := some w :: s4.stk } else s4
  if s5.chk w then (0, s5) else cExtract n w s5.stk.length s5

@[expose] def cLoop (call : Nat → Nat → SState → Nat × (Nat × SState)) (x : Nat) : List Nat → SState → Nat × SState
  | [], s => (0, s)
  | w :: ws, s => (((call x w s).1 + 1 + (cLoop call x ws (sStep x (call x w s).2)).1),
                   (cLoop call x ws (sStep x (call x w s).2)).2)

@[expose] def cBody (g : Digraph) (call : Nat → Nat → SState → Nat × (Nat × SState)) (w : Nat) (s1 : SState) :
    Nat × (Nat × SState) :=
  let q := cLoop call w (tsuccs (revG g) w) (sEnter w s1)
  let lv := cLeave g.n w q.2
  (2 + q.1 + lv.1, (lv.2.low w, lv.2))

@[expose] def cCall (g : Digraph) : Nat → Nat → Nat → SState → Nat × (Nat × SState)
  | f, x, w, s =>
    match (sPre x w s).ent w, f with
    | some k, _ => (1, (k, { sPre x w s with stk := (sPre x w s).stk.tail }))
    | none, 0 => (1, (0, sPre x w s))
    | none, f + 1 => (1 + (cBody g (cCall g f) w (sPre x w s)).1, (cBody g (cCall g f) w (sPre x w s)).2)

@[expose] def cntRun (g : Digraph) (fuel : Nat) : List Nat → SState → Nat × SState
  | [], s => (0, s)
  | v :: vs, s =>
    match s.ent v with
    | some _ => (1 + (cntRun g fuel vs s).1, (cntRun g fuel vs s).2)
    | none =>
      (1 + (cBody g (cCall g fuel) v { s with stk := none :: s.stk }).1 +
          (cntRun g fuel vs (cBody g (cCall g fuel) v { s with stk := none :: s.stk }).2.2).1,
        (cntRun g fuel vs (cBody g (cCall g fuel) v { s with stk := none :: s.stk }).2.2).2)

/-- The primitive operations of one run of the solver on the implication graph of `f`, with the solution phase. -/
@[expose] def smcSteps (f : TwoSat) : Nat :=
  let g := f.graph
  let r := cntRun g (g.n - 1) (List.range g.n) (SState.init g.n)
  r.1 + r.2.chain.length

/-! ### The mirrors compute the machine -/

theorem cExtract_state (n w : Nat) : ∀ (k : Nat) (s : SState), (cExtract n w k s).2 = sExtract n w k s := by
  intro k
  induction k with
  | zero => intro s; rfl
  | succ k ih =>
    intro s
    unfold cExtract sExtract
    cases hs : s.stk with
    | nil => rfl
    | cons a rest =>
      cases a with
      | none => rfl
      | some u =>
        by_cases hu : u = w
        · simp [hu]
        · simp only [hu, ↓reduceIte]
          exact ih _

theorem cLeave_state (n w : Nat) (s4 : SState) : (cLeave n w s4).2 = sLeave n w s4 := by
  unfold cLeave sLeave
  dsimp only
  by_cases h : s4.stk.length = s4.dep w <;> by_cases hc : s4.chk w = true <;> simp [h, hc, cExtract_state]

theorem cLoop_state (call : Nat → Nat → SState → Nat × SState) (ccall : Nat → Nat → SState → Nat × (Nat × SState))
    (h : ∀ x w s, (ccall x w s).2 = call x w s) (x : Nat) :
    ∀ (ws : List Nat) (s : SState), (cLoop ccall x ws s).2 = sLoop call x ws s := by
  intro ws
  induction ws with
  | nil => intro s; rfl
  | cons w ws ih => intro s; simp only [cLoop, sLoop, h]; exact ih _

theorem cBody_state (call : Nat → Nat → SState → Nat × SState) (ccall : Nat → Nat → SState → Nat × (Nat × SState))
    (h : ∀ x w s, (ccall x w s).2 = call x w s) (w : Nat) (s1 : SState) :
    (cBody g ccall w s1).2 = sBody g call w s1 := by
  unfold cBody sBody
  dsimp only
  rw [cLoop_state call ccall h, cLeave_state]

theorem cCall_state (g : Digraph) : ∀ (f x w : Nat) (s : SState), (cCall g f x w s).2 = sCall g f x w s := by
  intro f
  induction f with
  | zero =>
    intro x w s
    unfold cCall sCall
    cases h : (sPre x w s).ent w <;> simp [h]
  | succ f ih =>
    intro x w s
    unfold cCall sCall
    cases h : (sPre x w s).ent w
    · simp only [h]
      exact cBody_state (sCall g f) (cCall g f) ih _ _
    · simp [h]

theorem cntRun_state (g : Digraph) (fuel : Nat) : ∀ (vs : List Nat) (s : SState), (cntRun g fuel vs s).2 = sRun g fuel vs s := by
  intro vs
  induction vs with
  | nil => intro s; rfl
  | cons v vs ih =>
    intro s
    unfold cntRun sRun
    cases h : s.ent v with
    | some k => exact ih _
    | none =>
      dsimp only
      rw [← ih]
      rw [cBody_state (sCall g fuel) (cCall g fuel) (cCall_state g fuel)]

/-! ### The potential -/

/-- Weight of the nodes without an `ent` entry: entering a node pays for its entry, exit and successor loop. -/
@[expose] def mPot (g : Digraph) (ent : Nat → Option Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => mPot g ent k + (if ent k = none then 2 * (tsuccs (revG g) k).length + 4 else 0)

theorem mPot_mono (ent ent' : Nat → Option Nat) (h : ∀ u, ent u ≠ none → ent' u ≠ none) :
    ∀ k, mPot g ent' k ≤ mPot g ent k := by
  intro k
  induction k with
  | zero => exact Nat.le_refl _
  | succ k ih =>
    show mPot g ent' k + (if ent' k = none then _ else 0) ≤ mPot g ent k + (if ent k = none then _ else 0)
    by_cases h1 : ent' k = none
    · have h2 : ent k = none := by
        by_cases h3 : ent k = none
        · exact h3
        · exact absurd h1 (h k h3)
      simp only [h1, h2, ↓reduceIte]
      omega
    · simp only [h1, ↓reduceIte]
      omega

theorem mPot_congr (ent ent' : Nat → Option Nat) : ∀ k, (∀ u, u < k → ent' u = ent u) → mPot g ent' k = mPot g ent k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro h
    show mPot g ent' k + (if ent' k = none then _ else 0) = mPot g ent k + (if ent k = none then _ else 0)
    rw [ih (fun u hu => h u (by omega)), h k (by omega)]

theorem mPot_enter (ent ent' : Nat → Option Nat) (w : Nat) (h : ent w = none) (h2 : ent' w ≠ none)
    (h3 : ∀ u, u ≠ w → ent' u = ent u) :
    ∀ k, w < k → mPot g ent' k + (2 * (tsuccs (revG g) w).length + 4) = mPot g ent k := by
  intro k
  induction k with
  | zero => intro hk; omega
  | succ k ih =>
    intro hk
    show mPot g ent' k + (if ent' k = none then _ else 0) + _ = mPot g ent k + (if ent k = none then _ else 0)
    by_cases hkw : k = w
    · subst hkw
      have := mPot_congr (g := g) ent ent' k (fun u hu => h3 u (by omega))
      rw [this]
      simp only [h, h2, ↓reduceIte]
      omega
    · have := ih (by omega)
      rw [h3 k hkw]
      omega

/-! ### Facts about the primitives -/

theorem sStep_ent (x : Nat) (rs : Nat × SState) : (sStep x rs).ent = rs.2.ent := by
  unfold sStep; split <;> rfl

theorem sStep_chain (x : Nat) (rs : Nat × SState) : (sStep x rs).chain = rs.2.chain := by
  unfold sStep; split <;> rfl

theorem sPre_chain (x w : Nat) (s : SState) : (sPre x w s).chain = s.chain := by
  unfold sPre; dsimp only; split <;> rfl

theorem sEnter_chain (w : Nat) (s : SState) : (sEnter w s).chain = s.chain := rfl

theorem sEnter_ent (w : Nat) (s : SState) : (sEnter w s).ent = fupd s.ent w (some s.idx) := rfl

theorem cExtract_chain (n w : Nat) : ∀ (k : Nat) (s : SState),
    (cExtract n w k s).1 + s.chain.length = (cExtract n w k s).2.chain.length := by
  intro k
  induction k with
  | zero => intro s; simp [cExtract]
  | succ k ih =>
    intro s
    unfold cExtract
    cases hs : s.stk with
    | nil => simp
    | cons a rest =>
      cases a with
      | none => simp
      | some u =>
        by_cases hu : u = w
        · simp [hu]; omega
        · simp only [hu, ↓reduceIte]
          have := ih { s with stk := rest, chain := s.chain ++ [u], set := fupd s.set u w, ent := fupd s.ent u (some n) }
          simp at this ⊢
          omega

theorem cExtract_ent (n w : Nat) : ∀ (k : Nat) (s : SState) (u : Nat), s.ent u ≠ none → (cExtract n w k s).2.ent u ≠ none := by
  intro k
  induction k with
  | zero => intro s u h; exact h
  | succ k ih =>
    intro s u h
    unfold cExtract
    cases hs : s.stk with
    | nil => exact h
    | cons a rest =>
      cases a with
      | none => exact h
      | some v =>
        have h' : fupd s.ent v (some n) u ≠ none := by
          by_cases hv : u = v
          · simp [fupd, hv]
          · simpa [fupd, hv] using h
        by_cases hvw : v = w
        · simp only [hvw, ↓reduceIte]; simpa [hvw] using h'
        · simp only [hvw, ↓reduceIte]
          exact ih _ u h'

theorem cLeave_chain (n w : Nat) (s4 : SState) : (cLeave n w s4).1 + s4.chain.length = (cLeave n w s4).2.chain.length := by
  unfold cLeave
  dsimp only
  by_cases h : s4.stk.length = s4.dep w
  · simp only [h, ↓reduceIte]
    split
    · simp
    · have := cExtract_chain n w (({ s4 with stk := some w :: s4.stk } : SState).stk.length) { s4 with stk := some w :: s4.stk }
      simpa using this
  · simp only [h, ↓reduceIte]
    split
    · simp
    · exact cExtract_chain n w _ s4

theorem cLeave_ent (n w : Nat) (s4 : SState) (u : Nat) (hu : s4.ent u ≠ none) : (cLeave n w s4).2.ent u ≠ none := by
  unfold cLeave
  dsimp only
  by_cases h : s4.stk.length = s4.dep w
  · simp only [h, ↓reduceIte]
    split
    · exact hu
    · exact cExtract_ent n w _ _ u hu
  · simp only [h, ↓reduceIte]
    split
    · exact hu
    · exact cExtract_ent n w _ _ u hu

/-! ### The bound -/

/-- A call function whose cost is paid by the potential: each call costs at most one more than the potential it consumes
plus the cells popped. -/
@[expose] def CallBound (g : Digraph) (call : Nat → Nat → SState → Nat × (Nat × SState)) : Prop :=
  ∀ x w s, w < g.n → (call x w s).1 + mPot g (call x w s).2.2.ent g.n + s.chain.length ≤
    mPot g s.ent g.n + 1 + (call x w s).2.2.chain.length

theorem cLoop_bound (call : Nat → Nat → SState → Nat × (Nat × SState)) (hc : CallBound g call) (x : Nat) :
    ∀ (ws : List Nat) (s : SState), (∀ w ∈ ws, w < g.n) →
      (cLoop call x ws s).1 + mPot g (cLoop call x ws s).2.ent g.n + s.chain.length ≤
        mPot g s.ent g.n + 2 * ws.length + (cLoop call x ws s).2.chain.length := by
  intro ws
  induction ws with
  | nil => intro s _; simp [cLoop]
  | cons w ws ih =>
    intro s hw
    have h1 := hc x w s (hw w List.mem_cons_self)
    have h2 := ih (sStep x (call x w s).2) (fun u hu => hw u (List.mem_cons_of_mem _ hu))
    rw [sStep_ent, sStep_chain] at h2
    simp only [cLoop, List.length_cons]
    omega

theorem cBody_bound (call : Nat → Nat → SState → Nat × (Nat × SState)) (hc : CallBound g call) (w : Nat) (s1 : SState)
    (hw : w < g.n) (he : s1.ent w = none) :
    (cBody g call w s1).1 + 2 + mPot g (cBody g call w s1).2.2.ent g.n + s1.chain.length ≤
      mPot g s1.ent g.n + (cBody g call w s1).2.2.chain.length := by
  have hl := cLoop_bound call hc w (tsuccs (revG g) w) (sEnter w s1) (by
    intro u hu
    simp [tsuccs, List.mem_filter] at hu
    exact hu.2)
  have hen := mPot_enter (g := g) s1.ent (sEnter w s1).ent w he (by rw [sEnter_ent]; simp [fupd])
    (by intro u hu; rw [sEnter_ent]; simp [fupd, hu]) g.n hw
  have hlv := cLeave_chain g.n w (cLoop call w (tsuccs (revG g) w) (sEnter w s1)).2
  have hm := mPot_mono (g := g) (cLoop call w (tsuccs (revG g) w) (sEnter w s1)).2.ent
    (cLeave g.n w (cLoop call w (tsuccs (revG g) w) (sEnter w s1)).2).2.ent
    (fun u hu => cLeave_ent _ _ _ u hu) g.n
  rw [sEnter_chain] at hl
  simp only [cBody]
  omega

theorem cCall_bound (g : Digraph) : ∀ f, CallBound g (cCall g f) := by
  intro f
  induction f with
  | zero =>
    intro x w s hw
    unfold cCall
    cases h : (sPre x w s).ent w with
    | some k =>
      simp only [h]
      have e1 : mPot g (({ sPre x w s with stk := (sPre x w s).stk.tail } : SState)).ent g.n = mPot g s.ent g.n := by
        show mPot g (sPre x w s).ent g.n = _
        rw [sPre_ent]
      have e2 : (({ sPre x w s with stk := (sPre x w s).stk.tail } : SState)).chain.length = s.chain.length := by
        show (sPre x w s).chain.length = _
        rw [sPre_chain]
      simp only [e1, e2]
      omega
    | none =>
      simp only [h]
      have e1 : mPot g (sPre x w s).ent g.n = mPot g s.ent g.n := by rw [sPre_ent]
      have e2 : (sPre x w s).chain.length = s.chain.length := by rw [sPre_chain]
      simp only [e1, e2]
      omega
  | succ f ih =>
    intro x w s hw
    unfold cCall
    cases h : (sPre x w s).ent w with
    | some k =>
      simp only [h]
      have e1 : mPot g (({ sPre x w s with stk := (sPre x w s).stk.tail } : SState)).ent g.n = mPot g s.ent g.n := by
        show mPot g (sPre x w s).ent g.n = _
        rw [sPre_ent]
      have e2 : (({ sPre x w s with stk := (sPre x w s).stk.tail } : SState)).chain.length = s.chain.length := by
        show (sPre x w s).chain.length = _
        rw [sPre_chain]
      simp only [e1, e2]
      omega
    | none =>
      simp only [h]
      have hb := cBody_bound (cCall g f) ih w (sPre x w s) hw h
      have e1 : mPot g (sPre x w s).ent g.n = mPot g s.ent g.n := by rw [sPre_ent]
      have e2 : (sPre x w s).chain.length = s.chain.length := by rw [sPre_chain]
      rw [e1, e2] at hb
      omega

theorem cntRun_bound (g : Digraph) (fuel : Nat) : ∀ (vs : List Nat) (s : SState), (∀ v ∈ vs, v < g.n) →
    (cntRun g fuel vs s).1 + mPot g (cntRun g fuel vs s).2.ent g.n + s.chain.length ≤
      mPot g s.ent g.n + vs.length + (cntRun g fuel vs s).2.chain.length := by
  intro vs
  induction vs with
  | nil => intro s _; simp [cntRun]
  | cons v vs ih =>
    intro s hv
    have hvs : ∀ u ∈ vs, u < g.n := fun u hu => hv u (List.mem_cons_of_mem _ hu)
    unfold cntRun
    cases h : s.ent v with
    | some k =>
      simp only []
      have := ih s hvs
      simp only [List.length_cons]
      omega
    | none =>
      simp only []
      have hb := cBody_bound (cCall g fuel) (cCall_bound g fuel) v { s with stk := none :: s.stk } (hv v List.mem_cons_self) h
      have h2 := ih (cBody g (cCall g fuel) v { s with stk := none :: s.stk }).2.2 hvs
      simp only [List.length_cons]
      have e1 : mPot g ({ s with stk := none :: s.stk } : SState).ent g.n = mPot g s.ent g.n := rfl
      have e2 : ({ s with stk := none :: s.stk } : SState).chain.length = s.chain.length := rfl
      rw [e1, e2] at hb
      omega

/-- The potential at the start: every node weighs `2 · out-degree + 4`. -/
theorem mPot_init (g : Digraph) : ∀ k, mPot g (fun _ => none) k = 2 * tEdges (revG g) k + 4 * k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    show mPot g (fun _ => none) k + (if (none : Option Nat) = none then _ else 0) = _
    simp only [↓reduceIte]
    show _ = 2 * (tEdges (revG g) k + (tsuccs (revG g) k).length) + 4 * (k + 1)
    rw [ih]
    omega

theorem tEdges_revG (g : Digraph) : ∀ k, tEdges (revG g) k = tEdges g k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    show tEdges (revG g) k + (tsuccs (revG g) k).length = tEdges g k + (tsuccs g k).length
    rw [ih]
    have : (tsuccs (revG g) k).length = (tsuccs g k).length := by
      simp only [tsuccs, revG, List.filter_reverse, List.length_reverse]
      rfl
    rw [this]

/-- The chain of a finished run is a duplicate-free list of nodes, so it has at most `n` elements. -/
theorem chain_le (f : TwoSat) (hw : f.Wf) (hne : ∀ c ∈ f.clauses, c ≠ []) :
    (sRun f.graph (f.graph.n - 1) (List.range f.graph.n) (SState.init f.graph.n)).chain.length ≤ f.graph.n := by
  obtain ⟨_, _, hnd', hrng', _⟩ := tarjan_spec (revG f.graph)
  have hR := sRun_sim f.graph (f.graph.n - 1) rfl (List.range f.graph.n) TState.init (SState.init f.graph.n)
    (SRel.init f.graph) (by intro v hv; simpa using hv)
  rw [hR.chain]
  show (tarjanSccs (revG f.graph)).flatten.length ≤ f.graph.n
  have hsub : (tarjanSccs (revG f.graph)).flatten ⊆ List.range f.graph.n := by
    intro x hx
    obtain ⟨C, hC, hxC⟩ := List.mem_flatten.1 hx
    exact List.mem_range.2 (hrng' C hC x hxC)
  have := (hnd'.length_le_of_subset hsub)
  simpa using this

/-- G27: the machine performs at most `2 · |E| + 7 · |V|` primitive operations (calls, entries, exits, loop iterations,
popped cells, outer-loop iterations, solution-phase steps) on the implication graph of a formula: linear in the size of the
graph. A statement about the number of primitive operations of the machine of `Spec.SmcMachine`; it says nothing about the
cycles of a processor (a black box, plan D2). -/
theorem smcSteps_le (f : TwoSat) (hw : f.Wf) (hne : ∀ c ∈ f.clauses, c ≠ []) :
    smcSteps f ≤ 2 * tEdges f.graph f.graph.n + 7 * f.graph.n := by
  have hb := cntRun_bound f.graph (f.graph.n - 1) (List.range f.graph.n) (SState.init f.graph.n)
    (by intro v hv; simpa using hv)
  have hp : mPot f.graph (SState.init f.graph.n).ent f.graph.n = 2 * tEdges f.graph f.graph.n + 4 * f.graph.n := by
    show mPot f.graph (fun _ => none) f.graph.n = _
    rw [mPot_init, tEdges_revG]
  have hc := chain_le f hw hne
  rw [cntRun_state] at hb
  rw [hp] at hb
  have hc' : (sRun f.graph (f.graph.n - 1) (List.range f.graph.n) (SState.init f.graph.n)).chain.length ≤ f.graph.n := hc
  unfold smcSteps
  dsimp only
  rw [cntRun_state]
  simp only [List.length_range] at hb
  have e0 : (SState.init f.graph.n).chain.length = 0 := rfl
  omega

end SmcIrred
