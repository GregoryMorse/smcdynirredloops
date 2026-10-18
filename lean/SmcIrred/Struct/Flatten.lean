module

public import SmcIrred.Spec.Flatten
public import SmcIrred.Graph.Fig4

public section

namespace SmcIrred.Struct

variable {g : Digraph} {lab : Nat → List Nat} {ch : Nat → Nat}

/-- Well-formed graph: all successors are vertices. -/
@[expose] def WFg (g : Digraph) : Prop := ∀ v, v < g.n → ∀ w, w ∈ g.succ v → w < g.n

theorem nextState_lt (hwf : WFg g) {v : Nat} (hv : v < g.n) (k : Nat) (hne : g.succ v ≠ []) :
    nextState g ch v k < g.n := by
  unfold nextState
  rcases hs : g.succ v with _ | ⟨a, l⟩
  · exact absurd hs hne
  · simp only
    have hlt : ch k % (a :: l).length < (a :: l).length := Nat.mod_lt _ (by simp)
    have hmem : (a :: l).getD (ch k % (a :: l).length) g.n ∈ g.succ v := by
      have e : (a :: l).getD (ch k % (a :: l).length) g.n = (a :: l)[ch k % (a :: l).length] := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]; rfl
      rw [hs, e]
      exact List.getElem_mem hlt
    exact hwf v hv _ hmem

theorem frun_exit_inv {k : Nat} {t : List Nat} (h : FRun g lab ch g.n k t) : t = [] := by
  cases h with
  | exit => rfl
  | step hs _ => exact absurd rfl hs

/-- C31: the CFG semantics equals the semantics of the flat program with the single variable `state`, for every
condition-output sequence (trace equivalence, from every vertex). -/
theorem flatten_iff (hwf : WFg g) {t : List Nat} {v k : Nat} (hv : v < g.n) :
    Walk g lab ch v k t ↔ FRun g lab ch v k t := by
  constructor
  · intro h
    induction h with
    | @stop v k hs =>
      have hne : v ≠ g.n := by omega
      have h0 : nextState g ch v k = g.n := by simp [nextState, hs]
      have := FRun.step (g := g) (lab := lab) (ch := ch) (k := k) (s := v) hne (t := [])
        (by rw [h0]; exact .exit)
      simpa using this
    | go hne _ ih =>
      exact .step (by omega) (ih (nextState_lt hwf hv _ hne))
  · intro h
    induction h with
    | exit => omega
    | @step s k t hs h' ih =>
      by_cases hne : g.succ s = []
      · have h0 : nextState g ch s k = g.n := by simp [nextState, hne]
        rw [h0] at h'
        have := frun_exit_inv h'
        subst this
        simpa using Walk.stop (g := g) (lab := lab) (ch := ch) (k := k) hne
      · exact .go hne (ih (nextState_lt hwf hv k hne))

/-- The single variable ranges over `|V| + 1` values: after every move the state is a vertex or `EXIT`. -/
theorem state_range (hwf : WFg g) {s : Nat} (hs : s < g.n) (k : Nat) : nextState g ch s k < g.n + 1 := by
  by_cases hne : g.succ s = []
  · have h0 : nextState g ch s k = g.n := by simp [nextState, hne]
    omega
  · have := nextState_lt (ch := ch) hwf hs k hne
    omega

/-- The CFG of Figure 4 (irreducible) is well formed, so it is the flat program `while (state != EXIT) switch (state)` over
the seven values `0 … 6` with one variable. -/
theorem fig4_wf : WFg fig4 := by
  have key : ∀ v, v < 6 → ∀ w, w ∈ fig4.succ v → w < 6 := by decide
  exact key

end SmcIrred.Struct
