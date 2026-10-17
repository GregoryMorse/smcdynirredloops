module

public import SmcIrred.Graph.DfsInv

public section

namespace SmcIrred

/-- Summary of one completed visit of `v` from state `s` to state `s'` (`New` = discovered during the visit). -/
structure Done (g : Digraph) (v : Nat) (s s' : DfsState) : Prop where
  clock : s.clock + 2 ≤ s'.clock
  wf : s'.Wf
  unchanged : ∀ x, ¬ s.New s' x → s'.pre x = s.pre x ∧ s'.post x = s.post x
  new : ∀ x, s.New s' x → x < g.n ∧ s.clock ≤ s'.pre x ∧ s'.pre x < s'.post x ∧ s'.post x < s'.clock
  vroot : s'.pre v = s.clock ∧ s'.post v + 1 = s'.clock
  contain : ∀ x, s.New s' x → s'.pre v ≤ s'.pre x ∧ s'.post x ≤ s'.post v
  distinct : ∀ x y, s.New s' x → s.New s' y →
    (s'.pre x = s'.pre y → x = y) ∧ (s'.post x = s'.post y → x = y) ∧ s'.pre x ≠ s'.post y
  laminar : ∀ x y, s.New s' x → s.New s' y →
    s'.Anc x y ∨ s'.Anc y x ∨ s'.post x < s'.pre y ∨ s'.post y < s'.pre x
  parent : ∀ x, s.New s' x → x ≠ v → ∃ u, s.New s' u ∧ g.edge u x ∧ u ≠ x ∧ s'.Anc u x ∧
    ∀ w, s.New s' w → w ≠ x → s'.Anc w x → s'.Anc w u
  closure : ∀ x, s.New s' x → ∀ y, g.edge x y → s'.pre y ≠ 0 ∧ s'.pre y < s'.post x

/-- Invariant of the loop over the successors of `v`: `s1` is the state right after discovering `v`, `sk` the current
state, `done` the successors processed so far. -/
structure Loop (g : Digraph) (v : Nat) (s1 : DfsState) (done : List Nat) (sk : DfsState) : Prop where
  clock : s1.clock ≤ sk.clock
  wf : sk.Wf
  unchanged : ∀ x, ¬ s1.New sk x → sk.pre x = s1.pre x ∧ sk.post x = s1.post x
  new : ∀ x, s1.New sk x → x < g.n ∧ s1.clock ≤ sk.pre x ∧ sk.pre x < sk.post x ∧ sk.post x < sk.clock
  distinct : ∀ x y, s1.New sk x → s1.New sk y →
    (sk.pre x = sk.pre y → x = y) ∧ (sk.post x = sk.post y → x = y) ∧ sk.pre x ≠ sk.post y
  laminar : ∀ x y, s1.New sk x → s1.New sk y →
    sk.Anc x y ∨ sk.Anc y x ∨ sk.post x < sk.pre y ∨ sk.post y < sk.pre x
  parent : ∀ x, s1.New sk x →
    (∃ u, s1.New sk u ∧ g.edge u x ∧ u ≠ x ∧ sk.Anc u x ∧ ∀ w, s1.New sk w → w ≠ x → sk.Anc w x → sk.Anc w u) ∨
    (g.edge v x ∧ ∀ w, s1.New sk w → w ≠ x → ¬ sk.Anc w x)
  closure : ∀ x, s1.New sk x → ∀ y, g.edge x y → sk.pre y ≠ 0 ∧ sk.pre y < sk.post x
  proc : ∀ w ∈ done, w < g.n → sk.pre w ≠ 0

theorem Loop.init {g : Digraph} {v : Nat} {s1 : DfsState} (h : s1.Wf) : Loop g v s1 [] s1 where
  clock := Nat.le_refl _
  wf := h
  unchanged := fun _ _ => ⟨rfl, rfl⟩
  new := fun x hx => absurd hx.2 (by simp [hx.1])
  distinct := fun x _ hx => absurd hx.2 (by simp [hx.1])
  laminar := fun x _ hx => absurd hx.2 (by simp [hx.1])
  parent := fun x hx => absurd hx.2 (by simp [hx.1])
  closure := fun x hx => absurd hx.2 (by simp [hx.1])
  proc := fun _ hw => absurd hw (by simp)

end SmcIrred
