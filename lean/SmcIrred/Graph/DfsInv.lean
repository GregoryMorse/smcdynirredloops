module

public import SmcIrred.Graph.RunDFS

public section

namespace SmcIrred

/-- Number of undiscovered vertices (the fuel measure). -/
@[expose] def DfsState.undisc (g : Digraph) (s : DfsState) : Nat := ((List.range g.n).filter fun x => s.pre x = 0).length

/-- Stamps are below the clock; a finished vertex was discovered earlier. -/
structure DfsState.Wf (s : DfsState) : Prop where
  clock : 1 ≤ s.clock
  pre_lt : ∀ x, s.pre x < s.clock
  post_lt : ∀ x, s.post x < s.clock
  post_pre : ∀ x, s.post x ≠ 0 → s.pre x ≠ 0 ∧ s.pre x < s.post x

/-- `x` is discovered between the states `s` and `s'`. -/
@[expose, reducible] def DfsState.New (s s' : DfsState) (x : Nat) : Prop := s.pre x = 0 ∧ s'.pre x ≠ 0

/-- Ancestor relation of the final stamps in `s'`. -/
@[expose, reducible] def DfsState.Anc (s' : DfsState) (a b : Nat) : Prop := s'.pre a ≤ s'.pre b ∧ s'.post b ≤ s'.post a

theorem filter_len_le {p q : Nat → Bool} (h : ∀ x, p x = true → q x = true) (l : List Nat) :
    (l.filter p).length ≤ (l.filter q).length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    cases hp : p a <;> cases hq : q a <;> simp [hp, hq] <;> first | omega | (have := h a hp; simp_all)

theorem filter_len_lt {p q : Nat → Bool} (h : ∀ x, p x = true → q x = true) {v : Nat} {l : List Nat} (hv : v ∈ l)
    (hp : p v = false) (hq : q v = true) : (l.filter p).length < (l.filter q).length := by
  induction l with
  | nil => simp at hv
  | cons a l ih =>
    by_cases hav : a = v
    · subst hav
      have := filter_len_le h l
      simp [hp, hq]; omega
    · have hmem : v ∈ l := by simpa [Ne.symm hav] using hv
      have := ih hmem
      cases hpa : p a <;> cases hqa : q a <;> simp [hpa, hqa] <;> first | omega | (have := h a hpa; simp_all)

theorem undisc_le {g : Digraph} {s s' : DfsState} (h : ∀ x, s.pre x ≠ 0 → s'.pre x ≠ 0) :
    s'.undisc g ≤ s.undisc g := by
  unfold DfsState.undisc
  apply filter_len_le
  intro x hx
  simp only [decide_eq_true_eq] at hx ⊢
  by_cases hc : s.pre x = 0
  · exact hc
  · exact absurd hx (h x hc)

theorem undisc_lt {g : Digraph} {s s' : DfsState} (h : ∀ x, s.pre x ≠ 0 → s'.pre x ≠ 0) {v : Nat}
    (hv : v < g.n) (h0 : s.pre v = 0) (h1 : s'.pre v ≠ 0) : s'.undisc g < s.undisc g := by
  unfold DfsState.undisc
  refine filter_len_lt (v := v) ?_ (List.mem_range.2 hv) ?_ ?_
  · intro x hx
    simp only [decide_eq_true_eq] at hx ⊢
    by_cases hc : s.pre x = 0
    · exact hc
    · exact absurd hx (h x hc)
  · simpa using h1
  · simpa using h0

end SmcIrred
