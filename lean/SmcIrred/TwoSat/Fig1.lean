module

public import SmcIrred.TwoSat.APT

public section

namespace SmcIrred

instance (a : Nat → Bool) (l : Lit) : Decidable (l.Holds a) := by unfold Lit.Holds; infer_instance
instance (a : Nat → Bool) (c : List Lit) : Decidable (ClauseSat a c) := by unfold ClauseSat; infer_instance
instance (f : TwoSat) (a : Nat → Bool) : Decidable (f.Sat a) := by unfold TwoSat.Sat; infer_instance

/-- The paper's literal `k` (variables `x₁ … x₈`, negative `k` for `¬x_{|k|}`) as a literal of variable `|k| - 1`. -/
@[expose] def paperLit (k : Int) : Lit := ⟨k.natAbs - 1, decide (0 < k)⟩

/-- The formula of Fig. 1: `(x₁∨x₄)(¬x₂∨x₅)(x₃∨x₇)(x₂∨¬x₅)(¬x₈∨¬x₂)(x₃∨¬x₁)(x₄∨¬x₃)(x₅∨¬x₄)(¬x₃∨¬x₇)(x₆∨x₇)(x₁∨x₇)(¬x₇∨¬x₁)`. -/
@[expose] def fig1 : TwoSat :=
  ⟨8, ([[1, 4], [-2, 5], [3, 7], [2, -5], [-8, -2], [3, -1], [4, -3], [5, -4], [-3, -7], [6, 7], [1, 7], [-7, -1]] :
    List (List Int)).map (List.map paperLit)⟩

/-- The 24 edges drawn in Fig. 1 (paper literal numbering). -/
@[expose] def fig1Edges : List (Int × Int) :=
  [(2, 5), (5, 2), (-1, 7), (-3, -1), (-3, 7), (7, -3), (7, -1), (1, -7), (1, 3), (3, -7), (-7, 1), (-7, 3),
   (-2, -5), (-5, -2), (-1, 4), (-4, 1), (-4, -3), (4, 5), (2, -8), (-5, -4), (3, 4), (-7, 6), (8, -2), (-6, 7)]

/-- The strongly connected component numbers drawn in Fig. 1 (the order Tarjan's algorithm emits them). -/
@[expose] def fig1Scc : List (List Int) :=
  [[-8], [2, 5], [4], [-1, 7, -3], [6], [1, -7, 3], [-4], [-2, -5], [8], [-6]]

/-- The label (1 … 10) of the vertex `u` of the implication graph of `fig1`. -/
@[expose] def fig1Label (u : Nat) : Nat :=
  let k : Int := if u % 2 = 0 then (u / 2 + 1 : Nat) else -((u / 2 + 1 : Nat) : Int)
  ((fig1Scc.findIdx fun s => decide (k ∈ s)) + 1)

theorem fig1_wf : fig1.Wf := by unfold TwoSat.Wf; decide

theorem fig1_nonempty : ∀ c ∈ fig1.clauses, c ≠ [] := by decide

/-- The implication graph of `fig1` has exactly the 24 edges of the figure. -/
theorem fig1_edges :
    fig1.imps.length = 24 ∧
    ∀ u, u < 16 → ∀ w, w < 16 →
      (w ∈ fig1.graph.succ u ↔ ∃ p ∈ fig1Edges, (paperLit p.1).node = u ∧ (paperLit p.2).node = w) := by
  refine ⟨by decide, ?_⟩
  decide

/-- The drawn numbering is a labelling of the kind `apt_correct` needs: equal labels are one component, and labels do
not increase along an implication. -/
theorem fig1_label_ok :
    (∀ u, u < 16 → ∀ w, w < 16 → fig1Label u = fig1Label w → fig1.graph.SameSCC u w) ∧
    (∀ e ∈ fig1.imps, fig1Label e.2.node ≤ fig1Label e.1.node) := by
  refine ⟨?_, by decide⟩
  decide

/-- The green literals of Fig. 1 are the assignment read off the labels, and it satisfies the formula. -/
theorem fig1_apt :
    fig1.Sat (aptAssign fig1Label) ∧
    (List.range 8).map (fun x => aptAssign fig1Label x) = [false, true, false, true, true, true, true, false] := by
  constructor
  · decide
  · decide

/-- Of the 256 assignments of `x₁ … x₈`, exactly 3 satisfy the formula (bit `x` of the mask is the value of variable `x`). -/
theorem fig1_count :
    ((List.range 256).filter fun m => decide (fig1.Sat fun x => Nat.testBit m x)).length = 3 := by
  decide +kernel

end SmcIrred
