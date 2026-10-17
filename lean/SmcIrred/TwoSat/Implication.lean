module

public import SmcIrred.Spec.TwoSat

public section

namespace SmcIrred

theorem Lit.neg_neg (l : Lit) : l.neg.neg = l := by cases l; simp [Lit.neg]

theorem Lit.holds_neg (a : Nat → Bool) (l : Lit) : l.neg.Holds a ↔ ¬ l.Holds a := by
  unfold Lit.Holds Lit.neg; simp only; cases a l.var <;> cases l.pos <;> simp

theorem Lit.ofNode_node (l : Lit) : Lit.ofNode l.node = l := by
  cases l with
  | mk v p => cases p <;> simp [Lit.node, Lit.ofNode] <;> omega

theorem Lit.node_ofNode (u : Nat) : (Lit.ofNode u).node = u := by
  unfold Lit.node Lit.ofNode; simp only; by_cases h : u % 2 = 0 <;> simp [h] <;> omega

theorem Lit.node_inj {a b : Lit} (h : a.node = b.node) : a = b := by
  have := congrArg Lit.ofNode h
  rwa [Lit.ofNode_node, Lit.ofNode_node] at this

theorem Lit.node_lt {n : Nat} {l : Lit} (h : l.var < n) : l.node < 2 * n := by
  unfold Lit.node; split <;> omega

theorem Lit.node_neg (l : Lit) : l.neg.node = if l.pos then l.node + 1 else l.node - 1 := by
  cases l with
  | mk v p => cases p <;> simp [Lit.node, Lit.neg] <;> omega

/-- C24: `(p ∨ q)` is equivalent to `(¬p → q) ∧ (¬q → p)`. -/
theorem or_iff_implications (p q : Prop) : (p ∨ q) ↔ ((¬ p → q) ∧ (¬ q → p)) := by
  constructor
  · rintro (hp | hq)
    · exact ⟨fun hn => absurd hp hn, fun _ => hp⟩
    · exact ⟨fun _ => hq, fun hn => absurd hq hn⟩
  · rintro ⟨h1, h2⟩
    exact Classical.byCases (fun hp : p => Or.inl hp) (fun hp => Or.inr (h1 hp))

/-- A clause of at most two literals is satisfied iff it is not empty and every implication it yields is respected. -/
theorem clauseSat_iff {a : Nat → Bool} {c : List Lit} (hc : c.length ≤ 2) :
    ClauseSat a c ↔ c ≠ [] ∧ ∀ e ∈ clauseImps c, e.1.Holds a → e.2.Holds a := by
  match c, hc with
  | [], _ => simp [ClauseSat, clauseImps]
  | [p], _ =>
    simp only [ClauseSat, clauseImps, List.mem_singleton, forall_eq, ne_eq, List.cons_ne_nil, not_false_eq_true,
      true_and, List.mem_cons, exists_eq_or_imp, List.not_mem_nil, or_false, exists_eq_left]
    rw [Lit.holds_neg]
    exact ⟨fun h _ => h, fun h => Classical.byContradiction fun hn => hn (h hn)⟩
  | [p, q], _ =>
    simp only [ClauseSat, clauseImps, List.mem_cons, List.not_mem_nil, or_false, ne_eq, reduceCtorEq, not_false_eq_true,
      true_and, forall_eq_or_imp, forall_eq, exists_eq_or_imp, exists_eq_left]
    rw [Lit.holds_neg, Lit.holds_neg]
    constructor
    · intro h; exact ⟨fun hn => (or_iff_implications _ _).1 h |>.1 hn, fun hn => (or_iff_implications _ _).1 h |>.2 hn⟩
    · intro h; exact (or_iff_implications _ _).2 h
  | _ :: _ :: _ :: _, h => exact absurd h (by simp)

/-- C24/C22: an assignment satisfies the formula iff no clause is empty and the assignment is closed under the
implications of the implication graph (no edge from a true to a false literal). -/
theorem sat_iff_closed {f : TwoSat} (hw : f.Wf) {a : Nat → Bool} :
    f.Sat a ↔ (∀ c ∈ f.clauses, c ≠ []) ∧ ∀ e ∈ f.imps, e.1.Holds a → e.2.Holds a := by
  constructor
  · intro h
    refine ⟨fun c hc => ((clauseSat_iff (hw c hc).1).1 (h c hc)).1, fun e he => ?_⟩
    obtain ⟨c, hc, hec⟩ := List.mem_flatMap.1 he
    exact ((clauseSat_iff (hw c hc).1).1 (h c hc)).2 e hec
  · rintro ⟨hne, hcl⟩ c hc
    exact (clauseSat_iff (hw c hc).1).2 ⟨hne c hc, fun e he => hcl e (List.mem_flatMap.2 ⟨c, hc, he⟩)⟩

theorem graph_edge_iff (f : TwoSat) (u w : Nat) :
    f.graph.edge u w ↔ u < 2 * f.n ∧ w < 2 * f.n ∧ ∃ e ∈ f.imps, e.1.node = u ∧ e.2.node = w := by
  unfold Digraph.edge
  simp only [TwoSat.graph, List.mem_map, List.mem_filter, beq_iff_eq]
  constructor
  · rintro ⟨h1, h2, e, ⟨he, hu⟩, hw⟩
    exact ⟨h1, h2, e, he, hu, hw⟩
  · rintro ⟨h1, h2, e, he, hu, hw⟩
    exact ⟨h1, h2, e, ⟨he, hu⟩, hw⟩

/-- The implications come in contrapositive pairs: `p → q` and `¬q → ¬p`. -/
theorem imps_skew {f : TwoSat} {e : Lit × Lit} (he : e ∈ f.imps) : (e.2.neg, e.1.neg) ∈ f.imps := by
  obtain ⟨c, hc, hec⟩ := List.mem_flatMap.1 he
  refine List.mem_flatMap.2 ⟨c, hc, ?_⟩
  match c, hec with
  | [], h => simp [clauseImps] at h
  | [p], h =>
    simp only [clauseImps, List.mem_singleton] at h ⊢
    subst h; simp [Lit.neg_neg]
  | [p, q], h =>
    simp only [clauseImps, List.mem_cons, List.not_mem_nil, or_false] at h ⊢
    rcases h with rfl | rfl <;> simp [Lit.neg_neg]
  | _ :: _ :: _ :: _, h => simp [clauseImps] at h

/-- An assignment closed under the implications is monotone along paths of the implication graph. -/
theorem closed_reach {f : TwoSat} {a : Nat → Bool} (hcl : ∀ e ∈ f.imps, e.1.Holds a → e.2.Holds a) {u w : Nat}
    (h : f.graph.Reach u w) : (Lit.ofNode u).Holds a → (Lit.ofNode w).Holds a := by
  induction h with
  | refl _ => exact id
  | @step x y z he _ ih =>
    intro hu
    obtain ⟨-, -, e, hmem, hn1, hn2⟩ := (graph_edge_iff f _ _).1 he
    have e1 : e.1 = Lit.ofNode x := by rw [← hn1, Lit.ofNode_node]
    have e2 : e.2 = Lit.ofNode y := by rw [← hn2, Lit.ofNode_node]
    apply ih
    have := hcl e hmem
    rw [e1, e2] at this
    exact this hu

end SmcIrred
