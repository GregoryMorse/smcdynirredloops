module

public import SmcIrred.Prims.Eval

public section

namespace SmcIrred

/-! # The generated graph computes what the generator state evaluates (G30 b)

For a generator state built from simple nodes with earlier predecessors (`Reach`), the circuit `gb.toCirc` evaluated by the
Boolean-CFG evaluator `Circ.val` (any nesting depth, any library) has at every vertex the value `evalNodes` assigns to it. -/

theorem cnt_map_eq (acc : Nat → Bool) (l : List Nat) : cnt acc l = ((l.map acc).filter id).length := by
  unfold cnt
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.filter_cons, List.map_cons]
    cases h : acc a <;> simp [h, ih]

theorem evalNodes_get_new (inp : Nat → Bool) (nodes : List (Kind × List Nat)) (nd : Kind × List Nat) :
    (evalNodes inp (nodes ++ [nd])).getD nodes.length false =
      nodeVal nd.1 (nd.2.map fun u => (evalNodes inp nodes).getD u false) (inp nodes.length) := by
  rw [evalNodes_append]
  simp only [List.foldl_cons, List.foldl_nil, stepE]
  have hl : (evalNodes inp nodes).length = nodes.length := evalNodes_len inp nodes
  rw [← hl]
  simp [List.getD_eq_getElem?_getD]

theorem reach_local (inp : Nat → Bool) {gb : GB} (hr : Reach gb) : ∀ v, v < gb.n →
    (∀ u ∈ (gb.nodes.getD v (.flow, [])).2, u < v) ∧
    (evalNodes inp gb.nodes).getD v false =
      nodeVal (gb.nodes.getD v (.flow, [])).1
        ((gb.nodes.getD v (.flow, [])).2.map fun u => (evalNodes inp gb.nodes).getD u false) (inp v) := by
  induction hr with
  | empty => intro v hv; simp [GB.n] at hv
  | @add gb k ps hr0 hs hps ih =>
    intro v hv
    have hn : (gb.add k ps).2.nodes = gb.nodes ++ [(k, ps)] := rfl
    simp only [GB.n, hn, List.length_append, List.length_singleton] at hv
    by_cases hlt : v < gb.n
    · have hgetv : (gb.nodes ++ [(k, ps)]).getD v (.flow, []) = gb.nodes.getD v (.flow, []) := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
      obtain ⟨h1, h2⟩ := ih v hlt
      rw [hn, hgetv]
      refine ⟨h1, ?_⟩
      have e : ∀ u, u < gb.n → (evalNodes inp (gb.nodes ++ [(k, ps)])).getD u false = (evalNodes inp gb.nodes).getD u false :=
        fun u hu => evalNodes_ext (gb := gb) (gb' := (gb.add k ps).2) ⟨[(k, ps)], rfl⟩ hu
      rw [e v hlt, h2]
      congr 1
      apply List.map_congr_left
      intro u hu
      exact (e u (Nat.lt_trans (h1 u hu) hlt)).symm
    · have hv' : v = gb.n := by simp only [GB.n] at hlt hv ⊢; omega
      subst hv'
      have hgetv : (gb.nodes ++ [(k, ps)]).getD gb.n (.flow, []) = (k, ps) := by
        simp [GB.n, List.getD_eq_getElem?_getD]
      rw [hn]
      simp only [GB.n] at hgetv ⊢
      rw [hgetv]
      refine ⟨fun u hu => hps u hu, ?_⟩
      rw [evalNodes_get_new]
      congr 1
      apply List.map_congr_left
      intro u hu
      exact (evalNodes_ext (gb := gb) (gb' := (gb.add k ps).2) ⟨[(k, ps)], rfl⟩ (hps u hu)).symm

theorem baseVal_nodeVal (c : Circ) (inp acc : Nat → Bool) (v : Nat) (hs : Simple (c.kind v)) :
    baseVal c inp acc v = nodeVal (c.kind v) ((c.pred v).map acc) (inp v) := by
  unfold baseVal nodeVal
  simp only [cnt_map_eq, List.length_map]
  cases hk : c.kind v <;> simp_all [Simple]

theorem reach_simple {gb : GB} (hr : Reach gb) : ∀ v, v < gb.n → Simple (gb.toCirc.kind v) := by
  induction hr with
  | empty => intro v hv; simp [GB.n] at hv
  | @add gb k ps hr0 hs hps ih =>
    intro v hv
    have hn : (gb.add k ps).2.nodes = gb.nodes ++ [(k, ps)] := rfl
    simp only [GB.n, hn, List.length_append, List.length_singleton] at hv
    show Simple (((gb.add k ps).2.nodes.getD v (.flow, [])).1)
    rw [hn]
    by_cases hlt : v < gb.n
    · have : (gb.nodes ++ [(k, ps)]).getD v (.flow, []) = gb.nodes.getD v (.flow, []) := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
      rw [this]; exact ih v hlt
    · have hv' : v = gb.n := by simp only [GB.n] at hlt hv ⊢; omega
      subst hv'
      have : (gb.nodes ++ [(k, ps)]).getD gb.n (.flow, []) = (k, ps) := by
        simp [GB.n, List.getD_eq_getElem?_getD]
      rw [this]; exact hs

theorem valAt_eq_evalNodes (inp : Nat → Bool) (lib : Lib) (V : Circ → (Nat → Bool) → Nat → Nat → Bool) {gb : GB}
    (hr : Reach gb) : ∀ f v, v < f → v < gb.n →
    valAt lib V gb.toCirc inp f v = (evalNodes inp gb.nodes).getD v false := by
  intro f
  induction f with
  | zero => intro v hv; omega
  | succ f ih =>
    intro v hvf hvn
    obtain ⟨hlt, hval⟩ := reach_local inp hr v hvn
    have hsimp := reach_simple hr
    unfold valAt
    dsimp only
    have hw : ((gb.toCirc.pred v).any fun u => writtenBy lib V (valAt lib V gb.toCirc inp f) gb.toCirc u v) = false := by
      rw [List.any_eq_false]
      intro u hu
      have hu' : u < v := hlt u hu
      have := hsimp u (by omega)
      unfold writtenBy
      cases hk : gb.toCirc.kind u <;> simp_all [Simple]
    rw [hw, Bool.or_false, baseVal_nodeVal _ _ _ _ (hsimp v hvn), hval]
    show nodeVal (gb.toCirc.kind v) _ _ = nodeVal (gb.nodes.getD v (.flow, [])).1 _ _
    congr 1
    apply List.map_congr_left
    intro u hu
    exact ih u (Nat.lt_of_lt_of_le (hlt u hu) (by omega)) (by have := hlt u hu; omega)

theorem toCirc_val_eq (inp : Nat → Bool) (lib : Lib) (d : Nat) {gb : GB} (hr : Reach gb) {v : Nat} (hv : v < gb.n) :
    gb.toCirc.val lib d inp v = (evalNodes inp gb.nodes).getD v false := by
  unfold Circ.val
  cases d with
  | zero => exact valAt_eq_evalNodes inp lib _ hr _ v hv hv
  | succ d => exact valAt_eq_evalNodes inp lib _ hr _ v hv hv

end SmcIrred
