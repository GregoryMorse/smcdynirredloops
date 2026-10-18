module

public import SmcIrred.Prims.Gates
public import SmcIrred.Spec.Virt
public import SmcIrred.Circuit.Order

public section

namespace SmcIrred

/-! ### The local rule of a vertex (call-free, table-free kinds) and the evaluation of a generator state -/

@[expose] def nodeVal (k : Kind) (vs : List Bool) (t : Bool) : Bool :=
  let a := (vs.filter id).length + (if t then 1 else 0)
  let l := vs.length + (if t then 1 else 0)
  match k with
  | .flow => decide (l ≠ 0 ∧ a = l)
  | .any => decide (l ≠ 0 ∧ a ≠ 0)
  | .add => decide (a % 2 = 1)
  | .addneg => decide (a % 2 = 0)
  | _ => false

@[expose] def stepE (inp : Nat → Bool) (vs : List Bool) (nd : Kind × List Nat) : List Bool :=
  vs ++ [nodeVal nd.1 (nd.2.map fun u => vs.getD u false) (inp vs.length)]

@[expose] def evalNodes (inp : Nat → Bool) (nodes : List (Kind × List Nat)) : List Bool :=
  nodes.foldl (stepE inp) []

@[expose] def Wire.ev (vs : List Bool) : Wire → Bool
  | .cst b => b
  | .nd i => vs.getD i false

/-- The value of a wire in the state `gb` under the active inputs `inp`. -/
@[expose] def wev (gb : GB) (inp : Nat → Bool) (w : Wire) : Bool := w.ev (evalNodes inp gb.nodes)

@[expose] def Wire.ok (n : Nat) : Wire → Prop
  | .cst _ => True
  | .nd i => i < n

/-- Simple kinds: the four logic kinds. -/
@[expose] def Simple : Kind → Prop
  | .flow => True
  | .any => True
  | .add => True
  | .addneg => True
  | _ => False

/-- States built by adding nodes with simple kinds whose predecessors already exist. -/
inductive Reach : GB → Prop
  | empty : Reach ⟨[]⟩
  | add {gb : GB} (k : Kind) (ps : List Nat) : Reach gb → Simple k → (∀ u ∈ ps, u < gb.n) → Reach (gb.add k ps).2

@[expose] def Ext (gb gb' : GB) : Prop := ∃ ext, gb'.nodes = gb.nodes ++ ext

theorem Ext.refl (gb : GB) : Ext gb gb := ⟨[], by simp⟩
theorem Ext.trans {a b c : GB} (h1 : Ext a b) (h2 : Ext b c) : Ext a c := by
  obtain ⟨e1, h1⟩ := h1
  obtain ⟨e2, h2⟩ := h2
  exact ⟨e1 ++ e2, by rw [h2, h1, List.append_assoc]⟩

theorem Ext.n_le {a b : GB} (h : Ext a b) : a.n ≤ b.n := by
  obtain ⟨e, h⟩ := h
  unfold GB.n; rw [h]; simp

theorem foldl_stepE_len (inp : Nat → Bool) (b : List (Kind × List Nat)) :
    ∀ vs : List Bool, (b.foldl (stepE inp) vs).length = vs.length + b.length := by
  induction b with
  | nil => intro vs; simp
  | cons x t ih => intro vs; simp only [List.foldl_cons, ih, stepE, List.length_append, List.length_cons]; simp; omega

theorem foldl_stepE_prefix (inp : Nat → Bool) (b : List (Kind × List Nat)) :
    ∀ vs : List Bool, ∃ r, b.foldl (stepE inp) vs = vs ++ r := by
  induction b with
  | nil => intro vs; exact ⟨[], by simp⟩
  | cons x t ih =>
    intro vs
    obtain ⟨r, hr⟩ := ih (stepE inp vs x)
    refine ⟨[nodeVal x.1 (x.2.map fun u => vs.getD u false) (inp vs.length)] ++ r, ?_⟩
    rw [List.foldl_cons, hr]
    unfold stepE
    rw [List.append_assoc]

theorem evalNodes_len (inp : Nat → Bool) (nodes : List (Kind × List Nat)) : (evalNodes inp nodes).length = nodes.length := by
  unfold evalNodes; rw [foldl_stepE_len]; simp

theorem evalNodes_append (inp : Nat → Bool) (a b : List (Kind × List Nat)) :
    evalNodes inp (a ++ b) = b.foldl (stepE inp) (evalNodes inp a) := by
  unfold evalNodes; rw [List.foldl_append]

theorem evalNodes_ext {inp : Nat → Bool} {gb gb' : GB} (h : Ext gb gb') {i : Nat} (hi : i < gb.n) :
    (evalNodes inp gb'.nodes).getD i false = (evalNodes inp gb.nodes).getD i false := by
  obtain ⟨e, he⟩ := h
  rw [he, evalNodes_append]
  obtain ⟨r, hr⟩ := foldl_stepE_prefix inp e (evalNodes inp gb.nodes)
  rw [hr]
  have : i < (evalNodes inp gb.nodes).length := by rw [evalNodes_len]; exact hi
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left this]

theorem wev_ext {inp : Nat → Bool} {gb gb' : GB} (h : Ext gb gb') {w : Wire} (hw : w.ok gb.n) :
    wev gb' inp w = wev gb inp w := by
  cases w with
  | cst b => rfl
  | nd i => exact evalNodes_ext h hw

/-- Facts that every gadget guarantees about its result. -/
structure Post (gb gb' : GB) (inp : Nat → Bool) (w : Wire) (v : Bool) : Prop where
  ext : Ext gb gb'
  reach : Reach gb'
  ok : w.ok gb'.n
  val : wev gb' inp w = v

/-- Adding a node. -/
theorem add_post {gb : GB} {inp : Nat → Bool} {k : Nat} (hinp : ∀ i, k ≤ i → inp i = false) (hk : k ≤ gb.n)
    (hr : Reach gb) (kind : Kind) (ps : List Nat) (hs : Simple kind) (hps : ∀ u ∈ ps, u < gb.n) :
    Post gb (gb.add kind ps).2 inp (gb.add kind ps).1
      (nodeVal kind (ps.map fun u => wev gb inp (.nd u)) false) := by
  refine ⟨⟨[(kind, ps)], rfl⟩, Reach.add kind ps hr hs hps, ?_, ?_⟩
  · show gb.n < (gb.add kind ps).2.n
    simp [GB.add, GB.n]
  · show (evalNodes inp (gb.nodes ++ [(kind, ps)])).getD gb.n false = _
    rw [evalNodes_append]
    simp only [List.foldl_cons, List.foldl_nil, stepE]
    have hl : (evalNodes inp gb.nodes).length = gb.n := evalNodes_len inp gb.nodes
    have hi : inp (evalNodes inp gb.nodes).length = false := by rw [hl]; exact hinp _ hk
    rw [hi]
    have : (evalNodes inp gb.nodes ++ [nodeVal (kind, ps).1 ((kind, ps).2.map fun u => (evalNodes inp gb.nodes).getD u false) false]).getD
        gb.n false = nodeVal kind (ps.map fun u => (evalNodes inp gb.nodes).getD u false) false := by
      rw [← hl]; simp [List.getD_eq_getElem?_getD]
    rw [this]
    rfl

/-! ### Counting rules of the local rule -/

theorem fl_true (t : List Bool) : (true :: t).filter id = true :: t.filter id := rfl
theorem fl_false (t : List Bool) : (false :: t).filter id = t.filter id := rfl

theorem cnt_all (vs : List Bool) : (vs.filter id).length = vs.length ↔ andL vs = true := by
  induction vs with
  | nil => simp [andL]
  | cons b t ih =>
    rw [andL_cons]
    cases b
    · rw [fl_false, List.length_cons]
      have := List.length_filter_le id t
      simp only [Bool.false_and]
      constructor
      · intro h; omega
      · intro h; exact absurd h (by simp)
    · rw [fl_true, List.length_cons, List.length_cons, Bool.true_and]
      constructor
      · intro h; exact ih.1 (by omega)
      · intro h; have := ih.2 h; omega

theorem cnt_pos (vs : List Bool) : (vs.filter id).length ≠ 0 ↔ orL vs = true := by
  induction vs with
  | nil => simp [orL]
  | cons b t ih =>
    rw [orL_cons]
    cases b
    · rw [fl_false, Bool.false_or]; exact ih
    · rw [fl_true, List.length_cons, Bool.true_or]
      simp

theorem cnt_odd (vs : List Bool) : (vs.filter id).length % 2 = 1 ↔ xorL vs = true := by
  induction vs with
  | nil => simp [xorL_nil]
  | cons b t ih =>
    rw [xorL_cons]
    cases b
    · rw [fl_false]
      cases hx : xorL t
      · rw [hx] at ih; simpa using ih
      · rw [hx] at ih; simpa using ih
    · rw [fl_true, List.length_cons]
      cases hx : xorL t
      · rw [hx] at ih
        have : ¬ (t.filter id).length % 2 = 1 := fun h => absurd (ih.1 h) (by simp)
        have e : (true != false) = true := rfl
        rw [e]; simp; omega
      · rw [hx] at ih
        have h1 := ih.2 rfl
        have e : (true != true) = false := rfl
        rw [e]; simp; omega

theorem nodeVal_flow (vs : List Bool) (h : vs ≠ []) : nodeVal .flow vs false = andL vs := by
  have hl : vs.length ≠ 0 := by intro e; exact h (List.length_eq_zero_iff.1 e)
  have hc := cnt_all vs
  unfold nodeVal
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
  apply Bool.eq_iff_iff.2
  simp only [decide_eq_true_eq]
  constructor
  · intro h2; exact hc.1 h2.2
  · intro h2; exact ⟨hl, hc.2 h2⟩

theorem nodeVal_any (vs : List Bool) (h : vs ≠ []) : nodeVal .any vs false = orL vs := by
  have hl : vs.length ≠ 0 := by intro e; exact h (List.length_eq_zero_iff.1 e)
  have hc := cnt_pos vs
  unfold nodeVal
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
  apply Bool.eq_iff_iff.2
  simp only [decide_eq_true_eq]
  constructor
  · intro h2; exact hc.1 h2.2
  · intro h2; exact ⟨hl, hc.2 h2⟩

theorem nodeVal_add (vs : List Bool) : nodeVal .add vs false = xorL vs := by
  have hc := cnt_odd vs
  unfold nodeVal
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
  apply Bool.eq_iff_iff.2
  simp only [decide_eq_true_eq]
  exact hc

theorem nodeVal_addneg (vs : List Bool) : nodeVal .addneg vs false = !xorL vs := by
  have hc := cnt_odd vs
  unfold nodeVal
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
  apply Bool.eq_iff_iff.2
  simp only [decide_eq_true_eq, Bool.not_eq_true']
  constructor
  · intro h2
    cases hx : xorL vs
    · rfl
    · have := hc.2 hx; omega
  · intro h2
    have : ¬ (vs.filter id).length % 2 = 1 := fun h3 => by rw [hc.1 h3] at h2; exact absurd h2 (by simp)
    omega

end SmcIrred
