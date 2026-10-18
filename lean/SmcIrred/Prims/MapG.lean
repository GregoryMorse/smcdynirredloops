module

public import SmcIrred.Prims.Logic

public section

namespace SmcIrred

/-- Threading a gadget through a list: if every step is a gadget whose result value is a function `T` of the values of the
wires it reads, the whole list has the expected values. -/
theorem mapG_wire {α : Type} (f : GB → α → Wire × GB) (inputs : α → List Wire) (T : α → List Bool → Bool)
    (P : α → Prop) {inp : Nat → Bool} {k : Nat}
    (hf : ∀ (gb : GB) (a : α), P a → k ≤ gb.n → Reach gb → (∀ w ∈ inputs a, w.ok gb.n) →
      Post gb (f gb a).2 inp (f gb a).1 (T a ((inputs a).map (wev gb inp)))) :
    ∀ (l : List α) (gb : GB), (∀ a ∈ l, P a) → k ≤ gb.n → Reach gb → (∀ a ∈ l, ∀ w ∈ inputs a, w.ok gb.n) →
      Ext gb (mapG f gb l).2 ∧ Reach (mapG f gb l).2 ∧ (∀ w ∈ (mapG f gb l).1, w.ok (mapG f gb l).2.n) ∧
      (mapG f gb l).1.map (wev (mapG f gb l).2 inp) = l.map (fun a => T a ((inputs a).map (wev gb inp))) := by
  intro l
  induction l with
  | nil =>
    intro gb _ _ hr _
    exact ⟨Ext.refl _, hr, fun w hw => by simp [mapG] at hw, rfl⟩
  | cons a l ih =>
    intro gb hP hk hr hok
    have p := hf gb a (hP a List.mem_cons_self) hk hr (hok a List.mem_cons_self)
    have hk' : k ≤ (f gb a).2.n := Nat.le_trans hk p.ext.n_le
    have hok' : ∀ a' ∈ l, ∀ w ∈ inputs a', w.ok (f gb a).2.n := fun a' ha' w hw =>
      ok_mono (hok a' (List.mem_cons_of_mem _ ha') w hw) p.ext.n_le
    obtain ⟨e1, r1, o1, v1⟩ := ih (f gb a).2 (fun a' ha' => hP a' (List.mem_cons_of_mem _ ha')) hk' p.reach hok'
    have hm : mapG f gb (a :: l) = ((f gb a).1 :: (mapG f (f gb a).2 l).1, (mapG f (f gb a).2 l).2) := rfl
    rw [hm]
    refine ⟨p.ext.trans e1, r1, ?_, ?_⟩
    · intro w hw
      rcases List.mem_cons.1 hw with rfl | hw
      · exact ok_mono p.ok e1.n_le
      · exact o1 w hw
    · simp only [List.map_cons]
      have hh : wev (mapG f (f gb a).2 l).2 inp (f gb a).1 = T a ((inputs a).map (wev gb inp)) := by
        rw [wev_ext e1 p.ok]; exact p.val
      have ht : (mapG f (f gb a).2 l).1.map (wev (mapG f (f gb a).2 l).2 inp) =
          l.map (fun a => T a ((inputs a).map (wev gb inp))) := by
        rw [v1]
        apply List.map_congr_left
        intro a' ha'
        have : (inputs a').map (wev (f gb a).2 inp) = (inputs a').map (wev gb inp) :=
          List.map_congr_left (fun w hw => wev_ext p.ext (hok a' (List.mem_cons_of_mem _ ha') w hw))
        rw [this]
      rw [hh, ht]

theorem mapG_n {α : Type} (f : GB → α → Wire × GB) (c : α → Nat) (P : α → Prop)
    (hf : ∀ (gb : GB) (a : α), P a → (f gb a).2.n = gb.n + c a) :
    ∀ (l : List α) (gb : GB), (∀ a ∈ l, P a) → (mapG f gb l).2.n = gb.n + (l.map c).sum := by
  intro l
  induction l with
  | nil => intro gb _; simp [mapG]
  | cons a l ih =>
    intro gb hP
    have hm : mapG f gb (a :: l) = ((f gb a).1 :: (mapG f (f gb a).2 l).1, (mapG f (f gb a).2 l).2) := rfl
    rw [hm]
    show (mapG f (f gb a).2 l).2.n = _
    rw [ih _ (fun a' ha' => hP a' (List.mem_cons_of_mem _ ha')), hf gb a (hP a List.mem_cons_self)]
    simp [List.map_cons, List.sum_cons]
    omega

/-- If every step creates exactly one node and returns it, the outputs are consecutive fresh nodes. -/
theorem mapG_fresh {α : Type} (f : GB → α → Wire × GB) (P : α → Prop)
    (hf : ∀ (gb : GB) (a : α), P a → (f gb a).2.n = gb.n + 1 ∧ (f gb a).1 = .nd gb.n) :
    ∀ (l : List α) (gb : GB), (∀ a ∈ l, P a) →
      (mapG f gb l).2.n = gb.n + l.length ∧ (mapG f gb l).1 = (List.range l.length).map fun j => Wire.nd (gb.n + j) := by
  intro l
  induction l with
  | nil => intro gb _; simp [mapG]
  | cons a l ih =>
    intro gb hP
    have hm : mapG f gb (a :: l) = ((f gb a).1 :: (mapG f (f gb a).2 l).1, (mapG f (f gb a).2 l).2) := rfl
    rw [hm]
    obtain ⟨h1, h2⟩ := hf gb a (hP a List.mem_cons_self)
    obtain ⟨i1, i2⟩ := ih (f gb a).2 (fun a' ha' => hP a' (List.mem_cons_of_mem _ ha'))
    refine ⟨by simp only [List.length_cons]; show (mapG f (f gb a).2 l).2.n = _; rw [i1, h1]; omega, ?_⟩
    show (f gb a).1 :: (mapG f (f gb a).2 l).1 = _
    rw [i2, h2, h1, List.length_cons, List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, Nat.add_zero]
    congr 1
    apply List.map_congr_left
    intro j _
    simp [Function.comp, Nat.add_assoc, Nat.add_comm 1 j]

end SmcIrred
