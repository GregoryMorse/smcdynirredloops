module

public import SmcIrred.Extremal.Count

public section

namespace SmcIrred

theorem count_eq_sum {α : Type} (l : List α) (p : α → Bool) :
    (l.filter p).length = (l.map fun a => if p a = true then 1 else 0).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases h : p a = true
    · simp [List.filter_cons, h, ih]; omega
    · simp [List.filter_cons, h, ih]

theorem sum_zero_map (l : List Nat) : (l.map fun _ => 0).sum = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem sum_comm (f : Nat → Nat → Nat) (l1 l2 : List Nat) :
    (l1.map fun a => (l2.map fun b => f a b).sum).sum = (l2.map fun b => (l1.map fun a => f a b).sum).sum := by
  induction l1 with
  | nil => simp [sum_zero_map]
  | cons a l1 ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih]
    have := sum_map_add (fun b => f a b) (fun b => (l1.map fun a => f a b).sum) l2
    exact this.symm

open Classical in
/-- Double counting: the number of pairs, counted by either coordinate first. -/
theorem swap_count (n : Nat) (P : Nat → Nat → Prop) :
    ((List.range n).map fun y => ((List.range n).filter fun x => decide (P x y)).length).sum =
    ((List.range n).map fun x => ((List.range n).filter fun y => decide (P x y)).length).sum := by
  have e1 : ((List.range n).map fun y => ((List.range n).filter fun x => decide (P x y)).length) =
      (List.range n).map fun y => ((List.range n).map fun x => if P x y then 1 else 0).sum := by
    apply List.map_congr_left; intro y _
    rw [count_eq_sum]; simp
  have e2 : ((List.range n).map fun x => ((List.range n).filter fun y => decide (P x y)).length) =
      (List.range n).map fun x => ((List.range n).map fun y => if P x y then 1 else 0).sum := by
    apply List.map_congr_left; intro x _
    rw [count_eq_sum]; simp
  rw [e1, e2]
  exact (sum_comm (fun x y => if P x y then 1 else 0) (List.range n) (List.range n)).symm

/-- Filter lengths of two disjoint subsets of a third add up to at most its length. -/
theorem filter_len_add_le {l : List Nat} {p q r : Nat → Bool} (hp : ∀ a ∈ l, p a = true → r a = true)
    (hq : ∀ a ∈ l, q a = true → r a = true) (hd : ∀ a ∈ l, ¬ (p a = true ∧ q a = true)) :
    (l.filter p).length + (l.filter q).length ≤ (l.filter r).length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ih' := ih (fun b hb => hp b (List.mem_cons_of_mem _ hb)) (fun b hb => hq b (List.mem_cons_of_mem _ hb))
      (fun b hb => hd b (List.mem_cons_of_mem _ hb))
    have h1 := hp a (List.mem_cons_self ..)
    have h2 := hq a (List.mem_cons_self ..)
    have h3 := hd a (List.mem_cons_self ..)
    cases hpa : p a <;> cases hqa : q a <;> cases hra : r a <;> simp [List.filter_cons, hpa, hqa, hra] <;>
      first | omega | (simp_all)

/-- A three-way partition of a list by filters. -/
theorem filter_len_three {l : List Nat} {p q r : Nat → Bool}
    (h : ∀ a ∈ l, (p a = true ∧ q a = false ∧ r a = false) ∨ (p a = false ∧ q a = true ∧ r a = false) ∨
      (p a = false ∧ q a = false ∧ r a = true)) :
    (l.filter p).length + (l.filter q).length + (l.filter r).length = l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ih' := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    have ha := h a (List.mem_cons_self ..)
    rcases ha with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;> simp [List.filter_cons, h1, h2, h3] <;> omega

/-- A filter splits into two disjoint ones. -/
theorem filter_len_split {l : List Nat} {p q r : Nat → Bool}
    (h : ∀ a ∈ l, (p a = true ∧ q a = true ∧ r a = false) ∨ (p a = true ∧ q a = false ∧ r a = true) ∨
      (p a = false ∧ q a = false ∧ r a = false)) :
    (l.filter p).length = (l.filter q).length + (l.filter r).length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ih' := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    have ha := h a (List.mem_cons_self ..)
    rcases ha with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;> simp [List.filter_cons, h1, h2, h3] <;> omega

theorem filter_len_mono {l : List Nat} {p q : Nat → Bool} (h : ∀ a ∈ l, p a = true → q a = true) :
    (l.filter p).length ≤ (l.filter q).length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ih' := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    have h1 := h a (List.mem_cons_self ..)
    cases hpa : p a <;> cases hqa : q a <;> simp [List.filter_cons, hpa, hqa] <;> first | omega | (simp_all)

end SmcIrred
