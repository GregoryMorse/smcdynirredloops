module

public import SmcIrred.Spec.Extremal

public section

namespace SmcIrred

/-- Counting an interval inside `range n`. -/
theorem count_interval (n a b : Nat) :
    ((List.range n).filter fun w => decide (a ≤ w ∧ w < b)).length = min b n - min a n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.filter_append, List.length_append, ih]
    by_cases h : a ≤ n ∧ n < b
    · simp [h]; omega
    · simp [h]; omega

theorem sum_map_const (n c : Nat) : ((List.range n).map fun _ => c).sum = n * c := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih]; simp [Nat.succ_mul]

theorem sum_pred_aux : ∀ m : Nat, 2 * ((List.range (m + 2)).map fun y => y - 1).sum = (m + 1) * m := by
  intro m
  induction m with
  | zero => decide
  | succ m ih =>
    have e : m + 1 + 2 = (m + 2) + 1 := by omega
    rw [e, List.range_succ, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    have e2 : m + 2 - 1 = m + 1 := by omega
    rw [e2, Nat.mul_add, ih]
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
    omega

/-- `Σ_{y<n} (y - 1)`, the triangular number of multiple-entry edges. -/
theorem sum_pred (n : Nat) : 2 * ((List.range n).map fun y => y - 1).sum = (n - 1) * (n - 2) := by
  rcases n with _ | _ | m
  · simp
  · simp
  · have := sum_pred_aux m
    have e1 : m + 1 + 1 - 1 = m + 1 := by omega
    have e2 : m + 1 + 1 - 2 = m := by omega
    rw [e1, e2]
    exact this

theorem sum_map_add (f h : Nat → Nat) (l : List Nat) :
    (l.map fun a => f a + h a).sum = (l.map f).sum + (l.map h).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]; omega

/-- `Σ_{a<n} (n - 1 - a)`, twice a triangular number. -/
theorem sum_tri (n : Nat) : 2 * ((List.range n).map fun a => n - 1 - a).sum = n * (n - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    have e : ((List.range n).map fun a => n + 1 - 1 - a) = (List.range n).map fun a => (n - 1 - a) + 1 := by
      apply List.map_congr_left
      intro a ha
      have := List.mem_range.1 ha
      omega
    rw [e, sum_map_add, sum_map_const]
    have ih' : 2 * ((List.range n).map (HSub.hSub (n - 1))).sum = n * (n - 1) := ih
    have e2 : n + 1 - 1 - n = 0 := by omega
    rw [e2]
    generalize ((List.range n).map (HSub.hSub (n - 1))).sum = S at ih' ⊢
    rcases n with _ | m
    · simp at ih' ⊢; omega
    · have e3 : m + 1 - 1 = m := by omega
      rw [e3] at ih'
      have e4 : m + 1 + 1 - 1 = m + 1 := by omega
      rw [e4]
      simp only [Nat.mul_one, Nat.mul_zero, Nat.add_zero, Nat.mul_add, Nat.add_mul, Nat.one_mul] at ih' ⊢
      omega

/-- Only the last index contributes. -/
theorem sum_last (n c : Nat) (hn : 1 ≤ n) : ((List.range n).map fun a => if a + 1 = n then c else 0).sum = c := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [List.range_succ, List.map_append, List.sum_append]
  have e : ((List.range m).map fun a => if a + 1 = m + 1 then c else 0) = (List.range m).map fun _ => 0 := by
    apply List.map_congr_left
    intro a ha
    have := List.mem_range.1 ha
    simp; omega
  rw [e, sum_map_const]
  simp

theorem count_ne (n : Nat) : ∀ a, a < n → ((List.range n).filter fun b => decide (b ≠ a)).length = n - 1 := by
  induction n with
  | zero => intro a h; omega
  | succ n ih =>
    intro a ha
    rw [List.range_succ, List.filter_append, List.length_append]
    by_cases e : a = n
    · subst e
      have : (List.range a).filter (fun b => decide (b ≠ a)) = List.range a :=
        List.filter_eq_self.2 (fun b hb => by simp only [List.mem_range] at hb; simp; omega)
      rw [this]; simp
    · have := ih a (by omega)
      rw [this]
      have : n ≠ a := fun h => e h.symm
      simp [this]; omega

end SmcIrred
