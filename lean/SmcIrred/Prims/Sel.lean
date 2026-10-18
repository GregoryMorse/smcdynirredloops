module

public import SmcIrred.Prims.Gates

public section

namespace SmcIrred

theorem selL_filter (l : List (Bool × Bool)) : selL l = xorL ((l.filter fun p => p.1).map fun p => p.2) := by
  induction l with
  | nil => rfl
  | cons p t ih =>
    obtain ⟨s, v⟩ := p
    unfold selL at ih ⊢
    simp only [List.map_cons, xorL_cons]
    rw [ih]
    cases s
    · simp [xorL_cons]
    · simp [xorL_cons]

theorem selOrL_filter (l : List (Bool × Bool)) : selOrL l = orL ((l.filter fun p => p.1).map fun p => p.2) := by
  induction l with
  | nil => rfl
  | cons p t ih =>
    obtain ⟨s, v⟩ := p
    unfold selOrL at ih ⊢
    simp only [List.map_cons, orL_cons]
    rw [ih]
    cases s
    · simp [orL_cons]
    · simp [orL_cons]

/-- With exactly one true selector, `SEL` is the value paired with it. -/
theorem sel_one (l : List (Bool × Bool)) (x : Bool) (h : l.filter (fun p => p.1) = [(true, x)]) : selL l = x := by
  rw [selL_filter, h]
  simp [xorL_cons, xorL_nil]

/-- XOR may be replaced by OR when at most one selector is true. -/
theorem sel_or_eq_xor (l : List (Bool × Bool)) (h : (l.filter fun p => p.1).length ≤ 1) : selOrL l = selL l := by
  rw [selOrL_filter, selL_filter]
  generalize (l.filter fun p => p.1) = m at h
  match m, h with
  | [], _ => rfl
  | [p], _ => simp [xorL_cons, xorL_nil, orL_cons, orL]

/-- With two true selectors the replacement fails. -/
theorem sel_or_counterexample :
    selOrL [(true, true), (true, true)] = true ∧ selL [(true, true), (true, true)] = false := by decide

theorem bsel_eq_sel (s x0 x1 : Bool) : bsel s x0 x1 = selL [(s, x0), (!s, x1)] := by
  cases s <;> cases x0 <;> cases x1 <;> rfl

theorem bsel_ite (s x0 x1 : Bool) : bsel s x0 x1 = (if s then x0 else x1) := by
  cases s <;> cases x0 <;> cases x1 <;> rfl

/-- A table lookup is the vector of its single-bit functions. -/
theorem table_single_bits {m n : Nat} (f : Fin m → Fin n → Bool) :
    (fun x => fun j => f x j) = f := rfl

end SmcIrred
