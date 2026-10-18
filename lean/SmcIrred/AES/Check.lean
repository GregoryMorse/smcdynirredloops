module

public import SmcIrred.Spec.AES

public section

namespace SmcIrred.AES

theorem forall_lt (n : Nat) (f : Nat → Bool) (h : (List.range n).all f = true) : ∀ x < n, f x = true := by
  intro x hx
  exact List.all_eq_true.1 h x (List.mem_range.2 hx)

/-- Boolean check of a two-variable property over `[0, 256)²`, row by row. -/
theorem forall_lt2 (f : Nat → Nat → Bool) (h : (List.range 256).all (fun a => (List.range 256).all (f a)) = true) :
    ∀ a < 256, ∀ b < 256, f a b = true := by
  intro a ha b hb
  exact forall_lt 256 (f a) (List.all_eq_true.1 h a (List.mem_range.2 ha)) b hb


theorem forall_range (s n : Nat) (f : Nat → Bool) (h : (List.range' s n).all f = true) :
    ∀ x, s ≤ x → x < s + n → f x = true := by
  intro x h1 h2
  exact List.all_eq_true.1 h x (List.mem_range'_1.2 ⟨h1, h2⟩)

/-- Rows `[s, s+n)` of a two-variable check. -/
theorem forall_rows (s n : Nat) (f : Nat → Nat → Bool)
    (h : (List.range' s n).all (fun a => (List.range 256).all (f a)) = true) :
    ∀ a, s ≤ a → a < s + n → ∀ b < 256, f a b = true := by
  intro a h1 h2 b hb
  exact forall_lt 256 (f a) (List.all_eq_true.1 h a (List.mem_range'_1.2 ⟨h1, h2⟩)) b hb

/-- A chunked proof of a one-variable check over `[0, 256)`: four blocks of 64. -/
theorem forall_lt_4 (f : Nat → Bool)
    (h0 : (List.range' 0 64).all f = true) (h1 : (List.range' 64 64).all f = true)
    (h2 : (List.range' 128 64).all f = true) (h3 : (List.range' 192 64).all f = true) :
    ∀ x < 256, f x = true := by
  intro x hx
  by_cases c0 : x < 64
  · exact forall_range 0 64 f h0 x (by omega) (by omega)
  by_cases c1 : x < 128
  · exact forall_range 64 64 f h1 x (by omega) (by omega)
  by_cases c2 : x < 192
  · exact forall_range 128 64 f h2 x (by omega) (by omega)
  · exact forall_range 192 64 f h3 x (by omega) (by omega)

/-- A chunked proof of a two-variable check over `[0, 256)²`: four row blocks of 64. -/
theorem forall_lt2_4 (f : Nat → Nat → Bool)
    (h0 : (List.range' 0 64).all (fun a => (List.range 256).all (f a)) = true)
    (h1 : (List.range' 64 64).all (fun a => (List.range 256).all (f a)) = true)
    (h2 : (List.range' 128 64).all (fun a => (List.range 256).all (f a)) = true)
    (h3 : (List.range' 192 64).all (fun a => (List.range 256).all (f a)) = true) :
    ∀ a < 256, ∀ b < 256, f a b = true := by
  intro a ha b hb
  by_cases c0 : a < 64
  · exact forall_rows 0 64 f h0 a (by omega) (by omega) b hb
  by_cases c1 : a < 128
  · exact forall_rows 64 64 f h1 a (by omega) (by omega) b hb
  by_cases c2 : a < 192
  · exact forall_rows 128 64 f h2 a (by omega) (by omega) b hb
  · exact forall_rows 192 64 f h3 a (by omega) (by omega) b hb

end SmcIrred.AES
