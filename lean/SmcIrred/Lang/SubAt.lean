module

public import SmcIrred.Lang.Fwd

public section

namespace SmcIrred.Lang

/-- The code of an occurrence of a statement sits at its address inside the code of the whole statement. -/
theorem Sub.atAddr {u s : Stmt} {q p : Nat} (h : Sub u q s p) (labs : List (Nat × Nat)) {code : List Instr}
    (hc : AtAddr code p (comp labs p s)) : AtAddr code q (comp labs q u) := by
  induction h with
  | refl => exact hc
  | seqL _ ih => exact ih (hc.append_left)
  | seqR _ ih =>
    have := hc.append_right
    rw [comp_length] at this
    exact ih this
  | ite1 _ ih => exact ih (hc.cons).2
  | iteS _ ih => exact ih ((hc.cons).2.append_left)
  | iteT _ ih =>
    have h1 := (hc.cons).2.append_right
    rw [comp_length] at h1
    have h2 := (h1.cons).2
    have e : ∀ x y : Nat, x + 1 + y + 1 = x + 2 + y := fun x y => by omega
    rw [e] at h2
    exact ih h2
  | whl _ ih => exact ih ((hc.cons).2.append_left)
  | dow _ ih => exact ih hc.append_left

end SmcIrred.Lang
