module

public import SmcIrred.Prims.Gates

public section

namespace SmcIrred

/-- NOT, AND and OR realised by formulas over the gate `g`. -/
structure Comb (g : Bool → Bool → Bool) where
  not : F2 g → F2 g
  and : F2 g → F2 g → F2 g
  or : F2 g → F2 g → F2 g
  not_eval : ∀ a N, (not N).eval a = !N.eval a
  and_eval : ∀ a N M, (and N M).eval a = (N.eval a && M.eval a)
  or_eval : ∀ a N M, (or N M).eval a = (N.eval a || M.eval a)

@[expose] def nandComb : Comb nandG where
  not N := .gate N N
  and N M := .gate (.gate N M) (.gate N M)
  or N M := .gate (.gate N N) (.gate M M)
  not_eval a N := by simp [F2.eval, nandG]
  and_eval a N M := by simp [F2.eval, nandG]
  or_eval a N M := by
    simp only [F2.eval, nandG]
    cases N.eval a <;> cases M.eval a <;> rfl

@[expose] def norComb : Comb norG where
  not N := .gate N N
  and N M := .gate (.gate N N) (.gate M M)
  or N M := .gate (.gate N M) (.gate N M)
  not_eval a N := by simp [F2.eval, norG]
  and_eval a N M := by
    simp only [F2.eval, norG]
    cases N.eval a <;> cases M.eval a <;> rfl
  or_eval a N M := by simp [F2.eval, norG]

/-- `f` reads only the variables `0 … k`. -/
@[expose] def DependsOn (k : Nat) (f : (Nat → Bool) → Bool) : Prop :=
  ∀ a b : Nat → Bool, (∀ i, i ≤ k → a i = b i) → f a = f b

/-- Every Boolean function of `k + 1` variables has a circuit made only of the gate `g`, provided `g` realises NOT, AND, OR. -/
theorem complete_of_comb {g : Bool → Bool → Bool} (C : Comb g) :
    ∀ (k : Nat) (f : (Nat → Bool) → Bool), DependsOn k f → ∃ N : F2 g, ∀ a, N.eval a = f a := by
  intro k
  induction k with
  | zero =>
    intro f hf
    have hagree : ∀ (a : Nat → Bool) (c : Bool), a 0 = c → ∀ i, i ≤ 0 → a i = (fun _ => c) i := by
      intro a c h i hi
      have e : i = 0 := by omega
      subst e; exact h
    have hdep : ∀ a, f a = (if a 0 = true then f (fun _ => true) else f (fun _ => false)) := by
      intro a
      cases h : a 0
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact hf _ _ (hagree a false h)
      · simp only [↓reduceIte]
        exact hf _ _ (hagree a true h)
    let x : F2 g := .var 0
    cases hq : f (fun _ => true) <;> cases hp : f (fun _ => false)
    · exact ⟨C.and x (C.not x), fun a => by
        rw [hdep a, hq, hp, C.and_eval, C.not_eval]; simp [x, F2.eval]⟩
    · exact ⟨C.not x, fun a => by
        rw [hdep a, hq, hp, C.not_eval]; simp [x, F2.eval]⟩
    · exact ⟨x, fun a => by
        rw [hdep a, hq, hp]; simp [x, F2.eval]⟩
    · exact ⟨C.or x (C.not x), fun a => by
        rw [hdep a, hq, hp, C.or_eval, C.not_eval]; simp [x, F2.eval]⟩
  | succ k ih =>
    intro f hf
    let f0 : (Nat → Bool) → Bool := fun a => f (fun i => if i = k + 1 then false else a i)
    let f1 : (Nat → Bool) → Bool := fun a => f (fun i => if i = k + 1 then true else a i)
    have d0 : DependsOn k f0 := by
      intro a b hab
      apply hf
      intro i hi
      by_cases e : i = k + 1
      · simp [e]
      · simp only [e, ↓reduceIte]; exact hab i (by omega)
    have d1 : DependsOn k f1 := by
      intro a b hab
      apply hf
      intro i hi
      by_cases e : i = k + 1
      · simp [e]
      · simp only [e, ↓reduceIte]; exact hab i (by omega)
    obtain ⟨N0, h0⟩ := ih f0 d0
    obtain ⟨N1, h1⟩ := ih f1 d1
    let x : F2 g := .var (k + 1)
    refine ⟨C.or (C.and x N1) (C.and (C.not x) N0), fun a => ?_⟩
    rw [C.or_eval, C.and_eval, C.and_eval, C.not_eval, h0, h1]
    simp only [x, F2.eval, f0, f1]
    cases h : a (k + 1)
    · have : f a = f (fun i => if i = k + 1 then false else a i) := by
        apply hf; intro i hi
        by_cases e : i = k + 1
        · simp [e, h]
        · simp [e]
      simp [this]
    · have : f a = f (fun i => if i = k + 1 then true else a i) := by
        apply hf; intro i hi
        by_cases e : i = k + 1
        · simp [e, h]
        · simp [e]
      simp [this]

/-- NAND alone is functionally complete: every function of `k ≥ 1` variables has a NAND-only circuit. -/
theorem nand_complete (k : Nat) (f : (Nat → Bool) → Bool) (hf : DependsOn k f) :
    ∃ N : F2 nandG, ∀ a, N.eval a = f a := complete_of_comb nandComb k f hf

/-- NOR alone is functionally complete. -/
theorem nor_complete (k : Nat) (f : (Nat → Bool) → Bool) (hf : DependsOn k f) :
    ∃ N : F2 norG, ∀ a, N.eval a = f a := complete_of_comb norComb k f hf

end SmcIrred
