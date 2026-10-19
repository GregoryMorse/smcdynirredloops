module

public import SmcIrred.Spec.Toggle

public section

namespace SmcIrred.Lang

/-- The cell realizes the toggled variable: executing it returns the variable's value and leaves the cell encoding the
toggled value. -/
theorem cell_realizes_ttf (v : Bool) :
    (TCell.enc v).run = ((v, !v).1, TCell.enc (v, !v).2) := by
  cases v <;> rfl

theorem evalC_enc (sol : Nat → Bool) (env : Bool) : ∀ (k : Cond) (v : Bool),
    k.evalC sol env (TCell.enc v) = ((k.eval sol env v).1, TCell.enc (k.eval sol env v).2) := by
  intro k
  induction k with
  | falseC => intro v; rfl
  | ttf => intro v; exact cell_realizes_ttf v
  | c => intro v; rfl
  | out k => intro v; rfl
  | neg k ih => intro v; simp only [Cond.evalC, Cond.eval, ih]
  | and k l ihk ihl =>
    intro v
    simp only [Cond.evalC, Cond.eval, ihk]
    by_cases h : (k.eval sol env v).1 = true
    · simp only [h, ↓reduceIte]; exact ihl _
    · simp only [h, Bool.false_eq_true, ↓reduceIte]

/-- **The whole program semantics through the self-patched cell**: running any flat code with the cell as the toggled variable
gives the same block trace as running it with the Boolean variable, and the cell at the end encodes the final variable. -/
theorem execC_enc (sol : Nat → Bool) (env : Bool) : ∀ (f : Nat) (code : List Instr) (pc : Nat) (v : Bool) (tr : List Nat),
    execC f code sol env pc (TCell.enc v) tr = (exec f code sol env pc v tr).map fun r => (r.1, TCell.enc r.2) := by
  intro f
  induction f with
  | zero => intro code pc v tr; rfl
  | succ f ih =>
    intro code pc v tr
    unfold execC exec
    cases hi : code.getD pc .halt with
    | blk a => exact ih code (pc + 1) v (tr ++ [a])
    | jmp t => exact ih code t v tr
    | jmpIf k t =>
      simp only [evalC_enc]
      exact ih code _ _ tr
    | halt => rfl

end SmcIrred.Lang
