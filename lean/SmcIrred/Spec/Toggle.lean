module

public import SmcIrred.Spec.Lang

public section

namespace SmcIrred.Lang

/-! # The toggled variable as a self-patched code cell (C76, G34 c)

The variable read by `trueThenFalse` is realized by one code cell holding one of two instructions: `retT` (return true) and
`retF` (return false). Executing the cell returns its value and patches the cell into the other instruction. `evalC` and
`execC` are `Cond.eval` and `exec` with the Boolean state replaced by this cell. -/

inductive TCell where
  | retT : TCell
  | retF : TCell

/-- Execute the cell: the value it returns and the instruction it leaves behind (the patch). -/
@[expose] def TCell.run : TCell → Bool × TCell
  | .retT => (true, .retF)
  | .retF => (false, .retT)

/-- The cell encoding the Boolean `v`. -/
@[expose] def TCell.enc (v : Bool) : TCell := if v then .retT else .retF

@[expose] def Cond.evalC (sol : Nat → Bool) (env : Bool) : Cond → TCell → Bool × TCell
  | .falseC, v => (false, v)
  | .ttf, v => v.run
  | .c, v => (env, v)
  | .out k, v => (sol k, v)
  | .neg k, v => ((!(k.evalC sol env v).1), (k.evalC sol env v).2)
  | .and k l, v =>
    if (k.evalC sol env v).1 then l.evalC sol env (k.evalC sol env v).2 else (false, (k.evalC sol env v).2)

@[expose] def execC : Nat → List Instr → (Nat → Bool) → Bool → Nat → TCell → List Nat → Option (List Nat × TCell)
  | 0, _, _, _, _, _, _ => none
  | f + 1, code, sol, env, pc, v, tr =>
    match code.getD pc .halt with
    | .blk a => execC f code sol env (pc + 1) v (tr ++ [a])
    | .jmp t => execC f code sol env t v tr
    | .jmpIf k t => execC f code sol env (if (k.evalC sol env v).1 then t else pc + 1) (k.evalC sol env v).2 tr
    | .halt => some (tr, v)

end SmcIrred.Lang
