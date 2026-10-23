module

public import SmcIrred.Spec.Graph

public section

namespace SmcIrred.Lang

/-! The transformation language of Section 5: structured statements with labels and `goto` over abstract
blocks, compiled to flat code (the usual meaning of a C listing), whose basic blocks form the CFG.
Opaque conditions are modelled by their behaviour on an explicit state: `falseC` is always false, `ttf`
(`trueThenFalse`) reads a Boolean variable and toggles it, `c` is the program's own condition (a Boolean
constant of the run). Conditions are evaluated left to right with short-circuit `&&`. -/

inductive Cond where
  | falseC : Cond
  | ttf : Cond
  | c : Cond
  /-- Reads predicate cell `k` at run time; the second field is the value written into the code's bytes for this site
  before any self-modifying write (the placeholder read by a class that trusts the static code, `ImmCap`). -/
  | out : Nat → Bool → Cond
  | neg : Cond → Cond
  | and : Cond → Cond → Cond

/-- Value and new state of the variable read by `ttf`. The placeholder of `out` plays no role at run time: the running
machine always reads the predicate cell, after self-modification has written the solver's output into it. -/
@[expose] def Cond.eval (sol : Nat → Bool) (env : Bool) : Cond → Bool → Bool × Bool
  | .falseC, v => (false, v)
  | .ttf, v => (v, !v)
  | .c, v => (env, v)
  | .out k _, v => (sol k, v)
  | .neg k, v => ((!(k.eval sol env v).1), (k.eval sol env v).2)
  | .and k l, v => if (k.eval sol env v).1 then l.eval sol env (k.eval sol env v).2 else (false, (k.eval sol env v).2)

/-- Flat code. -/
inductive Instr where
  | blk : Nat → Instr
  | jmp : Nat → Instr
  | jmpIf : Cond → Nat → Instr
  | halt : Instr

/-- Execution with a fuel bound: the block trace and the final value of the variable read by `ttf`, if the
code halts within the fuel (running off the end counts as `halt`). -/
@[expose] def exec : Nat → List Instr → (Nat → Bool) → Bool → Nat → Bool → List Nat → Option (List Nat × Bool)
  | 0, _, _, _, _, _, _ => none
  | f + 1, code, sol, env, pc, v, tr =>
    match code.getD pc .halt with
    | .blk a => exec f code sol env (pc + 1) v (tr ++ [a])
    | .jmp t => exec f code sol env t v tr
    | .jmpIf k t => exec f code sol env (if (k.eval sol env v).1 then t else pc + 1) (k.eval sol env v).2 tr
    | .halt => some (tr, v)

/-- Structured statements. `ifGoto k l` is `if (k) goto l;`. -/
inductive Stmt where
  | skip : Stmt
  | blk : Nat → Stmt
  | seq : Stmt → Stmt → Stmt
  | ite1 : Cond → Stmt → Stmt
  | ite : Cond → Stmt → Stmt → Stmt
  | while : Cond → Stmt → Stmt
  | doWhile : Stmt → Cond → Stmt
  | goto : Nat → Stmt
  | ifGoto : Cond → Nat → Stmt
  | lab : Nat → Stmt → Stmt

@[expose] def Stmt.size : Stmt → Nat
  | .skip => 0
  | .blk _ => 1
  | .seq s t => s.size + t.size
  | .ite1 _ s => 1 + s.size
  | .ite _ s t => 2 + s.size + t.size
  | .while _ s => 2 + s.size
  | .doWhile s _ => s.size + 1
  | .goto _ => 1
  | .ifGoto _ _ => 1
  | .lab _ s => s.size

@[expose] def lookupLabel (labs : List (Nat × Nat)) (l : Nat) : Nat :=
  match labs.find? (fun q => q.1 == l) with
  | some q => q.2
  | none => 0

/-- Code of a statement placed at address `p`. -/
@[expose] def comp (labs : List (Nat × Nat)) : Nat → Stmt → List Instr
  | _, .skip => []
  | _, .blk a => [.blk a]
  | p, .seq s t => comp labs p s ++ comp labs (p + s.size) t
  | p, .ite1 k s => .jmpIf (.neg k) (p + 1 + s.size) :: comp labs (p + 1) s
  | p, .ite k s t =>
    .jmpIf (.neg k) (p + 2 + s.size) :: (comp labs (p + 1) s ++ (.jmp (p + 2 + s.size + t.size) :: comp labs (p + 2 + s.size) t))
  | p, .while k s => .jmpIf (.neg k) (p + 2 + s.size) :: (comp labs (p + 1) s ++ [.jmp p])
  | p, .doWhile s k => comp labs p s ++ [.jmpIf k p]
  | _, .goto l => [.jmp (lookupLabel labs l)]
  | _, .ifGoto k l => [.jmpIf k (lookupLabel labs l)]
  | p, .lab _ s => comp labs p s

/-- Addresses of the labels of a statement placed at address `p`. -/
@[expose] def labelsOf : Nat → Stmt → List (Nat × Nat)
  | _, .skip => []
  | _, .blk _ => []
  | p, .seq s t => labelsOf p s ++ labelsOf (p + s.size) t
  | p, .ite1 _ s => labelsOf (p + 1) s
  | p, .ite _ s t => labelsOf (p + 1) s ++ labelsOf (p + 2 + s.size) t
  | p, .while _ s => labelsOf (p + 1) s
  | p, .doWhile s _ => labelsOf p s
  | _, .goto _ => []
  | _, .ifGoto _ _ => []
  | p, .lab l s => (l, p) :: labelsOf p s

/-- The flat code of a program: its instructions followed by `halt`. -/
@[expose] def compile (s : Stmt) : List Instr := comp (labelsOf 0 s) 0 s ++ [.halt]

/-! ### Basic blocks -/

@[expose] def Instr.target : Instr → Option Nat
  | .jmp t => some t
  | .jmpIf _ t => some t
  | _ => none

@[expose] def Instr.isTerm : Instr → Bool
  | .blk _ => false
  | _ => true

/-- Address `i` starts a basic block: it is the first instruction, a jump target, or follows a jump or `halt`. -/
@[expose] def isLeader (code : List Instr) (i : Nat) : Bool :=
  i == 0 || (List.range code.length).any fun j =>
    (code.getD j .halt).target == some i || (j + 1 == i && (code.getD j .halt).isTerm)

@[expose] def leaders (code : List Instr) : List Nat := (List.range code.length).filter (isLeader code)

/-- Number of the block containing address `i`. -/
@[expose] def blockOf (code : List Instr) (i : Nat) : Nat := ((leaders code).filter (· ≤ i)).length - 1

/-- Address of the last instruction of block `k`. -/
@[expose] def blockEnd (code : List Instr) (k : Nat) : Nat := (leaders code).getD (k + 1) code.length - 1

/-- The abstract blocks executed in basic block `k`, in order. -/
@[expose] def blockLabels (code : List Instr) (k : Nat) : List Nat :=
  ((List.range code.length).filter fun i => (leaders code).getD k 0 ≤ i ∧ i ≤ blockEnd code k).filterMap fun i =>
    match code.getD i .halt with
    | .blk a => some a
    | _ => none

/-- Successors of block `k`: the jump target then the fall-through for a conditional jump. -/
@[expose] def blockSucc (code : List Instr) (k : Nat) : List Nat :=
  let e := blockEnd code k
  match code.getD e .halt with
  | .jmp t => [blockOf code t]
  | .jmpIf _ t => [blockOf code t, blockOf code (e + 1)]
  | .halt => []
  | .blk _ => if e + 1 < code.length then [blockOf code (e + 1)] else []

/-- The control-flow graph of flat code: one vertex per basic block. -/
@[expose] def cfgOf (code : List Instr) : Digraph where
  n := (leaders code).length
  succ := blockSucc code

/-- The generator outputs read by a condition. -/
@[expose] def Cond.reads : Cond → List Nat
  | .out k _ => [k]
  | .neg k => k.reads
  | .and a b => a.reads ++ b.reads
  | _ => []

@[expose] def Instr.reads : Instr → List Nat
  | .jmpIf k _ => k.reads
  | _ => []

/-- The generator outputs read by some instruction of the code. -/
@[expose] def codeReads (code : List Instr) : List Nat := code.flatMap Instr.reads

/-- The placeholder written into the code for predicate cell `k` by this condition, if it tests `k` directly or through
`neg`/`and` (the self-modifying write has not happened yet; this is the value an `ImmCap` analyzer reads). `none` if the
condition does not test `k`. -/
@[expose] def Cond.staticVal (k : Nat) : Cond → Option Bool
  | .out j b => if j = k then some b else none
  | .neg d => d.staticVal k
  | .and a b => a.staticVal k <|> b.staticVal k
  | _ => none

/-- The placeholder value of predicate cell `k` in the static bytes of compiled code: the first `jmpIf` condition that
tests it (scanning the code in order), or `false` if none does. -/
@[expose] def codeStatic (code : List Instr) (k : Nat) : Bool :=
  (code.filterMap fun i => match i with | .jmpIf c _ => c.staticVal k | _ => none).headD false

theorem Cond.staticVal_none_of_not_mem_reads {p : Cond} {k : Nat} (h : k ∉ p.reads) : p.staticVal k = none := by
  induction p with
  | falseC => rfl
  | ttf => rfl
  | c => rfl
  | out j _ =>
    simp only [Cond.reads, List.mem_singleton] at h
    simp [Cond.staticVal, Ne.symm h]
  | neg d ih =>
    simp only [Cond.reads] at h
    exact ih h
  | and a b iha ihb =>
    simp only [Cond.reads, List.mem_append, not_or] at h
    simp [Cond.staticVal, iha h.1, ihb h.2]

/-- No instruction of `code` matches cell `k`'s condition, so scanning for its static placeholder finds nothing. -/
theorem filterMap_static_nil_of_not_mem {code : List Instr} {k : Nat} (h : k ∉ codeReads code) :
    (code.filterMap fun i => match i with | .jmpIf c _ => c.staticVal k | _ => none) = [] := by
  induction code with
  | nil => rfl
  | cons i code ih =>
    simp only [codeReads, List.flatMap_cons, List.mem_append, not_or] at h
    have hih := ih h.2
    cases i with
    | jmpIf c t =>
      have hc : c.staticVal k = none := Cond.staticVal_none_of_not_mem_reads (by simpa [Instr.reads] using h.1)
      simp [List.filterMap_cons, hc, hih]
    | blk _ => simpa using hih
    | jmp _ => simpa using hih
    | halt => simpa using hih

theorem codeStatic_eq_false_of_not_mem {code : List Instr} {k : Nat} (h : k ∉ codeReads code) :
    codeStatic code k = false := by
  unfold codeStatic
  rw [filterMap_static_nil_of_not_mem h]
  rfl

/-- Scanning an appended code list for cell `k`'s placeholder skips a first part that does not read `k` at all. -/
theorem codeStatic_append_of_not_mem {A B : List Instr} {k : Nat} (h : k ∉ codeReads A) :
    codeStatic (A ++ B) k = codeStatic B k := by
  unfold codeStatic
  rw [List.filterMap_append, filterMap_static_nil_of_not_mem h]
  rfl

/-- The static placeholder of a condition tested directly by the first instruction: scanning finds it immediately,
whatever instructions follow. -/
theorem codeStatic_cons_eq {code : List Instr} {h : Cond} {t : Nat} {k : Nat} {b : Bool} (hs : h.staticVal k = some b) :
    codeStatic (Instr.jmpIf h t :: code) k = b := by
  unfold codeStatic
  simp [List.filterMap_cons, hs]

/-- The statements of the transformation language without `goto`, `ifGoto` and labels (structured programs). -/
@[expose] def Structured : Stmt → Prop
  | .skip => True
  | .blk _ => True
  | .seq s t => Structured s ∧ Structured t
  | .ite1 _ s => Structured s
  | .ite _ s t => Structured s ∧ Structured t
  | .while _ s => Structured s
  | .doWhile s _ => Structured s
  | .goto _ => False
  | .ifGoto _ _ => False
  | .lab _ _ => False

end SmcIrred.Lang
