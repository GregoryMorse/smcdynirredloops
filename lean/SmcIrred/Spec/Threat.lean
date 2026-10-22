module

public import SmcIrred.Spec.Generator
public import SmcIrred.Spec.SmcMachine
public import SmcIrred.Spec.Tarjan
public import SmcIrred.Spec.LangFigs
public import SmcIrred.Spec.Dynamic

public section

namespace SmcIrred.Threat

open Lang Dyn

/-! # The security model (Section 5.1)

**System.** The original program is a program of the transformation language (`Spec.Lang`) whose blocks are arbitrary
computations; the obfuscator `Obfuscates` applies the static scheme of Section 5 (Figures 5 and 6: the loop and
conditional transformations whose opaque conditions are read from predicate cells), and the predicate cells are filled at
run time by the self-modifying-code 2-SAT solver (`smcSolve`) on a planted formula (Sections 3 and 3.1). An obfuscated
*image* is the transformed program, the stamped formula and the placeholder values of the predicate cells in the static code
bytes (the blueprint).

**Adversary classes** are interfaces: an analyzer reports a value for every predicate cell; a class is a structure stating
its capability, never a claim that a tool exists. `ImmCap`: the analyzer reads the cells from the static code bytes (it
assumes code bytes are constant). `SmcSemCap`: the analyzer implements stamping and the machine semantics (it can run the
solver on the stamped formula). The classes for structuring, faults, traces and correlation are added with their theorems.

**Goals** are predicates on an analyzer and an image. **Assumptions** (`Assumptions`) are structural properties of the design;
no field mentions a goal (`validation/threat_audit.py`). -/

/-- An obfuscated image. -/
structure Image where
  prog : Stmt
  formula : TwoSat
  blueprint : Nat → Bool

/-- The value of predicate cell `k` at run time: the output of the self-modifying-code solver on the stamped formula. -/
@[expose] def rtVal (img : Image) (k : Nat) : Bool :=
  match smcSolve img.formula with
  | some sol => decide (2 * k ∈ sol)
  | none => false

/-- The predicate cells the program reads. -/
@[expose] def Image.cells (img : Image) : List Nat := codeReads (compile img.prog)

/-- The behaviour of the image: the block trace with the run-time cell values (the toggled variable starts true). -/
@[expose] def Image.run (img : Image) (c : Bool) : Option (List Nat × Bool) := traceS (rtVal img) img.prog c true

/-- What an analyzer that reads the cells from the static code bytes concludes the program does. -/
@[expose] def Image.staticRun (img : Image) (c : Bool) : Option (List Nat × Bool) :=
  traceS img.blueprint img.prog c true

/-- `p`, run with generator outputs `sol` and condition `c`, halts within some fuel with block trace and toggled value `r`. -/
@[expose] def Runs (sol : Nat → Bool) (p : Stmt) (c : Bool) (r : List Nat × Bool) : Prop :=
  ∃ f, exec f (compile p) sol c 0 true [] = some r

/-- The image halts with the same block trace and final value as `orig` (reading no generator output), for both conditions. -/
@[expose] def Image.Behaves (img : Image) (orig : Stmt) : Prop :=
  ∀ c r, Runs (rtVal img) img.prog c r ↔ Runs (fun _ => false) orig c r

/-- The static scheme for goto-free blocks `S`, `T`: `S; T` and `if (cd) S; T` become the irreducible forms of Figures 5(b), 5(c),
6(b), 6(c) with conditions read from predicate cells; the toggled-variable forms need conditions that do not read it. -/
inductive Obfuscates : Stmt → Stmt → Prop
  | b5 {S T : Stmt} : Structured S → Structured T → Obfuscates (.seq S T) (prot5 S T)
  | c5 {S T : Stmt} : Structured S → Structured T → (∀ c, PureS (fun _ => false) c S ∧ PureS (fun _ => false) c T) →
      Obfuscates (.seq S T) (protC (.out 1) S T)
  | b6 {cd : Cond} {S T : Stmt} : Structured S → Structured T → Obfuscates (.seq (.ite1 cd S) T) (prot6 cd S T)
  | c6 {cd : Cond} {S T : Stmt} : Structured S → Structured T →
      (∀ c, PureS (fun _ => false) c S ∧ PureS (fun _ => false) c T ∧ PureC (fun _ => false) c cd) →
      Obfuscates (.seq (.ite1 cd S) T) (protC6 cd (.out 1) S T)

/-- A design: the image, the original program, the planted formula data (variables `n`, intended assignment `σ`, required
variables `req`, the planted forest and the extra implications) and the dynamic scheme's circuit and schedule. -/
structure Design where
  img : Image
  orig : Stmt
  n : Nat
  σ : Nat → Bool
  req : Nat → Prop
  forest : List (Lit × Lit)
  extra : List (Lit × Lit)
  /-- A design is a formula over its `n` variables: every extra implication mentions variables below `n` (a typing
  condition of the data, like `TwoSat.Wf`, not a hypothesis about the generator or the attacker). -/
  extra_wf : ∀ e ∈ extra, e.1.var < n ∧ e.2.var < n
  circ : DCirc Bool
  acts : List (Act Bool)

/-- The structural assumptions. S1: the stamped formula is a planted formula generated under the conditions of the generator
(`Planted`, every extra implication respects the intended assignment and stays among the variables). S2: the predicate cells
the program reads are planted, required variables whose intended value is false (the opaque conditions are false conditions,
read only through the solver output). S3: the schedule of the dynamic scheme respects the dependencies of the circuit. -/
structure Assumptions (d : Design) : Prop where
  planted : Planted d.n d.σ d.req d.forest
  extra_respects : ∀ e ∈ d.extra, Respecting d.σ e
  stamped : d.img.formula = impFormula d.n (d.forest ++ d.extra)
  cells_planted : ∀ k ∈ d.img.cells, k < d.n ∧ d.req k ∧ d.σ k = false
  schedule_topo : d.circ.Topo
  schedule_ordered : FinalOrdered d.circ d.acts

/-- An analyzer reports a predicted value for every predicate cell of an image. -/
structure Analyzer where
  predict : Image → Nat → Bool

/-- Capability of the class `Imm`: the analyzer reads the predicate cell from the static code bytes. -/
structure ImmCap (A : Analyzer) : Prop where
  static_read : ∀ img k, A.predict img k = img.blueprint k

/-- Capability of the class `SmcSem`: the analyzer implements stamping and the machine semantics, so its report is the
run-time value of the cell. -/
structure SmcSemCap (A : Analyzer) : Prop where
  runs_machine : ∀ img k, A.predict img k = rtVal img k

/-- Goal: the analyzer reports every predicate cell the program reads with its run-time value. -/
@[expose] def Determines (A : Analyzer) (img : Image) : Prop := ∀ k ∈ img.cells, A.predict img k = rtVal img k

/-- The work of the analyzer that runs the solver on the stamped formula, in the clean Tarjan cost model (one unit per
vertex entry, examined edge and popped vertex of the implication graph). -/
@[expose] def recoverWork (img : Image) : Nat := (tarjan img.formula.graph).ticks

/-! ### Observations (the `Trace`, `Dca` and `Fault` classes and the size observable) -/

/-- The trace of a schedule as a dynamic tracer sees it: for each action, the address (vertex) and the value it left in that
vertex. An action `(v, none)` is an execution of `v`; `(v, some d)` a faulty one (the fault class replaces the written value). -/
@[expose] def obs {α : Type} (c : DCirc α) : (Nat → α) → List (Act α) → List (Nat × α)
  | _, [] => []
  | σ, a :: t => (a.1, stepA c σ a a.1) :: obs c (stepA c σ a) t

/-- The pairs (vertex, final value) of a schedule: the data a correlation attack aligned by address has for every vertex. -/
@[expose] def finalObs {α : Type} (c : DCirc α) (σ : Nat → α) (acts : List (Act α)) : List (Nat × α) :=
  (List.range c.n).map fun v => (v, runA c σ acts v)

/-- The observable size of a program: the number of vertices of its control-flow graph. -/
@[expose] def vcount (s : Stmt) : Nat := (cfgOf (compile s)).n

/-- Functional equivalence of programs: the same block trace for both values of the condition and of the toggled variable. -/
@[expose] def Equiv (p q : Stmt) : Prop := ∀ c v, trace p c v = trace q c v

/-- The property of an obfuscator that a notion of indistinguishability must have for the size observable: equivalent programs
get obfuscations with the same number of vertices. -/
@[expose] def SizeIndist (O : Stmt → Stmt) : Prop := ∀ p q, Equiv p q → vcount (O p) = vcount (O q)

end SmcIrred.Threat
