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

/-- The static scheme: the transformed program of an original program (Figures 5 and 6, the solver-output variants). -/
inductive Obfuscates : Stmt → Stmt → Prop
  | b5 : Obfuscates fig5a fig5bS
  | c5 : Obfuscates fig5a fig5cS
  | b6 : Obfuscates fig6a fig6bS
  | c6 : Obfuscates fig6a fig6cS

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
  circ : DCirc Bool
  acts : List (Act Bool)

/-- The structural assumptions. S1: the stamped formula is a planted formula generated under the conditions of the generator
(`Planted`, every extra implication respects the intended assignment and stays among the variables). S2: the predicate cells
the program reads are planted, required variables whose intended value is false (the opaque conditions are false conditions,
read only through the solver output). S3: the schedule of the dynamic scheme respects the dependencies of the circuit. -/
structure Assumptions (d : Design) : Prop where
  planted : Planted d.n d.σ d.req d.forest
  extra_respects : ∀ e ∈ d.extra, Respecting d.σ e
  extra_wf : ∀ e ∈ d.extra, e.1.var < d.n ∧ e.2.var < d.n
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

end SmcIrred.Threat
