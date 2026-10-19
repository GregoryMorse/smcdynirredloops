module

public import SmcIrred.Spec.SmcMachine

public section

namespace SmcIrred.Vm

/-! # The instruction-level virtual machine of the SMC 2-SAT solver (`selfmodvmtwosat`, G28)

A transcription of `selfmodvmtwosat` of `native/selfmodgraph.cpp` (the `USE_VM` build): the opcodes, the blueprint of 36
instructions per node with its patch targets, the initial image and the interpreter loop. The C++ lambdas of an instruction
(`std::function`) are defunctionalised: every lambda of the source is one constructor of an operand type, with the values
it captures as arguments. The instruction memory is a function from addresses to instructions that the machine rewrites.

Modelling choices: nodes are the numbers `0 … n-1` of the implication graph with `nneg` the opposite literal (the C++ nodes are
the signed literals and its `std::map` order is the node order); data and the register are integers (the C++ `size_t`
arithmetic does not wrap on the runs considered, and `-1` marks an unset cell); a store or read of a cell that is not a data
cell, an empty stack and an out-of-range successor index are faults (in C++: an `assert`, undefined behaviour).

Layout: address `0` is the index cell, `1 … n` the outer calls, `n + 1` the pointer to the end of the topological chain,
`n + 2` its first jump; the block of node `x` starts at `base x = n + 3 + 36 x`. -/

/-- Where a jump goes. -/
inductive Tgt
  | at (a : Nat)
  | sat
  | unsat

/-- The value written by a store. -/
inductive Src
  | k (v : Int)
  | rp (c : Int)

/-- The address written by a store. -/
inductive Dst
  | k (a : Nat)
  | rp (c : Int)

/-- The address patched by `MODINST`. -/
inductive MAddr
  | k (a : Nat)
  | rp (c : Int)
  | deref (a : Nat)
  | peekOf (x : Nat)

/-- The condition of a conditional jump. -/
inductive Cnd
  | tru
  | fls
  | regZ
  | stkNe (k : Nat)
  | regGeLow (x : Nat)
  | regNe (a : Nat)
  | regNeSet (x : Nat)

/-- The instruction `MODINST` writes. -/
inductive Mk
  | jmpReg
  | jmpRegPlus (c : Int)
  | jcStkNe (off : Int)
  | peek
  | ret
  | jcTrue (off : Int)

inductive Ins
  | call (a : Nat)
  | callS (x : Nat)
  | data (v : Int)
  | jmp (t : Tgt)
  | load (a : Nat)
  | store (s : Src) (d : Dst)
  | pop
  | modinst (m : Mk) (a : MAddr)
  | jc (c : Cnd) (off : Int)
  | ret
  | peek
  | nop
  | func (x : Nat)
  | push (a : Nat)

inductive Status
  | run
  | sat
  | unsat
  | fault

structure VM where
  mem : Nat → Ins
  pc : Nat
  reg : Int
  stk : List Nat
  sol : List Nat
  st : Status

/-- The start of the block of node `x` in a graph with `n` nodes. -/
@[expose] def base (n x : Nat) : Nat := n + 3 + 36 * x

@[expose] def memUpd (mem : Nat → Ins) (a : Nat) (i : Ins) : Nat → Ins := fun j => if j = a then i else mem j

/-- The data cell at `a`. -/
@[expose] def dataAt (mem : Nat → Ins) (a : Nat) : Option Int :=
  match mem a with
  | .data v => some v
  | _ => none

@[expose] def Src.eval (reg : Int) : Src → Int
  | .k v => v
  | .rp c => reg + c

@[expose] def Dst.eval (reg : Int) : Dst → Nat
  | .k a => a
  | .rp c => (reg + c).toNat

/-- The address patched by `MODINST`. -/
@[expose] def MAddr.eval (g : Digraph) (mem : Nat → Ins) (reg : Int) : MAddr → Option Nat
  | .k a => some a
  | .rp c => some (reg + c).toNat
  | .deref a => (dataAt mem a).map Int.toNat
  | .peekOf x => some (base g.n ((g.succ x).getD (reg - 1).toNat 0) + 5)

/-- The truth of a condition (`none`: it reads a cell that is not a data cell). -/
@[expose] def Cnd.eval (g : Digraph) (m : VM) : Cnd → Option Bool
  | .tru => some true
  | .fls => some false
  | .regZ => some (m.reg == 0)
  | .stkNe k => some (k != m.stk.length)
  | .regGeLow x => (dataAt m.mem (base g.n x + 29)).map fun v => decide (m.reg ≥ v)
  | .regNe a => some (decide ((a : Int) ≠ m.reg))
  | .regNeSet x => (dataAt m.mem (base g.n (nneg x) + 31)).map fun v => decide (m.reg ≠ v)

/-- The instruction `MODINST` writes. -/
@[expose] def Mk.build (m : VM) : Mk → Ins
  | .jmpReg => .jmp (.at m.reg.toNat)
  | .jmpRegPlus c => .jmp (.at (m.reg + c).toNat)
  | .jcStkNe off => .jc (.stkNe m.stk.length) off
  | .peek => .peek
  | .ret => .ret
  | .jcTrue off => .jc .tru off

@[expose] def fault (m : VM) : VM := { m with st := .fault }

/-- One step of the interpreter loop (`switch (instructions[instptr]->opcode)`). -/
@[expose] def step (g : Digraph) (m : VM) : VM :=
  match m.st with
  | .run =>
    match m.mem m.pc with
    | .call a => { m with stk := (m.pc + 1) :: m.stk, pc := a }
    | .callS x =>
      { m with stk := (m.pc + 1) :: m.stk, pc := base g.n ((g.succ x).getD (m.reg - 1).toNat 0) }
    | .data v => { m with reg := v, pc := m.pc + 1 }
    | .jmp (.at a) => { m with pc := a }
    | .jmp .sat => { m with st := .sat }
    | .jmp .unsat => { m with st := .unsat }
    | .load a =>
      match dataAt m.mem a with
      | some v => { m with reg := v, pc := m.pc + 1 }
      | none => fault m
    | .store s d =>
      match dataAt m.mem (d.eval m.reg) with
      | some _ => { m with mem := memUpd m.mem (d.eval m.reg) (.data (s.eval m.reg)), pc := m.pc + 1 }
      | none => fault m
    | .pop =>
      match m.stk with
      | a :: r => { m with reg := a, stk := r, pc := m.pc + 1 }
      | [] => fault m
    | .modinst mk ad =>
      match ad.eval g m.mem m.reg with
      | some a => { m with mem := memUpd m.mem a (mk.build m), pc := m.pc + 1 }
      | none => fault m
    | .jc c off =>
      match c.eval g m with
      | some true => { m with pc := (m.pc + off).toNat }
      | some false => { m with pc := m.pc + 1 }
      | none => fault m
    | .ret =>
      match m.stk with
      | a :: r => { m with stk := r, pc := a }
      | [] => fault m
    | .peek =>
      match m.stk with
      | a :: _ => { m with reg := a, pc := m.pc + 1 }
      | [] => fault m
    | .nop => { m with pc := m.pc + 1 }
    | .func x => { m with sol := if nneg x ∈ m.sol then m.sol else x :: m.sol, pc := m.pc + 1 }
    | .push a => { m with stk := a :: m.stk, pc := m.pc + 1 }
  | _ => m

/-- `n` steps. -/
@[expose] def run (g : Digraph) : Nat → VM → VM
  | 0, m => m
  | k + 1, m => run g k (step g m)

/-- The blueprint of the node `x`: the 36 instructions of the source (offsets `0 … 35`). -/
@[expose] def blueprint (g : Digraph) (x : Nat) : Nat → Ins
  | 0 => .data (-1)
  | 1 => .load 0
  | 2 => .store (.rp 0) (.k (base g.n x))
  | 3 => .store (.rp 0) (.k (base g.n x + 29))
  | 4 => .store (.rp 1) (.k 0)
  | 5 => .pop
  | 6 => .modinst .jmpReg (.k (base g.n x + 30))
  | 7 => .modinst (.jcStkNe 2) (.k (base g.n x + 20))
  | 8 => .modinst (.jcStkNe 2) (.k (base g.n x + 13))
  | 9 => .modinst .ret (.k (base g.n x + 1))
  | 10 => .data ((g.succ x).length : Nat)
  | 11 => .jc .regZ 9
  | 12 => .store (.rp (-1)) (.k (base g.n x + 10))
  | 13 => .jc .tru 2
  | 14 => .modinst .peek (.peekOf x)
  | 15 => .callS x
  | 16 => .jc (.regGeLow x) (-6)
  | 17 => .store (.rp 0) (.k (base g.n x + 29))
  | 18 => .modinst (.jcTrue 7) (.k (base g.n x + 22))
  | 19 => .jc .tru (-9)
  | 20 => .jc .tru 2
  | 21 => .push (base g.n x + 16)
  | 22 => .jc .fls 7
  | 23 => .pop
  | 24 => .modinst (.jmpRegPlus 15) (.deref (g.n + 1))
  | 25 => .store (.k (base g.n x : Nat)) (.rp 15)
  | 26 => .store (.rp 19) (.k (g.n + 1))
  | 27 => .store (.k (g.n : Nat)) (.rp (-16))
  | 28 => .jc (.regNe (base g.n x + 16)) (-5)
  | 29 => .data (-1)
  | 30 => .jmp (.at 0)
  | 31 => .data (-1)
  | 32 => .jc (.regNeSet x) 2
  | 33 => .jmp .unsat
  | 34 => .func x
  | _ => .jmp .sat

/-- The initial image: the index cell, the outer calls, the topological pointer and its first jump, the blocks. -/
@[expose] def image (g : Digraph) : Nat → Ins := fun a =>
  if a = 0 then .data 0
  else if a ≤ g.n then .call (base g.n (a - 1))
  else if a = g.n + 1 then .data ((g.n + 2 : Nat) : Int)
  else if a = g.n + 2 then .jmp .sat
  else blueprint g ((a - (g.n + 3)) / 36) ((a - (g.n + 3)) % 36)

@[expose] def VM.init (g : Digraph) : VM := ⟨image g, 0, 0, [], [], .run⟩

/-- The solution set returned by a run of `fuel` steps: `none` unless the run ended with `sat` or `unsat`. -/
@[expose] def vmResult (g : Digraph) (fuel : Nat) : Option (Option (List Nat)) :=
  match (run g fuel (VM.init g)).st with
  | .sat => some (some (run g fuel (VM.init g)).sol)
  | .unsat => some none
  | _ => none

/-- The offsets inside a block that the restamp resets: the visited marker and its `load`/`ret` (0, 1), the peek patch
(5), the counter (10), the depth checks (13, 20), the lowlink check (22), the lowlink (29), the return jump (30), the
component (31) and the chain link (35). -/
@[expose] def patchOffsets : List Nat := [0, 1, 5, 10, 13, 20, 22, 29, 30, 31, 35]

/-- The declared patch cells: the index cell, the tail pointer, the head jump and the `patchOffsets` of every block. -/
@[expose] def declared (g : Digraph) (a : Nat) : Bool :=
  a == 0 || a == g.n + 1 || a == g.n + 2 ||
    (decide (g.n + 3 ≤ a) && decide ((a - (g.n + 3)) / 36 < g.n) && decide ((a - (g.n + 3)) % 36 ∈ patchOffsets))

/-- Restamping (Fig. 2b "Reuse") at the level of the instruction memory: the declared cells are reset to the stamped
image, every other cell is kept. -/
@[expose] def restampMem (g : Digraph) (mem : Nat → Ins) : Nat → Ins := fun a => if declared g a then image g a else mem a

/-- The machine after a restamp: the stamped memory, a fresh start, empty stack and solution set. -/
@[expose] def vmRestamp (g : Digraph) (m : VM) : VM := ⟨restampMem g m.mem, 0, 0, [], [], .run⟩

/-- The answer of a finished run (`none`: it did not finish). -/
@[expose] def vmAnswer (m : VM) : Option (Option (List Nat)) :=
  match m.st with
  | .sat => some (some m.sol)
  | .unsat => some none
  | _ => none

/-- `k` successive queries of the stamped image, each run for `fuel` steps and followed by a restamp. -/
@[expose] def vmRounds (g : Digraph) (fuel : Nat) : Nat → VM → List (Option (Option (List Nat)))
  | 0, _ => []
  | k + 1, m => vmAnswer (run g fuel m) :: vmRounds g fuel k (vmRestamp g (run g fuel m))

end SmcIrred.Vm
