module

public import SmcIrred.Spec.Lang

public section

namespace SmcIrred.Lang

/-! The listings of Figures 5 and 6. Block `A` is `0`, block `B` is `1`; the label `labelA`/`labelB` is
`8`/`9`. `falseCondition1`, `falseCondition2` are `falseC`, `trueThenFalse` is `ttf`. -/

@[expose] def blkA : Stmt := .blk 0
@[expose] def blkB : Stmt := .blk 1

/-- Figure 5(a): `A; B;`. -/
@[expose] def fig5a : Stmt := .seq blkA blkB

/-- Figure 5(b): `if (falseCondition1) goto labelB; do { A; labelB: B; } while (falseCondition2);`. -/
@[expose] def fig5b : Stmt := .seq (.ifGoto .falseC 9) (.doWhile (.seq blkA (.lab 9 blkB)) .falseC)

/-- Figure 5(c): `if (falseCondition1) goto labelB; while (trueThenFalse) { A; labelB: B; }`. -/
@[expose] def fig5c : Stmt := .seq (.ifGoto .falseC 9) (.while .ttf (.seq blkA (.lab 9 blkB)))

/-- Figure 6(a): `if (c) A; B;`. -/
@[expose] def fig6a : Stmt := .seq (.ite1 .c blkA) blkB

/-- Figure 6(b): `if (!c) goto labelB; do { A; labelB: B; } while (falseCondition1);`. -/
@[expose] def fig6b : Stmt := .seq (.ifGoto (.neg .c) 9) (.doWhile (.seq blkA (.lab 9 blkB)) .falseC)

/-- Figure 6(c): `if (falseCondition1) goto labelA; while (c && trueThenFalse) { labelA: A; } B;`. -/
@[expose] def fig6c : Stmt := .seq (.ifGoto .falseC 8) (.seq (.while (.and .c .ttf) (.lab 8 blkA)) blkB)

/-- The block trace of a program run from a state of the `trueThenFalse` variable with condition constant `c`, when
the generator outputs are `sol` (the listings below do not read them). -/
@[expose] def traceS (sol : Nat → Bool) (p : Stmt) (c v : Bool) : Option (List Nat × Bool) :=
  exec 100 (compile p) sol c 0 v []

/-- The block trace of a program that reads no generator output. -/
@[expose] def trace (p : Stmt) (c v : Bool) : Option (List Nat × Bool) := traceS (fun _ => false) p c v

/-! ### The static scheme: constant conditions read from the generator outputs

`falseCondition1`, `falseCondition2` become the outputs `out 1`, `out 2` of the 2-SAT solver on a planted formula whose
desired assignment makes them false. -/

/-- Figure 5(b) with solver-output conditions. -/
@[expose] def fig5bS : Stmt := .seq (.ifGoto (.out 1 true) 9) (.doWhile (.seq blkA (.lab 9 blkB)) (.out 2 true))

/-- Figure 5(c) with a solver-output condition. -/
@[expose] def fig5cS : Stmt := .seq (.ifGoto (.out 1 true) 9) (.while .ttf (.seq blkA (.lab 9 blkB)))

/-- Figure 6(b) with a solver-output condition. -/
@[expose] def fig6bS : Stmt := .seq (.ifGoto (.neg .c) 9) (.doWhile (.seq blkA (.lab 9 blkB)) (.out 1 true))

/-- Figure 6(c) with a solver-output condition. -/
@[expose] def fig6cS : Stmt := .seq (.ifGoto (.out 1 true) 8) (.seq (.while (.and .c .ttf) (.lab 8 blkA)) blkB)

/-! ### The protected forms for arbitrary code

`prot h S T k` is the shape of Figures 5(b) and 6(b) with the blocks `A`, `B` replaced by arbitrary statements `S`, `T`:
`if (h) goto labelT; do { S; labelT: T; } while (k);`. The label `9` is the one of the figures (the statements `S`, `T` of the
theorems carry no labels). Figure 5(b) is `prot5` (conditions `out 1`, `out 2`), Figure 6(b) is `prot6 c` (`!c`, `out 1`). -/

@[expose] def prot (h : Cond) (S T : Stmt) (k : Cond) : Stmt :=
  .seq (.ifGoto h 9) (.doWhile (.seq S (.lab 9 T)) k)

@[expose] def prot5 (S T : Stmt) : Stmt := prot (.out 1 true) S T (.out 2 true)

@[expose] def prot6 (cd : Cond) (S T : Stmt) : Stmt := prot (.neg cd) S T (.out 1 true)

theorem fig5bS_eq : fig5bS = prot5 blkA blkB := rfl

theorem fig6bS_eq : fig6bS = prot6 .c blkA blkB := rfl


/-! ### The protected forms with the toggled loop variable (Figures 5(c) and 6(c)) for arbitrary code

`protC h S T` is `if (h) goto labelT; while (trueThenFalse) { S; labelT: T; }` (label `9`): Figure 5(c) with `S`, `T` in place of
the blocks `A`, `B`.  `protC6 cd h S T` is `if (h) goto labelS; while (cd && trueThenFalse) { labelS: S; } T;` (label `8`):
Figure 6(c) for `if (cd) S; T`. -/

@[expose] def protC (h : Cond) (S T : Stmt) : Stmt :=
  .seq (.ifGoto h 9) (.while .ttf (.seq S (.lab 9 T)))

@[expose] def protC6 (cd h : Cond) (S T : Stmt) : Stmt :=
  .seq (.ifGoto h 8) (.seq (.while (.and cd .ttf) (.lab 8 S)) T)

theorem fig5cS_eq : fig5cS = protC (.out 1 true) blkA blkB := rfl

theorem fig6cS_eq : fig6cS = protC6 .c (.out 1 true) blkA blkB := rfl

/-- A condition that does not read the toggled variable: its value does not depend on it and it leaves it unchanged. -/
@[expose] def PureC (sol : Nat → Bool) (env : Bool) (k : Cond) : Prop := ∃ b, ∀ v, k.eval sol env v = (b, v)

@[expose] def PureS (sol : Nat → Bool) (env : Bool) : Stmt → Prop
  | .skip | .blk _ | .goto _ | .ifGoto _ _ => True
  | .seq s t => PureS sol env s ∧ PureS sol env t
  | .ite1 k s => PureC sol env k ∧ PureS sol env s
  | .ite k s t => PureC sol env k ∧ PureS sol env s ∧ PureS sol env t
  | .while k s => PureC sol env k ∧ PureS sol env s
  | .doWhile s k => PureS sol env s ∧ PureC sol env k
  | .lab _ s => PureS sol env s

/-! ### The graphs as drawn (published Figures 5 and 6)

The invisible entry nodes of the drawings (`i0`, `i00`: one outside edge into `A` or `B`) are one entry vertex `0`;
invisible exit edges are not drawn. -/

/-- Figure 5(c) as drawn: `0` entry, `1` = `A`, `2` = `B`, `3` exit; edges entry→A, entry→B, A→B, B→A and the blue edge
A→exit. There is no node holding only the loop condition. -/
@[expose] def fig5cDrawn : Digraph where
  n := 4
  succ k := [[1, 2], [2, 3], [1], []].getD k []

/-- The block labels of the vertices of `fig5cDrawn` (`A` = 0, `B` = 1). -/
@[expose] def fig5cLabel (k : Nat) : List Nat := [[], [0], [1], []].getD k []

/-- Figure 6(c) as drawn: `0` entry, `1` = `c`, `2` = `A`, `3` = `B`; edges entry→c, entry→A, c→A, c→B (blue), A→B, A→c. -/
@[expose] def fig6cDrawn : Digraph where
  n := 4
  succ k := [[1, 2], [2, 3], [3, 1], []].getD k []

/-- Figure 5(b) as drawn: entry→A, entry→B, A→B, B→A. -/
@[expose] def fig5bDrawn : Digraph where
  n := 3
  succ k := [[1, 2], [2], [1]].getD k []

/-- Figure 6(b) as drawn: `0` = `c`, `1` = `A`, `2` = `B`; edges c→A, c→B, A→B, B→A. -/
@[expose] def fig6bDrawn : Digraph where
  n := 3
  succ k := [[1, 2], [2], [1]].getD k []

/-- A walk from `a` to the exit vertex `x` and the blocks it executes. -/
inductive WalkTr (g : Digraph) (lab : Nat → List Nat) (x : Nat) : Nat → List Nat → Prop
  | exit : x < g.n → WalkTr g lab x x (lab x)
  | step {a b : Nat} {t : List Nat} : g.edge a b → WalkTr g lab x b t → WalkTr g lab x a (lab a ++ t)

end SmcIrred.Lang
