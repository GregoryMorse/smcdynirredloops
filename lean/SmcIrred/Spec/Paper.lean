module

public import SmcIrred.Spec.Threat
public import SmcIrred.Spec.Extremal
public import SmcIrred.Spec.TwoSatSolve
public import SmcIrred.Spec.Edges
public import SmcIrred.Spec.AESProg
public import SmcIrred.Spec.Eval
public import SmcIrred.Spec.Flatten

public section

namespace SmcIrred.Paper

open SmcIrred.Lang SmcIrred.Dyn SmcIrred.Threat SmcIrred.Struct

/-! # The selected mathematical result

Morse, Alqaradaghi and Kozsik, *Control flow obfuscation with irreducible loops and self-modifying code*, Publ. Math.
Debrecen 100 (Supplementum) (2022) 617–637, with the corrections recorded in `lean/errata`. The statement selects five
result families; the paper's claims that are not in them (timings, tool experiments, literature statements, opinions) are
not part of the statement and are listed as non-claims in `lean/PAPER_MAP.md`.

* `SmcTwoSatCorrect`: the self-modifying-code solver is a correct 2-SAT solver (it reports unsatisfiability exactly when
  the formula is unsatisfiable and otherwise returns a satisfying assignment); for the implications of a planted forest
  (and for the output of the generator `genForest`/`genExtra` of Section 3.1, whatever its random choices) the solver
  succeeds and its solution takes the intended values on the required variables.
* `IrreducibleExtremal`: for every control-flow graph on `n` vertices and every valid depth-first jungle there are at most
  `n − 2` irreducible loops and at most `(n − 1)(n − 2) / 2` multiple-entry edges; both bounds are attained by the complete
  graph `K_n` and by the reduced graph `M_n`, and a graph with the maximal number of multiple-entry edges has at least
  `2n − 3` other edges (attained by `M_n` without its back edge to the first vertex).
* `TransformCorrect`: one added edge to a path never creates an irreducible loop, one edge from the join back into the first
  branch of an `n`-way conditional (`n ≥ 2`) does, and the Figure 5(b) and 6(b) transformations of any structured program
  with the two solver-generated false conditions give the same result as the original (for every environment), while the
  original has a reducible control-flow graph and every valid depth-first jungle of the transformed one has an irreducible
  loop.
* `CircuitCFGCorrect`: the Boolean control-flow graph generated for AES-128, AES-192 and AES-256 evaluates, for every key and
  block, to the encryption of the FIPS-197 specification.
* `SecurityModel`: relative to the explicit threat model of `lean/THREAT_MODEL.md` (structural assumptions on the design;
  adversary classes given as capability structures), correctness of the obfuscated image (T1) and unsoundness of analyzers that
  read the cells from the static code bytes (T2), both for the parameterized Figure 5/6 transformations of arbitrary goto-free blocks, the limit of analyzers that implement the machine semantics (T3), the
  structuring costs (T4), faults (T5), differential computation analysis on aligned traces (T6) and the absence of
  indistinguishability for the vertex count (T7), with a witness for the necessity of each assumption. No claim is made
  about any real tool, processor or compiler. -/

/-- **The self-modifying-code 2-SAT solver** (Section 3). For a well-formed formula without empty clauses: the solver of
the self-modifying machine (`smcSolve`) returns nothing exactly when the formula is unsatisfiable and otherwise the set of
true literal nodes of a satisfying assignment; the reference solver `twoSatSolve` (Tarjan components and the
Aspvall–Plass–Tarjan rule) is correct likewise; for a formula built from a planted forest (implications respecting the
intended assignment `σ`, with a forcing path for every required variable, plus further respecting implications) the solver
succeeds and agrees with `σ` on the required variables; and the planted generator as an algorithm (`genForest`: a forcing chain
through arbitrary intermediate variables for each required variable; `genExtra`: the candidate implications that respect `σ`)
produces such a forest for every choice of those variables and candidates, with the same conclusion. -/
@[expose] def SmcTwoSatCorrect : Prop :=
  (∀ f : TwoSat, f.Wf → (∀ c ∈ f.clauses, c ≠ []) →
    (smcSolve f = none ↔ ∀ a, ¬ f.Sat a) ∧ (∀ sol, smcSolve f = some sol → f.Sat (fun x => decide (2 * x ∈ sol)))) ∧
  (∀ f : TwoSat, f.Wf → (∀ c ∈ f.clauses, c ≠ []) →
    (twoSatSolve f = none ↔ ∀ a, ¬ f.Sat a) ∧ (∀ a, twoSatSolve f = some a → f.Sat a)) ∧
  (∀ (n : Nat) (σ : Nat → Bool) (req : Nat → Prop) (forest extra : List (Lit × Lit)),
    Planted n σ req forest → (∀ e ∈ extra, Respecting σ e) → (∀ e ∈ extra, e.1.var < n ∧ e.2.var < n) →
    ∃ sol, smcSolve (impFormula n (forest ++ extra)) = some sol ∧ ∀ x, x < n → req x → decide (2 * x ∈ sol) = σ x) ∧
  (∀ (n : Nat) (σ : Nat → Bool) (req : Nat → Prop) (specs : List (Nat × List Nat)) (cands : List (Lit × Lit)),
    (∀ s ∈ specs, s.1 < n ∧ ∀ m ∈ s.2, m < n) → (∀ x, x < n → req x → ∃ ms, (x, ms) ∈ specs) →
    Planted n σ req (genForest σ specs) ∧ (∀ e ∈ genExtra n σ cands, Respecting σ e ∧ e.1.var < n ∧ e.2.var < n) ∧
    ∃ sol, smcSolve (impFormula n (genForest σ specs ++ genExtra n σ cands)) = some sol ∧
      ∀ x, x < n → req x → decide (2 * x ∈ sol) = σ x)

/-- **Extremal irreducible loops and multiple-entry edges** (Section 5, Definition 4). Counts are taken over a valid
depth-first jungle `J` of a control-flow graph with root `r`. (1) At most `n − 2` irreducible loops and at most
`(n − 1)(n − 2) / 2` multiple-entry edges. (2) The complete graph `K_n` and (3) the reduced graph `M_n` with the chain jungle
attain both bounds. (4) A graph with the maximal number of multiple-entry edges has at least `2n − 3` further edges, and
(5) `M_n` without its back edge to the first vertex (`MnLite n`) is valid for the chain jungle, has the maximal number of
multiple-entry edges and exactly that many further edges. -/
@[expose] def IrreducibleExtremal : Prop :=
  (∀ (g : Digraph) (r : Nat) (J : Jungle), g.IsCFG r → J.Valid g r → 2 ≤ g.n →
    g.irrCount J ≤ g.n - 2 ∧ 2 * g.meeCount J ≤ (g.n - 1) * (g.n - 2)) ∧
  (∀ n : Nat, 2 ≤ n → (chainJungle n).Valid (Kn n) 0 ∧ (Kn n).irrCount (chainJungle n) = n - 2 ∧
    2 * (Kn n).meeCount (chainJungle n) = (n - 1) * (n - 2)) ∧
  (∀ n : Nat, 2 ≤ n → (chainJungle n).Valid (Mn n) 0 ∧ (Mn n).irrCount (chainJungle n) = n - 2 ∧
    2 * (Mn n).meeCount (chainJungle n) = (n - 1) * (n - 2)) ∧
  (∀ (g : Digraph) (r : Nat) (J : Jungle), g.IsCFG r → J.Valid g r → 2 ≤ g.n →
    2 * g.meeCount J = (g.n - 1) * (g.n - 2) → g.meeCount J + (2 * g.n - 3) ≤ g.edgeCount) ∧
  (∀ n : Nat, 2 ≤ n → (chainJungle n).Valid (MnLite n) 0 ∧ 2 * (MnLite n).meeCount (chainJungle n) = (n - 1) * (n - 2) ∧
    (MnLite n).edgeCount = (Kn n).meeCount (chainJungle n) + (2 * n - 3))

/-- **The irreducible-loop transformations** (Section 5). (1) One edge added to a path never creates an irreducible loop
(for the depth-first order of the code). (2) An `n`-way conditional (`n ≥ 2`) has none, and one edge from the join back into
its first branch creates one. (3) For a planted formula whose intended assignment makes the variables `1` and `2` false and
any structured programs `S`, `T` (`S` nonempty), the solver outputs `1` and `2` are false and, with them as the opaque
conditions, the transformed program of Figure 5(b) returns the same trace and state as `S; T` for every environment and
state of the toggled variable; `S; T` has a reducible control-flow graph and every valid depth-first jungle of the
transformed program has an irreducible loop. (4) The same for Figure 6(b): `if (cd) S; T` against its transformation with
the single opaque condition `1`. -/
@[expose] def TransformCorrect : Prop :=
  (∀ n : Nat, ∀ x, x < n → ∀ y, y < n → NoIrr (addEdge (pathG n) x y)) ∧
  (∀ k : Nat, 2 ≤ k → NoIrr (nwayG k) ∧ ∃ w, w < k + 2 ∧ (nwayE k).Irreducible (dfsRun (nwayE k) 0 2) w) ∧
  (∀ (n : Nat) (σ : Nat → Bool) (req : Nat → Prop) (forest extra : List (Lit × Lit)),
    Planted n σ req forest → (∀ e ∈ extra, Respecting σ e) → (∀ e ∈ extra, e.1.var < n ∧ e.2.var < n) →
    1 < n → 2 < n → req 1 → req 2 → σ 1 = false → σ 2 = false →
    ∀ (S T : Stmt), Structured S → Structured T → 1 ≤ S.size →
    ∃ sol, smcSolve (impFormula n (forest ++ extra)) = some sol ∧
      (let o : Nat → Bool := fun k => decide (2 * k ∈ sol)
       o 1 = false ∧ o 2 = false ∧
       ∀ (env v : Bool) (r : List Nat × Bool),
         ((∃ f, exec f (compile (.seq S T)) o env 0 v [] = some r) ↔
           ∃ f, exec f (compile (prot5 S T)) o env 0 v [] = some r)) ∧
      (cfgOf (compile (.seq S T))).Reducible 0 ∧
      (∀ {J : Jungle}, J.Valid (cfgOf (compile (prot5 S T))) 0 → ∃ w, (cfgOf (compile (prot5 S T))).Irreducible J w)) ∧
  (∀ (n : Nat) (σ : Nat → Bool) (req : Nat → Prop) (forest extra : List (Lit × Lit)),
    Planted n σ req forest → (∀ e ∈ extra, Respecting σ e) → (∀ e ∈ extra, e.1.var < n ∧ e.2.var < n) →
    1 < n → req 1 → σ 1 = false →
    ∀ (S T : Stmt), Structured S → Structured T → 1 ≤ S.size → ∀ cd : Cond,
    ∃ sol, smcSolve (impFormula n (forest ++ extra)) = some sol ∧
      (let o : Nat → Bool := fun k => decide (2 * k ∈ sol)
       o 1 = false ∧
       ∀ (env v : Bool) (r : List Nat × Bool),
         ((∃ f, exec f (compile (.seq (.ite1 cd S) T)) o env 0 v [] = some r) ↔
           ∃ f, exec f (compile (prot6 cd S T)) o env 0 v [] = some r)) ∧
      (cfgOf (compile (.seq (.ite1 cd S) T))).Reducible 0 ∧
      (∀ {J : Jungle}, J.Valid (cfgOf (compile (prot6 cd S T))) 0 → ∃ w, (cfgOf (compile (prot6 cd S T))).Irreducible J w))

/-- **The Boolean control-flow graphs of AES** (Section 4). The generated graph of AES with 10, 12 and 14 rounds (key
lengths 128, 192 and 256 bits), whose vertices are evaluated in the order they were generated (`evalNodes`), has as outputs
the bits of the FIPS-197 encryption (`encrypt`) of the block read from the first 128 input vertices, for every key and
block. -/
@[expose] def CircuitCFGCorrect : Prop :=
  (∀ (key : Nat) (inp : Nat → Bool), (∀ i, 128 ≤ i → inp i = false) →
    (AES.aesGraph 10 (AES.aes128 key)).1.map (wev (AES.aesGraph 10 (AES.aes128 key)).2 inp) =
      AES.bits8 (AES.encrypt 10 (AES.aes128 key) (AES.blockBytes inp))) ∧
  (∀ (key : Nat) (inp : Nat → Bool), (∀ i, 128 ≤ i → inp i = false) →
    (AES.aesGraph 12 (AES.aes192 key)).1.map (wev (AES.aesGraph 12 (AES.aes192 key)).2 inp) =
      AES.bits8 (AES.encrypt 12 (AES.aes192 key) (AES.blockBytes inp))) ∧
  (∀ (key : Nat) (inp : Nat → Bool), (∀ i, 128 ≤ i → inp i = false) →
    (AES.aesGraph 14 (AES.aes256 key)).1.map (wev (AES.aesGraph 14 (AES.aes256 key)).2 inp) =
      AES.bits8 (AES.encrypt 14 (AES.aes256 key) (AES.blockBytes inp)))

/-- **The security model** (Section 5.1, `lean/THREAT_MODEL.md`). Every statement is about the explicit model: a design `d`
(image, original program, planted data, circuit and schedule) satisfying the structural assumptions `Assumptions d` (planted
and stamped formula, false cells, dependency-respecting schedule), and analyzers given by their capability. T1: the image
behaves as the original (`Image.Behaves`) and the schedule's final values are the circuit's, for `S; T` or `if (cd) S; T` with
arbitrary goto-free blocks and the parameterized Figure 5/6 transformations (`Obfuscates`). T2: an analyzer that reads the cells
from the static code bytes fails to determine some design, for every such pair. T3: an analyzer that implements the machine
semantics reports the intended values, at a work bound in the clean Tarjan cost model. T4: one state variable resolves any
flattening and the multiple-entry edges of `K_n` number `(n − 1)(n − 2) / 2`. T5: a fault outside the final execution of a vertex
leaves every final value unchanged, one in it overwrites it. T6: address-aligned traces determine the same (vertex, final value)
pairs for every dependency-respecting schedule. T7: no obfuscator whose output size is within four vertices of its input's is
size-indistinguishable. Necessity: for each assumption a design (or circuit) violating only it for which the conclusion fails;
for the schedule and the numbering, a topologically numbered circuit with a schedule not in order that changes a final value, a
circuit with a dependency cycle (no ordered schedule) and an acyclic circuit not numbered topologically with an ordered schedule
whose final value differs from `valOf`. -/
@[expose] def SecurityModel : Prop :=
  (∀ d : Design, Assumptions d → Obfuscates d.orig d.img.prog →
    d.img.Behaves d.orig ∧
    (∀ σ0 τ : Nat → Bool, ∀ v, v < d.circ.n → runA d.circ σ0 d.acts v = valOf d.circ τ v)) ∧
  (∀ {orig prog : Stmt}, Obfuscates orig prog → ∀ {A : Analyzer}, ImmCap A →
    ∃ d : Design, Assumptions d ∧ d.orig = orig ∧ d.img.prog = prog ∧ ¬ Determines A d.img) ∧
  (∀ {A : Analyzer}, SmcSemCap A → ∀ {d : Design}, Assumptions d →
    (∀ k ∈ d.img.cells, A.predict d.img k = d.σ k) ∧
    recoverWork d.img ≤ 2 * d.img.formula.graph.n + tEdges d.img.formula.graph d.img.formula.graph.n) ∧
  (∀ (n : Nat), 2 * (Kn n).meeCount (chainJungle n) = (n - 1) * (n - 2)) ∧
  (∀ (g : Digraph), WFg g → ∀ (lab : Nat → List Nat) (ch : Nat → Nat),
    (∀ v k t, v < g.n → (Walk g lab ch v k t ↔ FRun g lab ch v k t)) ∧
    (∀ s k, s < g.n → nextState g ch s k < g.n + 1)) ∧
  (∀ {α : Type} (c : DCirc α), c.Topo → ∀ {a b : List Nat} {x : Nat},
    FinalOrdered c (execs (a ++ x :: b) : List (Act α)) → x ∈ b → ∀ (δ : α) (σ τ : Nat → α),
    ∀ v, v < c.n → runA c σ (execs a ++ (x, some δ) :: execs b) v = valOf c τ v) ∧
  (∀ {α : Type} (c : DCirc α) {a b : List Nat} {x : Nat}, x ∉ b → ∀ (δ : α) (σ : Nat → α),
    runA c σ (execs a ++ (x, some δ) :: execs b) x = δ) ∧
  (∀ {α : Type} (c : DCirc α), c.Topo → ∀ {a b : List (Act α)}, FinalOrdered c a → FinalOrdered c b →
    ∀ (σ σ' : Nat → α), finalObs c σ a = finalObs c σ' b) ∧
  (∀ O : Stmt → Stmt, (∀ s, vcount s ≤ vcount (O s)) → (∀ s, vcount (O s) ≤ vcount s + 4) → ¬ SizeIndist O) ∧
  (∃ d : Design, Obfuscates d.orig d.img.prog ∧ Planted d.n d.σ d.req d.forest ∧ (∀ e ∈ d.extra, Respecting d.σ e) ∧
    (∀ e ∈ d.extra, e.1.var < d.n ∧ e.2.var < d.n) ∧
    (∀ k ∈ d.img.cells, k < d.n ∧ d.req k ∧ d.σ k = false) ∧ d.circ.Topo ∧ FinalOrdered d.circ d.acts ∧
    d.img.formula.clauses ≠ (impFormula d.n (d.forest ++ d.extra)).clauses ∧ ¬ d.img.Behaves d.orig) ∧
  (∃ d : Design, Obfuscates d.orig d.img.prog ∧ (∀ e ∈ d.forest, e.1.var < d.n ∧ e.2.var < d.n) ∧
    (∀ e ∈ d.forest, Respecting d.σ e) ∧ (∀ e ∈ d.extra, Respecting d.σ e) ∧
    (∀ e ∈ d.extra, e.1.var < d.n ∧ e.2.var < d.n) ∧ d.img.formula = impFormula d.n (d.forest ++ d.extra) ∧
    (∀ k ∈ d.img.cells, k < d.n ∧ d.req k ∧ d.σ k = false) ∧ d.circ.Topo ∧ FinalOrdered d.circ d.acts ∧
    ¬ d.img.Behaves d.orig) ∧
  (∃ d : Design, Obfuscates d.orig d.img.prog ∧ Planted d.n d.σ d.req d.forest ∧ (∀ e ∈ d.extra, Respecting d.σ e) ∧
    (∀ e ∈ d.extra, e.1.var < d.n ∧ e.2.var < d.n) ∧ d.img.formula = impFormula d.n (d.forest ++ d.extra) ∧
    (∀ k ∈ d.img.cells, k < d.n ∧ d.req k) ∧ d.circ.Topo ∧ FinalOrdered d.circ d.acts ∧
    ¬ d.img.Behaves d.orig) ∧
  (∃ d : Design, Planted d.n d.σ d.req d.forest ∧ (∀ e ∈ d.extra, e.1.var < d.n ∧ e.2.var < d.n) ∧
    d.img.formula = impFormula d.n (d.forest ++ d.extra) ∧ ¬ (∀ e ∈ d.extra, Respecting d.σ e) ∧
    smcSolve d.img.formula = none) ∧
  (∃ c : DCirc Bool, c.Topo ∧ ∃ acts : List (Act Bool), ¬ FinalOrdered c acts ∧
    ∃ v, runA c (fun _ => false) acts v ≠ valOf c (fun _ => false) v) ∧
  (∃ c : DCirc Bool, ¬ c.Topo ∧ ∀ acts : List (Act Bool), ¬ FinalOrdered c acts) ∧
  (∃ c : DCirc Bool, ¬ c.Topo ∧ ∃ acts : List (Act Bool), FinalOrdered c acts ∧
    ∃ v, v < c.n ∧ runA c (fun _ => false) acts v ≠ valOf c (fun _ => false) v)

end SmcIrred.Paper
