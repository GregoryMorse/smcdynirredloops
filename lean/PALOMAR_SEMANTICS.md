# Palomar semantics: what the Challenges state and what they do not

Source: Morse, Alqaradaghi and Kozsik, *Control flow obfuscation with irreducible loops and self-modifying code*,
Publ. Math. Debrecen 100 (Supplementum) (2022) 617–637, DOI 10.5486/PMD.2022.Suppl.5 (the formalizer is its first
author). The development is `lean/SmcIrred/` (Lean 4.35.0-rc3, no Mathlib, no dependencies). The statement-level
definitions are `lean/SmcIrred/Spec/*.lean` (core imports only); `Challenge.lean` and `ChallengeAES.lean` are generated from
them by `validation/make_challenge.py` (`--check` in CI fails when a file differs), pruned to the declarations the statements
mention, and contain one `sorry` theorem each, `PalomarSIL.mathematical_result`. `Solution.lean` and `SolutionAES.lean`
prove them from `SmcIrred.Paper`, which derives each family from the theorems of the development. Two Challenges are
submitted because one Challenge may have at most 1,000 lines (`Challenge.lean` 867 lines, `ChallengeAES.lean` 526 lines;
both exceed the 300-line warning size: the statements need the definitions of the self-modifying machine, the depth-first
jungles, the extremal graphs and the security model, which cannot be shortened without dropping a principal claim).

## Compared declarations

| Declaration | Informal claim | Paper locator | Fidelity |
|---|---|---|---|
| `PalomarSIL.mathematical_result` (Challenge) — `SmcTwoSatCorrect` | The self-modifying 2-SAT solver is correct (`none` iff unsatisfiable, otherwise a satisfying assignment); the reference Tarjan/APT solver is too; for a planted forest (implications respecting the intended assignment, forcing paths for the required variables, extra respecting implications) the solver succeeds and agrees with the intended assignment on the required variables, and the generator as an algorithm (`genForest`, `genExtra`, for every choice of its intermediate variables and candidate implications) produces such a forest. | §2, §3, §3.1 | Proved. Formulas must be well-formed without empty clauses (errata P01–P03). |
| — `IrreducibleExtremal` | For every CFG on n ≥ 2 vertices and valid DFS jungle: at most n−2 irreducible loops and (n−1)(n−2)/2 multiple-entry edges; attained by K_n and M_n; a graph with the maximal number of multiple-entry edges has at least 2n−3 further edges, and M_n without its back edge to the first vertex has the maximal number of multiple-entry edges and exactly that many further edges (no classification of all extremal graphs). | §1, §5 Def. 4 | Proved. Definitions 3 and 4 are restated (P16); counts are claims, not definitions. |
| — `TransformCorrect` | One edge added to a path never creates an irreducible loop; one edge from the join into the first branch of an n-way conditional does; the Figure 5(b) and 6(b) transformations with solver-generated false conditions preserve behavior for all environments, start from a reducible CFG and every valid DFS jungle of the result has an irreducible loop. | §5, Figs. 5, 6 | Proved for structured programs `S`, `T` (`S` nonempty). Figure 5(c)/6(c) corrections P18, P19. |
| — `SecurityModel` | Relative to the explicit structural model (`lean/THREAT_MODEL.md`): T1 correctness of the image and T2 unsoundness of analyzers that report the placeholder a cell has in the program's own compiled code before the self-modifying write (the value is computed mechanically from the program, `codeStatic`, not an independent input) (both for the parameterized Figure 5/6 transformations of arbitrary goto-free blocks, `Obfuscates`), T3 success of the solver and recovery of the intended values by machine-semantics analyzers, with the tick count of the reference Tarjan run bounded (the analyzer's own work is not modeled), T4 structuring cost, T5 faults, T6 differential computation analysis, T7 no size-indistinguishability for obfuscators whose output size is within four vertices of the input's in either direction, plus necessity witnesses (each keeps every other assumption and breaks a conclusion: the image's behaviour for stamping, forcing, required and false cells; the solver's success, stated in T3, for the forest and the extra implications respecting the intended assignment; a final value for the schedule order; for the topological numbering, a circuit with no dependency-respecting schedule and one whose dependency-respecting schedule ends with a value different from `valOf`; the bounds below n are typing conditions). | §5.1 | Adapted. The paper states these claims without a threat model (P22–P25); here each is a theorem about stated structural assumptions. No claim about any real tool, processor or compiler. |
| `PalomarSIL.mathematical_result` (ChallengeAES) — `CircuitCFGCorrect` | The generated Boolean control-flow graphs of AES-128/192/256 (10/12/14 rounds) evaluate, for every key and block, to the FIPS-197 encryption. | §4 | Proved against the development's own `encrypt` (checked against the published test vectors as evidence). The graph variant is the one the development generates (open author question L09). |

## Definitions a reader should know

* `smcSolve`: the 2-SAT solver as the self-modifying machine runs it (implication graph, Tarjan components, the Aspvall–Plass–
  Tarjan rule), returning the true literal nodes of an assignment.
* `Jungle.Valid g r`: a depth-first jungle (tree, forward, back, cross edges with discovery/finish times) of `g` from `r`;
  `Irreducible J w` and `meeCount` follow Havlak's loop nesting forest of that jungle.
* `Planted n σ req forest`: a forest of implications that respects `σ` with a forcing path to every required variable.
* `Design`, `Assumptions`, `Analyzer`: the threat model; the assumptions are structural (planted and stamped formula, false
  cells, dependency-respecting schedule) and never state that an attacker fails (`validation/threat_audit.py`).
* `DCirc`, `runA`, `valOf`, `FinalOrdered`: dataflow circuits and their scheduled execution.
* `exec`, `compile`, `prot5`, `prot6`, `cfgOf`: the flat-code machine, compiler of structured programs, the protected programs
  of Figures 5(b) and 6(b) and their control-flow graphs.

## Not in the statements (non-claims)

Timings, tool experiments, the x86-64 machine code, compilers, decompilers, processors and timers (black boxes), the paper's
literature statements and opinions, and node-splitting complexity (Carter–Ferrante–Thomborson, not formalized: `lean/GAPS.md`
G33). Native runs and measurements are evidence, never proof. The paper itself is corrected only by `lean/errata/ERRATA.md`
(paper text, tables, figures, references); code and README fixes are in `lean/CODE_FIXES.md`.

## Provenance and review

AI-assisted: plan by Claude Opus 5.5, execution by Claude Sonnet 5.5 through Claude Code, one round per session
(`lean/ROUNDS.md`); statements, the threat model and all decisions are the author's. Review is self-assessed; no independent
human review is claimed. No Palomar submission or registration has been made. License: MIT (`LICENSE`, `lean/LICENSE_AUDIT.md`).
