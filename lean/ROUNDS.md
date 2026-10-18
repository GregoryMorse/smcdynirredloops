# Rounds

State machine for `lean/FORMALIZATION_PLAN.md`. Update at every round close (state, then a 5-line
handoff: done / next / open obligations / hazards / evidence file).

| Round | Deliverable | Priority | State |
| --- | --- | --- | --- |
| R0 | Bootstrap, references, baselines (authorization question) | must | DONE 2026-10-17 |
| R1 | Claim inventory, errata verification, sources, author questions | must | DONE 2026-10-17 |
| R2 | Graph foundations, DFS jungle, Figure 4(a)(b) | must | DONE 2026-10-17 |
| R3 | Havlak loop nesting forest, Figure 4(c), small CFGs, non-uniqueness | must | DONE 2026-10-17 (algorithm equivalence: open obligation) |
| R3b | Close G01/G02: Havlak algorithm = declarative LNF; reducible-CFG body uniqueness (scheduled after R5, before R6 if time; mandatory before R23) | must | DONE 2026-10-18 |
| R4 | Extremal results: K_n, M_n, n−2 bound (MEE bound should) | must | DONE 2026-10-17 (G19 open) |
| R4c | Close G19 (P15 second half: max-MEE CFGs have >= 2n-3 other edges), after R5 | should | DONE 2026-10-18 |
| R5 | 2-SAT: implication graph, APT theorem, unit clauses, Figure 1 | must | DONE 2026-10-17 |
| R6 | Tarjan's algorithm, cost, reference solver (`tarjan_scc` model -> R6b, G22) | must | done 2026-10-18 |
| R6b | `Tarjan/CodeModel` (G22) and DNF parity bound (G21) | must | done 2026-10-18 |
| R6c | G23 (re-emitted duplicates are exactly the roots; needs a done-vertex root invariant) | must | done 2026-10-18 |
| R7 | SMC 2-SAT solver Level 2 ⇒ Tarjan/APT; restamp lemma | must | done 2026-10-18 |
| R8 | SMC solver VM level (should); native vectors and listing evidence (must) | must/should | DONE 2026-10-18 (items 2–3; item 1 and G27 -> R8b) |
| R8b | G27 step bound for the Level 2 machine; G28 VM instruction-list refinement (R8 item 1) | should | PARTIAL 2026-10-19 (G27 done; G28 -> R8c) |
| R9 | Planted 2-SAT generator (§3.1, P04) | must | DONE 2026-10-18 |
| R10 | Boolean-CFG VM: order independence, data-independent counts, subgraphs | must | DONE |
| R11 | Gate primitives, decoders, adders (P05), DSL compiler correctness | must | DONE 2026-10-18 (DSL compiler, graph-level adder, Circ.val bridge -> G30/R13) |
| R12 | AES specification facts (S-box P07, xtime, key expansion, vectors) | must | DONE 2026-10-18 |
| R13 | AES compiler correctness | should | TODO |
| R14 | Arithmetic for RSA (Montgomery, windows, Karatsuba/Toom P08, word size P09) | must | DONE 2026-10-18 (items 1-6; items 7-8 partly -> R14b) |
| R14b | RBSD carry-free addition, NAF/MOF, Wallace counts (G31) | should | TODO |
| R15 | RSA compiler correctness | should | TODO |
| R16 | Tables 1–2: regeneration (M) and data checks (FD) | must | PARTIAL 2026-10-19 (regeneration done; Lean data checks, GMP re-measure -> R16b) |
| R17 | Transformation language, Figures 5–6 (P18, P19), minimal edges | must | DONE 2026-10-18 (figure instances; general n -> R17b) |
| R17b | General-n minimal edges, arbitrary-program transformation (G32) | should | TODO |
| R18 | Figure 4 C++ code, flattening; structured ⇒ reducible, CFT (should) | must/should | DONE 2026-10-18 (items 1-2; items 3-4 -> R18b) |
| R18b | Structured programs reducible, CFT leftist trees (G33) | should | TODO |
| R19 | Dynamic scheme, faults, static scheme end-to-end | must | DONE 2026-10-18 (abstract model; bridge -> R19c) |
| R19c | Bridge of the dynamic scheme to the CFG evaluator and schedule construction (G34) | should | DONE 2026-10-19 (call-free circuits; rest G34) |
| R20a | Security model I: definitions, T1–T3 (crux) | must | DONE 2026-10-18 |
| R20b | Security model II: T4–T7, necessity, §5.1 texts | must | DONE 2026-10-18 |
| R19b | Protected AES/RSA variant: the author implements it, this round integrates (P13, D03) | must | BLOCKED on the author |
| R21a | Portable native build system: CMake, build/ tree, VS 2022/2026, CI Windows/Linux/macOS | must | PARTIAL 2026-10-19 (local Windows verified; CI matrix pending, G37) |
| R21 | Code fixes (not errata) and native acceptance | must | PARTIAL 2026-10-19 (L01-L06, L11, D03 done; Linux/R16 reruns and L07-L09 open) |
| R22 | Errata list (paper only) | must | DONE 2026-10-18 (author review requested) |
| R23 | Coverage and fidelity audit | must | PARTIAL 2026-10-18 (audit passes; closes after the pending rounds) |
| R24 | Palomar package, CI, handoff (user submits and registers) | must | TODO |
| R25 | Tag (after registration); corrected manuscript deferred by the user (errata list only for now) | must | TODO |

## Handoff notes

### Planning (Claude Opus 5.5, 2026-10-17)

- Plan written from the published PDF (Publ. Math. Debrecen 100 Suppl. (2022) 617–637, SHA-256
  `e89a803c…`, rendered pages checked) and the author's manuscript TeX (OneDrive, reference only, SHA-256
  `309bc5d1…`). No arXiv version exists. §1 records the facts verified during planning: Figure 1 =
  `testformula3` and fully consistent; Figure 4 jungle and Havlak LNF correct; Section 5 bounds checked by
  `validation/planning/section5_bruteforce.py` (n ≤ 5 exhaustive, 6–7 sampled); CFT 2003 read.
- Errata seeds (plan §5): confirmed P01, P02, P03, P05, P07, P08, P12, P14, P16; confirmed after a Lean
  round or source check P04 (R9), P17 (R1 DOI), P18 (R17), P21 (R1), P22 (R20b); inferred P09, P19;
  wording ask-author P06, P15, P23, P24; ask-author P10, P13; pending P11 (R16); optional P25, P26;
  grouped T01 (typographical), B01 (bibliography).
- Code seeds (not errata): L01–L06, D01–D03 (`tarjan_scc` re-entry, harness labels/stubs, two latent
  Python defects, regeneration seed, AES key). The IL-protected AES/RSA variant and the §3.1 generator are
  not implemented in the repository (P13, D03).
- No authorization for commits/pushes yet in this repository: R0's single question asks (plus whether the
  manuscript may be committed; the published PDF stays out of git by default).
- Next: R0.

### R0 (Claude Sonnet 5.5, 2026-10-17)

- Done: authorization answered by the user (commits and pushes yes; errata list is committed; manuscript TeX/bib/cls and the published PDF are not; no corrected paper now, errata only; tag name still to ask in R25). `validation/fetch_reference.py` (4 hashes OK, 21 pages), manuscript builds to 21 pages (`build_tex.py`), Lake stub `SmcIrred.Spec.Graph` builds and audits clean under the guard, vendored infra (`lean/VENDORED.md`), `validation/data/paper_tables.json` + `check_tables.py` pass, `.gitignore`, workflows trimmed to the Lean/native baseline (`proof.yml`: linux-proof, windows-native, linux-native).
- Next: R1 (claim inventory, errata verification, sources; copy and adapt `audit_errata.py`, `make_errata.py` and the errata/Palomar templates from `../SelfModTamper/lean` at commit 69a9d34).
- Open obligations: `aes` and `ecdsa` native projects exceed the 1.5 GB local cap when compiled (generated/aesvm.cpp 10.8 MB; ecdsa256vm.c C1060): CI-only. Win32 and g++ baselines are CI-only. Round-close `limited_run.py` must be invoked with `python` (not `py -I`: it imports a sibling module).
- Hazards: `limited_run.py`/`build_modules.py` break under `py -I` for direct calls; `latexmk` exits 12 on the first-pass graphviz message (accepted by `build_tex.py`); Table 3, Fig. 1 and Fig. 4 page sign-off rests on the planning-time inspection (Tables 1-2 re-checked).
- Evidence: `validation/rounds/R0.json`.

### R1 (Claude Sonnet 5.5, 2026-10-17)

- Done: `lean/errata/edits.json` (31 items: 26 confirmed, ask-author P06, P10, P11, P13, P28), `lean/errata/POLICY.md`, `lean/CODE_FIXES.md` (adds L07), `lean/PAPER_MAP.md` (C01-C83 + C84, C85 with classes, pages, R-class source checks), `validation/audit_errata.py` rewritten (31/31 quotes found on the published pages and once in the manuscript TeX). New errata from the read-through: P27 (Fig. 3 comments), P28 ("exponential growth of multiplication"), P29 (static-analysis overclaims); T01 completed (17 sub-items), B01 (5 sub-items; [21] vol. 137 and [26] swapped names are publisher typesetting, the manuscript bib is right). Sources checked: see `validation/rounds/R1.json`; unverified: Denuvo [17], the Banescu quotation (C82).
- Author answers (one AskUserQuestion): P10 re-measure first (R16 step 4), minimal correction; P13: **the author implements the protected variant** (new round R19b, blocked on the author); wording minimal; T01, B01, P17b, P25, P26, P27 all appear; **new requirement:** every C/C++ project gets CMake, `build/` tree, CI Windows/Linux/macOS, VS 2022 and 2026 compatibility (new round R21a).
- Next: R2 (done, see below).
- Open obligations: P11 provenance (R16); `make_errata.py` is still the SelfModTamper copy (adapt in R22); the TeX `before_tex` of the P18/P19 figure edits reference dot source, not prose.
- Evidence: `validation/rounds/R1.json`.

### R2 (Claude Sonnet 5.5, 2026-10-17)

- Done: `Spec.Graph` (Digraph, IsCFG, vertex kinds), `Spec.DFS` (declarative `Jungle.Valid`, edge classes by timestamps), `Graph.Classify` (C27: tree/forward/back/cross iff-lemmas), `Graph.RunDFS` (computable fuel-bounded DFS in list order), `Graph.DfsValid.dfsRun_valid` (the algorithm's timestamps satisfy `Jungle.Valid` on any CFG, so the declarative notion covers real DFS runs), `Graph.Fig4` (published Fig. 4(a)(b): `fig4_dfs_eq` reproduces the published timestamps, jungle valid, classes; `fig4_kinds` = P03 evidence). Full build and axiom audit clean (0 violations, no sorry).
- Next: R3 (Havlak loop nesting forest, Fig. 4(c), non-uniqueness).
- Open obligations: Fig. 4 LNF part (R3); C65 C++ encodings (R18); P03 lean_ref is `SmcIrred.fig4_kinds` (checked via `audit_errata.py --refs` in R22).
- Hazards: Lean core only (no Mathlib tactics: use omega/decide/simp, by_cases); definitions used by decide need `@[expose]`.
- Evidence: validation/rounds/R2.json.

### R3 (Claude Sonnet 5.5, 2026-10-17)

- Done: `Spec.LNF` (PathIn, BackEdge, IsHeader, Body, Irreducible, LnfParent, IsMEE; all relative to a jungle, declarative); `LNF.Path` (decision procedure for paths inside a set, proved correct, gives `Decidable`); `LNF.Decide` (instances); `LNF.Facts` (root loop never irreducible; loop bodies nested or disjoint for every valid jungle; every MEE is forward or cross); `LNF.Small` (C71: no irreducible loop with <= 2 vertices for any jungle; the 3-vertex graph has one in every valid jungle); `LNF.Fig4` (Fig. 4(c): headers u,w,x; bodies; all irreducible; forest u>w>x>v; only MEE entry->v); `LNF.NonUnique` (C28: second DFS of Fig. 4 is valid and has different headers; also irreducible-set differs); `LNF.Algo` (Havlak's algorithm with union-find, executable; equals the declarative LNF on the two Fig. 4 DFS orders by `decide`). Full build + audit clean (479 declarations, 0 violations, no sorry).
- Next: R4 (extremal results K_n, M_n; may take two sessions). Use `Digraph.IsMEE`, `Irreducible`, `Body` from `Spec.LNF`; the decidable instances and `PathIn.trans/mono`, `Jungle.Valid.tree_path` help.
- Open obligations: (1) general proof that `havlak` equals the declarative LNF (plan risk fallback taken: M evidence only on Fig. 4); (2) C28 second half: loop bodies DFS-independent for reducible CFGs (marked "should").
- Hazards: core has no `push_neg`, `set`, `interval_cases`; `decide` on `Body` needs `set_option synthInstance.maxSize 2048`; Body is defined only through `IsHeader` (non-headers have empty bodies).
- Evidence: validation/rounds/R3.json.

### R4 (Claude Sonnet 5.5, 2026-10-17)

- Done: `Spec.Extremal` (Kn, Mn, MnLite, chainJungle, edgeCount/irrCount/meeCount); `Extremal.Chain` (generic chain-graph theory: headers, bodies, irreducible, MEE, counts); `Kn`/`Mn`/`MnCount` (canonical numbering: |E(K_n)| = n²−n, n−2 irreducible, C(n−1,2) MEE, |E(M_n)| = (n−1)(n+2)/2, |MEE(M_n)| = |MEE(K_n)|, disjoint edge classes, P14 formal, P15 witness with 2n−3 other edges); `KnAny` (same counts for any root and any DFS of K_n, Hamiltonian-path property); `IrrBound` (every CFG, n >= 2: <= n−2 irreducible loops); `MEEBound` (every CFG, every DFS: <= C(n−1,2) MEE; `K_n` attains it); `Evidence` (brute-force cross-check n <= 4, class M). Build + audit clean (819 declarations, 0 violations, no sorry).
- Next: R5 (2-SAT, APT, Figure 1). Round R4c (G19) is scheduled after R5; R3b (G01/G02) before R23.
- Open obligations: G19, G20 (see `lean/GAPS.md`).
- Hazards: `Evidence.lean` is a non-`module` file (module files cannot `#eval` imported code) and is not imported by `SmcIrred.lean`; classical `decide` inside Spec counts clashes with the `Decidable` instances: use `filter_congr` + `decide_eq_decide`.
- Evidence: validation/rounds/R4.json.

## R5 handoff (2-SAT)
- Done: `Spec/TwoSat` (literals, formula, Sat, implication graph with unit encoding ¬p→p, NoUnit/SelfLoop variants); `TwoSat/{Implication,Reach,APT,Unit,Fig1}`.
- `twoSat_iff_scc`: satisfiable iff no variable shares an SCC with its negation (unconditional, labelling `sccLabel`); `apt_correct` for any reverse-topological labelling; `unitClash` counterexample for both unit variants (P02); Fig. 1: 24 edges, drawn labels valid, green assignment satisfies, exactly 3 of 256 assignments.
- Open: G21 (DNF parity bound, C18) -> R6. Next: R6 (linear-time 2-SAT algorithm / Tarjan SCC), then R3b, R4c.

## R6 handoff (2026-10-18)
- Done: `Spec.Tarjan` (algorithm definitions live here, not in `Tarjan/Algo`), `Tarjan.{Inv,Finish,Mono,Correct}` (`tarjan_spec`: SCC partition, reverse topological order), `Spec.TwoSatSolve` + `Tarjan.Solver` (`twoSatSolveOf_spec`, `twoSatSolve_spec`), `Tarjan.Cost` (`tarjan_cost`: ticks <= 2n + m).
- Open: G21, G22 -> R6b (before R23). Next: R6b, then R3b, R4c, R7.

## R6b handoff (2026-10-18)
- Done: `Spec.TarjanCode` (literal C++ model: separate `onstack` flags and stack, re-entering outer loop; `tsComp`/`tsFold` model of `twosat`; `DupOf`), `Tarjan.CodeSim` (simulation by the clean model), `Tarjan.CodeModel` (`ctarjan_spec`), `Tarjan.TwoSatCode` (`tsFold_dup`), `Spec.Dnf` + `TwoSat.DNF` (`dnf_parity_terms`, G21 closed).
- Model note: the Lean model counts indices from 1 (`0` = key absent); the parent's lowlink update is done at the end of the child call, which is the same state change as the C++ lambda after the call.
- Also done in R6b (G24): `Tarjan.TwoSatLink` (`tsFold_link`) and `Tarjan.TwoSatLegacy` (`twosat_legacy_correct`: the legacy `twosat` over the legacy SCC vector is correct and its `sol` is the APT assignment).
- Open: G23 -> R6c. Next: R6c (small), R3b, R4c, R7.

## R7 handoff (2026-10-18)
- Done: `Spec.SmcMachine` (abstract self-modifying machine, D3 Level 2: per-node cell `ent/low/pk/dep/chk/set`, stack of return cells, topological chain, `restamp`, `smcSolve`), `Smc.Rel` (`SRel` simulation relation, entry), `Smc.Finish` (component extraction), `Smc.Sim`/`Smc.Visit` (`ssim_scan`, `ssim_visit`, `ssim_top`, `sRun_sim`: the machine simulates Tarjan on the graph with every successor list reversed), `Smc.Final` (`smc_link`), `Smc.Solve` (`smcSolve_spec`: `none` iff unsatisfiable; the returned literal nodes satisfy the formula; needs `Wf`, non-empty clauses), `Smc.Restamp` (`sRun_stk_nil`, `smcRound_restamp`, `smcRounds_replicate`).
- Modelling choices are in the `Spec.SmcMachine` docstring. A scratch `#eval` comparison of `smcSolve` with `twoSatSolve` on 3000 random formulas found one machine bug (fuel consumed by visited stubs) before the proof; it is evidence only and not committed.
- Open: G25, G26, G27 -> R8 (offsets, listing match, step bound). Next: R6c (small), R3b, R4c, R8.
- Hazard: names in `Smc/*` use the `ssim_` prefix because `Tarjan.CodeSim` owns `sim_*`.
- Evidence file: `validation/rounds/R7.json`.

## R6c handoff (2026-10-18)
- Done: `TInv` has a new field `done_low` (`DoneLow`: emitted components end with their root, root has lowlink = index, other members lowlink < index; preserved by `enter`, `lowStep`, `pop`, `keep`). `DupOf.dup` now requires `C.getLast? = some r`; `ctarjan_spec` therefore says the re-emitted singleton `[r]` follows a component with root `r`. G23 closed.
- Open: G25, G26, G27 -> R8; G01/G02 -> R3b; G19 -> R4c. Next: R3b, R4c, R8.

## R3b handoff (2026-10-18)
- Done: `LNF.Algo` (scanOne refactor of the worklist scan), `LNF.HvOrder`..`LNF.HvMain`: `havlak_hdr` (computed header of `x` is `some h` iff `LnfParent h x`), `havlak_hdr_none`, `havlak_irr` for every `J.Valid g r`; invariant `HInv` (union-find chain, representatives = outermost processed header containing the vertex, headers, irreducibility flags, recorded entry lists) preserved by `havlakStep` (`hstep`) and the fold over `byPreDesc` (`havlak_fold`, `havlak_inv`). `LNF.Reducible`: `Spec.LNF` gains `Digraph.Dom`, `NonDomPath`, `Reducible`; `body_dom` (bodies by dominance alone), `body_dfs_independent`, `header_dfs_independent`, `lnfParent_dfs_independent`. G01/G02 closed.
- `havlak_fig4*` stay as the earlier mechanical evidence; the general theorems supersede them.
- Open: G25, G26, G27 -> R8; G19 -> R4c. Next: R4c, R8.

## R4c handoff (2026-10-18)
- Done: `Extremal.MinOther`: `maxMEE_others` (every CFG with `n ≥ 2` whose multiple-entry count is `C(n−1,2)` has `edgeCount ≥ meeCount + (2n−3)`, for every valid jungle). Proof: tightness of `meeCount_bound` gives per-vertex equality (`per_vertex_strict`, `maxPairs_of_max`: each earlier non-parent vertex is MEE-adjacent), hence no vertex between a vertex and its parent in preorder (`between`), every non-last vertex has a child (`child_exists`), a vertex with parent and child heads a loop (`header_of_chain`), and an in-degree count (`indeg_bound`). With `MnLite_others` the bound 2n−3 is attained. G19 closed.
- Open: G25, G26, G27 -> R8. Next: R8.

## R8 handoff (2026-10-18)
- Done (M evidence, never proof): `validation/TwoSatVectors.lean` (4 test formulas + 2000 random formulas, fixed seed; verdict from `twoSatSolve`, cross-checked by brute force, counts) -> `validation/data/twosat_vectors.txt`; `validation/native/twosat_harness.cpp` + `validation/native_twosat.py` (MSVC x64/x86, with and without `USE_VM`: 0 failures; alltwosat counts compared on formulas 1–400); `.github/workflows/native-twosat.yml` (g++ Linux x64, with and without `USE_VM`: green); `validation/native_listing.py` (ml64 `/DWINDOWS /Fl /Sa` listing of `native/selfmodmodel.asm` through the product's `parseasmlisting`: `blueprint`, `callblueprint`, `jumptopo` arrays and all offset constants equal those in `native/selfmodgraph.cpp`). Results: `validation/rounds/R8_native.json`, `R8_listing.json`.
- Code fix L10 (`#include <memory>`).
- Pitfall: the listing must be assembled with `/DWINDOWS` (the asm has `IFDEF WINDOWS` branches); without it the Linux branch is listed and arrays differ. x86 listing (ml) not run.
- Open: G25 -> R23 (cell-to-offset correspondence), G27, G28 -> R8b. Next: R8b or R9.

## R9 handoff (2026-10-18)
- Done: `Spec.Generator` (`ImpPath`, `impFormula`, `Respecting`, `Planted`: forest of implications respecting the desired assignment `σ`, forcing path `¬ℓ ⇒* ℓ` for each required variable; further implications arbitrary but `σ`-respecting), `Gen.Planted`: `planted_sat` (σ solves the generated formula), `forcing_agree` (every solution agrees with σ on required variables), `planted_solve`/`planted_smc` (the reference solver and the Level 2 machine return a solution, hence agree with σ there), P04: `counter_violates`, `counter_unsat` (acyclic true→false implication destroys σ; with required ends the formula is unsatisfiable), `loop_keeps` (loops among σ-true literals are harmless), `no_loop_through_negation`. The probabilistic choices of the generator are universally quantified (every choice satisfying the conditions).
- P04 `after` text in `errata/edits.json` is backed (lean_refs set).
- Open: G25 -> R23; G27, G28 -> R8b. Next: R10 (or R8b).

## R10 handoff (2026-10-18)
- Done: `Spec.Circuit` (Kind/Circ/Sub/Lib, `valAt`, `callOf`, `writtenBy`, `costAt`, nesting-depth `level`, `Circ.val`, `Circ.cost`); `Circuit.CodeModel` (`stepCode`/`runPass`/`PassWF`, a literal elif-chain pass in any admissible vertex order); `Circuit.Order`: `order_independent` (every admissible order gives the same values), `runPass_eq_circ_val` (the code pass equals the specification value); `Circuit.Counts`: `callRuns_ungated` (an ungated call runs `reps + 1` times and its final accepting set is the `reps`-fold feedback iteration), `callCost_ungated`, `costAt_flat` (call-free circuits cost `(n, Σ edges)` for every input), `costAt_uniform` (cost independent of the input when every call is activated and ungated and subgraph costs are input independent), and the necessity witness `CostWitness` (a gated subgraph makes the cost data dependent: `gate_data_dependent`; the same circuit ungated costs the same for both inputs; the activation hypothesis is satisfiable).
- Modelling notes: start token = vertex `c.n`; `edgesOf` counts predecessor edges only (the Python `edgecount` also counts the token edge of each active input, a data-dependent term); the FLOW "pass" branch is needed for call outputs; calls enter the code model through the black-box evaluator `V`.
- Open: G25 -> R23; G27, G28 -> R8b; G29 (below). Next: R11 (or R8b).

## R11 handoff (2026-10-18)
- Done: `Spec.Gates`, `Spec.Virt` (literal BITSZ=1 transcription of `python/virt.py`: wires, graph builder, dedup/toggle set models, decoders, adder); `Prims.*`: gate chains/trees/XNOR/NAND/NOR (C42), functional completeness (C43), SEL/BSEL and the OR-for-XOR counterexample (C44), table single bits (C45), evaluation semantics `wev` with `Post` invariants, `decoder_post` (value = one-hot of the input), exact node/edge counts `decoderShift_cost`, `decoder_cost_ge2/one/zero` (C47), one-bit adder gadget `addBit_post` (all three branches of the literal code), `Ripple`: `ripple_add`, `ripple_sub`, `cout_combined`, `published_add_fails` (P05).
- Findings: Fig. 3 comment counts are approximations; real counts in PAPER_MAP C47. P05 errata `lean_refs` set.
- Not done (G30 -> R13): graph-level `addLoop`, DSL + compiler theorem, `evalNodes` = `Circ.val` bridge, decoder count script. Possible code observation: `not_to_virtual` on a constant indexes `g[True]` (unchecked, not exercised).
- Open: G25, G29 -> R23; G27, G28 -> R8b; G30 -> R13. Next: R12 (or R8b).

## R12 handoff (2026-10-18)
- Done: `Spec.AES` (xtime, GF(2^8) multiply, inverse by square-and-multiply, affine and inverse affine, S-box/inverse S-box as functions, the three tables of `aes.py` generated from the file, SubBytes/ShiftRows/MixColumns/AddRoundKey and inverses, key expansion over an abstract byte algebra for 128/192/256, encryption, decryption); `AES.*`: table = specification for all 256 bytes (`sbox_table`, `invSbox_table`), `ginv_mul`, affine invertible and GF(2)-affine, S-box not GF(2)-affine (witness 1, 2), round trip, `xtime` as selection and multiplication by 2, `keyExp_symbolic` (P07/C50), FIPS-197 Appendix C vectors (encryption and decryption, three key sizes) and Appendix A key-expansion tails.
- Tooling note: the kernel memory budget (Lean -M768) forces small modules and chunked Bool checks (`AES.Check`: `forall_lt_4`, `forall_lt2_4`); heavy `decide +kernel` goes one chunk per theorem, small files. Case-insensitive file system: `Tables.lean` and `TableS.lean` collide.
- Dropped extra: uniqueness of the inverse (`gmul x y = 1 -> y = ginv x`, 65536 products) exceeded the memory budget; not a paper claim (`ginv_mul` gives the inverse property). MixColumns vs the FIPS matrix form is covered by the vectors only.
- Open: G25, G29 -> R23; G27, G28 -> R8b; G30 -> R13. Next: R13 (needs R11's compiler, G30) or R8b.

## R14 handoff (2026-10-18)
- Done: `Spec.Arith` (literal models of `montgomeryBound` (non-subtraction), `montgomeryREDC`, `montgomeryREDC_eff`, `montgomeryREDC_mul_eff`, the square-and-multiply loop `sqmulF` (parametric in multiplication and squaring so values and counts come from the same loop), `modexpMontgomery`, the power table and main loop of `modexpMontgomeryWindow`, the window-size minimization, a Karatsuba step with split points, `get_consec_ones`/`consec_ones_to_num`, the ladder); `Arith.*`: REDC exact precondition (`T < R N`, result `< N`, `result R = T (mod N)`, necessity witness), bit-serial variants, Montgomery form (`toM`, `mmul_toM`, `redc_toM`), modular exponentiation and window exponentiation correct for every `w >= 1` and `e < 2^B`, counts (`sqmul_counts`, `winMuls_total`, `bestW_values`: 3, 3, 4, 4, 5, 6, 6, 7 for B = 32 ... 4096), Karatsuba identity and squaring variant, Toom counts and P08 witness, schoolbook squaring partial products, word counts (P09), runs of ones round trip and product by runs, the ladder. P08 and P09 errata `lean_refs` set.
- Findings: `modexpMontgomeryWindow` ends with a stray `print(tbl)` (debug output) and `mul_window`/`mul_const_window` are unfinished and unused (CODE_FIXES L11); the code's "transition points" comment was not recomputed.
- Not done (G31 -> R14b): RBSD, NAF, Wallace counts, `issub` bound, thresholds of the code's Karatsuba.
- Tooling note: memory budget again limits `decide +kernel` (`bestW_min_*` per size).
- Open: G25, G29 -> R23; G27, G28 -> R8b; G30 -> R13; G31 -> R14b. Next: R15 (needs the compiler, G30), R16, or R8b/R14b.

## R17 handoff (2026-10-18)
- Done: `Spec.Lang` (conditions `falseC`, `ttf` (read-and-toggle `trueThenFalse`), `c`, negation, short-circuit `&&`; flat code with block, jump, conditional jump, halt; structured statements with labels and `goto`; two-pass compilation; basic blocks and the CFG `cfgOf`; fuel-bounded trace semantics `exec`), `Spec.LangFigs` (the six listings of Figures 5 and 6, the five drawn graphs, `WalkTr`), `Lang.Common` (bounded reachability test, `isCFG_of_reachB`), `Lang.Fig5`, `Lang.Fig6`, `Lang.MinEdges`, `Lang.Induce` (`anc_reach`, `body_mono`, `induce_on_loop`), `Lang.NWay`.
- Findings: the CFGs of the compiled (b) and (c) listings have irreducible loops and the same traces as (a) (`ttf` starts true and is restored: two reads toggle twice). P18 confirmed: in the drawn 5(c) no walk executes A then B (`drawn5c_no_AB`); the corrected graph with the condition node H has one (`fig5c_cfg_AB`). P19 confirmed: the drawn 6(c) has the extra edge A -> B that the code CFG lacks (`fig6c_drawn_extra`, `fig6c_no_AB_edge`). Figures 5(b) and 6(b) as drawn equal the code CFGs minus exit.
- Not done (G32 -> R17b): general n for C73/C76, arbitrary programs for C14.
- Tooling note: `decide` on `cfgOf (compile _)` and on `Irreducible (dfsRun _)` works at these sizes (peak 0.65 GB for the path sweep).
- Open: G25, G29 -> R23; G27, G28 -> R8b; G30 -> R13; G31 -> R14b; G32 -> R17b. Next: R18 (Fig. 4 code, structuring), R19.

## R18 handoff (2026-10-18)
- Done: `Spec.IrredLoop` (call events, Figure 4 CFG semantics `G` with condition oracles, a flat machine with statement-level instructions, the three functions of `native/IrredLoop.cpp` as `codeGoto`, `codeLoops`, `codeNoGoto` with the intentional fall-through as `swFall`); `Struct.Machine` (`Star`, determinism `halts_unique`, `star_sound`); `Struct.IrredGoto/IrredLoops/IrredNoGoto` (halting trace of each function iff `Cfg`; per-address meaning functions and invariants); `Struct.IrredLoopCpp` (`three_versions_agree`, `G_moves_are_fig4_edges`); `Spec.Flatten`, `Struct.Flatten` (`flatten_iff`, `state_range`, `fig4_wf`).
- Findings: the invariants needed (e.g. `is_end` false except just after a `switch` with `EXIT`, `v_first` false after the first `v()`) are exactly those a reader uses; `break` leaving the middle loop skips its `while (!is_end)` test, which is why `EXIT` needs the fall-through into `LOOP`.
- Not done (G33 -> R18b): items 3-4 (structured programs reducible; CFT leftist trees), native run, front end.
- Tooling note: `simp [step, code..]` on literal instruction lists plus `cases` on flags decides each address; `refine .cons (c' := ...)` with explicit configurations avoids metavariable trouble.
- Open: G25, G29 -> R23; G27, G28 -> R8b; G30 -> R13; G31 -> R14b; G32 -> R17b; G33 -> R18b. Next: R19 (dynamic scheme, faults, static scheme).

## R19 handoff (2026-10-18)
- Done: `Spec.Dynamic` (abstract circuit DAG with gate functions, actions = execution or arbitrary write, `runA`, `IsVal`, `FinalOrdered`, `valOf`, `lastIdx`); `Dynamic.FinalExec` (C77: `final_isVal` needs no induction, `isVal_unique`, `execs_ordered`, `final_exec_eq_val`, `final_exec_input_tied`, `schedule_length_le`); `Dynamic.Fault` (T5: `fault_nonfinal`, `fault_final_overwrites`, `fault_final_changes`, witness circuit `wcirc` with `wcirc_bad_not_ordered`, `final_index_depends`, `fault_input_dependent`); `Spec.Lang` extended with `Cond.out k` and the generator-output argument `sol` of `Cond.eval`/`exec` (`Lang.Congr`: a run reads only the outputs its conditions mention); `Spec.LangFigs` has the solver-output variants `fig5bS`, `fig5cS`, `fig6bS`, `fig6cS`; `Dynamic.StaticScheme` (`static_behaviour`, `static_irreducible`, `static_scheme`: planted formula -> `planted_smc` -> outputs false -> transformed programs execute the original blocks, irreducible loops).
- Findings: the final-execution order theorem only needs, per vertex, that its last write is an execution and that no predecessor is written afterwards (the last executions of the predecessors are then automatically earlier); a fault in a non-final execution is exactly an insertion of a faulty write before a later execution of the same vertex.
- Not done (G34 -> R19c): bridge to R10, schedule construction, multiple faults, DCA/DPA (R20b).
- Open: G25, G29 -> R23; G27, G28 -> R8b; G30 -> R13; G31 -> R14b; G32 -> R17b; G33 -> R18b; G34 -> R19c. Next: R20a (security model I), R20b.

## R20a handoff (2026-10-18)
- Done: `Spec/Threat` (Image, rtVal, Obfuscates, Design, Assumptions S1-S3, ImmCap, SmcSemCap, Determines); `Threat/Correct` (T1 `correct`, `rtVal_planted`); `Threat/Immutable` (T2 `imm_fails`, `imm_determines_iff`, `imm_unsound`, `static_reading_wrong`, `witness`); `Threat/Recover` (T3 `recover`, `smcsem_determines`); `Lang/Congr.traceS_of_reads_false`; `validation/threat_audit.py` adapted (passes); `lean/THREAT_MODEL.md` §1-§4.
- Not done (G35 -> R20b): remaining literature checks; the `Struct`, `Trace`, `Fault`, `Dca` classes; necessity witnesses for S1-S3; T4-T7; errata `after` texts P21-P24 (P25 optional).
- Next: R20b; one question to the user: replace §5.1 (P25) or correct only P21-P24.

## R20b handoff (2026-10-18)
- Done: `Spec/Threat` extended (`obs`, `finalObs`, `vcount`, `Equiv`, `SizeIndist`); `Threat/Structuring` (T4), `Threat/DCA` (T5 wrapper, T6), `Threat/NotIO` (T7), `Threat/Necessity` (witnesses for S1–S3), `Threat.solver_succeeds`, `Lang.traceS_congr`; errata: `lean_refs` for P17, P22–P25 and the P25 replacement text of Section 5.1 in `edits.json`; `THREAT_MODEL.md` §3b.
- Open question to the user (one, batched): replace Section 5.1 by the P25 text, or apply only P21–P24 (P25 stays in the list as optional until answered). Fidelity pass (D10) of the P21–P25 sentences is R23.
- Not done (G36 -> R23, G35 -> R20b/R23): `extra_wf` witness, literature checks, node-splitting bound (G33).
- Next: R21a (portable native build), R21, R22 (errata list review), R23, R24, R25.

## R22 handoff (2026-10-18)
- Done: `validation/make_errata.py` adapted (published-version header, 31 items, P25 text as the appendix); `lean/errata/ERRATA.md`, `smcirred-2022-errata.tex`, `output/pdf/smcirred-2022-errata.pdf` (4 pages incl. the P25 appendix); `audit_errata.py` (inventory, evidence check, `--refs` 57 declarations all resolve, `--pdf` at most 5 pages).
- Open for the author (`lean/errata/QUESTIONS.md`): P25 yes/no, P06/P28 wording, P10/P11/P13 (measurements and the protected variant), review of the PDF.
- Next: R21a/R21 (native build and code corrections need CI and native toolchains; not done), R23 coverage and fidelity audit, R24 Palomar package, R25 tag.

## R23 handoff (2026-10-18, partial)
- Done: `validation/coverage_audit.py` adapted to the 8-column map (declaration index with namespace tracking, FT class, closed rows must name declarations, open rows must be explained, every P/T/B item mentioned): 85 rows, 180 declarations, 0 problems, `--build` compiles `CoverageRefs.lean`; PAPER_MAP rows C06, C09, C13, C17, C26, C27, C35, C37, C39–C41, C51, C60, C61, C67, C68, C71, C72, C84, C85 normalised; GAPS: G04 and G35 -> R23/author, G09, G10, G15 closed; fidelity pass of `Spec/Threat`, `Threat/*`, `THREAT_MODEL.md` and the P25 text: the T3 sentence claimed work for the analyzer; it now states only the cost of the Tarjan run in the clean model.
- Not done (R23 closes after the pending rounds): the D1 wording row by row for rows still `open` (C13, C51, C60, C61, C72, C84 and the rows of R8b/R13/R14b/R15/R16/R17b/R18b/R19c); G03, G05, G25, G29, G35, G36 owned by R23; fidelity pass of the planned README section.

## R19c handoff (2026-10-19)
- Done: `Spec/DynBridge` (`Circ.Flat`, `Circ.TopoR`, `lookupAcc`, `Circ.toD`); `Dynamic/Bridge`: `valAt_eq_valOf`, `dynamic_eq_evaluator` (every final-ordered schedule over `toD c inp` leaves the evaluator's `Circ.val` at every nesting depth), `range_schedule_eq_evaluator` (the hypotheses are satisfiable).
- Not done (G34 narrowed): circuits with calls (subgraph runs), schedule construction from the solver's conditions, multiple faults, DCA/DPA beyond T6, the SMC realization of the toggle.

## R21 handoff (2026-10-19, partial)
- Done: L01 (verified natively on this machine: the new `tarjan_scc` partition check fails without the fix and passes with it; MSVC x64 and x86 6012 runs, `--vm` x64 8016 runs, 0 failures), L02, L03, L04, L05 (`SMCIRRED_SEED`), L06 (comment), L11, D03; `validation/python_fixes_test.py`; `R8_native.json` regenerated after the fixes.
- Not done: Linux x64 vectors and R16 regeneration after the fixes (CI / R16); L07, L08, L09 (R21a and the author's decision, `QUESTIONS.md`); D01, D02 (after registration); the `aes`/`rsa`/`ecdsa` native builds are CI-only (L07).

## R21a handoff (2026-10-19, partial)
- Done: root `CMakeLists.txt` (targets `selfmodgraph`, `twosat_harness`, optional drivers with per-generated-source object libraries and GMP discovery, `ctest` of the native 2-SAT vectors; outputs under `build/`), checked locally with the Visual Studio 2022 and 2026 generators (build and `ctest` pass); `native/*.vcxproj` use `$(DefaultPlatformToolset)` and write to `build\msbuild` (checked: MSBuild with v143 and the default toolset); `.github/workflows/cmake.yml` (Windows 2022/2025, Ubuntu, macOS Intel and arm64, no stray files check); CONTRIBUTING/README commands.
- Not done (G37 -> R24): running the workflow (it needs a push and a look at the result), the driver builds on other platforms, L07-L09.

## R16 handoff (2026-10-19, partial)
- Done: regenerated the AES and RSA graphs after the code fixes (`SMCIRRED_SEED=1`, scratchpad copy so tracked `generated/` is untouched, `limited_run.py`, peak < 250 MB). Static nodes/edges for AES-128/192/256 and RSA-32/64/128/256 and the executed node counts equal Tables 1-2 (`validation/data/table_regen.json`); AES executed-edge counts vary with the random dependency order (541018-541694 for AES-256). Evidence class M, not proof.
- Not done (R16b: G06, G07, G38): Lean `Spec/Data` and ratio checks (C60, C61), the GMP re-measure for P10, P11 provenance, RSA-512/1024.

## R8b handoff (2026-10-19, partial)
- Done: `Smc/Cost`: instrumented mirrors `cExtract`, `cLeave`, `cLoop`, `cBody`, `cCall`, `cntRun` of the Level 2 machine with a count of primitive operations (calls, entries, exits, loop iterations, popped cells, outer-loop iterations); `cntRun_state` and friends prove the state component is the machine itself; potential `mPot` (weight `2·outdeg + 4` per node without an `ent` entry) gives `cCall_bound`, `cntRun_bound`; `chain_le` (the chain is a duplicate-free node list, via `sRun_sim`); `smcSteps_le`: `smcSteps f ≤ 2·|E| + 7·|V|`. Primitive operations only, not processor cycles.
- Not done (G28 -> R8c): transcription of the `selfmodvmtwosat` instruction list and its refinement of Level 2.
- Build green, axiom audit 0 violations (5082 declarations).
