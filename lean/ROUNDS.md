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
| R8b | G27 step bound for the Level 2 machine; G28 VM instruction-list refinement (R8 item 1) | should | TODO |
| R9 | Planted 2-SAT generator (§3.1, P04) | must | DONE 2026-10-18 |
| R10 | Boolean-CFG VM: order independence, data-independent counts, subgraphs | must | DONE |
| R11 | Gate primitives, decoders, adders (P05), DSL compiler correctness | must | DONE 2026-10-18 (DSL compiler, graph-level adder, Circ.val bridge -> G30/R13) |
| R12 | AES specification facts (S-box P07, xtime, key expansion, vectors) | must | DONE 2026-10-18 |
| R13 | AES compiler correctness | should | TODO |
| R14 | Arithmetic for RSA (Montgomery, windows, Karatsuba/Toom P08, word size P09) | must | TODO |
| R15 | RSA compiler correctness | should | TODO |
| R16 | Tables 1–2: regeneration (M) and data checks (FD) | must | TODO |
| R17 | Transformation language, Figures 5–6 (P18, P19), minimal edges | must | TODO |
| R18 | Figure 4 C++ code, flattening; structured ⇒ reducible, CFT (should) | must/should | TODO |
| R19 | Dynamic scheme, faults, static scheme end-to-end | must | TODO |
| R20a | Security model I: definitions, T1–T3 (crux) | must | TODO |
| R20b | Security model II: T4–T7, necessity, §5.1 texts | must | TODO |
| R19b | Protected AES/RSA variant: the author implements it, this round integrates (P13, D03) | must | BLOCKED on the author |
| R21a | Portable native build system: CMake, build/ tree, VS 2022/2026, CI Windows/Linux/macOS | must | TODO |
| R21 | Code fixes (not errata) and native acceptance | must | TODO |
| R22 | Errata list (paper only) | must | TODO |
| R23 | Coverage and fidelity audit | must | TODO |
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
