# Rounds

State machine for `lean/FORMALIZATION_PLAN.md`. Update at every round close (state, then a 5-line
handoff: done / next / open obligations / hazards / evidence file).

| Round | Deliverable | Priority | State |
| --- | --- | --- | --- |
| R0 | Bootstrap, references, baselines (authorization question) | must | DONE 2026-10-17 |
| R1 | Claim inventory, errata verification, sources, author questions | must | DONE 2026-10-17 |
| R2 | Graph foundations, DFS jungle, Figure 4(a)(b) | must | DONE 2026-10-17 |
| R3 | Havlak loop nesting forest, Figure 4(c), small CFGs, non-uniqueness | must | DONE 2026-10-17 (algorithm equivalence: open obligation) |
| R3b | Close G01/G02: Havlak algorithm = declarative LNF; reducible-CFG body uniqueness (scheduled after R5, before R6 if time; mandatory before R23) | must | TODO |
| R4 | Extremal results: K_n, M_n, n−2 bound (MEE bound should) | must | DONE 2026-10-17 (G19 open) |
| R4c | Close G19 (P15 second half: max-MEE CFGs have >= 2n-3 other edges), after R5 | should | TODO |
| R5 | 2-SAT: implication graph, APT theorem, unit clauses, Figure 1 | must | TODO |
| R6 | Tarjan's algorithm, cost, reference solver, `tarjan_scc` model | must | TODO |
| R7 | SMC 2-SAT solver Level 2 ⇒ Tarjan/APT; restamp lemma | must | TODO |
| R8 | SMC solver VM level (should); native vectors and listing evidence (must) | must/should | TODO |
| R9 | Planted 2-SAT generator (§3.1, P04) | must | TODO |
| R10 | Boolean-CFG VM: order independence, data-independent counts, subgraphs | must | TODO |
| R11 | Gate primitives, decoders, adders (P05), DSL compiler correctness | must | TODO |
| R12 | AES specification facts (S-box P07, xtime, key expansion, vectors) | must | TODO |
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
