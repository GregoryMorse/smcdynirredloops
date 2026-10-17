# Rounds

State machine for `lean/FORMALIZATION_PLAN.md`. Update at every round close (state, then a 5-line
handoff: done / next / open obligations / hazards / evidence file).

| Round | Deliverable | Priority | State |
| --- | --- | --- | --- |
| R0 | Bootstrap, references, baselines (authorization question) | must | DONE 2026-10-17 |
| R1 | Claim inventory, errata verification, sources, author questions | must | TODO |
| R2 | Graph foundations, DFS jungle, Figure 4(a)(b) | must | TODO |
| R3 | Havlak loop nesting forest, Figure 4(c), small CFGs, non-uniqueness | must | TODO |
| R4 | Extremal results: K_n, M_n, n−2 bound (MEE bound should) | must | TODO |
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
