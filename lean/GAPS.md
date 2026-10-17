# Gap register

Every known gap in the formalization, with the round that closes it. **No gap is dropped:** a round may defer a
gap, never delete it. Each round close (a) appends the gaps it found, (b) moves the gaps it closed to *closed*
with the declaration or commit, (c) copies none of them to the handoff without a row here. R23 requires: no
`open` row without an owner round and a stated fallback claim; R24 requires every row closed or listed in the
Palomar notes with its fallback.

Status: `open` (owner round named), `blocked` (needs the user/author), `closed` (evidence named).

| ID | Gap | Origin | Owner round | Fallback claim if never closed | Status |
|---|---|---|---|---|---|
| G01 | `LNF.Algo.havlak` = declarative LNF in general (only `decide` evidence on two DFS orders of Fig. 4) | R3 | R3b (before R23) | Havlak's algorithm is stated as M evidence; all theorems use the declarative LNF | open |
| G02 | Loop bodies are DFS-independent for reducible CFGs (C28, second half; "should") | R3 | R3b | The paper's uniqueness remark is cited (Havlak) and not Lean-verified | open |
| G03 | C05: Denuvo reference [17] (Karthik et al., ICCCNT 2020) unverified | R1 | R23 (re-search) / author | Listed as an unverified citation in the corrected text | open |
| G04 | C82: Banescu et al. quotation (opaque predicates defeated only in contrived scenarios) unverified | R1 | R20b / author | Claim marked as an unverified citation | open |
| G05 | C29/C69: Wei–Mao–Zou–Chen SAS 2007 (near-linear Havlak) and Cifuentes 1993 (DCC) not opened | R1 | R23 | Marked cited-unverified | open |
| G06 | P11 provenance of the quoted claim | R1 | R16 | Errata item stays `ask-author` | open |
| G07 | P10 re-measure with GMP (R16 step 4); minimal correction, regenerate if needed | R1 | R16 | Errata item stays `ask-author` | open |
| G08 | `native/aes` and `native/ecdsa` exceed the 1.5 GB local cap: build only in CI; Win32 and g++ baselines CI-only | R0 | R21a/R21 (CI) | Native evidence for them comes from CI logs only | open |
| G09 | `validation/make_errata.py` is still the SelfModTamper copy | R1 | R22 | None: R22 cannot close without it | open |
| G10 | `before_tex` of P18/P19 reference dot source, not prose | R1 | R22 | Errata quote the PDF text only | open |
| G11 | P13 protected AES/RSA variant (author implements it) | R1 | R19b | P13 stays an unfulfilled claim in the errata | blocked |
| G12 | Portable CMake build, `build/` tree, VS 2022/2026, CI Windows/Linux/macOS for every C/C++ project | R1 | R21a | None (user requirement) | open |
| G13 | `palomar-full.yml` dispatch needs the user's go-ahead; submission/registration by the user | R0 | R24 | None | open |
| G14 | C65: C++ encodings of Fig. 4 (`native/IrredLoop.cpp`) ↔ Lean `fig4` fidelity | R2 | R18 | Fig. 4 graph checked from the TeX only | open |
| G15 | Lean `ErrataRefs.lean` check (`audit_errata.py --refs`) never run on the committed `lean_refs` (P03) | R2 | R22 | None | open |
| G16 | `|MEE| ≤ C(n−1,2)` for every CFG and DFS (R4 item 4, "should"); proof idea found: no unordered pair is MEE in both directions, tree-adjacent pairs are never MEE | R4 | R4 | Only the K_n/M_n equalities are claimed (paper claims maximality) | closed: `Extremal.MEEBound.meeCount_le` (every CFG, every DFS) |
| G17 | K_n counts (headers chain, n−2 irreducible, C(n−1,2) MEE) for an **arbitrary** DFS labelling/root, not only the canonical numbering v_1…v_n (proved: canonical `chainJungle`, irreducible ≤ n−2 for every DFS) | R4 | R4 | Statements are for the paper's own convention (vertices named by DFS order) | closed: `Extremal.KnAny` (`Kn_comparable`, `Kn_headerCount_any`, `Kn_irrCount_any`, `Kn_meeCount_any`, any root/any DFS) |
| G18 | R4 item 6: `validation/planning/section5_bruteforce.py` cross-check against the Lean definitions via generated `#eval` file | R4 | R4 | Planning script stays unchecked evidence | closed for n ≤ 4: `Extremal/Evidence.lean` (`#eval` assertion, class M) |
| G19 | P15 second half: every CFG with C(n−1,2) MEE has ≥ 2n−3 non-MEE edges ("should"); proof plan: equality ⇒ per-vertex equality in `meeCount_bound` ⇒ every non-tree-adjacent pair is MEE-adjacent ⇒ ≤1 child per vertex ⇒ path ⇒ non-root non-leaf vertices are headers ⇒ tree edge + back edge into each | R4 | R4c (after R5, before R23) | Only the witness (`MnLite_others`) is claimed | open |
| G20 | Evidence enumeration for n = 5 (and sampled n = 6, 7) is too slow for the interpreter under the guard (>30 min); run it compiled in CI | R4 | R24 (CI) | The planning script's n = 5..7 results stay unchecked evidence | open |
| G21 | C18: DNF of the parity (XOR) function needs ≥ 2^(n−1) terms ("should"); proof idea: a term of a consistent DNF for parity must fix every variable, so covers one assignment; 2^(n−1) odd assignments | R5 | R6b | Not claimed | open |
| G22 | L01: literal model of the C++ `tarjan_scc` outer loop (re-enters visited vertices, appends duplicate singleton roots); proof that `twosat`'s assignment equals `twoSatSolve`'s (duplicates idempotent) | R6 | R6b | The Lean solver `twoSatSolve` is claimed correct; the C++ code's equivalence is only documented in CODE_FIXES L01 | open |
