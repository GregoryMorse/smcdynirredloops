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
