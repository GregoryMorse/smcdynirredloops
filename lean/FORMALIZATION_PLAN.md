# Control Flow Obfuscation with Irreducible Loops and Self-Modifying Code: formalization plan

Planner: Claude Opus 5.5, 2026-10-17. Executor: Claude Sonnet 5.5 (medium effort), one round per
session (a round may span sessions, but every session closes at least one numbered step with a green
build). Reviewer and decision owner: Gregory Morse (first author).

**How to use this file.** At the start of every session, read §0–§4 once and then **only the section
of the current round** (state and handoff notes: `lean/ROUNDS.md`). §1 facts are established; do not
re-derive them unless a gate fails. §2 decisions are settled; if one blocks you, stop and ask the user.
Do not browse `../SelfModTamper`, `../selfspectre`, `../smcTuring` or `../dyngraph` beyond the exact
paths named here.

---

## 0. Target

**Paper (version of record).** G. Morse, M. Alqaradaghi, T. Kozsik, *Control flow obfuscation with
irreducible loops and self-modifying code*, Publ. Math. Debrecen **100** (Supplementum) (2022) 617–637,
DOI 10.5486/PMD.2022.Suppl.5 (21 pages; CECC'21 proceedings). **No arXiv version exists** (search
2026-10-17). Errata are stated against this published version.

| Artifact | Location | Size | SHA-256 |
|---|---|---|---|
| Published PDF | `https://konferencia.unideb.hu/sites/default/files/upload_documents/10_5486_pmd.2022.suppl_.5.pdf` | 536,728 B, 21 pp. (pdfTeX, 2022-12-15) | `e89a803c6839c18bd3fe202e03c4dbdf090f418ae8e222d736de8f77337a21fc` |
| Author manuscript TeX (final, 2022-03-25) | `D:\OneDrive\Documents\Projects\ELTE\smcdynirredloops\SelfModifyingControlFlowObfuscationPaper.tex` | 53,049 B, 529 lines | `309bc5d1d0970a74a62e6f221697bb601a864fb3dc081af8bc879523fd635968` |
| `biblio.bib` (same folder) | | 24,900 B | `28968b3a2cbdc1b2c6b07cc90df0f6f5234fb7f4271c1dbcde87e6b7ba87837d` |
| `publmathdeb.cls` (same folder) | | 74,293 B | `2dbdc5da9e088dcb85bbfc3d95eb6142df8c8bde0d46093afadf53766e8a456f` |

`SelfModifyingControlFlowObfuscationPaperV2.zip` in the same folder holds byte-identical copies of the TeX
and bib. `SelfModifyingControlFlowObfuscationPaper.zip` (2021-09-30) is the earlier submitted version:
ignore it. `../smcobf/` is the CECC'21 extended abstract and `../obfuscation/` is a different paper
(Erlang): both out of scope.

**Reference material only (user, 2026-10-17).** The OneDrive manuscript is read, never written. All
work happens in this repository. The published PDF is the authority for every errata quote; the
manuscript TeX supplies the exact source fragments (`before_tex`) and figure graph sources. Neither file
is committed until the user allows it (R0 question; D9).

**Dissertation: out of scope.** The author's dissertation contains this paper. The author derives a
dissertation-wide errata list separately, with another agent. Do not read, quote or map the dissertation.
Consequence: every errata item here is **self-contained** (exact quote of the published text, corrected
text, one-sentence reason, evidence).

**What counts as an erratum.** Only statements in the paper's text, tables, figures, captions and
references. Code, README and CITATION fixes are **not** errata: the repository has no tagged release and
the paper links only the repository as a whole. They are tracked in `lean/CODE_FIXES.md` and must land
before the Palomar commit. The user wants the list **minimal but complete**: every real mistake is
recorded; trivia are grouped (one typographical item T01, one bibliography item B01).

**Sequence:** Lean development → code fixes → errata list → Palomar package (the user submits and
registers) → repository tag on the registered commit → corrected manuscript in `paper/` that states its
Lean verification, the Palomar entry and the tag. The venue for the corrected manuscript (first arXiv
posting, a Publ. Math. Debrecen corrigendum, or both) is the author's choice in R25.

**Artifacts in this repo.** `native/selfmodgraph.cpp` (reference Tarjan/2-SAT, the SMC 2-SAT solver
`selfmodtwosatasm` with blueprint byte arrays and stamp offsets, the listing parser `parseasmlisting`,
the high-level SMC pseudo-language `selfmodvmtwosathl`, the VM version `selfmodvmtwosat` under `USE_VM`,
driver `main` with test formulas 1–4), `native/selfmodmodel.asm` / `selfmodmodelgas.asm` (the blueprint),
`native/IrredLoop.cpp` (Figure 4 in three C++ styles), `python/virt.py` (Boolean-CFG generator, VM
interpreter `do_run_virtual`, arithmetic), `python/aes.py`, `python/rsa.py`, `python/graph.py`, the C
harnesses `native/aes*.c`, `native/rsa.c`.

**In scope: the whole paper.** Every sentence-level mathematical, algorithmic, quantitative or security
claim gets a class (D1) and is discharged in Lean, as a Lean-checked consistency fact about reported
data, as mechanical evidence that a Lean model matches the repository artifact, or by a primary-source
citation. Opinions and design intent are listed as such.

**The security model is a must (user, 2026-10-17: "we Lean verify all the mathematical results,
algorithms, security model").** §5.1 states security properties without an adversary model. The
formalization supplies one (D11, rounds R20a–R20b); the published overclaims become errata.

**Final deliverables (definition of done).**
1. `lean/` Lake project: zero `sorry` outside `Challenge.lean`; only `propext`, `Quot.sound`,
   `Classical.choice`; cold CI build and axiom audit green on GitHub.
2. `lean/PAPER_MAP.md` covering every claim C01–C83 (+ any found in R1) with class, declaration or
   source, status; `validation/coverage_audit.py` passing (R23). Only then may README/metadata use the D1
   wording.
3. Code and docs fixes (L, D items) as minimal diffs with native acceptance, listed in
   `lean/CODE_FIXES.md` with commit hashes (R21). Not errata.
4. Errata list (paper only, against the published version): `lean/errata/edits.json` (single source),
   generated `lean/errata/ERRATA.md` and `lean/errata/smcirred-2022-errata.tex` → PDF reviewed by the
   author (R22).
5. Palomar package (`Challenge.lean`, `Solution.lean`, `comparator.json`, `formalization.yaml`,
   `PALOMAR_SEMANTICS.md`, `PALOMAR_SUBMISSION.md`, `THREAT_MODEL.md`), full mechanical preflight passing
   on an exact public commit (R24). **The user submits and registers; never do it yourself.**
6. After registration (R25): an annotated tag on the registered commit, and the corrected manuscript
   `paper/SelfModifyingControlFlowObfuscationPaper.tex` = manuscript + every `confirmed` erratum + a short
   formal-verification statement (D1 wording) naming the Palomar entry, repository URL, tag and commit;
   `paper/manuscript-v2022.diff`; `output/pdf/smcirred-corrected-latexdiff.pdf`. The user uploads it.

---

## 1. Facts established during planning (do not re-verify unless a gate fails)

**Published text vs manuscript.** The published text equals the manuscript TeX up to the publisher's
copy-editing (sentence-case title and section headings, running head). Rendered pages 620, 629, 630,
631, 632, 633 were inspected: Table 2 is printed exactly as in the TeX (the 128- and 256-bit `C gmp`
cells are identical, see P10). The odd-page running head reads "…irreducible loopsand self-modifying
code" (publisher typesetting, T01). `pdftotext -layout` scrambles multirow tables and figure labels:
quote tables from the rendered page, never from the layout text.

**Page map (journal pages).** Abstract 617; §1 617–619; §2 619–622 (Fig. 1 p. 620); §3 622–623 (Fig. 2
p. 623); §3.1 623; §4 623–625; §4.1 625–626; §4.2 626–627; §4.3 627–629 (Fig. 3 p. 628; Tables 1–2
p. 629); §5 629–633 (Fig. 4 and Table 3 p. 630; Definitions 3–4 p. 631; Fig. 5 p. 632; Fig. 6 p. 633);
§5.1 634–635; §6 635; references 635–637.

**Figure 1 = `testformula3`** in `native/selfmodgraph.cpp` `main` (12 clauses over x1..x8; code comment
"3 solutions"). All 24 implications in Fig. 1(b) are the two contrapositives of the 12 clauses; the 24
edges of the graph in the TeX source match them one-to-one. The 10 SCCs and their labels: 1 {−8},
2 {2,5}, 3 {4}, 4 {−1,7,−3}, 5 {6}, 6 {1,−7,3}, 7 {−4}, 8 {−2,−5}, 9 {8}, 10 {−6}; every edge goes from a
higher to a lower label, so the labels are a reverse topological order (Tarjan's emission order). The
green literals are exactly the APT assignment "x true iff label(x) < label(¬x)": x1=F, x2=T, x3=F, x4=T,
x5=T, x6=T, x7=T, x8=F, which satisfies all 12 clauses.

**Figure 4 = `native/IrredLoop.cpp`.** CFG: entry→u, entry→v, u→w, v→x, w→{u,x,exit}, x→{v,w,exit}
(entry=1,u=2,v=3,w=4,x=5,exit=6). `irreducible_loops_only_goto`, `irreducible_loops` (hybrid) and
`irreducible_loops_no_goto` (one Boolean `v_first`, intentional `switch` fall-through EXIT→LOOP) encode it
with `w_cond`/`x_cond` ∈ {EXIT=0, LOOP=1, FORWARD=2}. Jungle (b): DFS 1→2→4→5→3, 5→6, timestamps
[pre,post] with the clock starting at 2 (consistent parenthesis structure); tree edges 1→2, 2→4, 4→5,
5→3, 5→6; non-tree 1→3 (forward), 4→6 (forward), 3→5, 4→2, 5→4 (back). Havlak LNF (c), checked by
hand with Havlak's algorithm: L(5)={5,3}, L(4)⊃L(5), L(2)⊃L(4), all three irreducible with the entry
1→3 recorded as "{3: {1}}"; 1 and 6 are top-level non-headers. Correct as published.

**Section 5 counting claims (planning brute force, `validation/planning/section5_bruteforce.py`,
evidence only).** Exhaustive over all (CFG, DFS) pairs for n ≤ 5, sampled for n = 6 (126,000) and
n = 7 (52,800), with Havlak's algorithm and MEE = "edge (x,y) with y in L*(w)\{w} and x not a DFS
descendant of w": max #irreducible loops = n−2; max #MEE = C(n−1,2); the root's loop is never
irreducible; K_n and M_n attain both bounds (n ≤ 9); |E(M_n)| = (n−1)(n+2)/2 (n ≤ 9). **But** among
CFGs with C(n−1,2) MEE the minimum number of non-MEE edges is 2n−3 (n = 3,4,5), while M_n has 2(n−1):
removing the back edge (v_n, v_1) keeps all MEE and both irreducible-loop counts (n ≤ 9). So "minimizing
all others" is off by one edge (P15). Definition 4's "removing extra back edges whose **successor** is
not the inner-most non-header node" must say **source/predecessor**: every kept back edge is (v_n, v_i)
and no back edge has successor v_n (P14).

**Node splitting is exponential, not quadratic (P17).** Carter, Ferrante, Thomborson, *Folklore
confirmed: reducible flow graphs are exponentially larger*, POPL 2003 (copy read 2026-10-17 from
`https://www.cs.tufts.edu/~nr/cs257/archive/larry-carter/exponential-node-splitting.pdf`): Theorem 4,
any reducible flow graph equivalent to the complete graph K_{Σ,e} (|Σ| = n) has at least 2^{n−1} nodes;
Theorem 5, the same for a bounded-degree (out-degree 2) variant; the paper explicitly suggests this for
obfuscation. The proof is short (Σ-complete leftist trees, S_n ≥ 2 S_{n−1}) and is a Lean target (R18).

**Code facts (read during planning; confirm in the named round).**
* `gettwosatgraph` encodes a unit clause (x, x) as the single edge ¬x → x (`if (x != y)` guard). This is
  correct and contradicts the paper's "need not effect the implication graph or could be a trivial
  self-loop" (P02). `alltwosat` relies on unit clauses to enumerate solutions.
* `twosat` reads SCCs in Tarjan emission order and inserts v unless ¬v is already in the solution set:
  the APT rule. `tarjan_scc`'s outer loop calls `strongconnect` on **every** key, including visited
  ones; a visited SCC root is re-emitted as a duplicate singleton and a visited non-root is left on the
  stack. Planning analysis: `twosat`'s result is unaffected (duplicates come after the original; one of
  v, ¬v is already decided). L01; R6 proves the model.
* `python/virt.py` `addition_bit_to_virtual` computes `S = A ^ B ^ carry_in` (correct; the paper prints
  `c_{i+1}`, P05) and `carry_out = (A&B) ^ (carry_in & (A^B))` with the add/sub selector exactly as the
  paper's combined formula.
* VM semantics (`do_run_virtual`): node ops FLOW (AND over predecessors), ANY (OR), ADD (XOR = odd
  count), ADDNEG (XNOR; NOT for one predecessor), SUBG (call of a reusable subgraph with an input tie-in
  node and a repetition count; the repetition loop can `break` on a data bit = gated repetition), TBL
  (constant table selection). Evaluation order = `topo_kahn(g, randomize=True)` (a random topological
  order on every run). Exec. N / Exec. E = per-run node count and predecessor-edge count summed over
  subgraph invocations (`show_stats`). Nodes/Edges = `reduce_all` totals (main graph + subgraph
  definitions after dead-node trimming) — R16 confirms which printed number is the table's.
* Fig. 3 code = `decoder_shift_to_virtual` and `decoder_to_virtual` in `virt.py` (identical text). With
  `BITSZ = 1` and constant folding, `decoder_shift_to_virtual` on m ≥ 1 bits creates 2^{m+1} + m − 4 nodes
  (the first AND layer folds against the constant 1); the comment says "2*2^n". `decoder_to_virtual`
  creates popcount(i) NOT nodes + 1 OR + 1 NOT per index i, i.e. (m/2 + 2)·2^m nodes for m ≥ 2
  (planning count; R11 proves the exact figure); the comment says "2^n". Both comments are
  approximations (X; no erratum unless the author asks).
* Keys: `rsa.py` hard-codes `rsa32_params` … `rsa1024_params` (fixed, once randomly generated: matches
  the paper). `aes.py` `gen_aes` uses `key = b'\x12' * (bits // 8)`, not a random key (P11 provenance).
  Modular exponentiation (`modexp_virtual`) = conversion into Montgomery form (multiplication by the
  constant R² mod N) → fixed windows (`modexp_window_to_virtual`; B = modulus bit size from `toMontgomery`;
  w minimizes ⌈B/w⌉ + 2^w − 2; 2^w − 2 table products; one product per window, the first by a constant;
  w squarings between windows, i.e. w·(⌈B/w⌉ − 1); zero windows still multiply by the Montgomery one) →
  conversion out (multiplication by 1). Each product is a Karatsuba subgraph (`mulKaratsuba_to_virtual`,
  squaring = the same recursion on equal operands) followed by a REDC subgraph
  (`montgomeryREDC_to_virtual`); a product by a constant with few runs of ones uses
  `mul_consec_ones_virtual` (add/sub per run). This matches §4.2 ¶3 ("Montgomery form, Montgomery and
  Karatsuba multiplication and squaring and window sizes to minimize products").
* `subg_virtual` and `multi_bit_selection_to_table_virtual` call an unseeded `random.shuffle`: graphs are
  relabelled randomly on each generation (counts should not change; L05 adds an optional seed).
* `native/aesmain.c`: `AES_192_obf_encrypt`/`AES_256_obf_encrypt` are empty stubs and the slot labelled
  "Irreducible Loop Graph Encryption" runs the VM (`AES_*_obf_virt_encrypt`); `AES_128_obf_il_encrypt` is
  commented out. `rsa.c` has the same labels. **The irreducible-loop + 2-SAT protection of AES/RSA is not
  implemented in the repository**, and no code generates 2-SAT formulas (§3.1) or applies the Figure 5/6
  transformations. The paper's measurements are of the plain Boolean CFG (Tables 1–2) and the Figure 4
  example (Table 3). See P13.
* Latent Python defects seen while reading (L03, L04; confirm before fixing): `set_bit_range` uses
  `num[a::b]` (a stride, not a stop); `do_run_virtual` reads `outp` when `outmap is None` (NameError).

**Data facts (Tables 1–2; arithmetic verified).**
* Table 2 `C gmp`: 128-bit and 256-bit cells identical (9.141 ms / 7.640 ms); 32-bit cells 851 ms /
  707 ms exceed the 64-bit cells 2.207 ms / 1.015 ms (non-monotone; consistent with µs for the 32-bit
  row). P10, ask-author.
* Executed nodes per doubling (Table 2): 6.612, 6.031, 6.136 (exponent ≈ 2.6) and CFG time 6.555,
  6.124, 5.955 (x86): "worse than quadratic" in time holds. Nodes per doubling 1.772, 2.198, 2.547:
  space grows sub-quadratically over 32–256 bits, so "impractical … in terms of … space after the 256-bit
  size" is not shown by the table (X, noted in the map; not an erratum).
* Time per executed node: RSA 4.90 s / (1000 · 686,447) = 7.14 ns … 1228.89 s / (1000 · 167,967,539)
  = 7.32 ns; AES-128 x86 0.58 s / (1000 · 134,455) = 4.31 ns. Internally consistent (FD).

**Primary sources already confirmed.** CFT 2003 (above). FIPS-197 §5.1.1: the S-box is the
multiplicative inverse in GF(2^8) followed by an affine transformation; non-linearity comes from the
inverse (P07). Toom-k costs (2k−1) multiplications of size n/k, i.e. O(n^{log_k(2k−1)}) (P08).

---

## 2. Decisions (made; ask the user before deviating)

**D1 — Coverage standard.** Every row of `PAPER_MAP.md` has exactly one class:

| Class | Meaning | Discharged by |
|---|---|---|
| **F** | mathematical / algorithmic statement | Lean theorem, no hypotheses beyond the statement's own |
| **FT** | security statement | Lean theorem whose hypotheses are the threat-model assumptions (D11) |
| **FD** | number or ratio reported from measurements | Lean `decide` check on the transcribed tables (`Spec/Data.lean`, not Challenge surface) |
| **M** | a Lean model matches a repository artifact | mechanical evidence: literal transcription + differential runs, regenerated counts, listing bytes |
| **R** | third-party fact (complexity class, algorithm cost, tool, standard) | primary-source citation in `PAPER_MAP.md` |
| **X** | opinion, design intent, empirical tool observation, future work | listed explicitly; nothing claimed |

Permitted public wording after R23: *"All mathematical, algorithmic and security statements of Morse,
Alqaradaghi and Kozsik, Publ. Math. Debrecen 100 (Suppl.) (2022) 617–637, are verified in Lean 4 —
security statements relative to an explicitly stated threat model — with corrections listed in the
errata; third-party facts are cited and empirical observations are listed as such."* Never shorten it to
"the paper is proved".

**D2 — Black boxes and contracts.** Nothing outside the algorithms is modelled as a white box:
1. *Processor execution of the x86 blueprint* is not modelled on the must path. The SMC algorithm is
   verified at the level of an abstract SMC machine (D3); fidelity to the bytes and to real runs is M.
2. *C++ callbacks* (`getsuccnodeaddr`, `addsolution`, `sat`, `unsat`) enter as contract fields: what
   each returns or does to the solution set.
3. *Decompilers* (IDA Free 7.6, Ghidra 9.2.4) are not modelled: Table 3 is X. Structuring algorithms
   enter only as abstract classes in the threat model (node splitting, state variables), never as
   claims about a specific tool.
4. *Timing* is never proved: tables are FD consistency checks.

**D3 — Levels for the SMC 2-SAT solver.** *Level 1* (`Spec/TwoSat.lean`): Tarjan SCC + APT assignment
(specification and reference algorithm). *Level 2* (`Spec/SmcMachine.lean`): an abstract SMC machine
following the paper's §3 description and the pseudo-language in `selfmodvmtwosathl`'s comments — one
code cell per implication-graph node whose first instruction is patched to `return` when the node
starts, a return-address stack replacing the call stack, per-node lowlink/index/counter immediates
patched in place, and the topological solution chain built by patching the previous node's check. Proved
to refine Level 1 (**must**). *Level 3* (`SmcIrred/Smc/VMList.lean`): the literal instruction list built
by `selfmodvmtwosat` (opcodes CALL…PUSH), proved to refine Level 2 (**should**). *Level 4*: the x86 bytes —
M evidence only (listing bytes = arrays, stamp offsets, native differential runs on Windows x86/x64 and
Linux x64) (**must** as evidence, **could** as proof).

**D4 — Lean setup.** Lean `leanprover/lean4:v4.35.0-rc3` (installed locally; accepted by Palomar in the
sibling projects). **No Mathlib**: graphs, SAT, Boolean circuits, GF(2^8) tables and `Nat` arithmetic fit
Lean core (`omega`, `decide`, `grind` for commutative-ring goals). If a *could* item needs Mathlib, ask
first. Package `smcdynirredloops`, library `SmcIrred`, Palomar namespace `PalomarSIL`,
`autoImplicit = false`, smcTuring-style headers (`module` / `public import` / `public section`) as in
`../SelfModTamper/lean/SmcTamper/Spec/Bits.lean`. Rice's theorem and complexity classes stay R-class.

**D5 — Reuse by copying.** Infrastructure from `../SelfModTamper` at commit `69a9d34`
(`git -C ../SelfModTamper show 69a9d34:<path>`), names adapted (`SmcTamper`→`SmcIrred`,
`PalomarSMT`→`PalomarSIL`, `selfmodtamper`→`smcdynirredloops`, branch `main`→`master`), behaviour kept,
recorded in `lean/VENDORED.md` (source path, first 16 hex of SHA-256, edits):
`validation/{limited_run,memory_budget,lean_build,build_modules,axiom_audit,make_challenge,audit_errata,make_errata,build_tex,coverage_audit,threat_audit}.py`,
`validation/ci/{axioms.py,linux.sh}`, `validation/palomar/{fetch_policy_assets,refresh_policy,validate_metadata}.py`,
`.github/workflows/{proof,palomar-full}.yml`; as templates only: `lean/errata/{POLICY.md,edits.json}`,
`lean/{formalization.yaml,comparator.json,PALOMAR_SEMANTICS.md,PALOMAR_SUBMISSION.md,LICENSE_AUDIT.md,PAPER_MAP.md,THREAT_MODEL.md}`.
Lean code: in R2 you may copy the core-only graph files `../dyngraph/enum_paper/formal/Graph.lean`
(`Reach`, `SameSCC`, `Dominates`) and the DFS/jungle files under `../dyngraph/lnf/formal/LNF/`
(`Reachability`, `Jungle`, `JungleFacts`, `DFS`) at dyngraph commit `c730e74a`, only if their import
closure is core-only and ≤ ~800 lines in total; otherwise write fresh. Same author; check the dyngraph
`LICENSE` and record it in `LICENSE_AUDIT.md`.

**D6 — Spec modules are the Challenge surface.** Every definition used in a selected statement lives in
`lean/SmcIrred/Spec/*.lean`: core imports only, `@[expose] def`, compact, no lemmas, docstrings that claim
nothing beyond the definition. `validation/make_challenge.py` generates `Challenge.lean`. `Spec/Data.lean`
is not selected.

**D7 — Tactic and axiom policy.** Forbidden: `sorry`/`admit` (outside Challenge), `axiom`,
`native_decide`, `bv_decide`, `Lean.ofReduceBool`, `implemented_by` in Spec, `unsafe`, `partial` in Spec.
`decide` up to a few thousand cases; split larger checks into `List.all` chunks of ≤ ~4,000 cases. Use
`Nat`/`Fin 256` representations for byte tables (kernel `Nat` arithmetic is fast); `BitVec` lemmas via
extensionality + `simp` + `omega`. `maxHeartbeats` above 400000 only with a one-line justification.
`#eval` is allowed only in `validation/` scripts that produce M evidence, never in proofs.

**D8 — Compute.** All builds/tests serially through `python validation/limited_run.py -- <cmd>` (1.5 GB
aggregate cap, Lean `-M768 -j1`). A capped failure is a failed check; never bypass the guard; do not
kill unrelated processes. No SSH/remote servers. Cold full builds and the Palomar preflight run on GitHub
Actions. Python: `py -I` locally, `PYTHONIOENCODING=utf-8`, `open(..., encoding='utf-8')`;
`pdftotext -enc UTF-8`. Graph regeneration scripts must stay under the cap (RSA-256 graphs are ~88k
nodes; never run the Python VM for RSA-256: compute executed counts statically).

**D9 — References, errata, tag, corrected manuscript.**
* The published PDF and the manuscript are **not committed** unless the user allows it (R0 question).
  Until then: `validation/fetch_reference.py` downloads the PDF from the URL in §0 into the gitignored
  `validation/reference/` and verifies its SHA-256; it copies the OneDrive manuscript files the same way
  (read-only, hash-checked). `pdftotext -layout -enc UTF-8` and `pdftotext -enc UTF-8` texts are derived
  locally. CI runs the inventory audit only when the download succeeds, else reports it UNVERIFIED (not
  failed).
* `edits.json` is the single source. Fields: `id`, `page` (journal page), `location`, `kind`
  (`replace|insert_after|clarify|group`), `before` (exact published wording, normalized only for
  ligatures/hyphenation/whitespace), `before_pdf` (fragments found in the PDF text, with page),
  `before_tex` (the manuscript TeX fragment the corrected manuscript replaces; `null` if the publisher's
  wording differs and the edit is applied by hand), `after`, `after_tex`, `reason` (one sentence),
  `class` (`formal|mechanical|editorial|typographical|bibliographic`), `status`
  (`confirmed|ask-author|withdrawn|optional`), `confidence` (`certain|inferred`), `evidence`, `lean_refs`,
  `source`. `make_errata.py` generates `ERRATA.md` and the errata TeX.
* Errata list finished before the Palomar package (R22), because `formalization.yaml` names the
  corrections as fidelity divergences.
* After the user reports the registration (R25): annotated tag on the registered commit (name confirmed
  with the user; suggested `palomar-v1`), pushed, never moved. Then `validation/apply_edits.py` builds the
  corrected manuscript from the manuscript TeX + `confirmed` items + one formal-verification paragraph and
  one bibliography entry; `audit_errata.py --corrected` checks that the diff is exactly that.

**D10 — Palomar selection and fidelity.** Select only result families of research interest:
`SmcTwoSatCorrect` (the SMC solver computes the APT assignment or reports unsatisfiability; planted
generator correctness), `IrreducibleExtremal` (at most n−2 irreducible loops and C(n−1,2) multi-entry
edges, attained by K_n and M_n; 2n−3 minimum other edges; the CFT lower bound if proved),
`TransformCorrect` (the Figure 5/6 primitives preserve semantics, induce irreducible loops with the
minimal number of edges; the static scheme end-to-end), `CircuitCFGCorrect` (VM order-independence and
data-independent execution counts; gate primitives; the AES compiler if proved), `SecurityModel` (D11).
Elementary arithmetic (Definition 3 sums, table ratios, Figure 1 checks) is supporting material. Every
sentence of `formalization.yaml`, `PALOMAR_SEMANTICS.md` and Spec docstrings claims no more than the Lean
hypotheses give (selfspectre lost three review rounds to this; see memory `palomar-review-fidelity`).

**D11 — The security model.** v1 §5.1 has goals in prose but no adversary, no assumption list and no
security statement; several sentences overclaim (P21–P24). The formalization supplies:
* **System.** Original program P (a structured program in the language of R17 whose basic blocks are
  Boolean-CFG computations, R10); obfuscator O = conversion to a Boolean CFG (§4) → irreducible-loop
  transformation with opaque predicates (§5) → predicate values produced at run time by the stamped SMC
  2-SAT solver on a planted formula (§3, §3.1). Obfuscated image = blueprint bytes + stamp data.
* **Adversary classes** (each an abstract interface with its capability stated as a structure, never a
  tool claim): `Struct` (structuring by node splitting, or by state variables), `Imm` (static analyzer
  that assumes code bytes are constant: reads predicate cells from the static image), `SmcSem` (static
  analyzer that implements stamping and the SMC machine semantics), `Trace` (dynamic tracer; sees
  (code address, value) pairs for chosen inputs), `Fault` (flips the value of one vertex execution),
  `Dca` (correlates aligned traces with a predicted intermediate value).
* **Goals.** recover a goto-free structured equivalent within a size budget; determine the opaque
  predicate values statically; change the output by one fault; correlate an intermediate value.
* **Assumptions** — structural properties of the design or of the class; **none may mention a goal
  predicate** (`validation/threat_audit.py` checks the `Assumptions` fields): S1 planted formula
  well-formed (R9 conditions); S2 predicate cells are written only by stamping/solver at run time; S3
  the schedule of the dynamic scheme respects dependencies; S4 the attacker class's capability bound.
* **Theorems (targets).** T1 correctness O(P) ≡ P under S1–S3. T2 `Imm` is unsound: for every
  obfuscated image some predicate read from the static image differs from its run-time value (witness
  family). T3 limit: an `SmcSem` analyzer recovers every predicate with work linear in the formula
  (APT) — opacity is relative to analyzers that do not implement the SMC semantics, not computational
  hardness. T4 structuring cost: node splitting of K_n-equivalent graphs needs ≥ 2^{n−1} nodes (CFT,
  if R18 proves it), while one state variable always suffices (flattening, R18): the "quadratic" cost is
  algorithm-specific. T5 faults: only a fault in the final execution of a vertex can change the output;
  the final-execution time depends on the input-tied schedule. T6 DCA: address-aligned traces of the
  dynamic scheme give the same multiset of (vertex, final value) as the static scheme — input-dependent
  ordering alone does not defeat DCA on aligned traces. T7 not iO: two functionally equivalent programs
  whose obfuscations differ in a public size measure (witness). Necessity: each Si gets a witness that
  the corresponding theorem fails without it.
* **Literature** (R20a; cite only after verifying the DOI): Barak et al. (VBB impossibility, JACM 2012),
  Collberg–Thomborson–Low (opaque predicates, POPL 1998), Banescu et al. 2015 [6] (check the quoted
  "defeated only in contrived scenarios"), Banescu et al. ACSAC 2016, Bos–Hubain–Michiels–Teuwen (DCA,
  CHES 2016), Carter–Ferrante–Thomborson (POPL 2003), Wang et al. 2001 [28], Chow et al. 2001 [9],
  Landi 1992 [18].

**D12 — Generator fidelity.** Python generators are ported to Lean only as *literal transcriptions*
(same function structure, same constant folding) or through the DSL of R11 whose node counts must equal
the Python counts (M evidence via `#eval` in a validation script). If counts differ, document the
difference; never tune the Lean model to match silently.

---

## 3. Target layout

```
CLAUDE.md                              standing rules (auto-loaded)
lean/
  FORMALIZATION_PLAN.md  ROUNDS.md     this plan; state machine + handoff notes
  lean-toolchain  lakefile.toml  lakefile.proof.toml (buildDir = ".lake/proof-build")  lake-manifest.json
  SmcIrred.lean                        root import
  SmcIrred/Spec/{Graph,DFS,LNF,TwoSat,SmcMachine,Generator,Circuit,Prims,AES,Arith,Lang,Dynamic,Threat,Paper}.lean
  SmcIrred/Spec/Data.lean              transcribed Tables 1–3 and figure data (FD, not selected)
  SmcIrred/Graph/{Reach,SCC,Jungle,Classify,Fig4}.lean
  SmcIrred/LNF/{Havlak,Algo,Facts,NonUnique,Small}.lean
  SmcIrred/Extremal/{Kn,Mn,IrrBound,MEEBound,MinOther}.lean
  SmcIrred/TwoSat/{Implication,APT,Unit,Fig1,DNF}.lean
  SmcIrred/Tarjan/{Algo,Correct,Cost,CodeModel}.lean
  SmcIrred/Smc/{Machine,Refine,Restamp,VMList,VMRefine}.lean
  SmcIrred/Gen/{Planted,Forcing,Counter}.lean
  SmcIrred/Circuit/{VM,Order,Counts,Subg,Gated,CodeModel}.lean
  SmcIrred/Prims/{Gates,Complete,Sel,Decoder,Adder,DSL,Compile}.lean
  SmcIrred/AES/{SBox,Spec,KeyExp,Vectors,Program,Circuit}.lean
  SmcIrred/Arith/{Montgomery,ModExp,Window,Karatsuba,Toom,Square,RBSD,Ladder,Word}.lean
  SmcIrred/Lang/{Syntax,CFG,Sem,Fig5,Fig6,MinEdges,Induce,NWay}.lean
  SmcIrred/Struct/{IrredLoopCpp,Flatten,StructuredReducible,Leftist,CFT}.lean
  SmcIrred/Dynamic/{Schedule,FinalExec,Fault,StaticScheme}.lean
  SmcIrred/Threat/{Model,Correct,Immutable,Recover,Structuring,DFA,DCA,NotIO,Necessity}.lean
  SmcIrred/Data/{Tables,Ratios}.lean
  SmcIrred/Paper.lean                  proofs of the Spec/Paper Props
  Challenge.lean Solution.lean ErrataRefs.lean CoverageRefs.lean comparator.json formalization.yaml   (R22–R24)
  PAPER_MAP.md VENDORED.md THREAT_MODEL.md PALOMAR_SEMANTICS.md PALOMAR_SUBMISSION.md LICENSE_AUDIT.md
  FINAL_ACCEPTANCE.json CODE_FIXES.md
  errata/{POLICY.md, edits.json, ERRATA.md, smcirred-2022-errata.tex, QUESTIONS.md}   paper only
paper/                                  (R25) corrected manuscript, biblio.bib, publmathdeb.cls, manuscript-v2022.diff
validation/
  limited_run.py memory_budget.py lean_build.py build_modules.py axiom_audit.{py,lean}
  make_challenge.py audit_errata.py make_errata.py apply_edits.py coverage_audit.py threat_audit.py
  fetch_reference.py build_tex.py check_tables.py graph_stats.py native.py
  planning/section5_bruteforce.py       planning evidence (§1)
  data/paper_tables.json  layout/  native/  reference/ (gitignored)  rounds/R*.json  palomar/  ci/
output/pdf/
.github/workflows/{ci.yml (existing), proof.yml, palomar-full.yml}
```

Add to `.gitignore` (R0): `lean/.lake/`, `validation/.build/`, `validation/.cache/`,
`validation/reference/`, `output/pdf/*.aux`, `output/pdf/*.log`, `/.private/`.

---

## 4. Global rules

**Economy.**
1. One round per session; read only the current round. Build only touched modules
   (`lean_build.py SmcIrred.TwoSat.APT`); full build once at round close.
2. Modules ≤ ~300 lines. State the theorem first, then prove. Commit compiling increments (once
   authorized).
3. A proof obstacle gets at most three focused attempts. Then weaken or split the statement with an
   explicit hypothesis, record it as an open obligation in `PAPER_MAP.md` (and `GAPS.md` if it affects a
   selected statement), and move on. Scope changes go to the user.
4. Never unfold long runs. Prove one-step lemmas and invariants, then induct.
5. Evidence is minimal: one `validation/rounds/Rk.json` per round (commit, commands, pass/fail, peak
   memory).

**Process.**
* All build/test commands go through `limited_run.py` (D8).
* Round close: full build, `axiom_audit.py`, round gate, update `ROUNDS.md` (state + 5-line handoff:
  done / next / open obligations / hazards / evidence), `PAPER_MAP.md`, `edits.json` `lean_refs`,
  `validation/rounds/Rk.json`, the "Current round" line in `CLAUDE.md`; commit (and push) if authorized.
  Commit messages end with the attribution line from the system prompt.
* At most one `AskUserQuestion` call per round (≤ 4 questions), at the start, only for decisions.
  Overflow questions go to `lean/errata/QUESTIONS.md` for the next round's call.

**Errata policy** (copy to `lean/errata/POLICY.md` in R1). Preserve the published construction and make
the smallest local correction that states its intended, provable result. Quote the published version
exactly; never attribute PDF-extraction artifacts (e.g. "Tama´s", scrambled tables) to the paper. Only
text, tables, figures, captions and references carry errata; code and docs fixes go to
`CODE_FIXES.md`. An item is `confirmed` only when it is certain (a Lean declaration, arithmetic on the
paper's own numbers, an internal inconsistency, or a primary source) or `inferred` with the evidence
written into the item; anything else stays `ask-author` and is not applied until answered. `optional`
items are real but minor; the author decides whether they appear. Typos are one grouped item (T01) and
reference corrections one grouped item (B01). Every item is self-contained. Evidence is never called
proof. Keep the errata PDF ≤ 4 pages plus an appendix page for any replaced passage.

---

## 5. Seed inventory (verify in R1; IDs are stable)

### Claims (seed for `PAPER_MAP.md`; class per D1, round that discharges it)

| ID | Location | Claim | Class | Round |
|---|---|---|---|---|
| C01 | Abstract; §5 ¶1 | static analysis of SMC has decidability limits "as per Rice's theorem" (P26) | R | R1 |
| C02 | Abstract; §2 ¶7; §5 | IL → reducible by node splitting or variables: quadratic increase (P17) | F + R | R4, R18 |
| C03 | Abstract; §4 | algorithms lowered to multi-input gates; applicable to any CFG | F | R10 |
| C04 | Abstract; §6 | the ideas can be applied separately | X | R1 |
| C05 | §1 ¶1 | VMProtect and Denuvo defeated [16, 17] | R | R1 |
| C06 | §1 ¶3 | DFS-based SCC + topological sort implemented by an SMC CFG of the queried graph | F + M | R7, R8 |
| C07 | §1 ¶3 | stack simplification; generalizable to largely any graph algorithm | X | R1 |
| C08 | §1 ¶3 | SCC + topological sort make an efficient linear 2-SAT solver [2] | F | R5, R6 |
| C09 | §1 ¶4 | an IL is a loop with multiple entries; hardest structure for static tools | F (def) + X | R3 |
| C10 | §1 ¶4 | nested ILs can cause quadratic LNF construction [22] | R | R1 |
| C11 | §1 ¶4 | "the only resolution" for structuring is variables + conditions (P12) | F + R | R18 |
| C12 | §1 ¶4 | almost-linear LNF algorithms exist; AST translation lacks the same reductions | R + X | R1 |
| C13 | §1 ¶5 | every construct embedded into an IL nest designed for quadratic identification | F + X | R4, R17 |
| C14 | §1 ¶5 | loops fictitious via opaque predicates: original looping or one iteration | F | R17 |
| C15 | §1 ¶5 | the 2-SAT solver fixes all exit conditions; beyond static tools | F + FT + X | R9, R19, R20b |
| C16 | §1 ¶5 | case study: protected AES/RSA, measured on Windows/Linux x86/x64, IDA/Ghidra (P13) | X | R1 |
| C17 | §2 ¶1 | SAT, CNF, 2-SAT definitions (P01) | F | R5 |
| C18 | §2 ¶1 | DNF trivially solvable but potentially O(2^n) clauses | F (should) | R5 |
| C19 | §2 ¶1 | k-SAT reduces to 3-SAT; 3-SAT NP-complete | R (+F could) | R1 |
| C20 | §2 ¶2 | 2-SAT NL-complete; NL ⊆ P | R | R1 |
| C21 | §2 ¶2 | linear time via implication graph + SCC; solution in reverse topological order | F | R5, R6 |
| C22 | §2 ¶2 | an empty clause means unsatisfiable | F | R5 |
| C23 | §2 ¶2 | unit-clause handling (P02) | F | R5 |
| C24 | §2 ¶2 | (p ∨ q) ≡ (¬p ⇒ q) ∧ (¬q ⇒ p) | F | R5 |
| C25 | Fig. 1 | formula, 24 implications, graph, SCC labels, highlighted solution | F + M | R5 |
| C26 | §2 ¶3 | CFG definition; vertex kinds by out-degree (P03) | F | R2 |
| C27 | §2 ¶3 | DFS edge classification by pre/post timestamps | F | R2 |
| C28 | §2 ¶4 | loops; LNF; unique for reducible CFGs, not for irreducible ones | F | R3 |
| C29 | §2 ¶4 | Havlak LNF: one header per loop; near-linear [26] | F (def) + R | R3 |
| C30 | §2 ¶4 | ILs not directly representable in Java/Python | F (should) | R18 |
| C31 | §2 ¶5 | state-machine model represents any CFG with one variable and an n-way conditional | F | R18 |
| C32 | §2 ¶6 | structuring ILs needs goto (absent new variables/duplication); tools named | F + R | R18 |
| C33 | §2 ¶7 | restructuring needs duplication [27] or state variables [30, 31]; quadratic variables/conditionals | F + R | R18 |
| C34 | §2 ¶8 | prior obfuscation methods; the contribution | R + X | R1 |
| C35 | §3 ¶1 | implication graph = CFG; node code = SCC + reverse topological sort | F | R7 |
| C36 | §3 ¶1 | implemented in x86 and x86-64 on Windows and Linux | M | R8 |
| C37 | §3 ¶1 | node stack replaces the call stack; first instruction → return; topological check marking | F + M | R7, R8 |
| C38 | §3 ¶1 | lambda callbacks for edges and solutions; set for unsatisfiability | M | R8 |
| C39 | §3 ¶2, Fig. 2 | blueprint generation; stamping; reuse by restamping SMC offsets | F + M | R7, R8 |
| C40 | §3.1 | planted 2-SAT generator yields the desired values (P04) | F | R9 |
| C41 | §4 ¶1 | Boolean-level description; word-level abstractions can be reintroduced | X + F (DSL) | R11 |
| C42 | §4, Def. 1 | multi-input AND/OR/XOR/XNOR; decomposition into |X|−1 two-input gates, sequential or tree | F | R11 |
| C43 | §4 | NAND, NOR functionally complete; XNOR/NAND/NOR negate one input | F | R11 |
| C44 | §4, Def. 2 | SEL; XOR replaceable by OR under one-hot selectors; BSEL | F | R11 |
| C45 | §4 | table lookup decomposes into single-bit outputs | F | R11 |
| C46 | §4; §4.1 ¶3 | optimal circuit synthesis "NP-hard based on circuit SAT" (P06) | R | R1 |
| C47 | §4; Fig. 3 | two table-lookup representations; nodes-vs-edges trade-off; Fig. 3 count comments | F | R11 |
| C48 | §4 | ripple addition (P05), subtraction with borrow, combined add/sub selector | F | R11 |
| C49 | §4 | constant time maintained; reusable subgraphs with activation edge and repetition; conditional execution loses constant time | F | R10 |
| C50 | §4.1 ¶1–2 | AES structure; key expansion by XOR + lookups; xtime as selection; S-box (P07); inverse | F + R | R12 |
| C51 | §4.1 ¶2 | S-box subgraph reuse; identification needs recognizing decoder circuits | M + X | R13, R16 |
| C52 | §4.1 ¶3 | spurious inputs/deeper circuits remove table uniformity | X | R1 |
| C53 | §4.2 ¶1 | RSA/PKCS background | R | R1 |
| C54 | §4.2 ¶1 | square-and-multiply O(Mn + Sn); windowing; addition chains [11] | F + R | R14 |
| C55 | §4.2 ¶1 | Karatsuba O(n^{log₂3}), Toom-Cook (P08), schoolbook O(n²), Schönhage–Strassen [7] | F + R | R14 |
| C56 | §4.2 ¶1 | carry-save/Wallace; squaring about twice as fast | F (count) + X | R14 |
| C57 | §4.2 ¶1 | Montgomery multiplication/reduction correct; cost = multiplication × constant | F | R14 |
| C58 | §4.2 ¶2 | RBSD carry-free addition [21]; NAF/MOF lower weight; sliding windows/chains not constant time; ladder constant time | F (should/could) + X | R14 |
| C59 | §4.2 ¶3 | implementation: Montgomery form, Montgomery + Karatsuba, windows minimizing products, subgraph reuse | M + F | R14, R16 |
| C60 | §4.3, Tables 1–2 | Nodes, Edges, Exec. N, Exec. E | M | R16 |
| C61 | §4.3, Tables 1–2 | timings; RSA worse than quadratic; impractical after 256 bits (P10) | FD + X | R16 |
| C62 | §4.3 | machine-word reductions gain "2^32 or 2^64" (P09) | F | R14 |
| C63 | Fig. 3 | the listed Python equals the generator code | M | R11 |
| C64 | §5 ¶1 | ILs rare in C [25]; undecidability [18]; read-only code segments | R + X | R1 |
| C65 | Fig. 4 | CFG, jungle with timestamps, Havlak LNF; C++ encodings | F + M | R3, R18 |
| C66 | Table 3 | decompiler counts | X | R1 |
| C67 | §5, Def. 3 | K_n: |E| = n²−n; any root gives a CFG; n−1 headers in a chain; entry loop reducible; ≤ n−2 irreducible loops; |MEE(K_n)| = (n−1)(n−2)/2 | F | R4 |
| C68 | §5, Def. 4 | M_n construction (P14), |E(M_n)|, |MEE(M_n)| = |MEE(K_n)|, MEE maximal, others minimal (P15, P16) | F | R4 |
| C69 | §5 | DCC/REC assumptions on Boolean latches | X + R | R1 |
| C70 | §5 | node splitting needs a quadratic amount of duplication (P17) | R + F (should) | R18 |
| C71 | §5 | 1- and 2-node CFGs never contain an IL | F | R3 |
| C72 | §5 | DREAM: n−2 integer variables; conditions by MEE; n−2 compound conditions | X + F (could) | R18 |
| C73 | §5 | minimal 2 edges for a sequence; simulated loop = one node + three edges + SMC/state variable | F | R17 |
| C74 | Figs. 5–6 | transformed programs equivalent; ILs induced; graphs match code (P18, P19) | F | R17 |
| C75 | §5 | inducing ILs on reducible loops by edges from unreached outside nodes | F | R17 |
| C76 | §5 | two-way / n-way extension; conditions from separate 2-SAT outputs; SMC or negated state variable | F | R17, R19 |
| C77 | §5 | dynamic scheme: dependency order guarantees all dependencies ran, in order; bounded duplication; input-tied order | F | R19 |
| C78 | §5.1 ¶1 | security goals; automated vs manual attacks; CFG identification as hard as circuit identification | FT + X | R20a |
| C79 | §5.1 ¶2 | "indistinguishable … from a practical standpoint" (P23) | FT + R | R20b |
| C80 | §5.1 ¶3 | both schemes practically resistant to static analysis | FT | R20a |
| C81 | §5.1 ¶4 | DFA resistance, final execution; DCA/DPA (P21, P22) | FT | R19, R20b |
| C82 | §5.1 ¶5 | Banescu framework; opaque predicates defeated only in contrived scenarios; SMC symbolic execution beyond tools; exponential dynamic time (P24) | R + FT + X | R20a, R20b |
| C83 | §6 | summary; open definitional questions for SMC; Kolmogorov complexity | X | R1 |

### Paper errata seeds (P, T, B)

Per the author's standing instruction "apply errata that are certain without asking; ask only about
uncertain ones". R1 re-verifies every quote (published PDF) and number before anything is written to
`edits.json`.

| ID | Page, location | Published text → correction | Class | Status |
|---|---|---|---|---|
| P01 | 619, §2 ¶1 | "a set of clauses C = {C1, ..., Cn} where ∀i ∈ [1..n]" reuses n (the number of variables) → C = {C1, …, Cm}, i ∈ [1..m]. Fig. 1 has 8 variables and 12 clauses | formal | confirmed |
| P02 | 619, §2 ¶2 | "A clause with one variable … Regardless it need not effect the implication graph or could be a trivial self-loop." → a unit clause (x) ≡ (x ∨ x) contributes the edge ¬x → x (not a self-loop) and must be kept unless x is substituted; dropping it would report (x) ∧ (¬x) satisfiable. The repository's `gettwosatgraph` already does this | formal | confirmed (Lean R5) |
| P03 | 619, §2 ¶3 | "otherwise it contains more than two out-edges and is an n-way conditional" omits vertices with no out-edge (exit/return vertices, e.g. *exit* in Fig. 4) | formal | confirmed (minor) |
| P04 | 623, §3.1 | "implications can randomly be added to the forest such that no loops are created which would imply unsatisfiability" → acyclicity is neither necessary nor sufficient; the condition that keeps the desired assignment σ a solution is that no implication from a σ-true literal to a σ-false literal is added; the "tree of implications" must give each required variable a forcing path ¬ℓ ⇒* ℓ so that every solution, hence the solver's output, agrees with σ | formal | confirmed after R9 |
| P05 | 625, §4 | "s_i = a_i ⊕ b_i ⊕ c_{i+1}" → "s_i = a_i ⊕ b_i ⊕ c_i" (c_i is the carry into bit i; counterexample a = b = 1) | formal | confirmed |
| P06 | 624 §4; 625–626 §4.1 | "using logic synthesis to construct an optimal circuit is NP-hard based on the circuit SAT problem"; "Although the optimal one is NP-hard" → for a truth-table input this is the Minimum Circuit Size Problem, whose NP-hardness is open (known: NP-hard for DNF minimization; multi-output version under randomized reductions); for a circuit input, minimization is coNP-hard via circuit satisfiability. R1 verifies sources (Kabanets–Cai 2000; Masek 1979 / Umans 2001; Ilango–Loff–Oliveira 2020) | editorial | ask-author (wording) |
| P07 | 625, §4.1 | "substitution (S)-boxes … provides non-linearity using an invertible affine transformation. This multiplicative inverse of the inverse of the affine transformation is used for decryption." → the S-box is the multiplicative inverse in GF(2^8) (the non-linear part) followed by an invertible affine map; decryption applies the inverse affine map, then the inverse (FIPS-197 §5.1.1) | formal + editorial | confirmed (Lean R12) |
| P08 | 626, §4.2 | "Toom-Cook (O(n^{log_k 2k−1}))" (reads as log_k(2k) − 1 = log_k 2) → O(n^{log_k(2k−1)}) | formal | confirmed |
| P09 | 627, §4.3 | "increase the potential of the representation by order of 2^32 or 2^64" → by a factor of order w (w = 32, 64) for linear operations and w² for schoolbook multiplication | formal | inferred (Lean count R14) |
| P10 | 629, Table 2 | `C gmp`: 256-bit cells duplicate the 128-bit cells (9.141 ms, 7.640 ms); the 32-bit cells (851 ms, 707 ms) exceed the 64-bit cells (likely µs). Correct values from the author's records or a re-measurement | mechanical (FD) | ask-author |
| P11 | 627–629, §4.3, Tables 1–2 | provenance: "AES … with a fixed randomly generated key" vs the repository key `0x12…`; Nodes/Edges/Exec. N/Exec. E must be reproduced by R16; any mismatch is reported here | mechanical | pending R16 |
| P12 | 618, §1 ¶4 | "the only resolution to structuring them into an abstract syntax tree (AST) involves introduction of variables and conditional expressions [30]" contradicts §2 ¶7 → resolutions involve code duplication (node splitting) [27] or the introduction of variables and conditional expressions [30] | editorial | confirmed |
| P13 | 618–619, §1 ¶5 | the announced case study (AES/RSA protected by IL nests with 2-SAT exit conditions; measurements under Windows and Linux; IDA/Ghidra on them) is not what §4–§5 report (plain Boolean CFGs in Tables 1–2; the Fig. 4 example in Table 3); the repository has no implementation of the protected variant | editorial | ask-author |
| P14 | 631, §5 before Def. 4 | "removing extra back edges whose successor is not the inner-most non-header node" → "whose source is not …" (Def. 4 keeps exactly the back edges (v_n, v_i)) | formal | confirmed |
| P15 | 631, §5 before Def. 4 | "will have maximized multi-entry edges while minimizing all others" → MEE is maximal (C(n−1,2), Lean); the other edges are minimal up to one: 2n−3 suffice, since (v_n, v_1) can be dropped | formal | confirmed fact; wording ask-author |
| P16 | 631, Defs. 3–4 | "Definition 3"/"Definition 4" state claims (|MEE(K_n)|, |E(M_n)|, |MEE(M_n)| = |MEE(K_n)|) and MEE is never defined → define MEE (relative to the Havlak LNF of the DFS v1…vn) and state the counts as a proposition; also "V_{M_n} = v_i ∀i" → {v_i : i ∈ [1..n]} | formal | confirmed (clarify) |
| P17 | 631, §5; 617 Abstract | "this optimization will still require a quadratic amount of code duplication for each multi-entry edge" → node splitting needs exponential duplication on K_n: every equivalent reducible graph has ≥ 2^{n−1} nodes (Carter–Ferrante–Thomborson, POPL 2003). P17.2 (Abstract, "can have a quadratic complexity increase") optional | editorial (+ formal if R18 proves CFT) | confirmed after R1 DOI check |
| P18 | 632, Fig. 5(c) | the drawn graph sends the loop exit from A and has no injected condition node, so no path executes A then B once; the code (c) and the text ("requires one node") need a condition node H: H→A, A→B, B→H, H→exit, goto→B | formal | confirmed after R17 |
| P19 | 633, Fig. 6(c) | the drawn graph keeps A→B, which the code `while (c && trueThenFalse) { labelA: A; } B;` lacks (A returns to the condition); caption "an extra edge" but two edges are added | formal | inferred → R17 |
| P21 | 634, §5.1 ¶4 | "differential computation analysis (DCA) and its subset differential power analysis (DPA)" → DCA is the software counterpart of DPA (Bos et al., CHES 2016); neither is a subset of the other | editorial | confirmed after R1 source check |
| P22 | 634, §5.1 ¶4 | "It is resistant to differential computation analysis … as the execution order changes based on the input." → unimplemented scheme; input-dependent order does not defeat DCA on address-aligned traces (Lean T6); state as a conjecture or remove | formal | confirmed after R20b |
| P23 | 634, §5.1 ¶2 | "indistinguishable from the underlying algorithm from a practical standpoint" is not a defined notion → what is proved is functional equivalence (T1); no iO or VBB property is claimed (T7 witness) | formal + editorial | ask-author (wording) |
| P24 | 635, §5.1 ¶5 | "the repeated operations would require exponential time without proving these operations as repeated" → unsupported; aligned traces expose repeated executions of the same vertex (T6) | formal | ask-author (wording) |
| P25 | 634–635, §5.1 | optional replacement of §5.1 by a short formal security subsection (D11: classes, S1–S4, T1–T7 with Lean names) | formal | optional (author decides in R20b) |
| P26 | 617 Abstract; 629 §5 ¶1 | "as per Rice's theorem": Rice's theorem concerns extensional properties; self-modification/reachability undecidability follows from the halting problem (Landi [18]) | editorial | optional |
| T01 | various | typographical group: running head "loopsand"; "need not effect" (affect); "Schonhage" (Schönhage); "elliptical curve digitial" (elliptic curve digital); "multliplication"; "penality"; "there performance" (their); "reprsented"; "suspectible"; "gratuitious"; "transfered"; "prefering"; "programing"; Fig. 3 caption "—xor to virtual—" (TeX `|…|` without `\lstinline`); Fig. 6(b) `if (!c): goto labelB;` (stray colon, not C); "their rarity in C … is exceedingly rare" | typographical | confirmed (R1 completes the list) |
| B01 | 635–637 | bibliography group: [21] Parhami, IEEE Trans. Computers **37** (not 137); [26] authors are T. Wei, J. Mao, W. Zou, Y. Chen (given/family names swapped); [8] ePrint 2015/412 dated 2018 (check); [19] "Scientarum" → "Scientiarum"; [10] "Inform'atica" → "Informática"; R1 checks every entry against its DOI | bibliographic | confirmed after R1 |

(P20 is retired: the Fig. 6(b) syntax error is in T01.)

### Code (L) and docs (D) seeds — not errata; tracked in `lean/CODE_FIXES.md`; all land before the Palomar commit

| ID | File | Fix (minimal) | Test |
|---|---|---|---|
| L01 | `native/selfmodgraph.cpp` `tarjan_scc` | skip visited nodes in the outer loop | duplicate-free SCC list; `twosat` vectors unchanged |
| L02 | `native/aesmain.c`, `native/rsa.c` | label the VM slot honestly ("Graph VM"), drop or guard the empty 192/256 stubs in `verify` | harness output |
| L03 | `python/virt.py` `set_bit_range` | slice stop, not stride (only if used; else delete) | unit test |
| L04 | `python/virt.py` `do_run_virtual` | define `outp = None` when `outmap is None` | unit test |
| L05 | `python/virt.py`, `aes.py`, `rsa.py` | optional `--seed` for reproducible regeneration (default behaviour unchanged) | `graph_stats.py` twice → identical counts |
| L06 | `python/aes.py` `gen_aes` | document the key; key choice per P11 answer | regenerate |
| D01 | `README.md` | Lean section (R24; Palomar ID and tag in R25) | — |
| D02 | `CITATION.cff` | add the formalization reference after registration | — |
| D03 | `README.md` / `CHANGELOG.md` | state that the IL-protected AES/RSA variant is not implemented (per P13 answer) | — |

---

## Rounds

Sizing: one session each unless noted. Priority: **must** / should / could. The **must** items alone give
a Palomar-ready, fully classified result ("MVP path", end of file).

### R0 — Bootstrap, references, baselines (must)

1. **One question** (`AskUserQuestion`, ≤ 4): (a) may commits to `master` at green increments and pushes
   to `origin` be made (never force-push, never move tags)? (b) may the published PDF be committed (journal
   copyright; default no) and may the manuscript TeX/bib/cls be committed under `paper/manuscript-2022/`
   (default: ask; without it they stay in gitignored `validation/reference/`)? (c) confirm the tag name
   suggestion `palomar-v1` for later. Record answers in `CLAUDE.md` "Authorizations".
2. `validation/fetch_reference.py`: download the published PDF (URL §0) and copy the four OneDrive files
   into `validation/reference/`, verify the five SHA-256 values of §0, write `SHA256SUMS`; derive
   `pmd.txt` (`pdftotext -layout -enc UTF-8`) and `pmd_raw.txt` (`pdftotext -enc UTF-8`). Never write to
   OneDrive.
3. Build the manuscript with `validation/build_tex.py` (vendored; scratch copy; needs `graphviz` `dot` and
   `-shell-escape` for the `graphviz` package; `publmathdeb.cls` from the reference copy) into
   `output/pdf/`; record the page count (expect 21) and any difference from the published PDF.
4. Lake project (D4): `lean-toolchain`, `lakefile.toml` (package `smcdynirredloops`,
   `defaultTargets = ["SmcIrred"]`, `weakLeanArgs = ["-M","768","-j","1"]`), `lakefile.proof.toml`,
   hand-written `lake-manifest.json`; root `SmcIrred.lean` importing a stub `SmcIrred/Spec/Graph.lean`.
5. Copy infra (D5), write `lean/VENDORED.md`. Check `limited_run.py` on a trivial command; build the stub
   under the guard (fall back to `build_modules.py` if Lake exceeds the cap).
6. `validation/axiom_audit.{lean,py}` for prefixes `SmcIrred`, `PalomarSIL`; passes on the stub.
7. `validation/data/paper_tables.json`: Tables 1–3, Fig. 1 (clauses, implications, graph edges, SCC
   labels, green literals), Fig. 4 (edges, jungle timestamps, LNF) transcribed **from the manuscript TeX
   with line numbers**, plus the published page number; `validation/check_tables.py` re-reads the TeX and
   compares, and checks each table value against the rendered page once (manual sign-off recorded in
   `R0.json`).
8. Native baseline (compile only): `validation/native.py` builds `native/selfmodgraph.sln`
   (`selfmodgraph`, `aes`, `rsa`, `ecdsa` Debug|x64 and Debug|Win32 if configured; locate MSBuild via
   `vswhere`; `--toolset v143` override for CI; GMP via `native/gmp.props`/Conan); Linux: `g++ -std=c++17
   native/selfmodgraph.cpp native/IrredLoop.cpp` (CI job). Do not run anything yet.
9. `.gitignore` additions (§3), `lean/ROUNDS.md` update, `validation/rounds/R0.json`.

**Gate:** reference hashes verified; manuscript builds; stub builds and audits clean under the guard;
native compiles; tables checker passes.

### R1 — Claim inventory, errata verification, sources, author questions (must; text work)

1. For each P/T/B item: find the exact published wording in `pmd_raw.txt` (page) and the manuscript
   fragment; recompute every number. Then read the whole paper once more for further
   mathematical/algorithmic/quantitative/security errors (complete the T01 list in the same pass; do not
   hunt for style). Add new items with a status per §4.
2. Verify every R-class claim and every reference against primary sources (DOI pages, publisher pages,
   ePrint, arXiv): C01, C05, C10, C12, C19, C20, C29, C34, C46 (P06 sources), C53–C55, C64, C69, C70 (CFT
   DOI 10.1145/604131.604141 — confirm), Banescu et al. quote (C82), Bos et al. (P21). Record URL + section
   in `PAPER_MAP.md`. A disagreement becomes a P or B item.
3. Write `lean/errata/POLICY.md` (§4), `edits.json` (D9 schema), `lean/CODE_FIXES.md` (L, D items),
   `lean/PAPER_MAP.md` (C01–C83 + new; columns ID, location, page, claim, class, round, status,
   declaration/evidence).
4. `validation/audit_errata.py --inventory`: every `before` is found in the published PDF text after
   normalizing whitespace/hyphenation/ligatures; every `before_tex` occurs verbatim in the manuscript TeX.
5. Last step, one `AskUserQuestion` (≤ 4) for the `ask-author` items with the most leverage: P10 (true
   `C gmp` values or re-measure), P13 (how to state the case study), P15/P23/P24 wording style (minimal vs
   explicit), and whether T01/B01/P26 appear in the errata document. Others go to `QUESTIONS.md`.

**Gate:** inventory audit passes; every claim has a class; every item has class, status and planned
evidence.

### R2 — Graph foundations, DFS jungle, Figure 4(a)(b) (must)

`Spec/Graph.lean`: finite digraphs on `Fin n` (`Adj := Fin n → Fin n → Bool`), `Reach`, rooted CFG
(root reaches every vertex), SCC (`SameSCC`), vertex kinds by out-degree (sequence / Boolean / n-way /
**exit** — the corrected P03 classification). `Spec/DFS.lean`: a *jungle* = DFS tree (parent map) with
preorder/postorder timestamps satisfying the parenthesis property and the white-path property; edge
classes tree/forward/back/cross. Copy from dyngraph per D5 if eligible.

1. `Graph/Classify`: the timestamp characterization (C27): for a valid jungle, (x,y) is tree/forward iff
   pre x < pre y ∧ post y < post x, back iff pre y ≤ pre x ∧ post x ≤ post y, cross iff post y < pre x;
   cross edges go right to left.
2. A computable DFS (successor order = list order) producing a valid jungle; proved valid.
3. `Graph/Fig4`: the Fig. 4 CFG; the DFS with the code's successor order gives exactly the jungle of
   Fig. 4(b) (timestamps with the clock starting at 2, edge classes) — `decide`.
4. P03 Lean evidence: the Fig. 4 *exit* vertex has out-degree 0.

**Gate:** C26, C27 proved; Fig. 4(b) reproduced.

### R3 — Havlak loop nesting forest (must)

`Spec/LNF.lean`: Havlak loops relative to a jungle — `header`, `L w` (body: descendants of w that reach
w through non-root back edges within the subtree), reducible/irreducible (some body vertex has a
predecessor that is not a descendant of w), **MEE** (edge (x,y) with y ∈ L*(w)\{w} and x not a
descendant of w for some header w), the LNF forest. Declarative definitions, plus `LNF/Algo` = Havlak's
worklist algorithm with union-find (fuel-bounded), proved equal to the declarative LNF.

1. `LNF/Facts`: the root's loop is never irreducible (all vertices are descendants of the root) (C67
   part); loop bodies are nested or disjoint; every MEE edge is a forward or cross edge.
2. `LNF/Small` (C71): every CFG with ≤ 2 vertices has no irreducible loop (any DFS); the 3-vertex
   witness r→a, r→b, a↔b has one.
3. Fig. 4(c) (C65): the computed LNF of Fig. 4 = loops 2 ⊃ 4 ⊃ 5 ⊃ {3}, all irreducible, entry edge 1→3,
   top-level {1, 6} — `decide`.
4. `LNF/NonUnique` (C28): exploring v before u in Fig. 4 yields a different Havlak LNF (different
   headers). For reducible CFGs the loop *bodies* are DFS-independent (should; via dominators: header =
   back-edge target that dominates its source).

**Gate:** Havlak algorithm = declarative LNF; Fig. 4(c) reproduced; C28 witness and C71 proved.

### R4 — Extremal results: K_n, M_n, upper bounds (must; up to two sessions)

1. `Extremal/Kn` (C67, Def. 3): K_n (no self-loops) is a CFG for every root; every DFS of K_n is a
   Hamiltonian path; headers = first n−1 DFS vertices in one chain; root loop reducible; exactly n−2
   irreducible loops (n ≥ 2); |MEE(K_n)| = Σ_{i=0}^{n−2} i = (n−1)(n−2)/2; |E| = n² − n.
2. `Extremal/Mn` (C68, Def. 4, P14, P16): the three edge sets are disjoint; |E(M_n)| = (n−1)(n+2)/2;
   same headers and irreducible loops as K_n; |MEE(M_n)| = |MEE(K_n)|; M_n = K_n minus exactly the back
   edges whose **source** is not v_n (P14 formal).
3. `Extremal/IrrBound` (must): for every CFG on n ≥ 2 vertices and every DFS, #irreducible loops ≤ n−2
   (root excluded; a DFS leaf heads no irreducible loop).
4. `Extremal/MEEBound` (should): #MEE ≤ C(n−1,2) for every CFG and DFS. Planning evidence: n ≤ 5
   exhaustive, 6–7 sampled. Warning: the naive injection (x,y) ↦ (child of lca toward y, y) is not
   injective for cross edges from different later subtrees; look for a counting argument per vertex y
   along its ancestor chain. If three attempts fail, record the open obligation and keep the K_n/M_n
   equalities.
5. `Extremal/MinOther` (P15): M_n minus (v_n, v_1) has the same MEE and irreducible loops with 2n−3
   other edges; (should) every CFG with C(n−1,2) MEE has ≥ 2n−3 non-MEE edges (n−1 tree edges + one back
   edge per required header v_2..v_{n−1}).
6. Re-run `validation/planning/section5_bruteforce.py` against the Lean definitions on n ≤ 5 via a
   generated `#eval` file (M evidence that the Lean MEE/Havlak match the planning script).

**Gate:** items 1–3 and 5 (witness part) proved; 4 proved or recorded open.

### R5 — 2-SAT: implication graph, APT theorem, Figure 1 (must)

`Spec/TwoSat.lean`: variables `Fin n`, literals, clauses of ≤ 2 literals (m clauses, P01), CNF
satisfaction, the implication graph (each clause (a ∨ b) gives ¬a→b and ¬b→a; unit (a) gives ¬a→a; the
empty clause makes the formula unsatisfiable), SCC labels.

1. `TwoSat/Implication` (C24): (p ∨ q) ↔ (¬p → q) ∧ (¬q → p); an assignment satisfies the formula iff it
   is closed under the implication edges (no edge from a true to a false literal).
2. `TwoSat/APT` (C21): unsatisfiable iff some x and ¬x are in the same SCC; given SCC labels in reverse
   topological order, "x true iff label(x) < label(¬x)" satisfies the formula (Aspvall–Plass–Tarjan).
3. `TwoSat/Unit` (C22, C23, P02): with the ¬x→x encoding the theorem holds for unit clauses; the
   variant that drops unit clauses (or uses a self-loop x→x) answers "satisfiable" for (x) ∧ (¬x) —
   explicit counterexample. Self-loop edges are irrelevant to satisfiability.
4. `TwoSat/Fig1` (C25): the 12 clauses = `testformula3`; the 24 implications; the graph edges; the SCCs
   and labels 1–10 are a valid reverse topological SCC labelling; the green literals = the APT assignment;
   it satisfies the formula; the formula has exactly 3 satisfying assignments (`decide` over 256).
5. `TwoSat/DNF` (C18, should): parity on n variables needs ≥ 2^{n−1} terms in any DNF (each term must
   mention all variables); DNF satisfiability is decided by one pass over the terms.

**Gate:** C17, C21–C25 proved; P02 counterexample proved.

### R6 — Tarjan's algorithm and the reference solver (must)

1. `Tarjan/Algo`: Tarjan's SCC algorithm as a fuel-bounded functional program (index, lowlink, stack,
   on-stack flags), outer loop over vertices **skipping visited ones**.
2. `Tarjan/Correct`: it returns exactly the SCCs, each once, in reverse topological order (emission
   order); hence `twosat` (APT over the emission order) is correct (C08, C21).
3. `Tarjan/Cost` (C21 "linear"): the algorithm examines each edge once and each vertex once; the
   step count is ≤ c·(n + m) for an explicit c.
4. `Tarjan/CodeModel` (L01): a literal model of `tarjan_scc`'s outer loop (re-entering visited
   vertices): its SCC list = the correct list plus duplicate singletons of SCC roots, appended after their
   originals; `twosat` on that list returns the same assignment. Then L01 is a clean-up, not a bug fix of
   the result.

**Gate:** Tarjan correctness and cost proved; L01 behaviour characterized.

### R7 — SMC 2-SAT solver, Level 2 (must; the core algorithm; up to two sessions)

`Spec/SmcMachine.lean` (D3 Level 2): state = per-node code cell `{entry : Entry := .run | .ret,
index lowlink counter : Option Nat, retAddr, onStackMark, checkScc : Bool, topoNext : Option Node}`, the
node stack (return addresses into node code), the global index, the topological chain head; steps follow
§3 and the `selfmodvmtwosathl` pseudo-language (`modexpr`, `modsb`, `returnjump`, `push/pop/peek/getsp`).
Read `selfmodvmtwosathl` (`native/selfmodgraph.cpp` lines 966–1034) and `selfmodmodel.asm` before
designing; record every modelling choice in the module docstring.

1. `Smc/Machine`: the step relation and a fuel-bounded run; well-formedness invariant.
2. `Smc/Refine`: simulation with Tarjan (R6): "entry = .ret" ↔ visited; the node stack ↔ Tarjan's
   call stack + SCC stack; lowlink immediates ↔ lowlink; the topological chain ↔ emission order; the
   solution checks ↔ APT; termination; result = `sat σ` with σ = APT assignment, or `unsat` iff some
   x, ¬x share an SCC (C06, C35, C37).
3. `Smc/Restamp` (C39, Fig. 2b "Reuse"): the stamped image before a run and after the run differ only at
   the declared SMC offsets; restamping those offsets restores it; hence k successive runs (with restamp)
   compute k independent answers.

**Gate:** Level 2 ⇒ Level 1 refinement and restamp lemma proved.

### R8 — SMC solver: VM level and native evidence (should for 1; must for 2–3)

1. *(should)* `Smc/VMList` + `Smc/VMRefine`: literal transcription of the instruction list that
   `selfmodvmtwosat` builds (enum `opcodes`, the `blueprint` lambdas, `MODINST` patches) and its
   interpreter loop; proved to refine Level 2.
2. *(must, M)* `validation/native_twosat.py` + `validation/native/twosat_harness.cpp` (includes the
   product source with `#define main product_main`): run `twosat`, `selfmodtwosatasm` (and the VM when
   compiled with `USE_VM`) on test formulas 1–4 and 2,000 random formulas (fixed seed) on Windows x64,
   Windows x86 and Linux x64; compare with Lean-generated expected answers
   (`lake env lean --run validation/TwoSatVectors.lean`); compare `alltwosat` solution counts (formula 3:
   3 solutions). Record per-platform results (C36, C38).
3. *(must, M)* Figure 2(a): assemble `selfmodmodel.asm` (ml64 / ml with `/Fl /Sa`), run
   `parseasmlisting` on the listing, and check that its output equals the byte arrays and offset constants
   in `selfmodgraph.cpp` (x64 Windows; others as available).

**Gate:** native vectors pass on every platform built; listing ↔ arrays equal.

### R9 — Planted 2-SAT generator (must)

`Spec/Generator.lean`: the §3.1 procedure made precise: desired assignment σ on required variables;
a forest of implications in which every required variable x has a forcing path from its σ-false literal
to its σ-true literal; optional free variables; random additional implications, each **σ-respecting**
(never from a σ-true to a σ-false literal) and closed under contraposition.

1. `Gen/Planted`: the output is satisfiable and σ (extended arbitrarily on free variables) satisfies it.
2. `Gen/Forcing`: every satisfying assignment agrees with σ on required variables; hence the APT output
   (R5) and the SMC solver output (R7) agree with σ there (C40, C15).
3. `Gen/Counter` (P04): an acyclic addition that violates σ (x ⇒ y with σ x = T, σ y = F) destroys
   the planted solution; a cycle among σ-true literals keeps it; so "no loops" is neither necessary nor
   sufficient. The corrected `after` text for P04 is written here.

**Gate:** C40 proved; P04 backed.

### R10 — Boolean-CFG virtual machine (must)

`Spec/Circuit.lean`: a gate graph (DAG on `Fin N`) with ops `flow` (AND of predecessors), `any` (OR),
`add` (XOR = odd count), `addneg` (XNOR), `subg` (call of a subgraph id with an input map, output map,
repetition count and optional gate bit), `tbl` (selector list × constant table); inputs = vertices with
the start token; value of a vertex = the op applied to its predecessors' values.

1. `Circuit/Order` (C49, C77 foundation): evaluating in **any** topological order gives the same values
   (the randomized `topo_kahn` order is harmless); evaluation = the recursive semantics.
2. `Circuit/Counts` (C49 "constant time"): without gated repetition, the number of executed vertices
   and examined predecessor edges per run is a function of the graph only (independent of input values
   and of the order); define `execN`, `execE` as those functions (they are Exec. N / Exec. E).
3. `Circuit/Subg`: a `subg` vertex with repetition r equals the inlined graph iterated r+1 times; counts
   add accordingly.
4. `Circuit/Gated`: with a gated repetition, counts depend on data (two-input witness): "conditional
   execution at the cost of maintaining constant time" made precise.
5. `Circuit/CodeModel` (M + F): literal transcription of `do_run_virtual` (single pass, `accepting` set,
   the elif chain) for `BITSZ = 1`; proved equal to the Spec semantics on well-formed graphs; note the
   `FLOW` "pass" branch is unreachable in one pass.

**Gate:** order independence, data-independent counts and subgraph inlining proved.

### R11 — Gate primitives, decoders, adders, DSL (must)

1. `Prims/Gates` (C42, Def. 1): multi-input AND/OR/XOR/XNOR over lists; decomposition into |X|−1
   two-input gates (sequential chain and balanced tree of depth ⌈log₂|X|⌉) for |X| ≥ 1, with XNOR =
   XOR-chain + one final XNOR (a pure XNOR chain computes XOR when |X| is odd — record it).
2. `Prims/Complete` (C43): NAND alone and NOR alone are functionally complete (every function on k
   inputs has a NAND-only and a NOR-only circuit); XNOR, NAND, NOR of a single input are negation.
3. `Prims/Sel` (C44, Def. 2): SEL with exactly one true selector equals the selected value; XOR may be
   replaced by OR under "at most one true selector" (counterexample with two true selectors); BSEL.
4. `Prims/Decoder` (C45, C47, C63): table lookup = n single-bit functions; `decoder_shift` (literal
   transcription of `decoder_shift_to_virtual` with `and_to_virtual`/`not_to_virtual` constant folding)
   outputs the one-hot vector of the input (bit i has weight 2^i), with exactly 2^{m+1} + m − 4 nodes
   (m ≥ 1) of in-degree ≤ 2; `decoder` (`decoder_to_virtual`) outputs the same one-hot vector with
   (m/2 + 2)·2^m nodes for m ≥ 2 (Σ_i popcount(i) + 2·2^m; prove the exact figure for the literal
   transcription, including m = 1) and OR in-degree m; hence the nodes-vs-edges
   trade-off. Record that the Fig. 3 comments are approximations (X).
5. `Prims/Adder` (C48, P05): ripple-carry with `s_i = a_i ⊕ b_i ⊕ c_i` computes (a + b) mod 2^n and
   the final carry; the published `c_{i+1}` version fails for a = b = 1 (1 bit); borrow subtraction
   computes (a − b) mod 2^n with final borrow [a < b]; the combined selector formula equals addition for
   s = 0 and subtraction for s = 1. Literal model of `addition_bit_to_virtual` proved equal.
6. `Prims/DSL` + `Prims/Compile`: a small typed DSL of bit-vector expressions (inputs, constants, XOR,
   AND, OR, NOT, add/sub, table lookup, shift by constant, subgraph call); a compiler to the gate graph of
   R10 built from items 1–5; **generic theorem: evaluating the compiled graph equals the DSL semantics**.

**Gate:** items 1–6 proved; the DSL compiler correctness theorem is the R12–R15 workhorse.

### R12 — AES specification facts (must)

`Spec/AES.lean`: bytes as `Fin 256` (or `Nat` < 256), GF(2^8) multiplication mod 0x11B, `xtime`, the
S-box defined as affine ∘ inverse, inverse S-box, SubBytes, ShiftRows, MixColumns, AddRoundKey, key
expansion for 128/192/256, encryption and decryption (FIPS-197).

1. `AES/SBox` (C50, P07): the S-box table (as transcribed in `aes.py`) = affine(inverse(x)) for all 256
   x; the inverse S-box = inverse(affine⁻¹(x)); the affine part is affine over GF(2) and the S-box is not
   (witness pair); `xtime b = (b ≪ 1) ⊕ (b₇ ? 0x1B : 0)` is a selection.
2. `AES/KeyExp` (C50): key expansion uses only XOR, S-box lookups and byte permutations (a syntactic
   statement on its DSL program).
3. `AES/Vectors`: FIPS-197 Appendix C vectors for AES-128/192/256 encryption and decryption (`decide`;
   split per round if slow).

**Gate:** P07 backed by declarations; vectors pass.

### R13 — AES compiler correctness (should; up to two sessions)

1. `AES/Program`: AES-128/192/256 encryption with a constant key as a DSL program mirroring
   `aes_virtual_encrypt` (key folded; S-box subgraph per byte); proof: DSL semantics = FIPS-197 spec.
2. `AES/Circuit`: with R11's compiler theorem, the compiled graph computes AES for every key and block.
3. M (D12): `validation/graph_stats.py --lean-compare`: Lean `#eval` node/edge counts of the compiled AES
   graphs vs `aes.py` counts with the same key; document every difference.

**Gate:** AES circuit correctness proved, or the remaining lemma recorded open with R11 + R12 + Python
asserts as the fallback (C51 stays M).

### R14 — Arithmetic for RSA (must for 1–6; should for 7–8)

1. `Arith/Montgomery` (C57): REDC correctness (T·R⁻¹ mod N, bound < 2N, one conditional subtraction;
   find the exact precondition on T, e.g. T < R·N), Montgomery multiplication, conversion in/out; literal
   models of `montgomeryREDC`, `montgomeryBound`, the bit-serial `montgomeryREDC_mul_eff` (Dusse–Kaliski)
   and `mul_consec_ones_virtual`'s arithmetic (product by a constant as ± shifted copies, one per run of
   ones).
2. `Arith/ModExp` (C54): square-and-multiply is correct; it uses exactly ⌊log₂ e⌋ squarings and
   popcount(e) − 1 multiplications (O(Mn + Sn)).
3. `Arith/Window` (C59): fixed-window exponentiation (literal model of `modexpMontgomeryWindow` /
   `modexp_window_to_virtual`, exponent < 2^B) correct for every w ≥ 1; cost ⌈B/w⌉ window products +
   w·(⌈B/w⌉ − 1) squarings + (2^w − 2) table products; zero windows still multiply (data independence);
   the code's choice of w minimizes ⌈B/w⌉ + 2^w − 2 (`decide` for B ∈ {32, 64, 128, 256}).
4. `Arith/Karatsuba` + `Arith/Toom` (C55, P08): the Karatsuba identity; 3^k half-size products for
   n = 2^k; Toom-k uses 2k−1 products of size n/k, hence (2k−1)^j for n = k^j, and
   n^{log_k(2k−1)} = (2k−1)^j (exact for powers); the published exponent log_k(2k) − 1 = log_k 2 would
   give fewer than n products (witness k = 3, j = 2).
5. `Arith/Square` (C56): schoolbook squaring needs n(n+1)/2 distinct partial products vs n².
6. `Arith/Word` (C62, P09): with w-bit words, schoolbook multiplication uses ⌈n/w⌉² word products vs n²
   bit products, a reduction by w² (not 2^w); linear operations by w.
7. *(should)* `Arith/Ladder` (C58): Montgomery ladder correctness; its operation sequence is independent
   of the exponent bits. `Arith/RBSD`: carry-free signed-digit addition (`to_rbsd`, `add_rbsd`) correct
   with a constant per-digit neighbourhood.
8. *(could)* NAF existence, uniqueness and weight ≤ ⌈(n+1)/2⌉.

**Gate:** items 1–6 proved.

### R15 — RSA compiler correctness (should; up to two sessions)

DSL programs for Montgomery multiplication/squaring with Karatsuba and fixed-window modexp mirroring
`modexp_window_to_virtual`, proved equal to `m^d mod N` for the fixed key sets (and generically for every
odd N); compiled-graph correctness by R11; `graph_stats.py --lean-compare` for RSA-32/64 counts.

**Gate:** RSA circuit correctness proved or recorded open (fallback: R14 arithmetic + Python asserts).

### R16 — Tables 1–2: regeneration and data checks (must; M + FD)

1. `validation/graph_stats.py`: import the generators (seeded, L05), build the AES-128/192/256 and
   RSA-32/64/128/256 graphs under the memory cap, print every candidate count (`reduce_all` raw/reduced/
   total; `show_stats` executed totals computed **statically** from subgraph invocation counts), and run
   `do_run_virtual` once for AES-128 and RSA-32 to confirm static = dynamic counts. Compare with Tables
   1–2; write `validation/data/table_regen.json`.
2. Native: build the C VMs (`generated/*vm.c`) and harnesses, run `aes` and `rsa` once each on this
   machine (evidence only; never compared as numbers with the paper).
3. `Spec/Data.lean` + `Data/Ratios` (C61, FD): per-executed-node times (4.3–7.3 ns), growth ratios
   (exponent between 2 and 3 in time), the P10 anomalies (equal 128/256 cells; non-monotone 32/64).
4. **P10 (author decision 2026-10-17):** re-measure the `C gmp` column (modular exponentiation with GMP,
   1000 operations in succession, RSA-32/64/128/256 with the fixed repository keys, x86 and x64) on this
   machine, with the same method as the paper's Table 2; first decide whether the printed 256-bit cells are
   really the 128-bit values (and whether the 32-bit row is a unit slip). If the printed cells are wrong,
   apply the minimal correction (re-measured values, labelled as such); regeneration of the column is
   allowed. Record method, machine and numbers in `validation/data/gmp_remeasure.json`.
5. Update P10/P11 with the evidence; questions to `QUESTIONS.md` (provenance: which key; which counts).

**Gate:** every Table 1–2 count is either reproduced or recorded as a mismatch in P11 with evidence.

### R17 — Transformation language, Figures 5 and 6 (must; up to two sessions)

`Spec/Lang.lean`: statements `skip | blk A | seq | if c s t | while c s | doWhile s c | goto ℓ | label ℓ
s` over abstract blocks and conditions; opaque conditions `falseCond`, `trueThenFalse` with explicit
state (SMC cell or Boolean variable toggled on each evaluation); CFG construction (one node per block,
one per condition; edges as the C semantics); trace semantics.

1. `Lang/Fig5`, `Lang/Fig6` (C14, C74): the programs (b) and (c) of each figure have the same block
   trace as (a), also under repeated execution (the toggled `trueThenFalse` state is restored: invariant
   "true at entry"); their CFGs contain an irreducible loop (R3).
2. `Lang/MinEdges` (C73): adding one edge to a path CFG never creates an irreducible loop; two suffice
   (Fig. 5b); for a one-sided conditional one edge suffices and zero do not (Fig. 6b); the simulated loop
   needs exactly one new node and three new edges.
3. Figures vs code (P18, P19): transcribe the drawn graphs (TeX `digraph` sources); compare with the CFG
   of each listing: 5(b), 6(b) match; 5(c) as drawn has no path whose trace is A·B (witness), the
   corrected graph with the injected node matches; 6(c) as drawn has the extra edge A→B. Write the P18,
   P19 `after` texts (corrected edge lists).
4. `Lang/Induce` (C75): adding an edge (x, y) with x outside a loop L(h), x not reachable from L, and
   y ∈ L\{h} makes L irreducible (and the condition "not reached from the loop" is necessary: witness).
5. `Lang/NWay` (C76, should): the construction for two-way and n-way conditionals; each opaque condition
   reads a distinct solver output.

**Gate:** C14, C73, C74, C75 proved; P18/P19 settled.

### R18 — Figure 4 code, structuring, node splitting (must for 1–2; should for 3–4)

1. `Struct/IrredLoopCpp` (C65, M + F): literal transcriptions of the three functions in
   `native/IrredLoop.cpp` (including the intentional fall-through) and of the Fig. 4 CFG semantics with
   condition oracles; all four produce the same call trace (`u`, `v`, `w`, `x`, `w_cond`, `x_cond`) for
   every oracle and both start choices.
2. `Struct/Flatten` (C31, C11, C33): every CFG equals a `while (state ≠ exit) switch (state)` program
   with one variable over |V| states (trace equivalence) — so a single state variable always suffices.
3. `Struct/StructuredReducible` (C30, C32, should): CFGs of goto-free programs (seq/if/while/do-while/
   break/continue) are reducible; with R3, an irreducible CFG has no goto-free, variable-free,
   duplication-free equivalent.
4. `Struct/Leftist` + `Struct/CFT` (C70, P17, should): Σ-complete leftist trees have ≥ 2^{n−1} leaves
   (CFT Theorem 2, by the S_n ≥ 2S_{n−1} induction), and the T1/T2 reduction argument of CFT Theorem 4:
   every reducible flow graph equivalent to K_n has ≥ 2^{n−1} nodes. Fallback: Theorem 2 only + R-class
   citation for Theorem 4.

**Gate:** items 1–2 proved; 3–4 proved or recorded open.

### R19 — Dynamic scheme, faults, static scheme end-to-end (must)

`Spec/Dynamic.lean`: a schedule = finite sequence of vertex executions of a circuit DAG (vertices may
repeat); a vertex execution reads the current values of its predecessors; "final execution" of v.

1. `Dynamic/FinalExec` (C77): if every vertex executes at least once and each vertex's final execution
   comes after the final executions of all its predecessors, the final values equal the circuit's values
   — for every such schedule (input-dependent or not). Bounded duplication: the schedule length is ≤ k·|V|
   when each vertex repeats ≤ k times.
2. `Dynamic/Fault` (C81, T5): a single fault in a non-final execution of v does not change the output;
   a fault in the final execution of an output-relevant vertex can (witness); the index of the final
   execution depends on the schedule, hence on the input when the schedule is input-tied.
3. `Dynamic/StaticScheme` (C15, C76): composition of R9 + R7 + R17: a program whose opaque conditions
   are read from the SMC solver's output on a planted formula behaves as the original program and its CFG
   has the irreducible loops of R17.

**Gate:** C77 proved; T5 proved; static scheme theorem proved.

### R20a — Security model I: definitions, correctness, immutable-code analyzers (must; the crux)

1. Literature pass (D11 list): verify each DOI; record in `THREAT_MODEL.md` each paper's adversary and
   assumptions and how it maps to the classes; check the Banescu et al. statement quoted in §5.1 ¶5.
2. `Spec/Threat.lean`: system, adversary classes, goals, `structure Assumptions` (S1–S4) exactly as
   D11. `validation/threat_audit.py` (vendored, adapted): fails if an `Assumptions` field mentions a goal
   predicate.
3. `Threat/Correct` (T1): O(P) ≡ P under S1–S3 (from R19, R11, R10).
4. `Threat/Immutable` (T2, C80): an analyzer that reads predicate cells from the static image is wrong on
   every obfuscated image whose planted values differ from the blueprint placeholders (and such images
   exist for every program with ≥ 1 opaque condition).
5. `Threat/Recover` (T3, C15, C82): an `SmcSem` analyzer recovers every predicate in O(formula size)
   (R6 cost + R7 refinement): the predicates are not computationally hard; their opacity is relative to
   analyzers lacking the SMC semantics.
6. Draft `THREAT_MODEL.md` §1–§3.

**Gate:** T1–T3 proved; threat audit passes; every literature citation verified.

### R20b — Security model II: structuring, faults, DCA, iO; §5.1 text (must)

1. `Threat/Structuring` (T4, C02, C78): node splitting on K_n-equivalent graphs ≥ 2^{n−1} nodes (R18 if
   proved, else stated as a cited hypothesis field); one state variable always suffices (R18 flattening);
   the "quadratic" overhead is that of specific restructuring algorithms (MEE count, R4).
2. `Threat/DFA` (T5): from R19.
3. `Threat/DCA` (T6, P22, P24): address-aligned traces of any two dependency-respecting schedules give
   the same multiset of (vertex, final value); repeated executions of one vertex are visible by address.
4. `Threat/NotIO` (T7, P23): two functionally equivalent programs whose obfuscations differ in vertex
   count (an observable): O is not an indistinguishability obfuscator; no VBB claim (cite Barak et al.).
5. `Threat/Necessity`: for each Si a witness that the theorem it supports fails without it.
6. Finish `THREAT_MODEL.md`. Write the `after` texts for P21–P24, and the optional P25 replacement of
   §5.1 (≤ 1 page: classes, S1–S4 in one sentence each, T1–T7 informally with Lean names, scope of what is
   not claimed). One question this round: replace §5.1 (P25) or correct only P21–P24? Fidelity check
   (D10) of every sentence.

**Gate:** T4–T7 and necessity witnesses proved; P21–P25 texts in `edits.json` with `lean_refs`.

### R19b — Protected AES/RSA variant (must; **the author implements it**; decision 2026-10-17)

The author will implement the irreducible-loop + planted-2-SAT protected variant of AES/RSA announced in §1
(P13) and the §3.1 generator (D03). This round **integrates** it and cannot start before the author says the
implementation is in the repository.

1. Review the code the author adds (generator of planted 2-SAT formulas, the Figure 5/6 transformations,
   the protected AES/RSA drivers); add it to `CODE_FIXES.md` as new code, not as a fix; native vectors on
   this machine.
2. Lean: connect it to R9 (generator), R17 (transformations) and R19 (static scheme end-to-end) as literal
   transcriptions with M evidence (D12).
3. Decide P13 with the author: if the case study now exists and is measured, the erratum becomes a
   statement of what Table 1-3 report versus the new measurements; otherwise state the scope.
4. `validation/rounds/R19b.json`.

**Gate:** protected variant builds and runs on the CI platforms (R21a); Lean models and M evidence in place;
P13 settled.

### R21a — Portable native build system (must; author decision 2026-10-17)

Every C/C++ project of the repository (`selfmodgraph`, `IrredLoop`, `aes`, `rsa`, `ecdsa`, `ecdsawhibox`, the
protected variant of R19b) gets the usual portable clean semantics:

1. A root `CMakeLists.txt` (CMake >= 3.20, C11/C++17) building every target; all build artifacts go to a
   `build/` tree outside the sources (no `x64/`, `Debug/`, `.obj` next to sources); `build/` is gitignored; the
   generated sources (`generated/*vm.c*`) are built as separate object libraries so the compiler memory stays
   bounded (R0 finding: the 10.8 MB `generated/aesvm.cpp` needs more than 1.5 GB with MSVC); GMP is found via
   `find_package`/Conan/vcpkg/`GMP_ROOT`.
2. The x86 SMC blueprint (`selfmodmodel.asm` MASM, `selfmodmodelgas.asm` GNU as) is selected per platform;
   non-x86 hosts (macOS arm64, Linux arm64) build and test everything except executing the x86 blueprint
   (CMake option `SMC_X86_EXECUTE`); macOS x86-64 (runner `macos-15-intel`) executes it.
3. Visual Studio projects keep working with VS 2022 (v143) and VS 2026 (v145): no hard-coded
   `PlatformToolset` (use `$(DefaultPlatformToolset)`), outputs under `build/` (`$(SolutionDir)build\...`), the
   CMake VS generators checked on both.
4. CI (`.github/workflows/`): Windows (2022, 2025), Linux (x86-64) and macOS (Intel and arm64) matrix; both
   the MSBuild solution and the CMake build, compile-only plus the native vectors that exist (R8); nothing
   outside `build/` may be written (`git status --porcelain` check).
5. `CONTRIBUTING.md` and `README.md` updated (commands, GMP, Conan); `validation/native.py` calls the new
   targets. Native acceptance in R21 uses these builds.

**Gate:** clean checkout builds on Windows (VS 2022 and 2026), Linux and macOS in CI; no artifact outside
`build/`; vectors pass where the platform can execute them.

### R21 — Code corrections and native acceptance (must)

1. Apply L01–L06 and D03 as decided, minimal diffs, no refactors; record each in `CODE_FIXES.md` with its
   commit hash. All land before the Palomar commit.
2. Re-run R8 vectors (Windows x64/x86, Linux x64) and R16 regeneration after the fixes; results must be
   unchanged except where a fix intends a change (L01: duplicate SCCs gone; `twosat` answers equal).
3. `validation/rounds/R21.json`.

**Gate:** vectors and counts pass after the fixes; L items have commit hashes.

### R22 — Errata list (must; no manuscript changes yet)

1. `QUESTIONS.md` items → one `AskUserQuestion` if any are still open.
2. `validation/make_errata.py` → `ERRATA.md` and `smcirred-2022-errata.tex` (title "Errata and
   clarifications — Control flow obfuscation with irreducible loops and self-modifying code"; cites Publ.
   Math. Debrecen 100 Suppl. (2022) 617–637, DOI 10.5486/PMD.2022.Suppl.5; per item: ID, page, location,
   exact before/after, one-sentence reason, confidence/evidence, Lean reference or source; T01 and B01 as
   compact grouped items; no code section). PDF in `output/pdf/`, ≤ 4 pages + one appendix page (P25 if
   chosen). Each item understandable without this repo.
3. `audit_errata.py`: inventory; every `lean_refs` name exists (generated `lean/ErrataRefs.lean` builds);
   PDF page count; no `confirmed` item without a Lean ref, number check, internal-consistency note or
   source.
4. Ask the author to review the errata PDF (the only question this round).

**Gate:** errata audit passes; PDF builds; author review requested.

### R23 — Coverage and fidelity audit (must)

1. `validation/coverage_audit.py`: every `PAPER_MAP.md` row has a class, a status
   (`proved`/`checked`/`cited`/`listed`/`open`) and a declaration (F/FT/FD), evidence path (M), URL (R) or
   note (X); every declaration exists (generated `lean/CoverageRefs.lean`); every P item maps to a claim
   row; no row `todo`; `open` rows are listed in `GAPS.md` with the fallback claim.
2. Fidelity pass (D10): reread every Spec docstring, `THREAT_MODEL.md` and the planned README section
   against the Lean statements; fix overclaims.

**Gate:** coverage audit passes; the D1 wording is justified row by row.

### R24 — Palomar package, CI, handoff (must)

1. `Spec/Paper.lean`: Props `SmcTwoSatCorrect`, `IrreducibleExtremal`, `TransformCorrect`,
   `CircuitCFGCorrect`, `SecurityModel` (D10); `Paper.lean` proves each. The informal account of
   `SecurityModel` matches `THREAT_MODEL.md` in scope (classes, S1–S4).
2. `make_challenge.py` → `Challenge.lean` (`PalomarSIL.mathematical_result : … ∧ …` with `sorry`);
   `Solution.lean`; `comparator.json` (three standard axioms, `enable_nanoda: true`). Limits: hard 1,000
   lines / 100 KiB, preferred 300 / 32 KiB (disclose if over).
3. `formalization.yaml` (schema v0.4, structure of `../SelfModTamper/lean/formalization.yaml`): license
   MIT (check `LICENSE`); sources: the PMD paper (`adapts`, author participated; DOI), CFT 2003 and
   Aspvall–Plass–Tarjan 1979 and Havlak 1997 (background or `independently-proves` where a theorem is
   reproved — decide per policy), FIPS-197 (background); honest `status.scope` naming the threat model;
   automation: Claude Opus 5.5 (planning), Claude Sonnet 5.5 (execution), Claude Code; the source note
   names the corrections by errata ID as fidelity divergences. Validate with `validate_metadata.py` after
   `refresh_policy.py`.
4. `PALOMAR_SEMANTICS.md`, `LICENSE_AUDIT.md`, README "Lean formalization" section (D1 wording, D01),
   `PALOMAR_SUBMISSION.md` (form values; `request_id: smcirred01`, `project_path: lean`).
5. CI: `proof.yml` (Linux cold build, axiom audit, `make_challenge.py --check`, `audit_errata.py`,
   `coverage_audit.py`, `threat_audit.py`, `check_tables.py`; Linux native twosat vectors; Windows job
   `native.py --all` with `--toolset v143`) and `palomar-full.yml`. Keep the existing `ci.yml`.
6. Push (if authorized) and get `proof.yml` green. Dispatching `palomar-full.yml` needs the user's
   go-ahead: the single question this round. Record run URLs in `FINAL_ACCEPTANCE.json`; hand the exact
   commit and preflight run ID to the user.

**Gate:** cold CI green, preflight passing on the recorded commit, errata reviewed, coverage audit green,
commit handed over. Then wait for the user to report the registration (entry ID and version).

### R25 — Tag and corrected manuscript (must; only after the user reports the registration)

1. One question: tag name (suggest `palomar-v1`), venue (arXiv posting of the corrected manuscript, PMD
   corrigendum, or both) and where the verification statement goes (end of §1 or a short "Formal
   verification" subsection before §6).
2. Annotated tag on the **registered** commit (message: Palomar entry ID/version, preflight run); push;
   never move or delete it.
3. `validation/apply_edits.py`: manuscript TeX + `confirmed` items (`before_tex` → `after_tex`; items
   with `before_tex = null` applied by hand and listed) + the verification statement (D1 wording; Palomar
   entry, repository URL, tag, commit) + one `biblio.bib` entry → `paper/SelfModifyingControlFlowObfuscationPaper.tex`;
   build the PDF; `paper/manuscript-v2022.diff`; latexdiff PDF in `output/pdf/`.
4. `audit_errata.py --corrected`: the diff is exactly the applied items plus the statement and bib entry;
   every sentence of the statement matches the registered Palomar statement.
5. Docs (not errata): README and `CITATION.cff` get the Palomar ID and tag (D01, D02). Update
   `PALOMAR_SUBMISSION.md`. Hand the corrected manuscript and the errata PDF to the user, who uploads them.

**Gate (= definition of done, §0):** tag pushed on the registered commit; corrected manuscript builds;
audit passes; PDFs handed to the user.

---

## MVP path (if budget is tight)

R0 → R1 → R2 → R3 → R4 (bounds 1–3, 5 witness) → R5 → R6 → R7 → R8 (2–3) → R9 → R10 → R11 → R12 → R14
(1–6) → R16 → R17 → R18 (1–2) → R19 → R20a → R20b → R21 → R22 → R23 → R24 → (user registers) → R25.
R20a/R20b are never cut (security model, user requirement). R13, R15, R8.1, R4.4, R18.3–4 and the
*should/could* items are later Palomar versions, not blockers (a later version gets its own tag).

## Risks and fallbacks

| Risk | Fallback |
|---|---|
| Havlak algorithm with union-find hard to relate to the declarative LNF (R3) | prove the declarative LNF facts directly; keep the algorithm as M evidence (`#eval` vs planning script) |
| MEE upper bound (R4.4) resists | record open; select only the proved equalities and the n−2 bound |
| SMC machine refinement (R7) too large | split: (a) visited marking + stack ↔ DFS, (b) lowlink immediates ↔ lowlink, (c) topological chain ↔ emission; prove each as a separate invariant |
| Native x86 build of the SMC solver fails on a platform | record the platform as not built; M evidence from the platforms that run (Windows x64 is the minimum) |
| `decide` on AES vectors too slow | `Nat`-based tables; split per round; `rfl` on closed terms |
| Python regeneration exceeds the memory cap | static counting only; process one graph per subprocess under the guard |
| Table counts not reproducible (key/version drift) | P11 records the mismatch with both numbers; the author decides |
| CFT formalization (R18.4) too long | Theorem 2 (leftist trees) only + citation for Theorem 4 |
| Security theorem becomes tautological | `threat_audit.py`; every assumption needs a necessity witness and must be a property of the design or the class |
| Palomar reviewer rejects elementary families | keep Definition 3/4 arithmetic and Figure checks as supporting material (D10) |
| Author unavailable for ask-author items | record both readings, choose the conservative wording, flag it in `ERRATA.md` |

## Round-close checklist (copy into each `ROUNDS.md` entry)

- [ ] full build of `SmcIrred` green under the guard
- [ ] `axiom_audit.py` clean (only `propext`, `Quot.sound`, `Classical.choice`)
- [ ] round gate commands green; `validation/rounds/Rk.json` written
- [ ] `PAPER_MAP.md`, `edits.json` (`lean_refs`), `ROUNDS.md` handoff, `CLAUDE.md` current-round line updated
- [ ] committed (and pushed) if authorized
