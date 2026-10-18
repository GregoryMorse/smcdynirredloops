# smcdynirredloops — Lean verification of "Control flow obfuscation with irreducible loops and self-modifying code"

Goal: Lean-verify every mathematical, algorithmic and security statement of Morse, Alqaradaghi & Kozsik,
Publ. Math. Debrecen 100 (Supplementum) (2022) 617–637, DOI 10.5486/PMD.2022.Suppl.5 (security statements
relative to an explicit threat model), fix the legacy code, produce a paper-only errata list, get the
development registered on Palomar, then tag the registered commit and produce a corrected manuscript that
states its Lean verification, the Palomar entry and the tag.

**Every session:** read `lean/FORMALIZATION_PLAN.md` §0–§4, then only the current round's section
(state and handoff notes: `lean/ROUNDS.md`). Decisions in plan §2 are settled; ask the user before
deviating. Do not browse sibling repositories beyond the paths the plan names.

**Current round: R21a** (R0–R5 done 2026-10-17, R6, R6b, R6c, R7, R3b, R4c, R8, R9, R10, R11, R12, R14, R17, R18, R19, R20a, R20b, R22 (errata list) 2026-10-18, R19c 2026-10-19; R8b, R13, R14b, R15, R16, R17b, R18b pending). Update this line at each round close.

## Hard rules

- Run every build/test serially through `python validation/limited_run.py -- <cmd>` (1.5 GB aggregate
  cap, Lean `-M768 -j1`) (copied in R0; call it with `python`, not `py -I`). A capped failure is a failed check; never bypass the
  guard. Do not kill unrelated processes.
- No SSH/remote servers. Cold full builds and Palomar runs use GitHub Actions.
- Pin: Lean `leanprover/lean4:v4.35.0-rc3`, no Mathlib (plan D4). Do not change either without asking.
- No `sorry`/`admit` (except `lean/Challenge.lean`), no `axiom`, `native_decide`, `bv_decide`,
  `Lean.ofReduceBool`, `unsafe`. Only `propext`, `Quot.sound`, `Classical.choice` may appear.
- Processors, compilers, decompilers and timers are black boxes: they enter only as contract fields or
  as mechanical evidence (plan D2), never as axioms or proved claims about real systems.
- The security model (plan D11, rounds R20a–R20b) is required by the user. Assumptions must be
  structural, never "the attacker fails" (`validation/threat_audit.py`). Each one needs a necessity
  witness. Never cut these rounds for budget.
- Statement-level definitions live in `lean/SmcIrred/Spec/` (core imports only, `@[expose]`);
  `Challenge.lean` is generated from them.
- Errata: paper text, tables, figures, captions and references only, quoted exactly from the **published**
  version (PDF in gitignored `validation/reference/`, hash-checked by `validation/fetch_reference.py`);
  each item self-contained; typos grouped in T01, references in B01. Code/README/CITATION fixes are
  **not** errata (no tagged release yet) and go to `lean/CODE_FIXES.md`. The dissertation is out of
  scope: do not read or quote it.
- OneDrive (`D:\OneDrive\Documents\Projects\ELTE\smcdynirredloops\`) is reference material only: read,
  never write. All changes stay inside this repository.
- Evidence (native runs, regenerated counts, listings, data checks) is never described as proof. Prose
  (docstrings, YAML, Markdown, the corrected manuscript's statement) must claim no more than the Lean
  hypotheses give.
- Gaps: never drop one. Every open obligation, narrowed claim or deferred item goes into `lean/GAPS.md` with an owner round and a
  fallback claim; round closes update it (new rows, closed rows). R23/R24 fail while a row has no owner.
- Economy: one round per session; build only touched modules until round close; three focused attempts
  per obstacle, then narrow the statement and record an open obligation in `lean/PAPER_MAP.md`; at most
  one batched question to the user per round.

## Authorizations

- Commits and pushes in this repository: **authorized** (user, 2026-10-17): commit at green increments and push to
  `origin master`; never force-push, never move or delete a tag. Commit messages end with the attribution line from
  the system prompt.
- The **errata list is committed**. The published PDF, the author's manuscript TeX/bib/cls and `output/pdf/manuscript-2022.pdf`
  are **never committed** (they stay in gitignored `validation/reference/`). No corrected manuscript is produced for now: only
  the errata list (R25's manuscript step is deferred until the user asks); the tag name is still to be asked in R25.
- Order: Palomar first, then the repository tag (R25, name confirmed with the user), then the corrected
  manuscript; the venue (arXiv posting and/or Publ. Math. Debrecen corrigendum) is the author's choice.
- Dispatching `palomar-full.yml` needs the user's go-ahead (ask in R24). Palomar submission and
  registration are always done by the user; never submit or register.
