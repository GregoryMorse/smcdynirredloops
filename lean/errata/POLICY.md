# Errata policy

Scope: the **text, tables, figures, captions and references** of G. Morse, M. Alqaradaghi, T. Kozsik, *Control flow
obfuscation with irreducible loops and self-modifying code*, Publ. Math. Debrecen 100 (Suppl.) (2022) 617-637,
DOI 10.5486/PMD.2022.Suppl.5. There is no arXiv version: every quotation is of the **published** version
(`validation/reference/pmd.pdf`, SHA-256 `e89a803c...`, never committed). Code, README and CITATION fixes are **not**
errata (the repository has no tagged release and the paper links only the repository as a whole); they live in
`lean/CODE_FIXES.md`.

1. Preserve the published construction; make the smallest local correction that states the intended, provable result.
2. Quote the published version exactly. Never attribute PDF-extraction artifacts (misplaced accents, scrambled tables,
   dropped hyphens) to the paper. Quote tables from the rendered page.
3. An item is `confirmed` only when it is certain: a Lean declaration, arithmetic on the paper's own numbers, an
   internal inconsistency, or a primary source. `confidence: inferred` states in `evidence` what the replacement
   wording rests on. Anything else is `ask-author` and is not applied until answered. `optional` items are real but
   minor; the author decides whether they appear.
4. Every real mistake is fixed however minor (author, 2026-10-21); how items are counted is unimportant, so each independent mistake is its own item: one typo per T item (T01-T17), one reference per B item (B01-B05). Every item is self-contained.
5. Evidence (native runs, regenerated counts, brute-force checks) is never called proof; only a Lean declaration is.
6. The list is complete: every real mistake is recorded. The wording of each correction stays minimal, except where a missing threat model or a conflated claim needs a fuller statement (P25, P06).
7. The dissertation is out of scope. This list is self-contained; the dissertation-wide list is built separately.
8. `edits.json` is the single source. Fields: `id`, `page` (journal page), `location`, `kind`
   (`replace|clarify|group`), `before` (published wording), `before_pdf` (`[{page, text}]`, found on that page of the
   published PDF text), `before_tex` (manuscript fragment(s), found exactly once; `null` if the publisher's wording
   differs), `after`, `after_tex`, `reason` (one sentence), `class`
   (`formal|mechanical|editorial|typographical|bibliographic`), `status`
   (`confirmed|ask-author|withdrawn|optional`), `confidence` (`certain|inferred`), `evidence`, `lean_refs`, `source`.
   `python validation/audit_errata.py` checks `before_pdf` and `before_tex`.
9. Presentation: the errata list (`ERRATA.md`, and a short PDF from `validation/make_errata.py`) is committed. No corrected
   manuscript is produced until the author asks (user decision 2026-10-17).
