# Vendored infrastructure

Source: `../SelfModTamper` at commit `69a9d34` (same author). Names adapted (`SmcTamper`→`SmcIrred`, `PalomarSMT`→`PalomarSIL`, `selfmodtamper`→`smcdynirredloops`); behaviour kept.
Hash = first 16 hex of SHA-256 of the source file / of the file as vendored. **Paper-specific scripts are copied unadapted** (they still name the SelfModTamper paper and are adapted in the round that first uses them): `audit_errata.py` and `make_errata.py` (R1/R22), `make_challenge.py` (R24), `coverage_audit.py` (R23), `threat_audit.py` (R20a).

| Path | Source hash | Vendored hash | Edits |
|---|---|---|---|
| `validation/limited_run.py` | `ec77aa6b083055a6` | `ec77aa6b083055a6` | name substitution only |
| `validation/memory_budget.py` | `d58355842b20eb80` | `34824ef6d5650cc2` | name substitution only |
| `validation/lean_build.py` | `b013080b94ce9475` | `b013080b94ce9475` | name substitution only |
| `validation/build_modules.py` | `2615565397eb5d22` | `ee0094262ed7abb1` | name substitution only |
| `validation/axiom_audit.py` | `53d82f95c5b5fb89` | `2d217b6d524341c5` | name substitution only |
| `validation/build_tex.py` | `a818d89518f75379` | `4006c952793e2820` | name substitution only |
| `validation/audit_errata.py` | `cd9ee77252ef019c` | `79de91f8918ed095` | name substitution only |
| `validation/make_errata.py` | `8d94fc3c04a6cba3` | `1cdef09b4a2be080` | name substitution only |
| `validation/coverage_audit.py` | `3dd437e5a5add620` | `2d2a70353a659247` | name substitution only |
| `validation/threat_audit.py` | `838a46126c0f8ddf` | `ad12764fda79323d` | name substitution only |
| `validation/make_challenge.py` | `1cd622059badce1d` | `a0e14c3d3ccdacf7` | name substitution only |
| `validation/ci/axioms.py` | `56b7c5bfd8137681` | `960dadee1ab48bb1` | name substitution only |
| `validation/ci/linux.sh` | `9491db4e00943d5a` | `25c52a2e46d51d9d` | name substitution only |
| `validation/palomar/fetch_policy_assets.py` | `532777ee8794341d` | `5eb96bfd76bcd4f9` | name substitution only |
| `validation/palomar/refresh_policy.py` | `ac37ac83c1b3cc2a` | `238b3fc0efb7381c` | name substitution only |
| `validation/palomar/validate_metadata.py` | `6f91be7c4509ca3e` | `6f91be7c4509ca3e` | name substitution only |
| `.github/workflows/proof.yml` | `1ff0f8700c2038de` | `cca2c3bdc1acdeb4` | name substitution only (branch `main` kept in proof.yml until R24) |
| `.github/workflows/palomar-full.yml` | `1074046ece021fc1` | `1074046ece021fc1` | name substitution only |
| `validation/build_tex.py` | `a818d89518f75379` | `4006c952793e2820` | rewritten for the PMD manuscript: tex name, .cls copied, -shell-escape (graphviz), accept latexmk exit 12 from the first-pass dot message |
| `validation/check_tables.py` | `1dc74b77079ea362` | `fab4a899147f6252` | rewritten (not copied): checks paper_tables.json against the PMD manuscript TeX |

Written fresh (not vendored): `validation/fetch_reference.py`, `validation/native.py` (MSBuild per project, compile only), `validation/check_tables.py`.

Templates not yet copied (copied and adapted by the round that needs them): `lean/errata/{POLICY.md,edits.json}` (R1), `lean/{formalization.yaml,comparator.json,PALOMAR_SEMANTICS.md,PALOMAR_SUBMISSION.md,LICENSE_AUDIT.md,PAPER_MAP.md,THREAT_MODEL.md}` (R1, R20a, R24).
Added in R2: `validation/lean_scratch.py` (SelfModTamper `69a9d34`, verbatim; runs one scratch Lean file under the guard).
