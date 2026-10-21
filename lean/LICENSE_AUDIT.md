# License audit

* Repository license: MIT, `LICENSE` at the repository root (copyright 2026 Gregory Morse); `lean/formalization.yaml`
  `project.license: "MIT"` and `CITATION.cff` `license: "MIT"` agree. `validation/palomar/validate_metadata.py` checks the
  text of `LICENSE` contains "MIT License" (it does not claim authoritative SPDX detection).
* Lean sources: no dependency (`lean/lake-manifest.json` has no packages); core Lean 4 only (Apache-2.0, not redistributed).
* The published paper, its TeX/bib/class files and the PDF are not in the repository (gitignored `validation/reference/`);
  the errata quote only the short passages they correct.
* Native sources: GMP is a build-time download pinned by SHA-256 in CI (LGPL/GPL dual license), not redistributed.
* Third-party material is cited in `formalization.yaml` as background only (Aspvall–Plass–Tarjan 1979, Havlak 1997,
  Carter–Ferrante–Thomborson 2003, FIPS 197); no text or code is copied from them.
