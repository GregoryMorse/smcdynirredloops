# Changelog

All notable changes to this project are documented here.

Format follows [Keep a Changelog](https://keepachangelog.com/en/1.0.0/).

---

## [Unreleased]

### Fixed
- `selfmodgraph.cpp` `tarjan_scc`: the outer loop skips nodes that were already visited (a visited SCC root was emitted again as a duplicate singleton component); `twosat` answers are unchanged. The `tarjan_scc` partition property is now checked by the native 2-SAT harness.
- `virt.py`: `set_bit_range` replaces the slice `[start, end)` (it used a stride), `reduce_all` no longer fails when `outmap` is `None`, the debug `print(tbl)` of `modexpMontgomeryWindow` and the unfinished unused `mul_window`/`mul_const_window` are removed; optional `SMCIRRED_SEED` environment variable seeds the graph shuffles for reproducible regeneration (default unchanged).
- `aesmain.c`, `rsa.c`: the virtual-machine column is labelled "Graph VM"; the AES-192/256 straight-line stubs are documented.

### Notes
- `native/protected.c`: planted 2-SAT generator (Section 3.1) and protected AES-128 and modular exponentiation (Figures 5(b), 6(b)), with a native self-test; the graph drivers remain unprotected.

---

## [1.0.0] — 2022

### Added

**Control-flow obfuscation framework**
- `IrredLoop.cpp` — C++ implementation of irreducible loops without `goto` (nested `do`/`while` construction) and with `goto`, based on Erosa & Hendren (1994).
- `selfmodgraph.cpp` — Self-modifying code graph engine: Tarjan strongly-connected-components (SCC), 2-SAT graph construction, topological sort, and blueprint-based self-modifying node dispatch.
- `selfmodmodel.asm` / `selfmodmodelgas.asm` — x86-64 self-modifying assembly blueprints for MASM (Windows) and GAS (Linux/macOS) targeting Tarjan SCC traversal.

**AES virtualization (AES-128 / 192 / 256)**
- `aes.c` — Reference AES implementation (correct, non-obfuscated) used as a baseline.
- `aesmain.c` — Entry point that drives the boolean-circuit VM for obfuscated AES encryption.
- `aesgraph.c` — Thin wrapper exposing `AES_128_obf_encrypt` via the virtual-machine path.
- `aes.py` — Python generator: encodes AES key schedules and round logic as boolean circuits, emits `aes128vm.c`, `aes192vm.c`, `aes256vm.c` and matching `*vmstr.c` string-initialiser variants.

**RSA virtualization (RSA-32 / 64 / 128 / 256 / 512 / 1024)**
- `rsa.c` — RSA VM driver: loads generated graph tables and executes the boolean-circuit VM for modular exponentiation.
- `rsa.py` — Python generator: Miller–Rabin prime generation, safe-prime construction, full RSA key generation, and boolean-circuit VM emission for multiple bit widths.

**ECDSA-256 virtualization**
- `ecdsa.c` — ECDSA-256 VM driver using the generated boolean-circuit graph.
- `dECDSA.c` — Reference ECDSA-256 signing implementation over NIST P-256 using GMP, used for correctness validation and key generation.
- `ecdsamain.c` — stdin/stdout signing harness for the obfuscated ECDSA VM.
- `ecdsawhibox.c` — White-box ECDSA variant generated for the WhibOx contest.
- `ecdsab.py` — Python generator: Montgomery arithmetic, point-addition circuits, ECDSA signing logic, and full boolean-circuit VM emission for P-256.

**Python support libraries**
- `virt.py` — Core virtualization helpers: BSD/RBSD recoding, Montgomery REDC, modular inversion, carry-save arithmetic, boolean-circuit graph construction and C code emission.
- `graph.py` — Graph algorithms: successor-to-predecessor conversion, Kahn topological sort, level-aware topological sort.

**Repository infrastructure**
- `requirements.txt` — Python dependencies (`pycryptodome`, `python-sat`, `pycryptosat`).
- `.github/workflows/ci.yml` — GitHub Actions CI: dependency install and syntax check across Python 3.10 / 3.11 / 3.12.
- `CITATION.cff` — Machine-readable citation metadata.
- Visual Studio solution and project files under `cpp/selfmodgraph/` for Windows builds.
- Conan package manifest for GMP dependency (`cpp/selfmodgraph/conanfile.txt`).

[Unreleased]: https://github.com/GregoryMorse/smcdynirredloops/compare/v1.0.0...HEAD
[1.0.0]: https://github.com/GregoryMorse/smcdynirredloops/releases/tag/v1.0.0
