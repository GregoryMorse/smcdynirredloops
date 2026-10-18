# smcdynirredloops

[![DOI](https://img.shields.io/badge/DOI-10.5486%2FPMD.2022.suppl.5-blue)](https://doi.org/10.5486/PMD.2022.suppl.5)
[![Journal](https://img.shields.io/badge/Journal-Publ.%20Math.%20Debrecen-green)](https://publi.math.unideb.hu/load_doi.php?pdoi=10_5486_PMD.2022.suppl.5)
[![Conference](https://img.shields.io/badge/Conference-CECC'21-orange)](https://konferencia.unideb.hu/en/program-central-european-conference-cryptology-2021)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)

Reference implementation and research code for **control-flow obfuscation using irreducible loops and self-modifying code**, with cryptographic virtual-machine generation for AES, RSA, and ECDSA.

## Citation

If you use this work, please cite the journal paper:

> Morse, G., Alqaradaghi, M., & Kozsik, T. (2022).
> **Control flow obfuscation with irreducible loops and self-modifying code.**
> *Publicationes Mathematicae Debrecen*, **100**(Supplementum), 617–637.
> DOI: [10.5486/PMD.2022.suppl.5](https://doi.org/10.5486/PMD.2022.suppl.5)
> PDF: <https://konferencia.unideb.hu/sites/default/files/upload_documents/10_5486_pmd.2022.suppl_.5.pdf>

### Conference presentation

> Morse, G., Alqaradaghi, M., & Kozsik, T. (2021).
> **Control flow obfuscation with irreducible loops and self-modifying code.**
> 21st Central European Conference on Cryptology (CECC'21), June 24, 2021, Debrecen, Hungary (virtual).
> <https://konferencia.unideb.hu/en/program-central-european-conference-cryptology-2021>

### Extended abstract

> Morse, G., Alqaradaghi, M., & Kozsik, T. (2021).
> **Control flow obfuscation with irreducible loops and self-modifying code.**
> In *21st Central European Conference on Cryptology – Book of Abstracts*, pp. 40–41.
> PDF: <https://konferencia.unideb.hu/sites/default/files/upload_documents/book_of_abstracts_v6.pdf>

A machine-readable citation is available in [`CITATION.cff`](CITATION.cff).

## What this repository contains

| Directory | Contents |
|---|---|
| `python/` | Source-of-truth Python generators and algorithm logic |
| `generated/` | Auto-generated C VM artifacts (output of `python/` emitters) |
| `native/` | Hand-written C/C++/ASM sources and Visual Studio solution |
| `scripts/` | Helper scripts (regeneration, CI) |

### Python source (`python/`)

| File | Role |
|---|---|
| `rsa.py` | RSA key generation, modular exponentiation VM emitter |
| `aes.py` | AES-128/192/256 VM emitter |
| `ecdsab.py` | ECDSA P-256 VM emitter (sign/verify with Montgomery arithmetic) |
| `virt.py` | Core virtual-machine graph engine and C code emitter |
| `graph.py` | Graph algorithms (SCC, topological sort, 2-SAT) |
| `ecdsa.py` | Pure-Python ECDSA reference (used by `ecdsab.py`) |

### Native C/C++ sources (`native/`)

| File | Role |
|---|---|
| `selfmodgraph.cpp` | Self-modifying code graph engine (main research program) |
| `IrredLoop.cpp` | Irreducible loop construction without `goto` |
| `selfmodmodel.asm` | x86-64 self-modifying assembly blueprint (MASM) |
| `selfmodmodelgas.asm` | x86-64 self-modifying assembly blueprint (GAS) |
| `rsa.c` | RSA C harness (GMP-backed) |
| `ecdsa.c` / `dECDSA.c` | ECDSA P-256 C implementation |
| `ecdsamain.c` | ECDSA stdin/stdout signing wrapper |
| `ecdsawhibox.c` | Whitebox ECDSA VM (WhibOx 2021 entry, checked-in generated) |
| `aes.c` / `aesmain.c` / `aesvm.cpp` | AES harness and VM runner |

## Prerequisites

- **Python 3.10+** for generator scripts
- **Visual Studio 2019–2026** (v145 toolset) for C/C++ projects
- **GMP 6.3+** via Conan 2.x (recommended) or manual install
- Python packages: `py -m pip install -r requirements.txt`

## Regenerating generated C artifacts

All generated C VM files are written to `generated/` by:

```powershell
# From repository root — regenerates RSA, AES, and ECDSA VMs
powershell -File scripts\regenerate.ps1
```

Or individually:

```powershell
py python\rsa.py      # → generated/rsa{32,64,128,256,512,1024}vm.c + vmstr.c
py python\aes.py      # → generated/aes{128,192,256}vm.c + vmstr.c + aesgraph.c
py python\ecdsab.py   # → generated/ecdsa256vm.c + ecdsa256vmstr.c
```

## Building the C/C++ projects (Visual Studio)

Open `native\selfmodgraph.sln`. GMP is resolved via `native\gmp.props`.

**Quickstart with Conan 2.x (recommended):**

```powershell
pip install "conan>=2.0"
powershell -ExecutionPolicy Bypass -File native\conan_setup.ps1
```

See [`CONTRIBUTING.md`](CONTRIBUTING.md) for alternative GMP setup options (environment variable or local `deps/` folder).

## Repository conventions

- **`python/`** is the canonical source. Generated C files are derived outputs.
- **`generated/`** is populated by `scripts/regenerate.ps1`; files there are gitignored (except `ecdsawhibox.c` which was a one-time contest entry).
- Build output folders and IDE user files are gitignored.

## Security and research notice

This project contains cryptographic implementations intended for **research and experimentation**. It is not audited or hardened for production use.

## Author

Gregory Morse — [gregory.morse@live.com](mailto:gregory.morse@live.com) — [GitHub](https://github.com/GregoryMorse)

## License

See LICENSE.

## Citation

If you use this code in research, please cite the paper above and include a repository citation. See CITATION.cff for machine-readable metadata.

## Scope note

The irreducible-loop-protected AES/RSA variant announced in the paper and the planted 2-SAT generator of Section 3.1 are not implemented in this repository: `IrredLoop.cpp` implements the stand-alone irreducible-loop constructions, and the AES/RSA/ECDSA drivers execute the graph virtual machine without irreducible-loop protection.
