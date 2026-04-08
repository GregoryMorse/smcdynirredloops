# smcdynirredloops

Reference implementation and research code for control-flow obfuscation with irreducible loops and self-modifying code, including cryptographic graph/VM generation for AES, RSA, and ECDSA.

## Research context

This repository is part of the work described in:

Morse, Gregory; Alqaradaghi, Midya; Kozsik, Tamas. Control flow obfuscation with irreducible loops and self-modifying code. Publicationes Mathematicae Debrecen 100 (Supplementum), 617-637 (2022).

Paper PDF:

https://konferencia.unideb.hu/sites/default/files/upload_documents/10_5486_pmd.2022.suppl_.5.pdf

Project maintainer:

- Gregory Morse (GitHub: GregoryMorse, email: gregory.morse@live.com)

## What this repository contains

- Python generators and algorithm logic:
  - aes.py
  - rsa.py
  - ecdsab.py
  - graph.py
  - virt.py
- Generated C artifacts (VM and VM string formats) used by native projects.
- C and C++ project files under cpp/selfmodgraph for Visual Studio builds.

## Repository conventions

- Source of truth is Python generation logic.
- Generated C artifacts should be regenerated from Python scripts when logic changes.
- Build output folders and IDE user files are ignored.

## Prerequisites

- Windows with Python 3.10+
- Optional: Visual Studio Build Tools / Visual Studio 2019+ for C/C++ project builds
- Python dependencies in requirements.txt

Install dependencies:

```powershell
py -m pip install -r requirements.txt
```

## Regenerating generated C artifacts

Run from repository root:

```powershell
py rsa.py
py aes.py
py ecdsab.py
```

These scripts generate VM artifacts such as:

- RSA: rsa32vm.c, rsa64vm.c, rsa128vm.c, rsa256vm.c, rsa512vm.c, rsa1024vm.c and matching vmstr files
- AES: aes128vm.c, aes192vm.c, aes256vm.c and matching vmstr files
- ECDSA: ecdsa256vm.c and ecdsa256vmstr.c

## Build notes

- Visual Studio solutions/projects are under cpp/selfmodgraph.
- Generated files are consumed by project files there.

## CI strategy

The default CI in this repo validates:

- Python dependency installation
- Python syntax checks for core scripts

It intentionally avoids running full generator scripts in CI because generation is heavy and can modify workspace state.

## Security and research warning

This project contains cryptographic implementations intended for research and experimentation. It is not audited or packaged as a hardened production cryptography library.

## License

See LICENSE.

## Citation

If you use this code in research, please cite the paper above and include a repository citation. See CITATION.cff for machine-readable metadata.
