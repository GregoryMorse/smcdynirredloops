# Security Policy

## Research disclaimer

This repository is **research and educational code** associated with the paper:

> Morse, Gregory; Alqaradaghi, Midya; Kozsik, Tamas. Control flow obfuscation with irreducible loops and self-modifying code. *Publicationes Mathematicae Debrecen* 100 (Supplementum), 617–637 (2022).

The cryptographic implementations of AES, RSA, and ECDSA in this repository are provided to demonstrate obfuscation and virtualization techniques. They are **not** audited, hardened, or intended for use in production systems. Do not use any generated C artifacts or VM code from this repository in security-critical applications.

## Scope

Security reports are in scope for:

- Correctness issues in the Python generation logic (`aes.py`, `rsa.py`, `ecdsab.py`, `virt.py`, `graph.py`) that cause generated artifacts to produce incorrect cryptographic output
- Bugs in the reference C implementations (`aes.c`, `rsa.c`, `ecdsa.c`, `dECDSA.c`) that silently produce wrong results
- Vulnerabilities in the self-modifying code assembly model (`selfmodmodel.asm`, `selfmodmodelgas.asm`) that could affect researchers running the code

Out of scope:

- Side-channel attacks on the generated VM code (the obfuscation is not a side-channel defence)
- Timing or power analysis weaknesses (not a goal of this research)
- Issues specific to SageMath (`aes.sage.py`) or optional tooling not part of the core generation pipeline

## Reporting a vulnerability

Please **do not** open a public GitHub issue for security vulnerabilities.

Send a private report by email to:

**Gregory Morse** — gregory.morse@live.com

Include in your report:

- A description of the vulnerability and its impact
- Steps to reproduce or a minimal proof-of-concept
- Affected files and version / commit hash

You should expect an acknowledgement within 7 days. Once a fix is confirmed, a coordinated disclosure timeline will be agreed upon before any public announcement.
