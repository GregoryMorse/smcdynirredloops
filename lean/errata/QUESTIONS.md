# Questions for the author

All questions are answered (R1 2026-10-17; 2026-10-21). Nothing is open. Record of the decisions:

* **P06 (circuit synthesis hardness, pp. 624-625):** needed; the replacement text separates circuit satisfiability (NP-complete),
  the Minimum Circuit Size Problem from a truth table (in NP, NP-hardness open for single-output circuits, known for DNF
  formulas and, under randomized reductions, for multi-output circuits) and minimization of a given circuit (coNP-hard). The
  second occurrence (p. 625) is its own item P30.
* **P28 ("exponential growth of multiplication"):** wrong; applied (polynomial, super-quadratic).
* **P25 (Section 5.1):** the full threat-model replacement stays; the paper's omission of a threat model is itself the error.
* **P10 (Table 2, gmp column):** applied with an estimated row 256 (the exact cells need the original machine).
* **P11 / AES key:** the author's first answer was to generate a random fixed key (the paper says "fixed randomly generated key"). It was tried on 2026-10-21 and reverted: the AES graph size depends on the key bits (a random key gives AES-192 61379/267335 and AES-256 71645/312001 instead of the printed 61364/267320 and 71568/311924), and only the key 0x12 in every byte reproduces the printed Tables 1-2 exactly. So the tables were built with 0x12 and the paper's wording is the error: P11 is an erratum (confirmed). Author: say if you prefer to regenerate the tables with a random key instead.
* **NAF/MOF (p. 627):** one item, P31 (the MOF does not in general reduce the Hamming weight; windowed NAF does not exceed
  the binary weight).
* **C05 / C82:** the Denuvo paper and the Banescu paper were read (author's ELTE copies, 2026-10-21): "defeated" is supported by
  the Denuvo paper, the Banescu statement is a fair paraphrase; no erratum (PAPER_MAP rows C05, C82).
* **L09:** the straight-line graph variant is reinstated (GAPS G43).
* **Counting:** items are split per independent mistake (T01-T17, B01-B05); the errata PDF is reviewed with the author's
  approval of these decisions.
