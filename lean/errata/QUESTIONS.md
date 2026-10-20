# Open questions for the author

Answered in R1 (2026-10-17): P10 (re-measure first), P13 (the author implements the protected variant), wording style
(minimal), inclusion (T01, B01, P17b, P25, P26, P27 all appear).

Open:

- P11: key provenance and regeneration counts (R16).
- C05 / C82: the Denuvo reference [17] content and the Banescu et al. quotation (opaque predicates defeated only in simple contrived scenarios) could not be located online; can the author supply the passages?
- P06, P28: wording is proposed in `edits.json`; confirm in R22.
- P25 / R20b: replace Section 5.1 by the proposed formal subsection (appendix of the errata PDF), or apply only P21-P24 and drop P25?
- Review of the errata PDF `output/pdf/smcirred-2022-errata.pdf` (R22 gate).
- L09: `generated/aesgraph.c` (the straight-line graph variant `AES_128_obf_encrypt`) has no emitter; reinstate the emitter (`graph_to_c`, needs `pred`, `deporder`) or drop the graph column/variant?
- L06 / P11: the AES key is 0x12 in every byte; keep it (and state so in the paper) or regenerate with another key?
- §4.2 (p. 627): "NAF and MOF and their windowed forms ... reduce the hamming weight of the exponent": Lean shows the MOF never lowers the weight of a number and raises the total over all n-bit strings (`Arith.mof_not_lighter`, `mofTotal_closed`) and the windowed NAF is never heavier than binary (`Arith.wnaf_wt_le_popc`); the paper does not define a windowed MOF. Add an erratum item for the MOF half of the sentence, or leave it as a remark?
