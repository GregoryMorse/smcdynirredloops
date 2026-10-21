# Questions for the author

Errata policy reminder: paper text, tables, figures, captions and references only; minimal but complete. Code that the
paper does not mention is fixed in the repository (`lean/CODE_FIXES.md`), not listed as an erratum.

Answered earlier (R1, 2026-10-17): P10 (re-measure first), P13 (the author implements the protected variant), wording style
(minimal), inclusion (T01, B01, P17b, P25, P26, P27 all appear).

Answered 2026-10-21: see "Decided" at the end (L09, AES key, NAF/MOF).

## Open: items where only the author can decide or supply a fact

### 1. P11 — which AES key, and what is fixed by it (Section 4.3, Tables 1-2)

The paper says the AES graphs were built with "a fixed randomly generated key". The repository's generator
(`python/aes.py`, `gen_aes`) uses the key `0x12 0x12 ... 0x12` (every byte 0x12), which is a constant, not a random key.
Regenerating the tables (evidence only, `validation/data/table_regen.json`) reproduces the printed Nodes, Edges and
Exec. N columns exactly; Exec. E (the executed-edge count) varies from run to run with the random dependency order
(AES-256: 541018 to 541694), so no key fixes it. The current proposed erratum P11 says: state the key used, and say
Exec. E is not determined by it.
Question: is P11 as proposed acceptable, or should it be dropped (see "Decided", AES key: a note only)?

### 2. C05 and C82 — two citations that could not be checked

* C05 (Section 1, paragraph 1): the paper says Denuvo was defeated, citing [17] (Karthik, Amritha, Sethumadhavan, ICCCNT
  2020). That paper is not available online, so the claim is unverified. VMProtect [16] was checked.
* C82 (Section 5.1, paragraph 5): the paper attributes to Banescu, Ochoa and Pretschner (and follow-ups) the statement that
  opaque predicates are defeated only in simple, contrived scenarios. I searched SPRO 2015, ACSAC 2016 and USENIX 2017; the
  accessible text contains no such sentence.
Neither claim is used by any Lean statement; both are recorded as unverified non-claims (GAPS G04). Question: can you
supply the passage (page and wording) for either, or should the sentence stay as is without an erratum?

### 3. P06 and P28 — two proposed wording corrections (confirm or reject)

* P06 (pp. 624-625): the paper says "using logic synthesis to construct an optimal circuit is NP-hard based on the circuit
  SAT problem". Circuit satisfiability does not by itself give NP-hardness of optimal synthesis from a truth table; for one
  output that is the open Minimum Circuit Size Problem (known NP-hard for DNF formulas, and for multi-output circuits only
  under randomized reductions); minimizing a given circuit is coNP-hard. The proposed text asks the author to say which problem
  is meant and cite it. Question: keep P06 as a clarification, or drop it?
* P28 (p. 627, Section 4.2): "the exponential growth of multiplication as the bit size gets to realistic cryptographic sizes".
  The node count of a multiplication circuit is polynomial (schoolbook n^2, Karatsuba n^1.58), and the paper's own Table 2
  grows polynomially. Proposed replacement: "super-quadratic (polynomial) growth". Question: apply it?

### 4. P25 — replace Section 5.1 or only fix it?

Section 5.1 (security) states claims without a threat model. Two ways to correct it:
* (a) P25: replace the whole subsection by a formal one in the errata appendix: a system (structured program, the static
  scheme of Figures 5-6, solver-generated opaque conditions), adversary classes described as capabilities (Imm, SmcSem,
  Struct, Trace/Dca, Fault), assumptions S1-S4, and results T1-T7, each a Lean theorem. It says, for example, that an
  analyzer that implements the machine semantics recovers every opaque cell, so the scheme's opacity is relative to analyzers
  without it, not computational hardness.
* (b) only the small corrections P21-P24 (specific sentences of Section 5.1), dropping P25.
(a) is what the Lean security model proves and is the only way the paper's security statements match the verified ones; (b)
is shorter but leaves the statements without a stated model. Question: (a) or (b)?

### 5. Review of the errata PDF

`output/pdf/smcirred-2022-errata.pdf` (generated, not committed) is the R22 review gate. Question: any item to change?

## Decided (2026-10-21, author)

* **L09 (code, not an erratum):** `generated/aesgraph.c`, the straight-line graph variant `AES_128_obf_encrypt`, has no emitter
  in the repository (`graph_to_c` is commented out in `python/virt.py`; it needs `pred` and `deporder`), so only a stub is
  linked in CI. Decision: reinstate the emitter. Tracked as GAPS G43 and CODE_FIXES L09; no paper change.
* **AES key 0x12 (L06):** if the constant key is only a dubious choice and not a mistake in the paper, it is a note, not an
  erratum. The code comment in `gen_aes` stays; the paper's "fixed randomly generated key" is mentioned only through P11's
  "state the key used" (item 1 above asks whether even that should go).
* **NAF/MOF (Section 4.2, p. 627):** the paper says "NAF and MOF and their windowed forms ... reduce the hamming weight of the
  exponent". Lean shows the windowed NAF is never heavier than binary (`Arith.wnaf_wt_le_popc`), but the MOF never lowers the
  weight of a number and raises the total over all n-bit strings (`Arith.mof_not_lighter`, `mofTotal_closed`), and the paper
  defines no windowed MOF. The author's ruling: either way is fine. Chosen: one combined erratum item (one sentence, one
  correction covering both the MOF claim and the undefined windowed MOF), to be added in R22 wording.
