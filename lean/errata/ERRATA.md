# Errata and clarifications — Control flow obfuscation with irreducible loops and self-modifying code

Against Publ. Math. Debrecen 100 (Suppl.) (2022) 617–637. Generated from `edits.json` by `validation/make_errata.py`.

## P01 — Section 2, paragraph 1 (p. 619; Lean; certain)

**Before:**

```tex
a set of clauses C = {C_1, ..., C_n} where for all i in [1..n]
```

**After:**

```tex
a set of clauses C = {C_1, ..., C_m} where for all i in [1..m]
```

**Reason:** The index bound n is already the number of variables; the number of clauses is a separate quantity (Fig. 1 has 8 variables and 12 clauses).

**Evidence:** Internal inconsistency within one sentence; Figure 1(b) has n = 8 variables and 12 clauses.

**Source:** published PDF p. 619

## P02 — Section 2, paragraph 2 (p. 619; Lean; certain)

**Before:**

```tex
A clause with one variable has a forced value which can be replaced in all other equations or considered to be a clause with the same variable twice. Regardless it need not effect the implication graph or could be a trivial self-loop.
```

**After:**

```tex
A clause with one literal l has a forced value which can be substituted into all other clauses, or the clause can be considered to be (l or l), which yields the single implication (not l) implies l. In the second case the implication is an edge of the implication graph (from the negation of the literal to the literal), not a self-loop, and it must not be dropped: omitting it would make (x) and (not x) together appear satisfiable.
```

**Reason:** For (l or l) the two contrapositive implications coincide in the single edge (not l) -> l, which is not a self-loop and carries the constraint; the published sentence says it is unnecessary or trivial.

**Evidence:** Derived from the clause/implication definition of the same paragraph; the repository gettwosatgraph encodes the unit clause as the edge (not x) -> x; Lean statement in R5.

**Source:** published PDF p. 619; native/selfmodgraph.cpp gettwosatgraph

## P03 — Section 2, paragraph 3 (p. 619; Lean; certain)

**Before:**

```tex
A vertex with two out-edges is a Boolean conditional, otherwise it contains more than two out-edges and is an n-way conditional.
```

**After:**

```tex
A vertex with two out-edges is a Boolean conditional, a vertex with more than two out-edges is an n-way conditional, and a vertex with no out-edge is an exit (return) vertex.
```

**Reason:** The published classification has no case for out-degree 0 although the paper's own examples contain such vertices (the exit of Fig. 4).

**Evidence:** Figure 4 (exit has no out-edge) contradicts the exhaustive-sounding 'otherwise'.

**Source:** published PDF p. 619, p. 630 Fig. 4

**Lean:** `SmcIrred.fig4_kinds`

## P04 — Section 3.1, last sentence (p. 623; Lean; inferred)

**Before:**

```tex
Finally, implications can randomly be added to the forest such that no loops are created which would imply unsatisfiability.
```

**After:**

```tex
Finally, implications can randomly be added to the forest, each together with its contrapositive, provided that none leads from a literal that is true under the desired assignment to a literal that is false under it. Loops are allowed (they only merge literals into one component); a loop through a variable and its negation would imply unsatisfiability and cannot arise under this condition.
```

**Reason:** Acyclicity is neither necessary (cycles within the true literals are harmless) nor sufficient (an acyclic implication from a true to a false literal makes the desired assignment violate the formula) for the generated formula to have the desired assignment as its solution.

**Evidence:** Counterexamples are elementary (x true, y false; add x -> y: acyclic but violated). The replacement condition is the one Lean proves in R9 (planted generator); the wording of the replacement is inferred from the published construction.

**Source:** published PDF p. 623

**Lean:** `SmcIrred.forcing_agree`, `SmcIrred.planted_solve`, `SmcIrred.counter_violates`, `SmcIrred.counter_unsat`, `SmcIrred.loop_keeps`, `SmcIrred.no_loop_through_negation`

## P05 — Section 4, addition (p. 625; Lean; certain)

**Before:**

```tex
s_i = a_i xor b_i xor c_{i+1}
```

**After:**

```tex
s_i = a_i xor b_i xor c_i
```

**Reason:** c_i is the carry into bit i (c_0 = 0, c_{i+1} is produced from bit i); with c_{i+1} the sum bit would depend on the carry out, e.g. a = b = 1 gives s_0 = 1 xor 1 xor 1 = 1 instead of 0.

**Evidence:** The next equation in the same sentence defines c_{i+1} from a_i, b_i, c_i; the repository addition_bit_to_virtual computes S = A ^ B ^ carry_in.

**Source:** published PDF p. 625; python/virt.py addition_bit_to_virtual

**Lean:** `SmcIrred.published_add_fails`, `SmcIrred.addBit_post`, `SmcIrred.ripple_add`

## P06 — Section 4 (p. 624) and Section 4.1 (p. 625) (p. 624; editorial, open; inferred)

**Before:**

```tex
using logic synthesis to construct an optimal circuit is NP-hard based on the circuit SAT problem; Although the optimal one is NP-hard
```

**After:**

```tex
Construct a minimum-size circuit for a given truth table is the Minimum Circuit Size Problem, whose NP-hardness is open (minimizing DNF formulas is NP-hard, and minimizing circuits for multi-output functions is NP-hard under randomized reductions); minimizing a given circuit is coNP-hard by reduction from circuit satisfiability. State which is meant and cite it.
```

**Reason:** Circuit satisfiability does not by itself give NP-hardness of optimal synthesis from a truth table, and for a single-output truth table the question is a well-known open problem.

**Evidence:** Ilango, Loff, Oliveira, NP-hardness of circuit minimization for multi-output functions, CCC 2020 (abstract: single-output NP-hardness open for general circuits, known for DNFs); Kabanets and Cai 2000 (MCSP). Wording left to the author.

**Source:** published PDF pp. 624-625; https://drops.dagstuhl.de/opus/volltexte/2020/12574/

## P07 — Section 4.1, paragraph 1 (p. 625; Lean; certain)

**Before:**

```tex
provides non-linearity using an invertible affine transformation. This multiplicative inverse of the inverse of the affine transformation is used for decryption.
```

**After:**

```tex
provides non-linearity through the multiplicative inverse in GF(2^8) followed by an invertible affine transformation. Decryption applies the inverse of the affine transformation followed by the multiplicative inverse.
```

**Reason:** An affine transformation is linear up to a constant, so the non-linearity comes from the multiplicative inverse (FIPS-197 section 5.1.1), and the quoted decryption sentence is not grammatical or correct as written.

**Evidence:** FIPS 197 section 5.1.1 (S-box = multiplicative inverse in GF(2^8), then affine transformation); Lean in R12.

**Source:** published PDF p. 625; FIPS 197

**Lean:** `SmcIrred.AES.sbox_table`, `SmcIrred.AES.ginv_mul`, `SmcIrred.AES.invAffine_affine`, `SmcIrred.AES.affine_is_affine`, `SmcIrred.AES.sbox_not_affine`, `SmcIrred.AES.invSbox_sbox`

## P08 — Section 4.2, paragraph 1 (p. 626; Lean; certain)

**Before:**

```tex
Toom-Cook (O(n^{log_k 2k-1}))
```

**After:**

```tex
Toom-Cook (O(n^{log_k (2k-1)}))
```

**Reason:** As printed the exponent reads log_k(2k) - 1 = log_k 2; Toom-k uses 2k-1 multiplications of size n/k, giving the exponent log_k(2k-1).

**Evidence:** Toom-k performs (2k-1) multiplications on operands of size n/k (standard; Bernstein, Multidigit multiplication for mathematicians); Lean in R14.

**Source:** published PDF p. 626

**Lean:** `SmcIrred.Arith.toomProds_eq`, `SmcIrred.Arith.toom_between`, `SmcIrred.Arith.toom_published_too_small`, `SmcIrred.Arith.toom_witness`

## P09 — Section 4.3, paragraph 2 (p. 627; Lean; inferred)

**Before:**

```tex
increase the potential of the representation by order of 2^32 or 2^64
```

**After:**

```tex
increase the potential of the representation by a factor of the order of 32 or 64 for bitwise operations and of 32^2 or 64^2 for schoolbook multiplication
```

**Reason:** Replacing one-bit gates by w-bit word operations reduces the operation count by a factor polynomial in w, not 2^w.

**Evidence:** Gate-count argument; exact counts for the repository generators in R14. The intended meaning is the author's: confirm in R1 question if kept.

**Source:** published PDF p. 627

**Lean:** `SmcIrred.Arith.words_exact`, `SmcIrred.Arith.word_products`, `SmcIrred.Arith.words_cover`, `SmcIrred.Arith.word_gain_not_exponential`

## P10 — Table 2, column C gmp (p. 629; listing, open; certain)

**Before:**

```tex
Rows 128 and 256 both show 9.141ms (x86) and 7.640ms (x86-64); row 32 shows 851ms and 707ms, larger than row 64 (2.207ms, 1.015ms)
```

**After:**

```tex
Replace the C gmp cells of row 256 (and 32 if a unit slip) by the measured values supplied by the author.
```

**Reason:** The 256-bit cells duplicate the 128-bit cells, which is implausible, and the 32-bit cells exceed the 64-bit cells (likely microseconds).

**Evidence:** Rendered page 629 compared with the manuscript TeX; validation/check_tables.py. The correct values are not recoverable from the repository. Author decision 2026-10-17: re-measure to confirm the cells are wrong first (R16), then apply the minimal correction, which may mean regenerating the column.

**Source:** published PDF p. 629

## P11 — Section 4.3 and Tables 1-2 (p. 627; listing, open; inferred)

**Before:**

```tex
AES encryption with a fixed randomly generated key; node and edge counts of Tables 1-2
```

**After:**

```tex
State the key used (the repository generates AES graphs with the key bytes 0x12...) and any difference between the regenerated Nodes/Edges/Exec. N/Exec. E and the printed values found in R16.
```

**Reason:** Provenance of the measured graph and counts; to be settled by regenerating the graphs (R16).

**Evidence:** python/aes.py gen_aes uses key = b'\x12' * (bits // 8); regeneration result in R16.

**Source:** published PDF p. 627; python/aes.py

## P12 — Section 1, paragraph 4 (p. 618; editorial; certain)

**Before:**

```tex
and the only resolution to structuring them into an abstract syntax tree (AST) involves introduction of variables and conditional expressions [30]
```

**After:**

```tex
and the resolutions to structuring them into an abstract syntax tree (AST) involve code duplication [27] or the introduction of variables and conditional expressions [30]
```

**Reason:** Section 2 (paragraph 7) states that restructuring is possible by code duplication [27] or by state variables [30, 31], so 'the only resolution' contradicts the paper itself.

**Evidence:** Internal inconsistency with Section 2 paragraph 7 (p. 620).

**Source:** published PDF pp. 618, 620

## P13 — Section 1, paragraph 5 (p. 618; editorial, open; certain)

**Before:**

```tex
This study will take a look at specifically a case study where every control flow construct ... will be further embedded or converted into an irreducible loop nest ... The 2-SAT solver will be used to determine the exit conditions for all of the loops in question ... Performance measurements and a look at how powerful tools such as IDA Pro and Ghidra ... will be presented under Windows and Linux
```

**After:**

```tex
State what the case study actually reports: Tables 1-2 measure plain Boolean-CFG implementations of AES and RSA, Table 3 a single hand-written irreducible-loop example; the transformation of Sections 5 with 2-SAT-generated exit conditions is described but not applied to AES or RSA and not measured.
```

**Reason:** The announced case study (AES/RSA protected by irreducible loop nests with solver-generated exit conditions, measured on both platforms) is not what Sections 4-5 report, and the repository does not implement it.

**Evidence:** Sections 4.3 and 5 read; native/aesmain.c and rsa.c run the plain graph VM; no code generates 2-SAT formulas or applies the Figure 5/6 transformations. Author decision 2026-10-17: the author will implement the protected variant; the erratum is deferred until that implementation exists (plan round R19b).

**Source:** published PDF pp. 618-619, 627-630

## P14 — Section 5, before Definition 4 (p. 631; Lean; certain)

**Before:**

```tex
removing extra back edges whose successor is not the inner-most non-header node
```

**After:**

```tex
removing extra back edges whose source is not the inner-most non-header node
```

**Reason:** Definition 4 keeps exactly the back edges (v_n, v_i), whose source (not successor) is the inner-most non-header node v_n; no back edge of M_n has v_n as successor.

**Evidence:** Definition 4 on the same page; brute-force check validation/planning/section5_bruteforce.py; Lean R4.

**Source:** published PDF p. 631

## P15 — Section 5, before Definition 4 (p. 631; Lean; certain)

**Before:**

```tex
will have maximized multi-entry edges while minimizing all others
```

**After:**

```tex
will have maximized multi-entry edges while minimizing the others up to one edge
```

**Reason:** Among graphs with the maximum number of multi-entry edges the other edges number at least 2n-3, while M_n has 2(n-1); removing (v_n, v_1) keeps both irreducible-loop and multi-entry-edge counts.

**Evidence:** Exhaustive for n <= 5 and sampled for n = 6, 7 (validation/planning/section5_bruteforce.py: minimum non-MEE edges 2n-3); Lean R4 proves it. Only the wording (minimal repair versus a smaller graph definition) is the author's choice. Wording style (author, 2026-10-17): minimal.

**Source:** published PDF p. 631

## P16 — Section 5, Definitions 3 and 4 (p. 631; Lean; certain)

**Before:**

```tex
Definition 3 |MEE(K_n)| = ...; Definition 4 E_{M_n} = ..., V_{M_n} = v_i for all i in [1..n]
```

**After:**

```tex
Define MEE(G) for a CFG with a DFS, relative to the Havlak loop nesting forest of that DFS: an edge (x, y) with y in the body of a loop headed by w, y different from w, and x not a DFS descendant of w. State the counts |MEE(K_n)| and |E(M_n)| as claims about these definitions (they are not definitions), and write V_{M_n} = {v_i : i in [1..n]}.
```

**Reason:** Multi-entry edge is never defined, Definitions 3 and 4 state counts rather than define objects, and V_{M_n} = v_i for all i is not a set.

**Evidence:** Lean R4 gives the definition under which both counts hold; the published text states facts under the heading Definition.

**Source:** published PDF p. 631

## P17 — Section 5, paragraph on node splitting (p. 631; Lean; certain)

**Before:**

```tex
However this optimization will still require a quadratic amount of code duplication for each multi-entry edge
```

**After:**

```tex
However this optimization can still require an exponential amount of code duplication: for the complete graph K_n every reducible graph equivalent to it has at least 2^(n-1) nodes (Carter, Ferrante and Thomborson, POPL 2003).
```

**Reason:** Node splitting on K_n is exponential, not quadratic, by Theorem 4 of Carter, Ferrante and Thomborson; the claim attributed to each multi-entry edge is unsupported.

**Evidence:** Carter, Ferrante, Thomborson, Folklore confirmed: reducible flow graphs are exponentially larger, POPL 2003, pp. 106-114 (Theorems 4 and 5), copy read at https://www.cs.tufts.edu/~nr/cs257/archive/larry-carter/exponential-node-splitting.pdf; Lean proof planned in R18.

**Source:** published PDF p. 631

**Lean:** `SmcIrred.Threat.one_variable_suffices`, `SmcIrred.Threat.quadratic_is_edge_count`

## P17b — Abstract (and Section 5, first sentence of paragraph 1 on p. 631) (p. 617; Lean; certain)

**Before:**

```tex
node-splitting or introduction of variables can have a quadratic complexity increase on the size of the control-flow graph
```

**After:**

```tex
node-splitting can have an exponential and introduction of variables a quadratic complexity increase on the size of the control-flow graph
```

**Reason:** Consequence of P17 for the abstract; the quadratic bound is the one the paper argues for the introduction of variables (DREAM).

**Evidence:** See P17; the quadratic claim for state variables is stated in Section 2 (p. 620) and Section 5. Included in the errata list by the author (2026-10-17).

**Source:** published PDF p. 617

## P18 — Figure 5(c) (p. 632; Lean; inferred)

**Before:**

```tex
Graph (c): A has an exit edge (blue) and there is no injected condition node
```

**After:**

```tex
Graph (c) with an injected condition node h: entry -> h, h -> A, A -> B, B -> h, h -> exit (blue), goto -> B (red), as in the code and in the text 'requires one node ... an increase of three edges'.
```

**Reason:** In the drawn graph the loop can exit directly from A, so the path that executes A then B once does not exist (A, B, A is forced); the code and the text place the condition in a separate injected node.

**Evidence:** Path analysis of the drawn graph against the code while (trueThenFalse) { A; labelB: B; }; Lean R17 proves the equivalence of the repaired graph.

**Source:** published PDF p. 632; manuscript TeX figure source

**Lean:** `SmcIrred.Lang.fig5_traces`, `SmcIrred.Lang.fig5c_cfg`, `SmcIrred.Lang.drawn5c_no_AB`, `SmcIrred.Lang.fig5c_cfg_AB`, `SmcIrred.Lang.fig5c_irreducible`

## P19 — Figure 6(c) and its caption (p. 633; Lean; inferred)

**Before:**

```tex
Graph (c) keeps the edge A -> B; caption 'or with an extra edge (c)'
```

**After:**

```tex
Graph (c) without the edge A -> B (A returns to the condition, as in the code while (c && trueThenFalse) { labelA: A; } B;) and the caption 'with two extra edges (c)'.
```

**Reason:** The code of (c) has no edge from A to B (control returns to the loop condition), and relative to (a) two edges are added (A -> c and the entry into A), not one.

**Evidence:** Reading of the code in (c); Lean R17 checks the repaired graph against the code semantics.

**Source:** published PDF p. 633; manuscript TeX figure source

**Lean:** `SmcIrred.Lang.fig6_traces`, `SmcIrred.Lang.fig6c_cfg`, `SmcIrred.Lang.fig6c_drawn_extra`, `SmcIrred.Lang.fig6c_no_AB_edge`, `SmcIrred.Lang.fig6c_irreducible`

## P21 — Section 5.1, paragraph 4 (p. 634; editorial; certain)

**Before:**

```tex
differential computation analysis (DCA) and its subset differential power analysis (DPA)
```

**After:**

```tex
differential computation analysis (DCA), the software counterpart of differential power analysis (DPA)
```

**Reason:** DCA (Bos, Hubain, Michiels, Teuwen, CHES 2016) applies the differential-power-analysis idea to software execution traces; neither attack is a subset of the other.

**Evidence:** Bos, Hubain, Michiels, Teuwen, Differential Computation Analysis: Hiding Your White-Box Designs is Not Enough, CHES 2016 (ePrint 2015/753).

**Source:** published PDF p. 634; https://eprint.iacr.org/2015/753

## P22 — Section 5.1, paragraph 4 (p. 634; Lean; inferred)

**Before:**

```tex
It is resistant to differential computation analysis (DCA) and its subset differential power analysis (DPA) as the execution order changes based on the input.
```

**After:**

```tex
It is conjectured to hinder differential computation analysis (DCA) when traces are not aligned by address, since the execution order changes based on the input; the scheme is not implemented or evaluated, and on address-aligned traces the same (vertex, value) pairs are observed as in the static scheme.
```

**Reason:** No analysis or experiment supports resistance, and an input-dependent order of vertex executions does not change the set of intermediate values observable at fixed code addresses.

**Evidence:** Lean statement T6 `Threat.dca_last` (multiset of (vertex, final value) pairs equal) planned for R20b; the replacement is made certain by that theorem, and is otherwise a wording choice.

**Source:** published PDF p. 634

**Lean:** `SmcIrred.Threat.dca_last`, `SmcIrred.Threat.dca_final_obs`, `SmcIrred.Threat.dca_witness`

## P23 — Section 5.1, paragraph 2 (p. 634; Lean; certain)

**Before:**

```tex
our proposed obfuscation scheme is indistinguishable from the underlying algorithm from a practical standpoint though not a theoretical one
```

**After:**

```tex
our proposed obfuscation scheme computes the same function as the underlying algorithm but makes no claim of cryptographic indistinguishability, which is an open problem [8]
```

**Reason:** 'Indistinguishable from a practical standpoint' is not a defined security notion; what holds (and is proved) is functional equivalence.

**Evidence:** Lean T1 (functional equivalence) and T7 (witness that obfuscations of equivalent programs differ in a public size measure) in R20; wording is the author's choice. Wording style (author, 2026-10-17): minimal.

**Source:** published PDF p. 634

**Lean:** `SmcIrred.Threat.correct`, `SmcIrred.Threat.scheme_overhead`, `SmcIrred.Threat.not_size_indist`

## P24 — Section 5.1, paragraph 5 (p. 635; Lean; inferred)

**Before:**

```tex
In the dynamic scheme, however, the repeated operations would require exponential time without proving these operations as repeated and removing them to reduce it to the static scheme.
```

**After:**

```tex
In the dynamic scheme, however, repeated executions of the same vertex are observable in a trace; whether removing them to reduce the scheme to the static scheme is hard is not shown here.
```

**Reason:** No argument or reference supports exponential time, and aligned traces expose which executions are repeats of the same vertex.

**Evidence:** Lean T6 (R20b) for the trace statement; wording is the author's choice. Wording style (author, 2026-10-17): minimal.

**Source:** published PDF p. 635

**Lean:** `SmcIrred.Threat.dca_repeats_visible`, `SmcIrred.Threat.dca_witness`

## P25 — Section 5.1 (p. 634; Lean; certain)

**Before:**

```tex
Section 5.1 as a whole
```

**After:**

```tex
Replace Section 5.1 by the following subsection (every statement is a Lean theorem; names in brackets).

5.1 Security. System: the original program is a structured program with goto over abstract blocks; the obfuscator is the static scheme of Figures 5 and 6 whose opaque conditions are outputs of the self-modifying 2-SAT solver on a planted formula; an image consists of the transformed program, the stamped formula and the placeholder bytes of the predicate cells. Adversary classes describe capabilities, not tools: Imm reads the predicate cells from the static code bytes; SmcSem implements stamping and the machine semantics; Struct restructures the control-flow graph; Trace and Dca see (address, value) pairs of a run; Fault replaces one written value. Assumptions: S1 the stamped formula is a planted formula whose extra implications respect the intended assignment; S2 the predicate cells the program reads are required variables whose intended value is false; S3 the circuit of the dynamic scheme is numbered topologically and its schedule has the final executions in dependency order; S4 only the capabilities above are considered. Results: T1 the image executes the blocks of the original program and the schedule yields the circuit's values [Threat.correct]; T2 an Imm analyzer is wrong on some image satisfying S1-S3 [Threat.imm_unsound]; T3 an SmcSem analyzer reports every predicate cell, and the Tarjan run on the stamped formula costs at most 2|V|+|E| steps in the clean cost model [Threat.recover], so opacity is relative to analyzers without the machine semantics and is not computational hardness; T4 one state variable always suffices to flatten a control-flow graph, and the quadratic quantity of Section 2 is the multi-entry-edge count of K_n, not a cost of restructuring [Threat.one_variable_suffices, Threat.quadratic_is_edge_count] (an exponential lower bound for node splitting is due to Carter, Ferrante and Thomborson and is not proved here); T5 a fault in a non-final execution does not change the output, a fault in a final execution does [Threat.fault_class, Dyn.fault_final_changes]; T6 on address-aligned traces every dependency-respecting schedule gives the same (vertex, final value) pairs, and repeated executions of a vertex are visible [Threat.dca_last, Threat.dca_final_obs, Threat.dca_repeats_visible]; T7 the scheme is not an indistinguishability obfuscator for the number of vertices [Threat.not_size_indist]. Each assumption is necessary for the theorem it supports [Threat.nec_forcing, nec_stamped, nec_false_cells, nec_extra_respects, nec_schedule, nec_topo]. Not claimed: hardness of the predicates against an analyzer with SmcSem, resistance to any existing tool, any indistinguishability or virtual-black-box property.
```

**Reason:** Section 5.1 states security goals without an adversary model, assumption list or statement.

**Evidence:** Lean development, rounds R20a-R20b (Threat/*). Included in the errata list by the author (2026-10-17); whether it replaces Section 5.1 or P21-P24 only are applied is the author's choice.

**Source:** published PDF pp. 634-635

**Lean:** `SmcIrred.Threat.correct`, `SmcIrred.Threat.imm_unsound`, `SmcIrred.Threat.recover`, `SmcIrred.Threat.one_variable_suffices`, `SmcIrred.Threat.fault_class`, `SmcIrred.Threat.dca_last`, `SmcIrred.Threat.not_size_indist`, `SmcIrred.Threat.nec_forcing`, `SmcIrred.Threat.nec_stamped`, `SmcIrred.Threat.nec_false_cells`, `SmcIrred.Threat.nec_extra_respects`, `SmcIrred.Threat.nec_schedule`, `SmcIrred.Threat.nec_topo`

## P26 — Abstract; Section 5 paragraph 1 (p. 617; editorial; inferred)

**Before:**

```tex
limits in decidability as per Rice's theorem
```

**After:**

```tex
static analysis of self-modifying code has limits in decidability (Rice's theorem and, for static analysis, Landi [18])
```

**Reason:** Rice's theorem concerns extensional properties of programs; the cited reference for undecidable static analysis is Landi's alias-analysis result.

**Evidence:** Landi, Undecidability of static analysis, ACM LOPLAS 1(4) 1992 (alias analysis); Rice 1953. Included in the errata list by the author (2026-10-17).

**Source:** published PDF pp. 617, 629

## P27 — Figure 3 code comments (p. 628; listing; inferred)

**Before:**

```tex
#2*2^n nodes, 2 predecessors per node; #2^n nodes, n predecessors per node
```

**After:**

```tex
State the exact node counts of the two listed generators (Lean R11) or mark the comments as asymptotic.
```

**Reason:** For BITSZ = 1 the generator decoder_shift_to_virtual creates 2^(m+1) + m - 4 nodes and decoder_to_virtual (m/2 + 2) 2^m nodes, so the comment '2^n nodes' for the latter is not its node count.

**Evidence:** Planning count from python/virt.py; exact figures proved in R11 and matched to the Python count by evidence. Included in the errata list by the author (2026-10-17).

**Source:** published PDF p. 628

## P28 — Section 4.2, paragraph 3 (p. 627; Lean, open; inferred)

**Before:**

```tex
the exponential growth of multiplication as the bit size gets to realistic cryptographic sizes
```

**After:**

```tex
due to the super-quadratic (polynomial) growth of multiplication as the bit size gets to realistic cryptographic sizes
```

**Reason:** The number of nodes of a Boolean multiplication circuit is polynomial in the bit size (schoolbook n^2, Karatsuba n^1.58), not exponential.

**Evidence:** Node counts of the repository generators in R14; the paper's own Table 2 grows polynomially.

**Source:** published PDF p. 627

## P29 — Section 1 paragraph 5; Section 5.1 paragraph 3 (p. 618; Lean; inferred)

**Before:**

```tex
will be beyond the scope of any state-of-the-art static analysis tools; Both schemes are practically resistant to static analysis, as the presence of dynamic SMC makes a static analyzer unable to safely analyze past the point that it is detected
```

**After:**

```tex
will be beyond the scope of any state-of-the-art static analysis tools that treat the code as immutable; Both schemes are practically resistant to static analysis that treats code bytes as immutable
```

**Reason:** Unqualified claims about all static analysis tools; the solver outputs are computable in linear time by an analyzer that models the self-modification, so the claim holds only for analyzers that do not.

**Evidence:** Lean statements T2 and T3 in R20a (immutable-code analyzers unsound; SMC-aware analyzers recover every predicate); wording is the author's choice. Wording style (author, 2026-10-17): minimal.

**Source:** published PDF pp. 618, 634

## T01 — Typographical group (p. 619; typographical; certain)

**Before:**

```tex
p. 619: need not effect the implication graph; p. 619: |C_i|<=2; p. 626: Schonhage-Strassen; p. 626: elliptical curve digitial signature algorithm; p. 626: multliplication; p. 626: a performance penality; p. 626: there performance will; p. 634: reprsented as CFGs; p. 634: suspectible to such tools; p. 630: gratuitious computations; p. 632: transfered to the first node; p. 631: if prefering to avoid; p. 630: structured programing; p. 629: a language whose syntax allows them is exceedingly rare; p. 628: \textbf{|xor\_to\_virtual|}; p. 633: if (!c): goto labelB;
```

**After:**

```tex
need not effect the implication graph -> need not affect the implication graph; |C_i|<=2 -> |C_i| \le 2; Schonhage-Strassen -> Sch\"onhage-Strassen; elliptical curve digitial signature algorithm -> elliptic curve digital signature algorithm; multliplication -> multiplication; a performance penality -> a performance penalty; there performance will -> their performance will; reprsented as CFGs -> represented as CFGs; suspectible to such tools -> susceptible to such tools; gratuitious computations -> gratuitous computations; transfered to the first node -> transferred to the first node; if prefering to avoid -> if preferring to avoid; structured programing -> structured programming; a language whose syntax allows them is exceedingly rare -> a language whose syntax allows them, is exceedingly rare; \textbf{|xor\_to\_virtual|} -> \textbf{\lstinline|xor\_to\_virtual|}; if (!c): goto labelB; -> if (!c) goto labelB;; (published running head: loopsand) -> irreducible loops and self-modifying code
```

**Reason:** Spelling, symbol and code-listing typos; the odd-page running head reads 'irreducible loopsand self-modifying code' (publisher typesetting).

**Evidence:** Read-through of the manuscript TeX and the published PDF.

**Source:** manuscript TeX; published PDF

## B01 — References (p. 636; bibliographic; certain)

**Before:**

```tex
[21]: IEEE Transactions on Computers 137 (1988); [26]: W. Tao, M. Jian, Z. Wei and C. Yu; [8]: L. Buttyán and M. Horváth; [19]: Annales Universitatis Scientarum Budapestinensis; [10]: Inform’atica
```

**After:**

```tex
[21]: IEEE Transactions on Computers 37 (1988); [26]: T. Wei, J. Mao, W. Zou and Y. Chen; [8]: M. Horváth and L. Buttyán; [19]: Annales Universitatis Scientiarum Budapestinensis; [10]: Informática
```

**Reason:** Reference errors found by comparing every entry with its DOI or publisher page: [21]: Parhami 1988: vol. 37, no. 11, pp. 1470-1476, DOI 10.1109/12.8722 (the manuscript bib has volume 37) | [26]: given and family names swapped in the published list; the manuscript bib has Wei, Tao and Mao, Jian and Zou, Wei and Chen, Yu | [8]: ePrint 2015/412 lists M. Horváth first | [19]: Latin plural of scientia | [10]: the accent is typeset as an apostrophe

**Evidence:** Parhami, IEEE TC 37(11) 1988; Wei, Mao, Zou, Chen, SAS 2007 (Springer LNCS 4634, 170-183); ePrint 2015/412 author order.

**Source:** published PDF pp. 635-637; manuscript biblio.bib

