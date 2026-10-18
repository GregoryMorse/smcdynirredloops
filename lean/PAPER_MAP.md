# PAPER_MAP: claim inventory for Publ. Math. Debrecen 100 (Suppl.) (2022) 617-637

Classes (plan D1): **F** formal, **FT** security statement relative to the threat model, **FD** data check, **M** model/artifact match (evidence), **R** third-party fact (citation), **X** opinion or intent (nothing claimed). Page = journal page range of the published version. Status: `open` until the round named in *Round* closes it; R-class rows carry the R1 source check. Declarations/evidence are filled by the discharging round.

| ID | Location | Page | Claim | Class | Round | Status | Declaration / evidence / source |
|---|---|---|---|---|---|---|---|
| C01 | Abstract; §5 ¶1 | 617 | static analysis of SMC has decidability limits "as per Rice's theorem" (P26) | R | R1 | R1 checked | source-partial: Landi, ACM LOPLAS 1(4) 1992 is alias-analysis undecidability, not Rice; see P26 |
| C02 | Abstract; §2 ¶7; §5 | 617 | IL → reducible by node splitting or variables: quadratic increase (P17) | F + R | R4, R18 | open |  |
| C03 | Abstract; §4 | 617 | algorithms lowered to multi-input gates; applicable to any CFG | F | R10 | open |  |
| C04 | Abstract; §6 | 617 | the ideas can be applied separately | X | R1 | listed (X) |  |
| C05 | §1 ¶1 | 617–619 | VMProtect and Denuvo defeated [16, 17] | R | R1 | R1 checked | source-partial: VMAttack (Kalysch, Götzfried, Müller, ARES 2017, doi 10.1145/3098954.3098995) deobfuscates VMProtect (checked); Denuvo reference [17] (Karthik, Amritha, Sethumadhavan, ICCCNT 2020) not found online: UNVERIFIED |
| C06 | §1 ¶3 | 617–619 | DFS-based SCC + topological sort implemented by an SMC CFG of the queried graph | F + M | R7, R8 | F part done (Smc.Solve `smcSolve_spec`, Smc.Visit `sRun_sim`); M part and step bound open (G26, G27, R8) |
| C07 | §1 ¶3 | 617–619 | stack simplification; generalizable to largely any graph algorithm | X | R1 | listed (X) |  |
| C08 | §1 ¶3 | 617–619 | SCC + topological sort make an efficient linear 2-SAT solver [2] | F | R5, R6 | done (Tarjan.Solver `twoSatSolve_spec`, Tarjan.Correct `tarjan_spec`) |  |
| C09 | §1 ¶4 | 617–619 | an IL is a loop with multiple entries; hardest structure for static tools | F (def) + X | R3 | open |  |
| C10 | §1 ¶4 | 617–619 | nested ILs can cause quadratic LNF construction [22] | R | R1 | R1 checked | source-checked: Ramalingam, Identifying loops in almost linear time, TOPLAS 21(2) 1999, 175-188: abstract states Havlak's algorithm is quadratic in the worst case (IBM Research page) |
| C11 | §1 ¶4 | 617–619 | "the only resolution" for structuring is variables + conditions (P12) | F + R | R18 | open |  |
| C12 | §1 ¶4 | 617–619 | almost-linear LNF algorithms exist; AST translation lacks the same reductions | R + X | R1 | R1 checked | source-checked (almost linear: Ramalingam 1999); AST translation part is X |
| C13 | §1 ¶5 | 617–619 | every construct embedded into an IL nest designed for quadratic identification | F + X | R4, R17 | open |  |
| C14 | §1 ¶5 | 617–619 | loops fictitious via opaque predicates: original looping or one iteration | F | R17 | open |  |
| C15 | §1 ¶5 | 617–619 | the 2-SAT solver fixes all exit conditions; beyond static tools | F + FT + X | R9, R19, R20b | open |  |
| C16 | §1 ¶5 | 617–619 | case study: protected AES/RSA, measured on Windows/Linux x86/x64, IDA/Ghidra (P13) | X | R1 | listed (X) |  |
| C17 | §2 ¶1 | 619–622 | SAT, CNF, 2-SAT definitions (P01) | F | R5 | done (Spec.TwoSat (TwoSat, Sat, graph)) |  |
| C18 | §2 ¶1 | 619–622 | DNF trivially solvable but potentially O(2^n) clauses | F (should) | R5 | done (TwoSat.DNF `dnf_parity_terms`) |  |
| C19 | §2 ¶1 | 619–622 | k-SAT reduces to 3-SAT; 3-SAT NP-complete | R (+F could) | R1 | R1 checked | standard: Cook-Levin; Karp 1972 (not opened this round) |
| C20 | §2 ¶2 | 619–622 | 2-SAT NL-complete; NL ⊆ P | R | R1 | R1 checked | standard: Papadimitriou, Computational Complexity, 1994, Ch. 16 (2-SAT NL-complete); Jones, Lien, Laaser 1976 (not opened this round) |
| C21 | §2 ¶2 | 619–622 | linear time via implication graph + SCC; solution in reverse topological order | F | R5, R6 | done (TwoSat.APT `twoSat_iff_scc`, `apt_correct`; Tarjan.Cost `tarjan_cost`) |  |
| C22 | §2 ¶2 | 619–622 | an empty clause means unsatisfiable | F | R5 | done (TwoSat.APT `unsat_of_empty`) |  |
| C23 | §2 ¶2 | 619–622 | unit-clause handling (P02) | F | R5 | done (TwoSat.Unit `noUnit_sccCriterion_fails`) |  |
| C24 | §2 ¶2 | 619–622 | (p ∨ q) ≡ (¬p ⇒ q) ∧ (¬q ⇒ p) | F | R5 | done (TwoSat.Implication `or_iff_implications`) |  |
| C25 | Fig. 1 | 620 | formula, 24 implications, graph, SCC labels, highlighted solution | F + M | R5 | done (TwoSat.Fig1 `fig1_edges`, `fig1_label_ok`, `fig1_apt`, `fig1_count`) |  |
| C26 | §2 ¶3 | 619–622 | CFG definition; vertex kinds by out-degree (P03) | F | R2 | done | Spec.Graph IsCFG/kind; Graph.Fig4.fig4_kinds |
| C27 | §2 ¶3 | 619–622 | DFS edge classification by pre/post timestamps | F | R2 | done | Graph.Classify (cls_*_iff); Graph.DfsValid.dfsRun_valid |
| C28 | §2 ¶4 | 619–622 | loops; LNF; unique for reducible CFGs, not for irreducible ones | F | R3 | done | R3: LNF.NonUnique.lnf_not_unique, irreducible_not_unique (non-uniqueness for irreducible CFGs); R3b: LNF.Reducible.body_dfs_independent, lnfParent_dfs_independent (reducible CFGs: bodies and LNF independent of the DFS) |
| C29 | §2 ¶4 | 619–622 | Havlak LNF: one header per loop; near-linear [26] | F (def) + R | R3 | partial | Spec.LNF (declarative Havlak loops); LNF.Algo.havlak with LNF.Algo.havlak_fig4/havlak_fig4Swap (M evidence on two DFS orders of Fig. 4; general algorithm = declarative equivalence is an OPEN OBLIGATION, plan risk fallback); source-partial: Havlak TOPLAS 19(4) 1997 557-567 (definition); near-linear claim cites Wei, Mao, Zou, Chen, SAS 2007 (not opened); Ramalingam 1999 shows Havlak's worst case is quadratic |
| C30 | §2 ¶4 | 619–622 | ILs not directly representable in Java/Python | F (should) | R18 | open |  |
| C31 | §2 ¶5 | 619–622 | state-machine model represents any CFG with one variable and an n-way conditional | F | R18 | open |  |
| C32 | §2 ¶6 | 619–622 | structuring ILs needs goto (absent new variables/duplication); tools named | F + R | R18 | open |  |
| C33 | §2 ¶7 | 619–622 | restructuring needs duplication [27] or state variables [30, 31]; quadratic variables/conditionals | F + R | R18 | open |  |
| C34 | §2 ¶8 | 619–622 | prior obfuscation methods; the contribution | R + X | R1 | R1 checked | references exist (published list [3],[4],[5],[9],[19],[20],[28]); content not checked: contribution claims are X |
| C35 | §3 ¶1 | 622–623 | implication graph = CFG; node code = SCC + reverse topological sort | F | R7 | done (Smc.Solve `smcSolve_spec`, Smc.Visit `sRun_sim`; machine reading of the blueprint: G26) |
| C36 | §3 ¶1 | 622–623 | implemented in x86 and x86-64 on Windows and Linux | M | R8 | open |  |
| C37 | §3 ¶1 | 622–623 | node stack replaces the call stack; first instruction → return; topological check marking | F + M | R7, R8 | F part done (Smc.Solve `smcSolve_spec`, Smc.Visit `sRun_sim`); M part and step bound open (G26, G27, R8) |
| C38 | §3 ¶1 | 622–623 | lambda callbacks for edges and solutions; set for unsatisfiability | M | R8 | open |  |
| C39 | §3 ¶2, Fig. 2 | 622–623 | blueprint generation; stamping; reuse by restamping SMC offsets | F + M | R7, R8 | F part done in the abstract machine (Smc.Restamp `smcRounds_replicate`); offsets/stamping M part open (G25, R8) |
| C40 | §3.1 | 623 | planted 2-SAT generator yields the desired values (P04) | F | R9 | open |  |
| C41 | §4 ¶1 | 623–629 | Boolean-level description; word-level abstractions can be reintroduced | X + F (DSL) | R11 | open |  |
| C42 | §4, Def. 1 | 623–629 | multi-input AND/OR/XOR/XNOR; decomposition into / X / −1 two-input gates, sequential or tree | F | R11 | open |  |
| C43 | §4 | 623–629 | NAND, NOR functionally complete; XNOR/NAND/NOR negate one input | F | R11 | open |  |
| C44 | §4, Def. 2 | 623–629 | SEL; XOR replaceable by OR under one-hot selectors; BSEL | F | R11 | open |  |
| C45 | §4 | 623–629 | table lookup decomposes into single-bit outputs | F | R11 | open |  |
| C46 | §4; §4.1 ¶3 | 623–629 | optimal circuit synthesis "NP-hard based on circuit SAT" (P06) | R | R1 | R1 checked | source-checked: see P06 (Ilango, Loff, Oliveira, CCC 2020, https://drops.dagstuhl.de/opus/volltexte/2020/12574/) |
| C47 | §4; Fig. 3 | 623–629 | two table-lookup representations; nodes-vs-edges trade-off; Fig. 3 count comments | F | R11 | open |  |
| C48 | §4 | 623–629 | ripple addition (P05), subtraction with borrow, combined add/sub selector | F | R11 | open |  |
| C49 | §4 | 623–629 | constant time maintained; reusable subgraphs with activation edge and repetition; conditional execution loses constant time | F | R10 | open |  |
| C50 | §4.1 ¶1–2 | 625–626 | AES structure; key expansion by XOR + lookups; xtime as selection; S-box (P07); inverse | F + R | R12 | open |  |
| C51 | §4.1 ¶2 | 625–626 | S-box subgraph reuse; identification needs recognizing decoder circuits | M + X | R13, R16 | open |  |
| C52 | §4.1 ¶3 | 625–626 | spurious inputs/deeper circuits remove table uniformity | X | R1 | listed (X) |  |
| C53 | §4.2 ¶1 | 626–627 | RSA/PKCS background | R | R1 | R1 checked | standard: PKCS #1 / RFC 8017 (not opened) |
| C54 | §4.2 ¶1 | 626–627 | square-and-multiply O(Mn + Sn); windowing; addition chains [11] | F + R | R14 | open | source-partial: Clift, Computing 91 (2011) 265-284 (existence checked in the bib); O(Mn+Sn) is the textbook bound for square-and-multiply |
| C55 | §4.2 ¶1 | 626–627 | Karatsuba O(n^{log₂3}), Toom-Cook (P08), schoolbook O(n²), Schönhage–Strassen [7] | F + R | R14 | open | source-partial: Bernstein, Multidigit multiplication for mathematicians, 2001 (cr.yp.to/papers/m3.pdf); Karatsuba and Schönhage-Strassen are standard; Toom-k is P08 |
| C56 | §4.2 ¶1 | 626–627 | carry-save/Wallace; squaring about twice as fast | F (count) + X | R14 | open |  |
| C57 | §4.2 ¶1 | 626–627 | Montgomery multiplication/reduction correct; cost = multiplication × constant | F | R14 | open |  |
| C58 | §4.2 ¶2 | 626–627 | RBSD carry-free addition [21]; NAF/MOF lower weight; sliding windows/chains not constant time; ladder constant time | F (should/could) + X | R14 | open |  |
| C59 | §4.2 ¶3 | 626–627 | implementation: Montgomery form, Montgomery + Karatsuba, windows minimizing products, subgraph reuse | M + F | R14, R16 | open |  |
| C60 | §4.3, Tables 1–2 | 627–629 | Nodes, Edges, Exec. N, Exec. E | M | R16 | open |  |
| C61 | §4.3, Tables 1–2 | 627–629 | timings; RSA worse than quadratic; impractical after 256 bits (P10) | FD + X | R16 | open |  |
| C62 | §4.3 | 627–629 | machine-word reductions gain "2^32 or 2^64" (P09) | F | R14 | open |  |
| C63 | Fig. 3 | 628 | the listed Python equals the generator code | M | R11 | open |  |
| C64 | §5 ¶1 | 629–633 | ILs rare in C [25]; undecidability [18]; read-only code segments | R + X | R1 | R1 checked | source-checked: Stanier and Watson, Softw. Pract. Exper. 42(1) 2012, 117-130, abstract: irreducibility is extremely rare in open-source C |
| C65 | Fig. 4 | 630 | CFG, jungle with timestamps, Havlak LNF; C++ encodings | F + M | R3, R18 | partial | R2 Graph.Fig4 (CFG, jungle); R3 LNF.Fig4 (fig4_headers, fig4_bodies, fig4_irreducible, fig4_lnf, fig4_mee); R3b LNF.HvMain.havlak_hdr, havlak_irr (Havlak's algorithm = declarative LNF for every valid jungle); C++ encodings R18 |
| C66 | Table 3 | 630 | decompiler counts | X | R1 | listed (X) |  |
| C67 | §5, Def. 3 | 629–633 | K_n: / E / = n²−n; any root gives a CFG; n−1 headers in a chain; entry loop reducible; ≤ n−2 irreducible loops; / MEE(K_n) / = (n−1)(n−2)/2 | F | R4 | done | Extremal.Kn (canonical) and Extremal.KnAny (any root, any DFS): Kn_isCFG, Kn_edgeCount, Kn_comparable, Kn_headerCount_any, Kn_irrCount_any, Kn_meeCount_any; irrCount_le; meeCount_le (maximality) |
| C68 | §5, Def. 4 | 629–633 | M_n construction (P14), / E(M_n) / , / MEE(M_n) / = / MEE(K_n) / , MEE maximal, others minimal (P15, P16) | F | R4, R4c | done | Extremal.Mn/MnCount: Mn_edgeCount, Mn_meeCount_eq, Mn_classes_disjoint, Mn_eq_Kn_minus_back (P14), MnLite_others (P15 witness), Extremal.MinOther.maxMEE_others (every max-MEE CFG has >= 2n-3 other edges) |
| C69 | §5 | 629–633 | DCC/REC assumptions on Boolean latches | X + R | R1 | open | source-partial: Cifuentes, Latin American Informatics Conf. 1993 (not opened); REC Studio page cited without access date |
| C70 | §5 | 629–633 | node splitting needs a quadratic amount of duplication (P17) | R + F (should) | R18 | open | source-checked: Carter, Ferrante, Thomborson, POPL 2003, pp. 106-114 (PDF read): exponential, not quadratic; see P17 |
| C71 | §5 | 629–633 | 1- and 2-node CFGs never contain an IL | F | R3 | done | LNF.Small no_irreducible_of_small, threeNode_irreducible (every valid jungle), threeNode_dfs_valid |
| C72 | §5 | 629–633 | DREAM: n−2 integer variables; conditions by MEE; n−2 compound conditions | X + F (could) | R18 | open |  |
| C73 | §5 | 629–633 | minimal 2 edges for a sequence; simulated loop = one node + three edges + SMC/state variable | F | R17 | open |  |
| C74 | Figs. 5–6 | 632–633 | transformed programs equivalent; ILs induced; graphs match code (P18, P19) | F | R17 | open |  |
| C75 | §5 | 629–633 | inducing ILs on reducible loops by edges from unreached outside nodes | F | R17 | open |  |
| C76 | §5 | 629–633 | two-way / n-way extension; conditions from separate 2-SAT outputs; SMC or negated state variable | F | R17, R19 | open |  |
| C77 | §5 | 629–633 | dynamic scheme: dependency order guarantees all dependencies ran, in order; bounded duplication; input-tied order | F | R19 | open |  |
| C78 | §5.1 ¶1 | 634–635 | security goals; automated vs manual attacks; CFG identification as hard as circuit identification | FT + X | R20a | open |  |
| C79 | §5.1 ¶2 | 634–635 | "indistinguishable … from a practical standpoint" (P23) | FT + R | R20b | open | source-partial: Buttyán-Horváth survey = ePrint 2015/412 (exists; iO under standard assumptions open); Xu et al. arXiv:1710.01139 listed in the published bibliography |
| C80 | §5.1 ¶3 | 634–635 | both schemes practically resistant to static analysis | FT | R20a | open |  |
| C81 | §5.1 ¶4 | 634–635 | DFA resistance, final execution; DCA/DPA (P21, P22) | FT | R19, R20b | open | source-checked for DCA/DPA: Bos, Hubain, Michiels, Teuwen, CHES 2016 (ePrint 2015/753); see P21 |
| C82 | §5.1 ¶5 | 634–635 | Banescu framework; opaque predicates defeated only in contrived scenarios; SMC symbolic execution beyond tools; exponential dynamic time (P24) | R + FT + X | R20a, R20b | open | source-partial: Banescu, Ochoa, Pretschner, SPRO 2015, 45-51, doi 10.1109/SPRO.2015.16 exists; the quoted statement about opaque predicates defeated only in simple contrived scenarios could not be located online: UNVERIFIED |
| C83 | §6 | 635 | summary; open definitional questions for SMC; Kolmogorov complexity | X | R1 | listed (X) |  |

New claims found in R1 (no seed existed):

| ID | Location | Page | Claim | Class | Round | Status | Declaration / evidence / source |
|---|---|---|---|---|---|---|---|
| C84 | §4.2 ¶3 | 627 | a CFG without subgraph reuse becomes too large through "exponential growth of multiplication" (P28) | F | R14 | open | |
| C85 | §1 ¶5; §5.1 ¶3 | 618, 634 | the scheme is beyond any state-of-the-art static analysis tool / practically resistant to static analysis (P29) | FT | R20a | open | |

## Open obligations

See `lean/GAPS.md` (single register; every `partial`/`open` row here has a G-row there).
