# Threat model (D11; round R20a, sections 1–3)

Scope: what the Lean development states about the security discussion of §5.1 of the paper, and exactly what it does not.
Nothing here claims that a real tool fails or succeeds; classes of analyzers are interfaces with a stated capability.

## 1. System (`lean/SmcIrred/Spec/Threat.lean`)
* Original program: a `Stmt` of the transformation language (`Spec/Lang.lean`); its blocks are abstract (any computation).
* Obfuscator `Obfuscates`: the static scheme of Figures 5 and 6 (loop and conditional transformations), with the opaque
  conditions read as outputs `Cond.out k` of the self-modifying-code 2-SAT solver (`smcSolve`) on a planted formula.
* Image: transformed program, stamped formula, blueprint (the placeholder values in the static code bytes).
* Run-time value of a predicate cell: `rtVal img k`. Behaviour: `Image.run`. Static reading: `Image.staticRun`.

## 2. Adversary classes, goals, assumptions
| Class | Capability (structure) | Status |
|---|---|---|
| `Imm` | `ImmCap`: predicts every cell as its static code byte | R20a |
| `SmcSem` | `SmcSemCap`: predicts every cell as its run-time value (implements stamping and machine semantics) | R20a |
| `Struct` | restructures the CFG; state variables (`one_variable_suffices`) | R20b |
| `Trace`, `Dca` | see `obs`, `finalObs` (address, value) pairs | R20b |
| `Fault` | one replaced write `(v, some d)` | R20b |

Goal `Determines A img`: the analyzer reports every cell the program reads with its run-time value.
Assumptions (`structure Assumptions`; no field mentions a goal, checked by `validation/threat_audit.py`):
S1 planted formula (`planted`, `extra_respects`, `stamped`; that the extra implications mention only the `n` variables is a typing field `Design.extra_wf` of the data, not an assumption); S2 the cells read are planted, required, false-valued
(`cells_planted`); S3 the dynamic schedule respects dependencies (`schedule_topo`, `schedule_ordered`). S4 (class capability
bounds) is the capability structures themselves. Necessity witnesses: below.

## 3. Theorems proved in R20a
* T1 `Threat.correct`: under S1–S3 the image executes exactly the blocks of the original (both condition values), and the
  final values of the dynamic schedule are the circuit's values. `Obfuscates` relates the four fixed programs of Figures 5 and 6
  (T1 and T2 are results about those four, not about arbitrary structured programs; `TransformCorrect` states the equivalence
  of the transformations for arbitrary structured programs).
* T2 `imm_fails`, `imm_determines_iff`, `imm_unsound` (witness design satisfying S1–S3, blueprint true, run-time false),
  `static_reading_wrong` (behavioural difference for the four programs).
* T3 `recover`, `smcsem_determines`: an `SmcSem` analyzer reports the intended values; the Tarjan run on the implication graph
  costs at most `2|V|+|E|` steps in the clean cost model (`tarjan_cost`); this bounds that run, not the work of an arbitrary
  analyzer nor the machine (G27/R8b).
  Opacity is therefore relative to analyzers lacking the machine semantics; it is not computational hardness.

## 3b. Theorems proved in R20b
* T4 `one_variable_suffices` (flattening, no duplication), `quadratic_is_edge_count` (`2·MEE = (n−1)(n−2)` for K_n). The
  exponential node-splitting bound of Carter–Ferrante–Thomborson is cited, not proved (G33).
* T5 `fault_class` (non-final fault harmless), with `Dyn.fault_final_overwrites`, `fault_final_changes`, `fault_input_dependent`.
* T6 `dca_last`, `dca_final_obs`, `dca_repeats_visible`, `dca_witness`: on address-aligned traces any two dependency-respecting
  schedules give the same (vertex, final value) pairs; repeated executions are visible by address.
* T7 `not_size_indist`, `scheme_overhead`: not an indistinguishability obfuscator for the vertex count; no VBB claim.
* Necessity: `nec_forcing`, `nec_stamped`, `nec_false_cells` (run misbehaves), `nec_extra_respects` (solver returns nothing),
  `nec_schedule`, `nec_topo` (no ordered schedule exists in a cyclic circuit), `ncirc_not_topo`, `ncirc_ordered`, `ncirc_bad` (an acyclic circuit that is not numbered topologically: it has an ordered schedule, yet the final value of vertex 0 differs from `valOf`, so dropping only `schedule_topo` makes the conclusion fail). `extra_wf` is not an assumption: it is a field of `Design` (a formula over its n variables), so it needs no witness.
* `Threat.solver_succeeds`: under S1 the solver returns a solution.

## 3c. Non-claims (G36)
These are scope statements: none of them is proved, assumed or hidden in a hypothesis.
* T4 has no lower bound on node splitting or on any restructuring method's cost (Carter-Ferrante-Thomborson and DREAM are literature, G33).
* The classes `Struct`, `Trace`, `Fault` and `Dca` are views of the model (state variable, `obs`, a replaced write, `finalObs`), not
  attacker algorithms; no lower bound on the cost of any analyzer is claimed.
* T7 concerns the vertex-count observable only; it is not a statement about any other observable and not about virtual black-box
  obfuscation.
* Assumptions S1-S3 are structural and each has a necessity witness (`nec_*`); `extra_wf` is a typing field, not an assumption.

## 4. Literature pass (D11 list)
Verified online this round: Barak et al., J. ACM 59(2), 2012, doi 10.1145/2160158.2160159 (impossibility of black-box
obfuscation in general; the model: virtual black box); Collberg–Thomborson–Low, POPL 1998, pp. 184–196 (opaque constructs;
potency/resilience/cost/stealth; DOI not located); Banescu et al., ACSAC 2016, pp. 189–200 (symbolic-execution
deobfuscation; author spelling Newsham; DOI inferred 10.1145/2991079.2991114, UNVERIFIED); Bos–Hubain–Michiels–Teuwen,
CHES 2016, doi 10.1007/978-3-662-53140-2_11, pp. 215–236 (differential computation analysis of white-box AES);
Banescu–Ochoa–Pretschner, SPRO 2015, pp. 45–51 (doi 10.1109/SPRO.2015.16, per PAPER_MAP C82). Not yet checked:
Carter–Ferrante–Thomborson 2003, Wang 2001, Chow 2001, Landi 1992, and the §5.1 quotation about opaque predicates
(UNVERIFIED) — G35, owner R20b.
Mapping: Barak et al. rule out general virtual-black-box guarantees, so no such guarantee is claimed here; CTL98 opaque
predicates correspond to the cells read through `Imm`; Banescu et al. and Bos et al. are the `SmcSem`-like and `Dca`/`Trace`
classes.
