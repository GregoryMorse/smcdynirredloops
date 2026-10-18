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
| `Struct`, `Trace`, `Fault`, `Dca` | added with T4–T6 | R20b |

Goal `Determines A img`: the analyzer reports every cell the program reads with its run-time value.
Assumptions (`structure Assumptions`; no field mentions a goal, checked by `validation/threat_audit.py`):
S1 planted formula (`planted`, `extra_respects`, `extra_wf`, `stamped`); S2 the cells read are planted, required, false-valued
(`cells_planted`); S3 the dynamic schedule respects dependencies (`schedule_topo`, `schedule_ordered`). S4 (class capability
bounds) is the capability structures themselves. Necessity witnesses for S1–S3: R20b.

## 3. Theorems proved in R20a
* T1 `Threat.correct`: under S1–S3 the image executes exactly the blocks of the original (both condition values), and the
  final values of the dynamic schedule are the circuit's values.
* T2 `imm_fails`, `imm_determines_iff`, `imm_unsound` (witness design satisfying S1–S3, blueprint true, run-time false),
  `static_reading_wrong` (behavioural difference for the four programs).
* T3 `recover`, `smcsem_determines`: an `SmcSem` analyzer reports the intended values; the work bound `2|V|+|E|` is in the clean
  Tarjan cost model of the implication graph (`tarjan_cost`), not a bound on the machine (G27/R8b).
  Opacity is therefore relative to analyzers lacking the machine semantics; it is not computational hardness.

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
