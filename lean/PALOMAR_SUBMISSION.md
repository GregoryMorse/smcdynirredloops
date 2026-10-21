# Palomar submission values (draft; nothing has been submitted or registered)

The user submits and registers; the assistant never does. The commit is the pushed R24 commit named in the handoff
(`validation/rounds/R24.json`); a later commit needs a fresh check.

| Field | Value |
|---|---|
| Repository | `GregoryMorse/smcdynirredloops` |
| Commit | the exact 40-character SHA of the pushed R24 commit (see the handoff) |
| Project directory (`project_path`) | `lean` |
| Comparator configuration | `lean/comparator.json` (theorem `PalomarSIL.mathematical_result`; Challenge `Challenge`, Solution `Solution`) |
| Second Comparator configuration (optional, separate registration identity) | `lean/comparator-aes.json` (`ChallengeAES`, `SolutionAES`) |
| Formalization metadata | `lean/formalization.yaml` |
| Existing Palomar ID | blank (new result) unless the registry identity query says otherwise |
| Relationship | the user's truthful attestation: responsible author/maintainer (the formalizer is the paper's first author) |
| Preliminary-check override | not used; the official workflow is `.github/workflows/palomar-full.yml` (`mode: full`, pinned to PalomarSubmission `d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44`, `request_id: smcirred1`), dispatched by the user |

## Notes for the submission form (public-safe)

AI-assisted formalization (Claude Opus 5.5 planning, Claude Sonnet 5.5 execution, Claude Code); statements, threat model and
decisions by the author; self-assessed review. The Challenge is generated from `lean/SmcIrred/Spec/` (`validation/make_challenge.py`).
Size: `Challenge.lean` is 985 lines (51 KB) and `ChallengeAES.lean` 626 lines (26 KB), above the 300-line/32 KiB warning size and under
the hard limit; the statements need the definitions of the self-modifying machine, DFS jungles, the extremal graphs and the
security model. The security statements hold relative to explicit structural assumptions, each with a necessity witness, and
claim nothing about real tools. Non-claims (timings, native code, node splitting, literature opinions) are listed in
`lean/PALOMAR_SEMANTICS.md` and `lean/PAPER_MAP.md`; open author questions are in `lean/errata/QUESTIONS.md`.

## Mechanical state at the recorded commit

* Local: `lake build SmcIrred Challenge Solution ChallengeAES SolutionAES` (serial, memory-capped), axiom audit
  (`validation/axiom_audit.py`: only `propext`, `Quot.sound`, `Classical.choice`), `make_challenge.py --check`,
  `coverage_audit.py`, `threat_audit.py`, `check_tables.py`, `audit_errata.py`, `validate_metadata.py`.
* CI: `proof.yml` (cold Linux build, axiom audit, generated-file and audit checks, Windows native baseline).
* Not run: the official `palomar-full.yml` (needs the user's go-ahead; the assistant reports it UNVERIFIED); Comparator and NanoDa are
  its job.
