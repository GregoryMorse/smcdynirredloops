#!/usr/bin/env bash
# Linux proof job body (run inside a bounded cgroup by .github/workflows/proof.yml):
# cold build of the library, the Challenge and the Solution, axiom audit, generated-file checks.
# No Mathlib (plan D4). Later rounds append their checks (make_challenge, audit_errata, coverage, threat).
set -euo pipefail
export PATH="$HOME/.elan/bin:$PATH"
cd "$(dirname "$0")/../.."
ROOT="$PWD"
cd lean
lean --version
lake build SmcIrred Challenge Solution ChallengeAES SolutionAES 2>&1 | tee "$ROOT/lake-build.log"
cd "$ROOT"
python3 validation/ci/axioms.py
# generated-file and audit checks (R24): Challenge files regenerate byte-for-byte, coverage and threat audits
# (audit_errata.py and check_tables.py read the published PDF / manuscript TeX, which are never committed: local only)
python3 validation/make_challenge.py --check
python3 validation/coverage_audit.py
python3 validation/threat_audit.py
echo "linux-proof: OK"
