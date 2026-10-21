"""CI axiom audit: import SmcIrred (all modules) and, in turn, Solution and SolutionAES (they declare the same name
`PalomarSIL.mathematical_result`, so they cannot be imported together); every constant declared in a
SmcIrred.* module or in the Solution module may depend only on propext, Quot.sound, Classical.choice
(`sorryAx`, `Lean.ofReduceBool`, custom axioms count as violations). Run from the repository root
after `lake build`:  python3 validation/ci/axioms.py   (uses `lake env lean` in lean/)."""
import subprocess, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[2]
TEMPLATE = """import Lean.Util.CollectAxioms
import Lean.CoreM
import SmcIrred
import SOLUTION
open Lean
def okAx : List Name := [`propext, `Quot.sound, `Classical.choice]
#eval show CoreM Unit from do
  let env ← getEnv
  let mut n := 0
  let mut bad : Array String := #[]
  for (name, _) in env.constants.map₁.toList do
    if let some idx := env.getModuleIdxFor? name then
      let root := (env.header.moduleNames[idx.toNat]!).getRoot
      if root == `SmcIrred || root == `SOLUTION then
        n := n + 1
        let axs ← collectAxioms name
        for a in axs do
          if !(okAx.contains a) then bad := bad.push s!"{name} uses {a}"
  let hasMain := env.contains `PalomarSIL.mathematical_result
  IO.println s!"AUDIT SOLUTION declarations={n} violations={bad.size} main={hasMain}"
  for b in bad do IO.println b
"""
def main():
    ok = True
    for sol in ("Solution", "SolutionAES"):
        f = ROOT / "lean" / "AxiomAuditCI.lean"
        f.write_text(TEMPLATE.replace("SOLUTION", sol), encoding="utf-8")
        try:
            r = subprocess.run(["lake", "env", "lean", f.name], cwd=ROOT / "lean", capture_output=True, text=True)
        finally:
            f.unlink()
        print(r.stdout, r.stderr[-2000:])
        ok = ok and r.returncode == 0 and "violations=0" in r.stdout and "main=true" in r.stdout
    sys.exit(0 if ok else 1)
main()
