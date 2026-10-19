"""Threat-model audit: no field of `structure Assumptions` (Spec/Threat.lean) may mention a goal
(Determines, Recovers, wins, Breaks, Defeats, detection...) in its statement. Docstrings are stripped first.
Usage: python validation/threat_audit.py"""
import re, sys
from pathlib import Path
src = (Path(__file__).parent.parent / "lean/SmcIrred/Spec/Threat.lean").read_text(encoding="utf8")
start = src.index("structure Assumptions")
end = src.index("\n/--", start)
body = src[start:end]
bad = re.compile(r"\b(Determines|Recovers?|Alarm|alarm|Wins|wins|Breaks?|Defeats?|Fails|detect\w*|ExecViolation|attacker\w*)\b")
errs = []
code = re.sub(r"/--.*?-/", "", body, flags=re.S)
for ln in code.splitlines()[1:]:
    mm = bad.search(ln)
    if mm:
        errs.append(f"assumption text mentions '{mm.group(0)}': {ln.strip()}")
names = re.findall(r"\n  (\w+) :", code)
print("fields:", ", ".join(names))
if len(names) < 6:
    errs.append("expected the six Assumptions fields (extra_wf is a typing field of Design)")
if errs:
    print("\n".join(errs)); sys.exit(1)
print("THREAT AUDIT OK: no Assumptions field mentions a goal")
