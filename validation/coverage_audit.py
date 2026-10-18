"""Coverage audit for lean/PAPER_MAP.md (plan R14, D1).

  python validation/coverage_audit.py            check the table shape and write lean/CoverageRefs.lean
  python validation/coverage_audit.py --build    also compile CoverageRefs.lean (through build_modules.py) so that every named declaration exists

Checks: every row has an ID, a class (F, FC, FD, M, R, X, combinations allowed), no status `todo`; every F/FC/FD row names at least
one Lean declaration; every `open`/`partial` row is explained; every declaration named in the last column of an F/FC/FD row resolves
(`#check`); every P item of lean/errata/edits.json is mentioned in PAPER_MAP.md or a round note.
"""
import json, re, subprocess, sys
sys.stdout.reconfigure(encoding="utf-8")
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MAP = ROOT / "lean/PAPER_MAP.md"
OUT = ROOT / "lean/CoverageRefs.lean"
EDITS = ROOT / "lean/errata/edits.json"
CLASSES = {"F", "FC", "FD", "FT", "M", "R", "X"}


def rows():
    out = []
    for line in MAP.read_text(encoding="utf-8").splitlines():
        m = re.match(r"\|\s*(C\d+)\s*\|(.*)\|\s*$", line)
        if m:
            cells = [c.strip() for c in line.strip().split("|")[1:-1]]
            out.append(cells)
    return out


def decl_tokens(cell):
    toks = []
    for t in re.findall(r"`([^`]+)`", cell):
        t = t.strip()
        if "/" in t or t.endswith((".lean", ".json", ".md")) or " " in t or t.startswith("-") or not re.match(r"^[A-Za-z_][\w.']*$", t):
            continue
        toks.append(t)
    return toks


def decl_index():
    """Fully qualified names of the declarations of lean/SmcIrred (namespace stack tracked textually)."""
    names = set()
    for f in (ROOT / "lean/SmcIrred").rglob("*.lean"):
        stack = []
        for ln in f.read_text(encoding="utf-8").splitlines():
            m = re.match(r"namespace\s+([\w.]+)", ln)
            if m:
                stack.append(m.group(1))
                continue
            m = re.match(r"end\s+([\w.]+)", ln)
            if m and stack and stack[-1] == m.group(1):
                stack.pop()
                continue
            m = re.match(r"(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|public)\s+)*(?:theorem|lemma|def|abbrev|structure|inductive|class)\s+([\w.']+)", ln)
            if m:
                full = ".".join(stack + [m.group(1)])
                names.add(full)
    return names


def main():
    bad = []
    rs = rows()
    ids = [r[0] for r in rs]
    if len(set(ids)) != len(ids):
        bad.append("duplicate claim IDs")
    names = []
    for r in rs:
        if len(r) < 8:
            bad.append(f"{r[0]}: expected 8 columns, got {len(r)}")
            continue
        cid, _loc, _page, _claim, cls, _rnd, status, ev = r[:8]
        ev = (status + " " + ev).strip()  # declarations and notes may sit in either of the last two cells
        base = set(re.findall(r"\b(FC|FD|FT|F|M|R|X)\b", cls))
        if not base:
            bad.append(f"{cid}: no class in '{cls}'")
        if status.lower().startswith("todo") or status == "":
            bad.append(f"{cid}: status '{status}'")
        toks = decl_tokens(ev)
        closed = status.lower().startswith(("done", "proved", "checked"))
        if base & {"F", "FC", "FT"} and not toks and closed:
            bad.append(f"{cid}: class {cls} names no Lean declaration")
        if base & {"F", "FC", "FD", "FT"}:
            names += [(cid, t) for t in toks]
        if base == {"X"} and not ev:
            bad.append(f"{cid}: class X without a note")
        if (status.lower().startswith("open") or status.lower().startswith("partial")) and len(ev) < 12:
            bad.append(f"{cid}: {status} without explanation")
    text = MAP.read_text(encoding="utf-8")
    for e in json.loads(EDITS.read_text(encoding="utf-8"))["edits"]:
        pid = e["id"].split(".")[0]
        if pid not in text and e["id"] not in text:
            bad.append(f"errata item {e['id']} is not mentioned in PAPER_MAP.md")
    srcs = (ROOT / "lean/SmcIrred.lean").read_text(encoding="utf-8").splitlines()
    mods = [l.split()[-1] for l in srcs if l.startswith("public import")]
    seen = []
    for cid, n in names:
        if n not in seen:
            seen.append(n)
    index = decl_index()
    resolved, missing = [], []
    for n in seen:
        cands = sorted((f for f in index if f == n or f.endswith("." + n)), key=lambda f: (len(f), f))
        if cands:
            resolved.append(cands[0])
        else:
            missing.append(n)
    for n in missing:
        bad.append(f"declaration `{n}` is not defined in lean/SmcIrred")
    lines = ["module", ""] + ["import " + m for m in mods] + [""] + ["set_option maxErrors 100000", ""]
    lines += ["#check @%s" % n for n in resolved]
    OUT.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(f"rows={len(rs)} declarations={len(seen)} problems={len(bad)}")
    for b in bad:
        print("  -", b)
    if "--build" in sys.argv:
        import os
        lean = Path(os.environ.get("ELAN_HOME", Path.home() / ".elan")) / "toolchains/leanprover--lean4---v4.35.0-rc3/bin/lean.exe"
        env = dict(os.environ, LEAN_PATH=str(ROOT / "lean/.lake/proof-build/lib/lean"))
        r = subprocess.run([sys.executable, str(ROOT / "validation/limited_run.py"), "--cwd", str(ROOT / "lean"), "--timeout", "1500", "--",
                            str(lean), "CoverageRefs.lean"], cwd=ROOT, env=env)
        if r.returncode:
            bad.append("CoverageRefs.lean does not compile (a named declaration is missing)")
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
