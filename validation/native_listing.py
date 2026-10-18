"""Figure 2(a) check (plan R8 item 3): assemble native/selfmodmodel.asm with ml64 (/Fl /Sa), run the product's
parseasmlisting on the listing and compare its byte arrays and offset constants with those in native/selfmodgraph.cpp
(x64 Windows block). Usage: python validation/native_listing.py. Writes validation/rounds/R8_listing.json.
Mechanical evidence only: it compares two texts, it proves nothing about the processor."""
import json, re, subprocess, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "validation"))
from native import vcvars  # noqa: E402

B = ROOT / "validation/.build/native"
B.mkdir(parents=True, exist_ok=True)


def run(cmd, cwd=ROOT):
    r = subprocess.run([sys.executable, str(ROOT / "validation/limited_run.py"), "--cwd", str(cwd), "--"] + cmd,
                       capture_output=True, text=True, encoding="utf-8", errors="replace", stdin=subprocess.DEVNULL)
    return r.returncode, r.stdout + r.stderr


def norm(text):
    """name -> list of byte tokens; offset constants name -> expression (whitespace removed)."""
    arrays, consts = {}, {}
    for m in re.finditer(r"unsigned char (\w+)\[\]\s*=\s*\{(.*?)\};", text, re.S):
        body = re.sub(r"//[^\n]*", "", m.group(2))
        arrays[m.group(1)] = [t.lower() for t in re.findall(r"0x[0-9A-Fa-f]{2}", body)]
    for m in re.finditer(r"const size_t (\w+)\s*=\s*([^;]*);", text):
        expr = re.sub(r"\s+", "", m.group(2)).lower()
        consts[m.group(1)] = expr
    return arrays, consts


def main() -> int:
    bat = B / "listing.bat"
    bat.write_text("@echo off" + chr(13) + chr(10) +
                   f'call "{vcvars(None)}" x64 >nul' + chr(13) + chr(10) +
                   f'cd /d "{B}"' + chr(13) + chr(10) +
                   f'ml64 /nologo /c /DWINDOWS /Fl /Sa /Fo selfmodmodel.obj "{ROOT / "native/selfmodmodel.asm"}"' + chr(13) + chr(10) +
                   f'cl /nologo /EHsc /O2 /w /std:c++17 /Fo:listing.obj /Fe:listing_x64.exe "{ROOT / "validation/native/listing_harness.cpp"}"' + chr(13) + chr(10))
    rc, log = run(["cmd", "/c", str(bat)])
    print(log[-1500:])
    if rc != 0:
        return 1
    rc, log = run([str(B / "listing_x64.exe"), str(B / "selfmodmodel.lst")])
    # the limited runner mixes stdout and stderr; keep the text between the first array and the end
    (B / "parsed_x64.txt").write_text(log, encoding="utf-8")
    parsed = norm(log)
    src = (ROOT / "native/selfmodgraph.cpp").read_text(encoding="utf-8", errors="replace")
    lo = src.index("selfmodtwosatasm(std::vector")
    hi = src.index("selfmodvmtwosathl")
    block = src[lo:hi]
    # restrict to the Windows x64 branch
    w = block.index("#if defined(_WIN32) || defined(_WIN64)")
    e = block.index("#else", w)
    ref = norm(block[w:e])
    res = {"parsed_arrays": {k: len(v) for k, v in parsed[0].items()},
           "source_arrays": {k: len(v) for k, v in ref[0].items()},
           "arrays_equal": {k: parsed[0].get(k) == v for k, v in ref[0].items()},
           "consts_equal": {k: parsed[1].get(k) == v for k, v in ref[1].items()},
           "const_diffs": {k: [parsed[1].get(k), v] for k, v in ref[1].items() if parsed[1].get(k) != v}}
    res["ok"] = bool(ref[0]) and all(res["arrays_equal"].values()) and all(res["consts_equal"].values())
    (ROOT / "validation/rounds/R8_listing.json").write_text(json.dumps(res, indent=1) + "\n")
    print(json.dumps({k: res[k] for k in ("parsed_arrays", "source_arrays", "arrays_equal", "ok")}, indent=1))
    print(json.dumps(res["const_diffs"], indent=1)[:2500])
    return 0 if res["ok"] else 1


if __name__ == "__main__":
    sys.exit(main())
