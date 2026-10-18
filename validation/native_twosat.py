"""Build and run the native 2-SAT harness (plan R8 item 2) with MSVC: python validation/native_twosat.py [--archs x64 x86]
[--vm]. Needs validation/data/twosat_vectors.txt (regenerate: python validation/lean_scratch.py validation/TwoSatVectors.lean).
Writes validation/rounds/R8_native.json. Mechanical evidence about the compiled product code on this machine only."""
import argparse, json, subprocess, sys, time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "validation"))
from native import vcvars  # noqa: E402

def run(cmd, cwd):
    r = subprocess.run([sys.executable, str(ROOT / "validation/limited_run.py"), "--cwd", str(cwd), "--"] + cmd,
                       capture_output=True, text=True, encoding="utf-8", errors="replace")
    return r.returncode, (r.stdout + r.stderr)

def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--archs", nargs="*", default=["x64", "x86"])
    ap.add_argument("--vm", action="store_true")
    a = ap.parse_args()
    out_dir = ROOT / "validation/.build/native"
    out_dir.mkdir(parents=True, exist_ok=True)
    results = {}
    for arch in a.archs:
        exe = out_dir / f"twosat_harness_{arch}{'_vm' if a.vm else ''}.exe"
        defs = "/DUSE_VM " if a.vm else ""
        build = (f'call "{vcvars(None)}" {arch} >nul && cl /nologo /EHsc /O2 /std:c++17 /w {defs}'
                 f'/Fo:"{out_dir}\\\\" /Fe:"{exe}" validation/native/twosat_harness.cpp')
        t = time.time()
        bat = out_dir / f"build_{arch}.bat"
        bat.write_text('@echo off' + chr(13) + chr(10) + build + chr(13) + chr(10))
        rc, log = run(["cmd", "/c", str(bat)], ROOT)
        rec = {"build_ok": rc == 0 and exe.exists(), "build_seconds": round(time.time() - t)}
        if not rec["build_ok"]:
            rec["build_tail"] = log[-2500:]
        else:
            t = time.time()
            rc, log = run([str(exe), str(ROOT / "validation/data/twosat_vectors.txt")], ROOT)
            rec.update(run_ok=rc == 0, run_seconds=round(time.time() - t), run_tail=log[-1500:])
        results[f"msvc-{arch}{'-vm' if a.vm else ''}"] = rec
        print(arch, json.dumps(rec)[:1500], flush=True)
    p = ROOT / "validation/rounds/R8_native.json"
    old = json.loads(p.read_text()) if p.exists() else {}
    old.update(results)
    p.write_text(json.dumps(old, indent=1) + "\n")
    return 0 if all(v.get("run_ok") for v in results.values()) else 1

if __name__ == "__main__":
    sys.exit(main())
