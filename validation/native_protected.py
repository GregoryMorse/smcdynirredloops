"""Build and run native/protected.c (plan R19b) with MSVC: python validation/native_protected.py [--archs x64 x86].
Self-test: FIPS-197 and random AES-128 (plain vs protected), a known 32-bit RSA vector, 200 planted formulas (satisfiable,
required outputs are the planted values, every implication respects the planted assignment). Writes
validation/rounds/R19b_native.json. Mechanical evidence about the compiled code on this machine only."""
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
    a = ap.parse_args()
    out_dir = ROOT / "validation/.build/native"
    out_dir.mkdir(parents=True, exist_ok=True)
    results = {}
    for arch in a.archs:
        exe = out_dir / f"protected_{arch}.exe"
        build = (f'call "{vcvars(None)}" {arch} >nul && cl /nologo /O2 /W3 /TC /Fo:"{out_dir}\\\\" /Fe:"{exe}" native/protected.c')
        bat = out_dir / f"build_protected_{arch}.bat"
        bat.write_text("@echo off" + chr(13) + chr(10) + build + chr(13) + chr(10))
        t = time.time()
        rc, log = run(["cmd", "/c", str(bat)], ROOT)
        rec = {"build_ok": rc == 0 and exe.exists(), "build_seconds": round(time.time() - t)}
        if not rec["build_ok"]:
            rec["build_tail"] = log[-2500:]
        else:
            rc, log = run([str(exe)], ROOT)
            rec.update(run_ok=rc == 0, run_tail=log[-600:])
        results[f"msvc-{arch}"] = rec
        print(arch, json.dumps(rec)[:1200], flush=True)
    p = ROOT / "validation/rounds/R19b_native.json"
    p.write_text(json.dumps(results, indent=1) + "\n")
    return 0 if all(v.get("run_ok") for v in results.values()) else 1


if __name__ == "__main__":
    sys.exit(main())
