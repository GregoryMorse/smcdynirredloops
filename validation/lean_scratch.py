"""Run one scratch Lean file under the memory guard: python validation/lean_scratch.py <file.lean> (imports resolve against the built library)."""
import sys as _s; _s.stdout.reconfigure(encoding="utf-8", errors="replace")
import subprocess, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
BIN = Path.home() / ".elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin/lean.exe"
src = Path(sys.argv[1]).resolve()
if src.suffix != ".lean":
    # `.leanscript` files are interpreter scripts (plain `import`, not part of the project): run them as a temporary `.lean`
    import tempfile
    tmp = Path(tempfile.mkdtemp()) / (src.stem + ".lean")
    tmp.write_bytes(src.read_bytes())
    src = tmp
r = subprocess.run([sys.executable, str(ROOT / "validation/limited_run.py"), "--cwd", str(ROOT / "lean"), "--",
                    str(BIN), str(src)], capture_output=True, text=True, encoding="utf-8", errors="replace")
print(r.stdout[-12000:], r.stderr[-2000:])
sys.exit(r.returncode)
