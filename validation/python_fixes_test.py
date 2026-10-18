"""Unit tests for the Python code fixes L03-L05, L11 (python/virt.py). Usage: python validation/python_fixes_test.py"""
import os, subprocess, sys
from pathlib import Path
PY = Path(__file__).resolve().parents[1] / "python"
sys.path.insert(0, str(PY))
import virt
# L03: set_bit_range replaces the slice [start, end) (BITSZ = 1), not a strided slice
num = list(range(10))
virt.set_bit_range(num, 2, 5, [90, 91, 92])
assert num == [0, 1, 90, 91, 92, 5, 6, 7, 8, 9], num
num = list(range(6))
virt.set_bit_range(num, 4, None, [7, 8])
assert num == [0, 1, 2, 3, 7, 8], num
# L04: reduce_all with outmap None does not raise
op, g = {}, {0: []}
virt.reduce_all(op, g, [0], None)
# L11: modexpMontgomeryWindow prints nothing
src = (PY / "virt.py").read_text(encoding="utf-8")
assert "print(tbl)" not in src and "def mul_window" not in src and "def mul_const_window" not in src
# L05: SMCIRRED_SEED makes the shuffles reproducible, the default is untouched
code = "import sys; sys.path.insert(0, %r); import virt, random; print(random.random())" % str(PY)
def run(seed):
    env = dict(os.environ)
    env.pop("SMCIRRED_SEED", None)
    if seed is not None: env["SMCIRRED_SEED"] = seed
    return subprocess.run([sys.executable, "-c", code], capture_output=True, text=True, env=env).stdout
assert run("7") == run("7") and run("7") != run("8")
print("python fixes: ok")
