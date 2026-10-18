"""Evidence (class M, not proof): compare the Lean model of to_rbsd/add_rbsd (Spec/RBSD.lean) with python/virt.py.

Every signed-digit list of at most 5 digits is recoded, and 300 additions/subtractions of recoded operands are replayed;
the generated Lean file checks each result by `decide`. Run: python validation/rbsd_vectors.py
"""
import itertools, os, random, subprocess, sys, tempfile

root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(root, "python"))
import virt


def lst(l): return "[" + ", ".join("(%d : Int)" % d for d in l) + "]"


def main():
    random.seed(5)
    lines = ["import SmcIrred.Arith.RBSD", "open SmcIrred.Arith"]
    cases = [list(t) for n in range(6) for t in itertools.product((-1, 0, 1), repeat=n)]
    for c in cases:
        lines.append("example : rToRbsd %s = some %s := by decide" % (lst(c), lst(virt.to_rbsd(c))))
    rec = [virt.to_rbsd(c) for c in cases if len(c) <= 3]
    random.shuffle(rec)
    for i in range(150):
        a, b = rec[i % len(rec)], rec[(i * 7 + 3) % len(rec)]
        for sub in (False, True):
            lines.append("example : rAdd %s %s %s = some %s := by decide"
                         % (lst(a), lst(b), "true" if sub else "false", lst(virt.add_rbsd(a, b, sub))))
    path = os.path.join(tempfile.mkdtemp(), "rbsd_check.lean")
    with open(path, "w") as f: f.write("\n".join(lines) + "\n")
    r = subprocess.run([sys.executable, os.path.join(root, "validation", "lean_scratch.py"), path])
    sys.exit(r.returncode)


if __name__ == "__main__":
    main()
