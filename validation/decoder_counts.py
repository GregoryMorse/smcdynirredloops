"""Node and edge counts of the legacy decoder generators against the Lean cost theorems (G30 c).

  python validation/limited_run.py -- python validation/decoder_counts.py

Runs `decoder_to_virtual` and `decoder_shift_to_virtual` of python/virt.py on `m` fresh input nodes and compares the created
nodes and edges with `SmcIrred.decoder_cost_ge2` (n = (m+4) 2^(m-1), e = (3m+2) 2^(m-1) for m >= 2) and
`SmcIrred.decoderShift_cost` (n = 2^(m+1) + m - 4, e = 2^(m+2) + m - 8 for m >= 1). This is evidence about the legacy code
(class M), not a proof; the Lean theorems are about the transcription in `Prims`.
"""
import sys
from pathlib import Path

sys.stdout.reconfigure(encoding="utf-8")
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "python"))
import virt  # noqa: E402


def counts(builder, m):
    node, g, op, _subg = virt.make_graph()
    inp = virt.make_input(m, node, g, op)
    base_nodes = node[0]
    base_edges = sum(len(v) for v in g.values())
    builder(inp, node, g, op)
    return node[0] - base_nodes, sum(len(v) for v in g.values()) - base_edges


def main():
    bad = 0
    for m in range(1, 9):
        n, e = counts(virt.decoder_shift_to_virtual, m)
        ln, le = 2 ** (m + 1) + m - 4, 2 ** (m + 2) + m - 8
        ok = (n, e) == (ln, le)
        bad += not ok
        print(f"decoder_shift m={m}: nodes {n} (Lean {ln}), edges {e} (Lean {le}) {'OK' if ok else 'MISMATCH'}")
    for m in range(2, 9):
        n, e = counts(virt.decoder_to_virtual, m)
        ln, le = (m + 4) * 2 ** (m - 1), (3 * m + 2) * 2 ** (m - 1)
        ok = (n, e) == (ln, le)
        bad += not ok
        print(f"decoder       m={m}: nodes {n} (Lean {ln}), edges {e} (Lean {le}) {'OK' if ok else 'MISMATCH'}")
    print("RESULT", "all counts agree" if bad == 0 else f"{bad} mismatches")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
