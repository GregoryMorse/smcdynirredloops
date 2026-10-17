"""Re-read the manuscript TeX (validation/reference/) and compare with validation/data/paper_tables.json.
Also checks the internal consistency of Fig. 1 and Fig. 4. Evidence only (class FD/M); the rendered-page
sign-off is manual and recorded in validation/rounds/R0.json.
Usage: python validation/check_tables.py"""
import json, re, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TEX = ROOT / "validation/reference/SelfModifyingControlFlowObfuscationPaper.tex"
DATA = json.loads((ROOT / "validation/data/paper_tables.json").read_text(encoding="utf-8"))
lines = TEX.read_text(encoding="utf-8").splitlines()
fails = []


def check(ok, msg):
    if not ok:
        fails.append(msg)
        print("FAIL", msg)


def seg(a, b):
    return "\n".join(lines[a - 1:b])


def cells(row):
    row = re.sub(r"\\multirow\{2\}\{\*\}\{([^}]*)\}", r"\1", row.replace("\\\\", "").replace("\\hline", ""))
    return [c.strip() for c in row.split("&")]


def table_rows(key):
    a, b = DATA[key]["tex_lines"]
    body = [l for l in lines[a - 1:b] if "&" in l]
    return [cells(l) for l in body[1:]]  # skip the header row


for key in ("table1_aes", "table2_rsa"):
    rows = table_rows(key)
    check(len(rows) == 2 * len(DATA[key]["rows"]), key + " row count")
    for i, r in enumerate(DATA[key]["rows"]):
        a, b = rows[2 * i], rows[2 * i + 1]
        check(int(a[0]) == r["bits"], f"{key} bits {r['bits']}")
        got = [int(x) for x in a[-4:]]
        check(got == [r["nodes"], r["edges"], r["exec_n"], r["exec_e"]], f"{key} {r['bits']} counts {got}")
        for first, line, ar in ((True, a, r["arch"][0]), (False, b, r["arch"][1])):
            off = 1  # the second physical row has an empty first cell
            check(line[off] == ar["arch"], f"{key} {r['bits']} arch {line[off]}")
            if key == "table1_aes":
                vals = [line[off + 1].replace("$\\mu$", "u"), line[off + 2].replace("$\\mu$", "u"), line[off + 3]]
                check(vals == [ar["cref"], ar["intrin"], ar["cfg"]], f"{key} {r['bits']} {ar['arch']} times {vals}")
            else:
                vals = [line[off + 1], line[off + 2]]
                check(vals == [ar["cgmp"], ar["cfg"]], f"{key} {r['bits']} {ar['arch']} times {vals}")
    for r in DATA[key]["rows"]:
        check(r["exec_e"] > r["exec_n"] and r["edges"] > r["nodes"], f"{key} {r['bits']} edges exceed nodes")

for r, want in zip(table_rows("table3_decompilers"), DATA["table3_decompilers"]["rows"]):
    check([r[0], r[1]] + [int(x) for x in r[2:]] == want, f"table3 {r}")

f1 = DATA["fig1"]
text = seg(*f1["tex_lines"])
block = text.split("\\subcaption{}")[0].split("TWOSAT1")[0]
formula = re.search(r"\$\(x_1\\vee x_4\).*?\)\$", text, re.S).group(0)
parsed = [[(-1 if m.group(1) else 1) * int(m.group(2)), (-1 if m.group(3) else 1) * int(m.group(4))]
          for m in re.finditer(r"\((\\lnot )?x_(\d)\\vee (\\lnot )?x_(\d)\)", formula)]
check(parsed == f1["clauses"], "fig1 clauses")
dot = text.split("TWOSAT1")[1].split("\\subcaption")[0]
tex_edges = [(int(a), int(b)) for a, b in re.findall(r"(-?\d+)->(-?\d+)", dot)]
check(sorted(tex_edges) == sorted(map(tuple, f1["edges"])), "fig1 edges vs TeX")
imps = {(-x, y) for x, y in f1["clauses"]} | {(-y, x) for x, y in f1["clauses"]}
check(imps == set(map(tuple, f1["edges"])) and len(f1["edges"]) == 24, "fig1 edges = contrapositive pairs of the clauses")
tex_clusters = re.findall(r"cluster_\d+ \{(.*?)label=\"(\d+)\"", dot, re.S)
tex_sccs = {}
for body, lab in tex_clusters:
    nodes = set(int(x) for x in re.findall(r"(?<![\w-])(-?\d+)(?=;|->)", body.replace("->", ";")))
    nodes |= {int(x) for x in re.findall(r"->(-?\d+)", body)}
    tex_sccs[lab] = sorted(nodes)
check(all(sorted(f1["sccs"][k]) == v for k, v in tex_sccs.items()) and len(tex_sccs) == 10, f"fig1 clusters {tex_sccs}")
label = {lit: int(k) for k, v in f1["sccs"].items() for lit in v}
check(len(label) == 16, "fig1 SCC cover of the 16 literals")
check(all(label[a] >= label[b] for a, b in f1["edges"]), "fig1 labels form a reverse topological order")
assign = {v: label[v] < label[-v] for v in range(1, 9)}
check(all(assign[abs(x)] == (x > 0) or assign[abs(y)] == (y > 0) for x, y in f1["clauses"]), "fig1 APT assignment satisfies all clauses")
check(sorted(f1["green"]) == sorted(v if assign[v] else -v for v in assign), "fig1 green literals = APT assignment")
tex_green = sorted(int(x) for x in re.findall(r"(-?\d+)\[style=filled; color=green\]", dot))
check(tex_green == sorted(f1["green"]), "fig1 green vs TeX")

f4 = DATA["fig4"]
text = seg(*f4["tex_lines"])
cfg = re.findall(r"(\w+) -> (\w+)", text.split("irredjung")[0])
check(sorted(cfg) == sorted(map(tuple, f4["cfg_edges"])), "fig4 cfg edges")
iv = {m.group(1): [int(m.group(2)), int(m.group(3))] for m in re.finditer(r't\d \[label="(\d) \[(\d+),(\d+)\]"\]', text)}
check(iv == f4["jungle_intervals"], "fig4 jungle intervals")
jung = text.split("irredjung")[1].split("irredlnf")[0]
tree = [[int(a), int(b)] for a, b in re.findall(r"t(\d)->t(\d);", jung)]
other = [[int(a), int(b)] for a, b in re.findall(r"t(\d)->t(\d)\[style=dashed", jung)]
check(tree == f4["jungle_tree_edges"], "fig4 jungle tree edges")
check(other == f4["jungle_other_edges"], "fig4 jungle dashed edges")
for a, b in f4["jungle_tree_edges"]:
    check(iv[str(a)][0] < iv[str(b)][0] and iv[str(b)][1] < iv[str(a)][1], f"fig4 tree edge {a}->{b} nested")
lt = [[int(a), int(b)] for a, b in re.findall(r"l(\d)->l(\d);", text.split("irredlnf")[1]) if a != "0"]
check(lt == f4["lnf_tree_edges"], f"fig4 lnf tree edges {lt}")

print("check_tables:", "FAIL (%d)" % len(fails) if fails else "OK")
sys.exit(1 if fails else 0)
