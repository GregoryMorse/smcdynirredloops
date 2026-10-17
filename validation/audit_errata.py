"""Errata audit for lean/errata/edits.json (paper-only errata against the published PMD version).

  --inventory (default): every `before` occurs verbatim (line endings normalised) in the v1 TeX, and every fragment of
      `before_pdf` occurs, after whitespace/hyphenation/ligature normalisation, on one page of the v1 PDF text;
      the page found is reported (`--fill-pages` writes it into `page`).
  --refs: write lean/ErrataRefs.lean (a #check for every declaration named in `lean_refs`).
  --pdf: the errata PDF exists and has at most 3 pages.
"""
import json, re, sys, unicodedata
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
EDITS = ROOT / "lean/errata/edits.json"
TEX = ROOT / "validation/reference/SelfModifyingControlFlowObfuscationPaper.tex"
PDF_TXT = ROOT / "validation/reference/pmd_raw.txt"
FIRST_PAGE = 617  # journal page of the first PDF page


def norm(s: str) -> str:
    s = unicodedata.normalize("NFKC", s).replace("­", "")
    return re.sub(r"[\s\-]+", "", s)  # hyphens and whitespace are layout noise in the PDF text


def refs() -> int:
    data = json.loads(EDITS.read_text(encoding="utf-8"))
    names = [r for e in data["edits"] for r in e.get("lean_refs", [])]
    root = (ROOT / "lean/SmcIrred.lean").read_text(encoding="utf-8").splitlines()
    mods = [l.split()[-1] for l in root if l.startswith("public import")]
    lines = ["module", ""] + ["import " + m for m in mods] + [""] + ["#check @%s" % n for n in names]
    (ROOT / "lean/ErrataRefs.lean").write_text("\n".join(lines) + "\n", encoding="utf-8")
    print("wrote lean/ErrataRefs.lean,", len(names), "references")
    return 0


def pdf() -> int:
    p = ROOT / "output/pdf/smcirred-2022-errata.pdf"
    n = len(re.findall(rb"/Type\s*/Page[^s]", p.read_bytes()))
    print("errata pdf pages", n)
    return 0 if 1 <= n <= 3 else 1


def inventory(fill: bool) -> int:
    """Each `before_pdf` entry {page, text} occurs (normalised) on that journal page of the published PDF text;
    each `before_tex` (when not null) occurs exactly once in the manuscript TeX (line endings normalised)."""
    data = json.loads(EDITS.read_text(encoding="utf-8"))
    tex = TEX.read_bytes().decode("utf-8").replace(chr(13) + chr(10), chr(10))
    pages = {FIRST_PAGE + i: norm(p) for i, p in enumerate(PDF_TXT.read_text(encoding="utf-8").split(chr(12)))}
    bad = 0
    for e in data["edits"]:
        tex_ok = True
        for frag in ([e["before_tex"]] if isinstance(e.get("before_tex"), str) else e.get("before_tex") or []):
            tex_ok &= tex.count(frag) == 1
        pdf_ok = True
        for f in e.get("before_pdf") or []:
            pdf_ok &= norm(f["text"]) in pages.get(f["page"], "")
        ok = tex_ok and pdf_ok
        bad += not ok
        print("ok  " if ok else "FAIL", e["id"], "tex=%s pdf=%s" % (tex_ok, pdf_ok), e["status"])
    return 1 if bad else 0


def main() -> int:
    if "--refs" in sys.argv:
        return refs()
    if "--pdf" in sys.argv:
        return pdf()
    return inventory("--fill-pages" in sys.argv)


if __name__ == "__main__":
    sys.exit(main())
