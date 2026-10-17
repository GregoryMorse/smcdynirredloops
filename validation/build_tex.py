"""Build a manuscript directory with latexmk in a scratch copy; write the PDF to output/pdf/<name>.pdf.

Usage: python validation/build_tex.py <tex-dir> <out-name>
The scratch copy avoids bibtex path problems with an external -outdir and keeps the source tree clean.
"""
import pathlib, shutil, subprocess, sys, tempfile

def main(src: str, name: str) -> int:
    src_dir = pathlib.Path(src).resolve()
    out = pathlib.Path(__file__).resolve().parent.parent / "output" / "pdf"
    out.mkdir(parents=True, exist_ok=True)
    tex = "SelfModifyingControlFlowObfuscationPaper"
    with tempfile.TemporaryDirectory() as tmp:
        for f in src_dir.iterdir():
            if f.is_file() and f.suffix in {".tex", ".bib", ".eps", ".bst", ".sty", ".cls"}:
                shutil.copy(f, tmp)
        r = subprocess.run(["latexmk", "-pdf", "-shell-escape", "-interaction=nonstopmode", f"{tex}.tex"],
                           cwd=tmp, capture_output=True, text=True, encoding="utf-8", errors="replace")
        pdf = pathlib.Path(tmp) / f"{tex}.pdf"
        log = (pathlib.Path(tmp) / f"{tex}.log").read_text(encoding="utf-8", errors="replace")
        undefined = log.count("undefined")
        if pdf.exists():
            shutil.copy(pdf, out / f"{name}.pdf")
        print(f"{name}: latexmk exit {r.returncode}, pdf={'yes' if pdf.exists() else 'NO'}, 'undefined' lines={undefined}")
        # latexmk exits 12 here: the graphviz package runs dot before it has written the .dot file on the first
        # pass ("can't open X.dot"); the second pass succeeds. Accept when the PDF exists and no reference is undefined.
        return 0 if pdf.exists() and undefined == 0 and r.returncode in (0, 12) else 1

if __name__ == "__main__":
    sys.exit(main(sys.argv[1], sys.argv[2]))
