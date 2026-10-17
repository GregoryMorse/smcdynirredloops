"""Fetch the published PDF and copy the author's OneDrive manuscript files (read-only) into the gitignored
validation/reference/, verify SHA-256 values, write SHA256SUMS and derive pmd.txt / pmd_raw.txt.
Usage: python validation/fetch_reference.py   (set SMCIRRED_ONEDRIVE to override the manuscript folder)"""
import hashlib, os, shutil, subprocess, sys, urllib.request
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
REF = ROOT / "validation/reference"
PDF_URL = "https://konferencia.unideb.hu/sites/default/files/upload_documents/10_5486_pmd.2022.suppl_.5.pdf"
ONEDRIVE = Path(os.environ.get("SMCIRRED_ONEDRIVE", r"D:\OneDrive\Documents\Projects\ELTE\smcdynirredloops"))
EXPECT = {
    "pmd.pdf": "e89a803c6839c18bd3fe202e03c4dbdf090f418ae8e222d736de8f77337a21fc",
    "SelfModifyingControlFlowObfuscationPaper.tex": "309bc5d1d0970a74a62e6f221697bb601a864fb3dc081af8bc879523fd635968",
    "biblio.bib": "28968b3a2cbdc1b2c6b07cc90df0f6f5234fb7f4271c1dbcde87e6b7ba87837d",
    "publmathdeb.cls": "2dbdc5da9e088dcb85bbfc3d95eb6142df8c8bde0d46093afadf53766e8a456f",
}

def sha(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()

def main() -> int:
    REF.mkdir(parents=True, exist_ok=True)
    pdf = REF / "pmd.pdf"
    if not pdf.exists() or sha(pdf) != EXPECT["pmd.pdf"]:
        req = urllib.request.Request(PDF_URL, headers={"User-Agent": "Mozilla/5.0"})
        pdf.write_bytes(urllib.request.urlopen(req, timeout=120).read())
    for name in list(EXPECT)[1:]:
        src = ONEDRIVE / name
        if src.exists():
            shutil.copyfile(src, REF / name)  # read from OneDrive, never write there
    bad = 0
    lines = []
    for name, want in EXPECT.items():
        p = REF / name
        got = sha(p) if p.exists() else "MISSING"
        ok = got == want
        bad += not ok
        print(("OK   " if ok else "FAIL ") + name, got)
        lines.append(f"{got}  {name}")
    (REF / "SHA256SUMS").write_text("\n".join(lines) + "\n", encoding="utf-8")
    if not bad:
        for out, flag in (("pmd.txt", ["-layout"]), ("pmd_raw.txt", [])):
            subprocess.run(["pdftotext", *flag, "-enc", "UTF-8", str(pdf), str(REF / out)], check=True)
        pages = subprocess.run(["pdfinfo", str(pdf)], capture_output=True, text=True).stdout
        print([l for l in pages.splitlines() if l.startswith("Pages")])
    return 1 if bad else 0

if __name__ == "__main__":
    sys.exit(main())
