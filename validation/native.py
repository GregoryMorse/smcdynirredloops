"""Compile native/selfmodgraph.sln with MSBuild (compile-only baseline, plan R0 step 8). Nothing is run.

Evidence that the sources build; no behaviour is claimed. GMP comes from native/gmp.props (Conan, GMP_ROOT or
native/deps/gmp). Projects: selfmodgraph, aes, rsa, ecdsa (ecdsawhibox is not part of the baseline).
Usage: python validation/native.py [--toolset v143|v145] [--configs "Debug|x64" ...] [--projects selfmodgraph aes ...]
The Visual Studio install is chosen from the toolset: v143 -> Visual Studio 2022, v145 -> Visual Studio 2026
(the projects pin v145); without --toolset the latest install and the project's toolset are used."""
import argparse, json, subprocess, sys, time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
VSWHERE = Path(r"C:\Program Files (x86)\Microsoft Visual Studio\Installer\vswhere.exe")
MAJOR = {"v143": "[17.0,18.0)", "v145": "[18.0,19.0)"}


def vcvars(toolset) -> Path:
    cmd = [str(VSWHERE), "-products", "*", "-property", "installationPath"]
    cmd += ["-version", MAJOR[toolset]] if toolset in MAJOR else ["-latest"]
    out = subprocess.run(cmd, capture_output=True, text=True).stdout.strip().splitlines()
    if not out:
        out = subprocess.run([str(VSWHERE), "-latest", "-products", "*", "-property", "installationPath"],
                             capture_output=True, text=True).stdout.strip().splitlines()
    if not out:
        sys.exit("no Visual Studio install found")
    return Path(out[0]) / r"VC\Auxiliary\Build\vcvarsall.bat"


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--toolset")
    ap.add_argument("--configs", nargs="*", default=["Debug|x64"])
    ap.add_argument("--projects", nargs="*", default=["selfmodgraph", "aes", "rsa", "ecdsa"])
    a = ap.parse_args()
    results = {}
    for cfg in a.configs:
        conf, plat = cfg.split("|")
        arch = "x86" if plat == "Win32" else "x64"
        ts = f" /p:PlatformToolset={a.toolset}" if a.toolset else ""
        for proj in a.projects:
            cmd = (f'call "{vcvars(a.toolset)}" {arch} >nul && msbuild native\\{proj}.vcxproj /nologo /v:m '
                   f'/p:Configuration={conf} /p:Platform={plat}{ts}')
            start = time.time()
            b = subprocess.run('cmd /s /c "' + cmd + '"', cwd=ROOT, capture_output=True, text=True, errors="replace")
            rec = {"build_ok": b.returncode == 0, "build_seconds": round(time.time() - start)}
            if b.returncode:
                rec["build_tail"] = (b.stdout + b.stderr)[-2500:]
            results[f"{proj} {cfg}"] = rec
            print(proj, cfg, json.dumps(rec), flush=True)
    return 0 if all(v["build_ok"] for v in results.values()) else 1


if __name__ == "__main__":
    sys.exit(main())
