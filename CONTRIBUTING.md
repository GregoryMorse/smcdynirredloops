# Contributing

## Getting started

1. Install Python dependencies:
   - py -m pip install -r requirements.txt
2. Regenerate artifacts after relevant changes:
   - powershell -File scripts\regenerate.ps1
   - (or individually: py python\rsa.py / py python\aes.py / py python\ecdsab.py)
3. Run local checks:
   - py -m py_compile virt.py aes.py rsa.py ecdsab.py

## Building the C/C++ projects (Visual Studio)

The `ecdsa` project (`ecdsa.vcxproj`) depends on GMP.
GMP paths are resolved via `native\gmp.props` in this priority order:

### Option A — Conan 2.x (recommended)

```powershell
pip install "conan>=2.0"
powershell -ExecutionPolicy Bypass -File native\conan_setup.ps1
```

This runs `conan profile detect --force` (picks up the installed VS toolset
automatically — VS2019 through VS2026 all work) then writes
`native\build\conandeps.props` which `gmp.props` imports.

### Option B — Environment variable

```powershell
# ShiftMediaProject prebuilt: https://github.com/ShiftMediaProject/gmp/releases
setx GMP_ROOT C:\path\to\libgmp_6.2.1-2_msvc16
```

Restart Visual Studio after setting the variable. The expected layout is:
```
<GMP_ROOT>\include\gmp.h
<GMP_ROOT>\lib\x86\gmp.lib
<GMP_ROOT>\lib\x64\gmp.lib
```

### Option C — Local deps folder (portable)

Extract a GMP build under `native\deps\gmp\`:
```
native\deps\gmp\include\gmp.h
native\deps\gmp\lib\x86\gmp.lib
native\deps\gmp\lib\x64\gmp.lib
```

No environment variables or Conan required.

## Contribution guidelines

- Keep algorithm logic in Python sources as canonical.
- Treat generated C files as derived outputs.
- Keep commits focused and include a short rationale.
- Document behavior changes in README when generation or build flow changes.
- Preserve and update citation metadata when publication details change.

## Pull request checklist

- [ ] Code changes are minimal and scoped.
- [ ] Generated artifacts updated if generation logic changed.
- [ ] Python files compile successfully.
- [ ] README updated for any workflow changes.
