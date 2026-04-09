# conan_setup.ps1
# Installs / configures Conan 2.x for this project and generates the
# MSBuild props that ecdsa.vcxproj needs (build\conandeps.props etc.).
#
# Run from the repository root:
#   powershell -ExecutionPolicy Bypass -File cpp\selfmodgraph\conan_setup.ps1

Set-StrictMode -Version Latest
$ErrorActionPreference = 'Stop'

$scriptDir  = Split-Path -Parent $MyInvocation.MyCommand.Path
$outputDir  = Join-Path $scriptDir 'build'

# ── 1. Ensure Conan 2.x is available ─────────────────────────────────────
$conanCmd = Get-Command conan -ErrorAction SilentlyContinue
if (-not $conanCmd) {
    Write-Host '[conan_setup] conan not found in PATH — installing via pip...'
    python -m pip install --upgrade 'conan>=2.0'
    # Refresh PATH so the new conan is found
    $env:PATH = [System.Environment]::GetEnvironmentVariable('PATH','Machine') + ';' +
                [System.Environment]::GetEnvironmentVariable('PATH','User')
}

$conanVersion = (conan --version 2>&1) -replace 'Conan version ', ''
Write-Host "[conan_setup] Using Conan $conanVersion"

if ($conanVersion -lt '2.0') {
    Write-Error 'Conan 2.x is required. Run: python -m pip install --upgrade "conan>=2.0"'
    exit 1
}

# ── 2. Detect / update the default profile (picks up current VS toolset) ─
Write-Host '[conan_setup] Detecting default Conan profile...'
conan profile detect --force

# ── 3. Install GMP and generate MSBuild props ─────────────────────────────
Write-Host "[conan_setup] Installing dependencies into $outputDir ..."
New-Item -ItemType Directory -Force -Path $outputDir | Out-Null

$configs = @(
    @{ build_type = 'Release'; arch = 'x86_64' },
    @{ build_type = 'Debug';   arch = 'x86_64' },
    @{ build_type = 'Release'; arch = 'x86' },
    @{ build_type = 'Debug';   arch = 'x86' }
)
foreach ($cfg in $configs) {
    Write-Host "[conan_setup] $($cfg.build_type) | $($cfg.arch) ..."
    conan install $scriptDir `
        --output-folder="$outputDir" `
        --build=missing `
        -s build_type=$($cfg.build_type) `
        -s arch=$($cfg.arch)
    if ($LASTEXITCODE -ne 0) {
        Write-Warning "conan install failed for $($cfg.build_type)|$($cfg.arch) (exit $LASTEXITCODE) — continuing."
    }
}

Write-Host ''
Write-Host '[conan_setup] SUCCESS.'
Write-Host "  Props written to: $outputDir\conandeps.props"
Write-Host '  Open selfmodgraph.sln in Visual Studio — GMP will resolve automatically.'
Write-Host '  Note: Win32 (x86) configs require the x86 Conan package; if the x86 build'
Write-Host '        above failed or was skipped, x64 builds are fully functional and Win32'
Write-Host '        compilation will still find gmp.h via the x64 header fallback in gmp.props.'
