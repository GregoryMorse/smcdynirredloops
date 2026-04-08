Set-StrictMode -Version Latest
$ErrorActionPreference = "Stop"

$repoRoot = Split-Path -Parent $PSScriptRoot

Write-Host "Regenerating RSA VM artifacts..."
py "$repoRoot\python\rsa.py"

Write-Host "Regenerating AES VM artifacts..."
py "$repoRoot\python\aes.py"

Write-Host "Regenerating ECDSA VM artifacts..."
py "$repoRoot\python\ecdsab.py"

Write-Host "Regeneration complete. Output written to $repoRoot\generated\"
