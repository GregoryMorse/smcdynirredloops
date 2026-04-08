Set-StrictMode -Version Latest
$ErrorActionPreference = "Stop"

Write-Host "Regenerating RSA VM artifacts..."
py rsa.py

Write-Host "Regenerating AES VM artifacts..."
py aes.py

Write-Host "Regenerating ECDSA VM artifacts..."
py ecdsab.py

Write-Host "Regeneration complete."
