param(
  [string]$PerlPath = "C:\Users\kaihong\Desktop\Isabelle2025\contrib\cygwin\bin\perl.exe",
  [string]$Pcre2TestPath = $env:PCRE2TEST
)

$ErrorActionPreference = "Stop"
$root = Split-Path -Parent $PSScriptRoot

function Resolve-Pcre2Test {
  param([string]$ExplicitPath)

  if ($ExplicitPath -and (Test-Path -LiteralPath $ExplicitPath)) {
    return (Resolve-Path -LiteralPath $ExplicitPath).Path
  }

  $cmd = Get-Command pcre2test -ErrorAction SilentlyContinue
  if ($cmd) {
    return $cmd.Source
  }

  return $null
}

Write-Host "== Perl compatibility oracle =="
if (Test-Path -LiteralPath $PerlPath) {
  & $PerlPath (Join-Path $PSScriptRoot "perl_possessive_smoke.pl")
  if ($LASTEXITCODE -ne 0) { throw "Perl smoke test failed" }
} else {
  Write-Warning "Perl not found at $PerlPath"
}

Write-Host "== PCRE2 pcre2test oracle =="
$pcre2 = Resolve-Pcre2Test -ExplicitPath $Pcre2TestPath
if ($pcre2) {
  & $pcre2 (Join-Path $PSScriptRoot "pcre2_possessive_smoke.txt")
  if ($LASTEXITCODE -ne 0) { throw "pcre2test smoke test failed" }
} else {
  Write-Warning "pcre2test is not installed or not on PATH; pass -Pcre2TestPath or set PCRE2TEST before claiming PCRE2-specific fidelity."
}
