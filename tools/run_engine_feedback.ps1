param(
  [string]$PerlPath = "C:\Users\kaihong\Desktop\Isabelle2025\contrib\cygwin\bin\perl.exe"
)

$ErrorActionPreference = "Stop"
$root = Split-Path -Parent $PSScriptRoot

Write-Host "== Perl compatibility oracle =="
if (Test-Path -LiteralPath $PerlPath) {
  & $PerlPath (Join-Path $PSScriptRoot "perl_possessive_smoke.pl")
  if ($LASTEXITCODE -ne 0) { throw "Perl smoke test failed" }
} else {
  Write-Warning "Perl not found at $PerlPath"
}

Write-Host "== PCRE2 pcre2test oracle =="
$pcre2 = Get-Command pcre2test -ErrorAction SilentlyContinue
if ($pcre2) {
  & $pcre2.Source (Join-Path $PSScriptRoot "pcre2_possessive_smoke.txt")
  if ($LASTEXITCODE -ne 0) { throw "pcre2test smoke test failed" }
} else {
  Write-Warning "pcre2test is not installed or not on PATH; install PCRE2 tools before claiming PCRE2-specific fidelity."
}