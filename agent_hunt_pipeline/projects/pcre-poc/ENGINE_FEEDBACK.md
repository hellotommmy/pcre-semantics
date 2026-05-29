# PCRE Engine Feedback

Status: current transcript notes for the standalone PCRE semantics repository.

## 2026-05-29

Command:

```powershell
powershell -ExecutionPolicy Bypass -File tools\run_engine_feedback.ps1
```

Observed output:

```text
== Perl compatibility oracle ==
possessive	no	expected=no
greedy	yes	expected=yes
== PCRE2 pcre2test oracle ==
WARNING: pcre2test is not installed or not on PATH; pass -Pcre2TestPath or set PCRE2TEST before claiming PCRE2-specific fidelity.
```

Notes:

- Perl currently agrees with the canonical `ababa` compatibility smoke test:
  greedy `^(aba|ab|a)*$` accepts and possessive `^(aba|ab|a)*+$` rejects.
- This is not a PCRE2 transcript. Do not claim PCRE2-specific fidelity until
  `pcre2test` is installed and this file records a real PCRE2 run.
- The feedback script accepts `-Pcre2TestPath` or the `PCRE2TEST` environment
  variable once a local `pcre2test` binary is available.
