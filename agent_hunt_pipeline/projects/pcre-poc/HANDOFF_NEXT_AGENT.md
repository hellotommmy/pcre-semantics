# PCRE Semantics Handoff

Status: short handoff for continuing the PCRE semantics work from a fresh
checkout.

Remote:

```text
https://github.com/hellotommmy/pcre-semantics.git
```

## Read First

- `AGENTS.md`
- `CLAUDE.md`
- `agent_hunt_pipeline/projects/pcre-poc/CLAUDE.md`
- `PCRE_BOUNTIES.md`
- `PROGRESS_PCRE.md`
- `agent_hunt_pipeline/projects/pcre-poc/BOUNTY_THEOREM_CANDIDATES.md`
- `agent_hunt_pipeline/projects/pcre-poc/PROOF_TIME_RECOVERY_PLAN.md`
- `agent_hunt_pipeline/projects/pcre-poc/VALUE_THEORY_SPLIT_MAP.md`
- `agent_hunt_pipeline/projects/pcre-poc/ENGINE_FEEDBACK.md`

## Current State

- The repo is the standalone PCRE semantics repo. Do not do PCRE work in the
  POSIX/formalising repo.
- PCRE-001's `ababa` pair is only a sanity target. Do not spend the main effort
  proving many individual examples.
- Current useful checked value layer:
  - `pval_core_run`
  - `pval_possessive_zero_run`
  - `pval_ordered_run`
  - `pmatch_iff_ordered_value_explains_atomic`
  - `pval_ordered_atomic_first_result`
  - `pval_ordered_atomic_output_unique`
- The value relation is fragment-level, not full PCRE.
- The fullmatch/value wrapper theorem was tried and removed because it is not
  bounty-level and made the fast check flaky.

## Engine Feedback

Run:

```powershell
powershell -ExecutionPolicy Bypass -File tools\run_engine_feedback.ps1
```

Current expected status:

- Perl oracle available:
  - possessive `^(aba|ab|a)*+$` on `ababa`: `no`
  - greedy `^(aba|ab|a)*$` on `ababa`: `yes`
- PCRE2 `pcre2test` is still missing in the previous environment.
- Do not claim PCRE2-specific fidelity until a real `pcre2test` transcript is
  recorded.
- The feedback script accepts `-Pcre2TestPath` or `PCRE2TEST` once `pcre2test`
  is available.

## Proof-Time Rules

- Public fast-loop verifier:

```powershell
$env:USER_HOME='/cygdrive/c/Users/kaihong/Documents/pcre_semantics/.codex/isabelle-home'
& 'C:\Users\kaihong\Desktop\Isabelle2025\contrib\cygwin\bin\bash.exe' -lc 'cd /cygdrive/c/Users/kaihong/Documents/pcre_semantics && timeout 180s /cygdrive/c/Users/kaihong/Desktop/Isabelle2025/bin/isabelle build -c -v -j 1 -o timeout=20 -d . PcrePOC 2>&1'
```

- `-o timeout=19` is unstable. Treat it only as a trend probe.
- Do not raise timeouts as a fix.
- Avoid `by eval` for examples touching `pstate`/captures because `capenv` is
  function-valued.
- Avoid wrapper theorems unless they enable a real semantic layer.

## Best Next Moves

Recommended order:

1. Split `Pcre_Values.thy` according to `VALUE_THEORY_SPLIT_MAP.md`, without
   semantic changes.
2. Add scoped sessions as in `PROOF_TIME_RECOVERY_PLAN.md`.
3. Then work on a real PCRE-002 candidate:
   `pval_backtracking_zero_run` for `Greedy` and `Lazy`, restricted to
   `pcore_supported` repeated bodies.
4. Alternatively, formalize the PCRE-001 general strictness side condition
   sketched as `ambiguous_repair_point` in `BOUNTY_THEOREM_CANDIDATES.md`.

Do not make the next step another pile of `ababa`-style individual proofs.

## Validation Before Pushing

```powershell
python tools\pcre_no_cheat_guard.py --root .
python tools\pcre_bounty_guard.py --file PCRE_BOUNTIES.md
powershell -ExecutionPolicy Bypass -File tools\run_engine_feedback.ps1
```

Then run the Isabelle `PcrePOC` build with `-o timeout=20`.
