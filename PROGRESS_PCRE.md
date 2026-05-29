# PCRE Progress

Last updated: 2026-05-29 (standalone repo created)

## Submatch Value Scaffold and Proof-Performance Rules (2026-05-29)

- Branch: `master`.
- Files changed: `AGENTS.md`, `CLAUDE.md`,
  `agent_hunt_pipeline/projects/pcre-poc/CLAUDE.md`,
  `agent_hunt_pipeline/projects/pcre-poc/SUBMATCH_VALUE_RESEARCH.md`,
  `Pcre_POC.thy`, `Pcre_Values.thy`, and `ROOT`.
- Rule update:
  - recorded the `backref-values` proof-performance lesson: slow Isabelle
    commands are proof-script bugs, broad automation should be split quickly,
    and heavy overlapping `fun` definitions should be replaced by `primrec`,
    `definition`, or simpler structural recursion with explicit value cases.
- New research note:
  - `SUBMATCH_VALUE_RESEARCH.md` records that the current PCRE kernel has
    `capenv`, `valid_caps`, `pmatch/qmatch`, and `ptrace/qtrace`, but no full
    submatch-value inhabitation relation yet.
  - The note proposes a state-indexed value relation because backreferences,
    conditionals, captures, and lookaround depend on the current capture
    environment.
- New checked theory:
  - `Pcre_Values.thy`.
- New definitions:
  - `pval`
  - `pflat`
  - `pcaps_after`
  - `pcaps_after_list`
  - `pval_explains_state`
- New checked lemmas:
  - `pval_explains_state_spine`
  - `pval_explains_state_consumes_prefix`
  - `pval_explains_state_caps`
  - `pval_explains_stateI`
  - `pcaps_after_seq`
  - `pcaps_after_capture`
  - `pflat_rep_append`
  - `pcaps_after_list_append`
  - `pcaps_after_rep_append`
  - `pval_explains_state_void`
  - `pval_explains_state_assert`
  - `pval_explains_state_look`
  - `pval_explains_state_lookbehind`
  - `pval_explains_state_char`
  - `pval_explains_state_class`
  - `pval_explains_state_dot`
  - `pval_explains_state_seq`
  - `pval_explains_state_left`
  - `pval_explains_state_right`
  - `pval_explains_state_atomic`
  - `pval_explains_state_cond_yes`
  - `pval_explains_state_cond_no`
  - `pval_explains_state_capture`
  - `pval_explains_state_backref`
- Refactored checked proofs in `Pcre_POC.thy`:
  - replaced the broad `auto/metis` proof of `pmatch_consumes_prefix` and
    `qmatch_consumes_prefix` with explicit constructor/case proofs;
  - replaced broad qmatch set/subset proofs with `set_concat_map_cong`,
    `set_concat_map_subset`, and explicit induction cases:
    `qmatch_greedy_lazy_set`, `qmatch_possessive_subset_greedy`,
    `qmatch_linear_subset_possessive_zero`;
  - simplified `pcre_search_states_iff_leftmost_trace` to direct `simp`
    unfolding instead of a broad `auto`.
- Real-engine feedback:
  - `powershell -ExecutionPolicy Bypass -File tools/run_engine_feedback.ps1`
    PASS for the Perl compatibility oracle:
    `possessive no expected=no`, `greedy yes expected=yes`.
  - PCRE2 `pcre2test` is still not installed/on PATH. Do not claim
    PCRE2-specific fidelity yet.
- Isabelle verifier:
  - `timeout 180s isabelle build -v -j 1 -o timeout=20 -d . PcrePOC` PASS,
    with `PcrePOC` timing about 16 seconds elapsed.
  - `-o timeout=10` still finds one remaining 10-20 second command later in
    `Pcre_POC.thy`; this is a proof-performance issue to continue reducing,
    not a reason to raise timeouts as the normal workflow.
- Guards:
  - `python tools/pcre_no_cheat_guard.py --root .` PASS.
  - `python tools/pcre_bounty_guard.py --file PCRE_BOUNTIES.md` PASS.
- Next smallest safe step:
  - define a real state-indexed inhabitation relation, probably in
    `Pcre_Values.thy`, for a capture-free ordered fragment first;
  - then prove the first bridge theorem from inhabitation to
    `pval_explains_state`, before attempting full `pmatch_value_sound`.
- Blockers:
  - PCRE2 transcript still missing because `pcre2test` is unavailable locally.
  - Full PCRE2 positive-assertion capture retention is not modeled by the
    current `PLook` semantics, which returns the input capture environment
    unchanged.

## Standalone Repo Bootstrap (2026-05-29)

- Repository path: `C:\Users\kaihong\Documents\pcre_semantics`.
- Remote target: `hellotommmy/pcre-semantics`.
- Migrated seed theory `Pcre_POC.thy` out of the POSIX/backreference repo.
- Added standalone `ROOT`, `README.md`, `AGENTS.md`, `CLAUDE.md`, PCRE bounty board, and real-engine feedback harness.
- Seeded AST definitions for the motivating example; the exact checked theorem
  pair remains open as PCRE-001.
- Real-engine baseline: Perl from Isabelle's Cygwin distribution is available and is used as the current compatibility oracle. PCRE2 `pcre2test` is not yet installed on this machine.
- Next smallest safe step: install or vendor PCRE2 tools, then add a PCRE2 transcript for the same smoke test and record exact PCRE2 version.
