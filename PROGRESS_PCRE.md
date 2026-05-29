# PCRE Progress

Last updated: 2026-05-29 (standalone repo created)

## Possessive Fullmatch Language Subset (2026-05-29)

- Branch: `master`.
- Files changed: `Pcre_POC.thy`, `PROGRESS_PCRE.md`.
- New checked definition:
  - `pcre_fullmatch_language`, a fuelled fullmatch language/match-set view:
    `{s. pcre_fullmatch fuel r s}`.
- New checked lemmas:
  - `set_concat_map_mono`
  - `pmatch_possessive_quant_subset_greedy`
  - `pmatch_seq_possessive_quant_subset_greedy`
  - `pcre_fullmatch_language_possessive_quant_subset_greedy`
  - `pcre_fullmatch_language_seq_possessive_quant_subset_greedy`
- Statement summary:
  - possessive quantifier outputs are included in greedy quantifier outputs;
  - the same inclusion is preserved when the quantifier is followed by a right
    sequence context;
  - therefore the fuelled fullmatch language of the possessive form is a subset
    of the corresponding greedy form.
- Why this matters:
  - this is the general match-set theorem the `ababa` smoke test should lean on,
    instead of treating the individual smoke test as the main proof artifact.
- Verifier:
  - `timeout 180s isabelle build -c -v -j 1 -o timeout=20 -d . PcrePOC` PASS,
    with `PcrePOC` timing about 16.2 seconds elapsed.
- Next smallest safe step:
  - extend the context theorem beyond one right `PSeq` frame, or add a negative
    witness theorem showing strictness for the `ababa` pattern as a sanity
    corollary only.

## Atomic First-Only Trace Bridge (2026-05-29)

- Branch: `master`.
- Files changed: `Pcre_POC.thy`, `PROGRESS_PCRE.md`.
- New checked lemmas:
  - `first_only_length_le_one`
  - `first_only_member_head`
  - `ptrace_atomic_first_result`
  - `ptrace_atomic_unique`
- Statement summary:
  - any successful atomic trace comes from the head of the wrapped matcher's
    output list;
  - atomic traces are unique for the same wrapped regex, state, and fuel.
- Proof-engineering note:
  - an initial `blast`/`auto` shape caused clean builds to hit the session
    timeout before leaving `Pcre_POC.thy`; replacing it with explicit list
    cases restored `timeout=20` cold checks.
- Verifier:
  - `timeout 180s isabelle build -c -v -j 1 -o timeout=20 -d . PcrePOC` PASS,
    with `PcrePOC` timing about 16.6 seconds elapsed.
- Next smallest safe step:
  - connect atomic uniqueness with capture update invariants, or lift atomic
    first-only behavior to structured values once repetition values are added.

## Possessive First-Result Bridge (2026-05-29)

- Branch: `master`.
- Files changed: `Pcre_POC.thy`, `PROGRESS_PCRE.md`.
- New checked lemmas:
  - `length_le_one_member_singleton`
  - `qmatch_possessive_zero_first_greedy`
  - `qtrace_possessive_zero_first_greedy`
- Statement summary:
  - if zero-phase possessive repetition returns `[out]`, then the same `out`
    is the head of the corresponding greedy repetition output list;
  - equivalently, any relational zero-phase possessive trace is the first
    greedy executable result for the same matcher state and fuel.
- Why this matters:
  - this is a general first-result/commitment theorem for the current kernel,
    closer to PCRE-002 than a set-inclusion fact.
  - It avoids the finite-fuel corner case where possessive can return `[]`
    after choosing a recursive path that runs out of fuel while greedy still has
    a base fallback.
- Verifier:
  - `timeout 180s isabelle build -c -v -j 1 -o timeout=20 -d . PcrePOC` PASS,
    with `PcrePOC` timing about 16.7 seconds elapsed.
- Next smallest safe step:
  - lift the first-result bridge to `pval_core_run`/future repetition values,
    or relate atomic grouping to this first greedy result theorem.

## Possessive Zero-Phase Determinism (2026-05-29)

- Branch: `master`.
- Files changed: `Pcre_POC.thy`, `PROGRESS_PCRE.md`.
- New checked lemmas:
  - `length_le_one_set_unique`
  - `qmatch_possessive_zero_length_le_one`
  - `qtrace_possessive_zero_unique`
- Statement summary:
  - once a possessive quantifier is in its `lo = 0` phase, the executable
    `qmatch` relation exposes at most one output state;
  - the relational `qtrace` view is therefore unique for
    `qtrace fuel Possessive 0 hi r st out`.
- Why this matters:
  - it states a general commitment property behind PCRE-001/PCRE-002 instead
    of another `ababa` instance proof.
  - It remains a current-kernel theorem; PCRE2-specific fidelity still needs a
    `pcre2test` transcript before claiming exact PCRE2 behavior.
- Verifier:
  - `timeout 180s isabelle build -c -v -j 1 -o timeout=20 -d . PcrePOC` PASS,
    with `PcrePOC` timing about 15.3 seconds elapsed.
- Next smallest safe step:
  - lift this uniqueness result to structured possessive values, or prove a
    first-result theorem relating the zero-phase possessive path to greedy
    ordering under a fuel condition.

## Core Executable Completeness Bridge (2026-05-29)

- Branch: `master`.
- Files changed: `Pcre_Values.thy`, `PROGRESS_PCRE.md`.
- New checked predicate:
  - `pcore_supported`, a syntactic boundary for the executable core fragment
    covered by the current value relation. It excludes ordered repetition,
    atomic groups, and lookaround until their value/ordering semantics are
    stated explicitly.
- New checked lemma:
  - `pmatch_core_run_complete`
- Statement summary:
  - for every `pcore_supported r`, if the executable matcher returns an output
    state `out \<in> set (pmatch fuel r st)`, then there exists a structured value
    `v` such that `pval_core_run fuel r st v out`.
  - Together with `pval_core_run_sound_pmatch`, this gives a checked
    correspondence between executable core matches and structured submatch
    value inhabitants.
- Verifier:
  - `timeout 180s isabelle build -v -j 1 -o timeout=20 -d . PcrePOC` PASS,
    with `PcrePOC` timing about 16.5 seconds elapsed.
- Next smallest safe step:
  - decide the next relation boundary for ordered quantifiers and atomic
    commitment, or keep reducing the remaining 10-second-check bottleneck in
    `Pcre_POC.thy`.

## Fuelled Core Value Bridge (2026-05-29)

- Branch: `master`.
- Files changed: `Pcre_Values.thy`, `PROGRESS_PCRE.md`.
- New checked relation:
  - `pval_core_run`, a fuelled state-indexed value relation that mirrors the
    executable `pmatch` fuel discipline for the same core fragment as
    `pval_core_trace`.
- New checked lemmas:
  - `pval_core_run_trace`
  - `pval_core_run_explains_state`
  - `pval_core_run_sound_pmatch`
- Statement summary:
  - every fuelled core value run is an un-fuelled core value trace;
  - every fuelled core value run explains its state transition via
    `pval_explains_state`;
  - every fuelled core value run is sound for the executable matcher:
    `out \<in> set (pmatch fuel r st)`.
- Verifier:
  - `timeout 180s isabelle build -v -j 1 -o timeout=20 -d . PcrePOC` PASS,
    with `PcrePOC` timing about 17 seconds elapsed.
- Next smallest safe step:
  - define a syntactic predicate for the core fragment and prove a converse
    witness theorem for selected constructors, or start a separate ordered
    relation for quantifier value lists.

## Core Value Inhabitation Relation (2026-05-29)

- Branch: `master`.
- Files changed: `Pcre_Values.thy`, `PROGRESS_PCRE.md`.
- New checked relation:
  - `pval_core_trace`, a state-indexed value inhabitation relation for the
    core fragment whose value behavior is not affected by ordered repetition
    or atomic commitment.
- Covered constructors:
  - `PEps`, `PChar`, `PClass`, `PDot`, `PSeq`, `PAlt`, `PCapture`,
    `PBackref`, `PCond`, `PWordBoundary`, `PLineStart`, `PLineEnd`,
    `PStart`, and `PEnd`.
- Deliberately not covered yet:
  - `PQuant`, `PAtomic`, `PLook`, and `PLookBehind`, because they require
    ordered first-result and assertion-capture fidelity decisions.
- New checked lemmas:
  - `pval_core_trace_explains_state`
  - `pval_core_trace_consumes_prefix`
  - `pval_core_trace_spine`
- Verifier:
  - `timeout 180s isabelle build -v -j 1 -o timeout=20 -d . PcrePOC` PASS,
    with `PcrePOC` timing about 16 seconds elapsed.
- Notes:
  - This relation is the first formal answer to the missing submatch-value
    inhabitation layer question. It is intentionally a fragment relation, not
    a false full-PCRE relation.
- Next smallest safe step:
  - prove a soundness bridge from `pval_core_trace` to the executable matcher
    for the same core fragment, likely by defining a syntactic predicate for
    the supported core fragment first.

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
