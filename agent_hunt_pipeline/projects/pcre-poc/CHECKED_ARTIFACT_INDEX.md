# Checked PCRE Artifact Index

Status: curated index for checked Isabelle artifacts in the standalone PCRE
semantics repository.

## Match-Set And Context Facts

- `pcre_fullmatch_language`
- `pmatch_possessive_quant_subset_greedy`
- `pmatch_seq_possessive_quant_subset_greedy`
- `pcre_fullmatch_language_possessive_quant_subset_greedy`
- `pcre_fullmatch_language_seq_possessive_quant_subset_greedy`
- `pmonctx`
- `plug_mon_context`
- `pmatch_mon_context_mono`
- `pmatch_mon_context_possessive_quant_subset_greedy`
- `pcre_fullmatch_language_mon_context_possessive_quant_subset_greedy`

Use: general match-set infrastructure for PCRE-001/PCRE-002. Not a full bounty
claim by itself.

## Possessive Ordering Facts

- `qmatch_possessive_zero_length_le_one`
- `qtrace_possessive_zero_unique`
- `qmatch_possessive_zero_first_greedy`
- `qtrace_possessive_zero_first_greedy`

Use: zero-phase possessive commitment and first-greedy-result infrastructure.

## Core Value Relation

- `pval`
- `pflat`
- `pcaps_after`
- `pval_explains_state`
- `pcore_supported`
- `pval_core_trace`
- `pval_core_run`
- `pval_core_run_sound_pmatch`
- `pmatch_core_run_complete`
- `pmonctx_core_supported`
- `pmatch_mon_context_core_run_complete`

Use: first checked submatch-value inhabitation layer for the core fragment.

## Possessive Value Relation

- `pval_possessive_zero_run`
- `pval_possessive_zero_run_sound_qmatch`
- `qmatch_possessive_zero_core_value_complete`
- `pval_possessive_zero_run_explains_state`
- `pval_possessive_zero_run_sound_pmatch_quant`
- `pmatch_possessive_zero_core_value_complete`

Use: possessive zero-phase repetition values for core-supported repeated bodies.

## Ordered Value Relation

- `pval_ordered_run`
- `pordered_supported`
- `pordered_supported_atomic`
- `pordered_supported_imp_atomic`
- `pval_ordered_run_sound_pmatch`
- `pval_ordered_run_explains_state`
- `pval_ordered_run_consumes_prefix`
- `pval_ordered_run_spine`
- `pval_ordered_run_left`
- `pval_ordered_run_right`
- `pval_ordered_run_caps`
- `pmatch_ordered_value_complete`
- `pmatch_iff_ordered_value_run`
- `pmatch_iff_ordered_value_explains`
- `pmatch_ordered_value_complete_atomic`
- `pmatch_iff_ordered_value_run_atomic`
- `pmatch_iff_ordered_value_explains_atomic`

Use: current preferred value-inhabitation theorem family. Covers core,
possessive zero-phase quantifiers with core bodies, and nested atomic wrappers.

## Atomic Infrastructure

- `ptrace_atomic_first_result`
- `ptrace_atomic_unique`
- `pmatch_atomic_ordered_value_complete`
- `pval_ordered_atomic_first_result`
- `pval_ordered_atomic_output_unique`

Use: PCRE-003 infrastructure. The ordered-value facts lift first-result
commitment and output uniqueness to atomic value runs. Capture-specific atomic
interaction remains open.

## Lookaround Fidelity Gap

- `lookahead_preserves_caps_current_kernel`
- `lookbehind_preserves_caps_current_kernel`

Use: documents current PoC behavior and the PCRE2 positive-assertion capture
gap.

## External Engine Feedback

- `agent_hunt_pipeline/projects/pcre-poc/ENGINE_FEEDBACK.md`

Current status: Perl compatibility oracle agrees with the canonical smoke test;
PCRE2 `pcre2test` is still missing.
