# PCRE Value Theory Split Map

Status: line-oriented map for splitting `Pcre_Values.thy` without changing
theorem statements.

## Current Sections

`Pcre_Values.thy` currently has these main blocks:

- Lines 5-255: value datatype, flattening/capture update functions, and
  generic `pval_explains_state` lemmas.
- Lines 256-470: core value inhabitation support predicates and
  `pval_core_trace`.
- Lines 471-1017: fuelled core value runs, soundness, completeness, and
  monotone-context core lifting.
- Lines 1018-1152: possessive zero-phase value runs.
- Lines 1153-1527: ordered value runs, atomic-saturated support, iff bridges,
  and atomic ordered-value facts.

## Proposed Move Map

`Pcre_Value_Base.thy`:

- `pval`
- `pflat`
- `pcaps_after`
- `pval_explains_state`
- `pval_explains_state_*` generic lemmas
- list/capture helper lemmas:
  - `pcaps_after_seq`
  - `pcaps_after_capture`
  - `pflat_rep_append`
  - `pcaps_after_list_append`
  - `pcaps_after_rep_append`

`Pcre_Core_Values.thy`:

- `pcore_supported`
- `pmonctx_core_supported`
- `pcore_supported_plug_mon_context`
- `pval_core_trace`
- `pval_core_trace_explains_state`
- `pval_core_trace_consumes_prefix`
- `pval_core_trace_spine`
- `pval_core_run`
- `pval_core_run_trace`
- `pval_core_run_explains_state`
- `pval_core_run_sound_pmatch`
- `pmatch_core_run_complete`
- `pmatch_mon_context_core_run_complete`

`Pcre_Quant_Values.thy`:

- `pval_possessive_zero_run`
- `pval_possessive_zero_run_sound_qmatch`
- `qmatch_possessive_zero_core_value_complete`
- `pval_possessive_zero_run_explains_state`
- `pval_possessive_zero_run_sound_pmatch_quant`
- `pmatch_possessive_zero_core_value_complete`
- future `pval_backtracking_zero_run` for `Greedy`/`Lazy`

`Pcre_Ordered_Values.thy`:

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
- `pmatch_atomic_ordered_value_complete`
- `pmatch_ordered_value_complete_atomic`
- `pmatch_iff_ordered_value_run_atomic`
- `pmatch_iff_ordered_value_explains_atomic`
- `pval_ordered_atomic_first_result`
- `pval_ordered_atomic_output_unique`

## Dependency Order

```text
Pcre_POC
  -> Pcre_Value_Base
    -> Pcre_Core_Values
      -> Pcre_Quant_Values
        -> Pcre_Ordered_Values
```

Do not merge the split with semantic changes. First move definitions and prove
the same exported names. Then add greedy/lazy value runs in
`Pcre_Quant_Values.thy`.

## Risk Notes

- Keep theorem names stable so downstream bounty notes remain valid.
- Do not add global simp rules during the split.
- Check each move with a scoped session before re-running `PcrePOC`.
- If a moved proof starts using broad automation, split it before committing;
  do not compensate by raising `timeout`.
