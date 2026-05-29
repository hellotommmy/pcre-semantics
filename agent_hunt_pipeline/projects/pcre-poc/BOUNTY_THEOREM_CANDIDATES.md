# PCRE General Theorem Candidates

Status: research triage for bounty-worthy PCRE semantic statements. This file
is intentionally about general properties, not a pile of individual examples.

## Current Value Relation Answer

Yes: a submatch-value inhabitation layer now exists, but only for a checked
fragment.

Checked relations and bridges:

- `pval_core_trace`
- `pval_core_run`
- `pval_possessive_zero_run`
- `pval_ordered_run`
- `pordered_supported`
- `pordered_supported_atomic`
- `pmatch_iff_ordered_value_explains`
- `pmatch_iff_ordered_value_explains_atomic`

Meaning: for the supported fragment, executable `pmatch` success is equivalent
to existence of a structured ordered value run, and that value explains the
state transition through consumed text and capture updates. A fullmatch-language
bridge is a useful wrapper candidate, but it should wait until proof-time
headroom is recovered.

Boundary: this is not a full-PCRE value relation yet. Greedy/lazy ordered
repetition values, positive-lookaround capture retention, and first inner
atomic value selection remain open.

## Candidate 1: Strict Possessive Fullmatch Separation

Possible statement shape:

```isabelle
possessive_quant_strict_under_context:
  pcre_fullmatch_language fuel
    (plug_mon_context C (PQuant Possessive 0 hi body))
  \<subset>
  pcre_fullmatch_language fuel
    (plug_mon_context C (PQuant Greedy 0 hi body))
```

Why it may be bounty-worthy: this upgrades the existing subset theorem into a
proper semantic separation, which is the general fact behind the canonical
`ababa` smoke test.

Current checked infrastructure:

- `pcre_fullmatch_language_mon_context_possessive_quant_subset_greedy`
- `qtrace_possessive_zero_first_greedy`
- Perl transcript for `^(aba|ab|a)*$` yes and `^(aba|ab|a)*+$` no.

Risk: a useful strictness theorem needs a parametric ambiguity/repair
hypothesis, not just a concrete witness. A single `ababa` proof should only be
a sanity corollary.

Promising side-condition shape:

```isabelle
ambiguous_repair_point fuel body tail st long short \<Longrightarrow>
  pmatch fuel body st = long # more \<Longrightarrow>
  short \<in> set more \<Longrightarrow>
  progress_outputs st [long, short] = [long, short] \<Longrightarrow>
  set (pmatch fuel tail long) = {} \<Longrightarrow>
  set (pmatch fuel tail short) \<noteq> {}
```

Intended theorem shape:

```isabelle
possessive_greedy_strict_from_repair:
  ambiguous_repair_point fuel body tail st long short \<Longrightarrow>
  set (pmatch fuel (PSeq (PQuant Possessive 0 hi body) tail) st)
    \<subset>
  set (pmatch fuel (PSeq (PQuant Greedy 0 hi body) tail) st)
```

This captures the `ababa` phenomenon without baking in `aba|ab|a`: the
possessive quantifier commits to the first progress state, while greedy
backtracking may later use a shorter progress state that makes the tail match.
A fullmatch-language strictness corollary should then instantiate `st` as the
initial state for the witness subject.

Suggested bounty status: good candidate after the strictness side condition is
stated cleanly.

## Candidate 2: Ordered Greedy/Lazy Value Runs

Possible statement shape:

```isabelle
qmatch_backtracking_zero_core_value_complete:
  q \<in> {Greedy, Lazy} \<Longrightarrow>
  pcore_supported r \<Longrightarrow>
  out \<in> set (qmatch fuel q 0 hi r st) \<Longrightarrow>
  \<exists>vs. pval_backtracking_zero_run q fuel hi r st vs out
```

Why it may be bounty-worthy: PCRE greedy/lazy behavior is observable through
ordered results and captures. A value-list relation would explain each ordered
backtracking result rather than just set membership.

Current checked infrastructure:

- `qmatch_greedy_lazy_set`
- `qmatch_lazy_zero_first`
- `qmatch_greedy_zero_last`
- `pval_possessive_zero_run`
- `pval_ordered_run`

Risk: this likely needs a new relation. Do not add it to the hot theory until
proof-time headroom is recovered or the value layer is split into a focused
session.

Suggested bounty status: strong PCRE-002 candidate.

## Candidate 3: Atomic First Inner Value Commitment

Possible statement shape:

```isabelle
pval_ordered_atomic_first_value:
  pval_ordered_run (Suc fuel) (PAtomic r) st (PAtomicVal v) out \<Longrightarrow>
  first_value_for r fuel st v out
```

Why it may be bounty-worthy: it ties atomic grouping to the committed inner
submatch value, including capture updates.

Current checked infrastructure:

- `ptrace_atomic_first_result`
- `ptrace_atomic_unique`
- `pmatch_atomic_ordered_value_complete`
- `pval_ordered_atomic_first_result`
- `pval_ordered_atomic_output_unique`

Risk: output-state uniqueness is already checked; value uniqueness is stronger
and may fail for ambiguous inner values that produce the same output state. The
right theorem should talk about first ordered value, not arbitrary uniqueness.

Suggested bounty status: strong PCRE-003 candidate once the first-value
projection relation is defined.

## Candidate 4: Capture Reconstruction For Engine Results

Possible statement shape:

```isabelle
pcre_exec_value_caps:
  pcre_exec fuel r s = Some (PResult i j caps) \<Longrightarrow>
  supported_exec_value r \<Longrightarrow>
  \<exists>v. pcaps_after v empty_caps = caps \<and> pflat v = take (j - i) (drop i s)
```

Why it may be bounty-worthy: PCRE APIs expose captures, not just acceptance.
This bridges executable engine results to the value inhabitation layer.

Current checked infrastructure:

- `pcre_exec_sound`
- `pcre_exec_valid_caps`
- `pval_ordered_run_caps`
- `pval_ordered_run_left`
- `pval_ordered_run_right`

Risk: needs a clean supported-fragment predicate for search/exec, not just
single-state `pmatch`.

Suggested bounty status: strong PCRE-004 candidate.

## Candidate 5: Positive Lookaround Capture Fidelity

Possible statement shape:

```isabelle
positive_lookaround_retains_success_caps:
  successful positive assertion captures are available to later pattern pieces
```

Why it may be bounty-worthy: this is a real PCRE2 fidelity gap in the current
PoC. The checked kernel currently preserves captures unchanged for lookaround,
which is intentionally recorded as a gap rather than a PCRE2 claim.

Current checked gap facts:

- `lookahead_preserves_caps_current_kernel`
- `lookbehind_preserves_caps_current_kernel`

Risk: requires changing the lookaround state model and then repairing value and
capture invariants. Needs PCRE2 transcript before claiming PCRE2-specific
fidelity.

Suggested bounty status: strong PCRE-009 or PCRE-004/009 cross-candidate after
PCRE2 tooling is available.

## Not Bounty-Worthy By Itself

- More individual examples after the canonical smoke test.
- `iff` wrappers that only restate existing completeness/soundness lemmas.
- Pure set equality when the PCRE behavior is observable through ordering,
  captures, first result, or committed failure.
- Raising Isabelle timeouts instead of shrinking proof search.

## Recommended Next Confirmation

Ask the maintainer to choose between:

- strict possessive separation with one sanity witness;
- greedy/lazy ordered value runs;
- atomic first inner value commitment;
- engine-result capture reconstruction;
- positive lookaround capture fidelity repair.

The safest next formal move is not a new large relation in `Pcre_Values.thy`.
It is either a small strictness-side-condition theorem in `Pcre_POC.thy`, or a
split theory/session for greedy/lazy value runs.
