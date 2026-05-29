# PCRE Submatch Value Research

Status: research note for the PCRE semantics track.

## Motivation

The current `Pcre_POC.thy` kernel has executable matching states and capture
environments:

- `pstate = PState pleft pright pcaps`
- `capenv = nat => string option`
- `pmatch` / `qmatch`
- `ptrace` / `qtrace`
- `valid_caps`

This is enough to state that returned captures are substrings of the original
subject, but it is not a submatch-value inhabitation layer. There is no PCRE
analogue yet of the POSIX backreference pilot's `bval`, `bflat`, and `BPrf`
relation.

For PCRE, a useful value layer must be state-indexed because backreferences,
conditionals, lookaround, and repeated captures depend on the capture
environment at the point where a subpattern is entered.

## Official PCRE2 Anchors

Primary references:

- `https://pcre.org/current/doc/html/pcre2pattern.html`
- `https://pcre.org/current/doc/html/pcre2matching.html`
- `https://pcre.org/current/doc/html/pcre2api.html`

Relevant claims to preserve:

- `pcre2_match()` is the standard Perl-compatible matching algorithm and
  exposes captured substrings through match data.
- Capture groups pick out substrings in addition to the whole match.
- Repeated capture groups report the substring from the final iteration, while
  nested groups may retain values from earlier iterations.
- Traditional lookaround assertions are zero-width and atomic.
- Positive assertions can retain captures from the successful assertion branch;
  successful negative assertions do not retain assertion-internal captures.
- Possessive quantifiers have the same meaning as equivalent atomic groups and
  prevent later failure from re-entering the repeated item.

The current `Pcre_POC.thy` intentionally simplifies some of this. In
particular, `PLook` returns the input state unchanged, so it does not yet model
positive-assertion capture retention. Any value relation should make that gap
explicit instead of hiding it.

## Suggested Shape

Use a value datatype that records the chosen parse branch and enough metadata
to recover consumed text and capture updates:

```isabelle
datatype pval =
  PVoid
| PCharVal char
| PClassVal char
| PDotVal char
| PSeqVal pval pval
| PLeftVal pval
| PRightVal pval
| PRepVal qkind "pval list"
| PCaptureVal nat pval
| PBackrefVal nat string
| PAtomicVal pval
| PLookVal bool
| PLookBehindVal bool
| PCondYesVal pval
| PCondNoVal pval
| PAssertVal
```

The exact constructors can be refined, but the key operations should be:

```isabelle
fun pflat :: "pval => string"
fun pcaps_after :: "capenv => pval => capenv"
inductive pval_trace ::
  "pcre => pstate => pval => pstate => bool"
```

The inhabitation relation should be state-indexed:

```isabelle
pval_trace r st v out
```

meaning that value `v` is a checked explanation of one successful `r` match
from `st` to `out`. This is more useful than a regex-only `PVal v r` relation
because `PBackref n` needs `pcaps st n`, `PCond n yes no` needs the current
capture environment, and capture updates happen in sequence.

Checked seed relation:

```isabelle
pval_ordered_run fuel r st v out
```

This currently covers the core fragment plus `PQuant Possessive 0 hi body`
when `body` is core-supported. The corresponding supported-fragment theorem is:

```isabelle
pmatch_ordered_value_complete:
  pordered_supported r ==>
  out in set (pmatch fuel r st) ==>
  exists v. pval_ordered_run fuel r st v out

pval_ordered_run_explains_state:
  pval_ordered_run fuel r st v out ==>
  pval_explains_state st v out

pmatch_atomic_ordered_value_complete:
  pordered_supported r ==>
  out in set (pmatch (Suc fuel) (PAtomic r) st) ==>
  exists v. pval_ordered_run (Suc fuel) (PAtomic r) st v out

pmatch_iff_ordered_value_explains:
  pordered_supported r ==>
  (out in set (pmatch fuel r st)) =
    (exists v. pval_ordered_run fuel r st v out /\
      pval_explains_state st v out)

pmatch_ordered_value_complete_atomic:
  pordered_supported_atomic r ==>
  out in set (pmatch fuel r st) ==>
  exists v. pval_ordered_run fuel r st v out

pordered_supported_imp_atomic:
  pordered_supported r ==> pordered_supported_atomic r

pmatch_iff_ordered_value_explains_atomic:
  pordered_supported_atomic r ==>
  (out in set (pmatch fuel r st)) =
    (exists v. pval_ordered_run fuel r st v out /\
      pval_explains_state st v out)
```

## Proof-Engineering Rules For This Layer

Follow the `backref-values` performance lesson from the start:

- avoid large overlapping `fun (sequential)` definitions over values;
- prefer `primrec` over `pcre` with explicit `case v of ...` branches if a
  value-injection/reconstruction function is needed;
- keep the relation inductive and prove constructor-specific elimination facts;
- prove output-shape facts before final bridge theorems;
- avoid sending the full matcher plus full value relation to `auto`.

Good local helper facts:

- `pflat (PSeqVal v1 v2) = pflat v1 @ pflat v2`
- `pcaps_after caps (PCaptureVal n v) =
   (pcaps_after caps v)(n := Some (pflat v))`
- if `pval_trace r st v out`, then
  `pleft out = pleft st @ pflat v`
- if `pval_trace r st v out`, then
  `pright st = pflat v @ pright out`
- if `valid_caps (pleft st @ pright st) (pcaps st)` and
  `pval_trace r st v out`, then
  `valid_caps (pleft st @ pright st) (pcaps out)`

## Bounty-Worthy Theorem Candidates

## Current Bounty Triage

Status after the checked value/context work on 2026-05-29:

- Strong infrastructure, not a standalone bounty claim:
  `pcre_fullmatch_language_mon_context_possessive_quant_subset_greedy`.
  This is the general match-set inclusion shape the user suggested, but it
  should be paired with a strictness witness and PCRE2 transcript before
  claiming PCRE-001 fidelity.
- Strong infrastructure, plausible sub-bounty material after extension:
  `pval_ordered_run` and `pmatch_ordered_value_complete`. This is a real
  submatch-value inhabitation relation, currently covering core plus
  possessive zero-phase quantifiers. It becomes more PCRE-002-shaped once
  greedy/lazy ordered value lists are added.
- PCRE-003 infrastructure only:
  `ptrace_atomic_first_result` and `ptrace_atomic_unique`. These state atomic
  first-result commitment, but do not yet prove capture interaction through an
  atomic context.
- Ordered-value atomic infrastructure:
  `pval_ordered_run` now has an atomic constructor and
  `pmatch_atomic_ordered_value_complete`, requiring the wrapped matcher output
  list to start with the committed output. This is closer to PCRE-003, but still
  needs capture-specific interaction theorems.
- Do not claim PCRE2-specific fidelity yet:
  the engine feedback loop still has Perl only; `pcre2test` is not installed.

Candidate 0: fullmatch language/match-set inclusion for possessive repetition.

```isabelle
pcre_fullmatch_language_possessive_quant_subset_greedy:
  pcre_fullmatch_language fuel (PQuant Possessive lo hi r)
    subseteq pcre_fullmatch_language fuel (PQuant Greedy lo hi r)

pcre_fullmatch_language_seq_possessive_quant_subset_greedy:
  pcre_fullmatch_language fuel (PSeq (PQuant Possessive lo hi r) tail)
    subseteq pcre_fullmatch_language fuel (PSeq (PQuant Greedy lo hi r) tail)

pcre_fullmatch_language_right_context_possessive_quant_subset_greedy:
  pcre_fullmatch_language fuel (plug_right_context C (PQuant Possessive lo hi r))
    subseteq
  pcre_fullmatch_language fuel (plug_right_context C (PQuant Greedy lo hi r))

pcre_fullmatch_language_mon_context_possessive_quant_subset_greedy:
  pcre_fullmatch_language fuel (plug_mon_context C (PQuant Possessive lo hi r))
    subseteq
  pcre_fullmatch_language fuel (plug_mon_context C (PQuant Greedy lo hi r))
```

These are checked general match-set facts. They are useful PCRE-001/PCRE-002
infrastructure. The monotone-context version is the preferred statement; it
should still be paired with ordering/value theorems before claiming a full
bounty. Its context boundary is intentional: atomic groups, lookaround,
conditionals, and nested quantifier positions are not monotone for free.

Candidate A: value soundness for the existing executable matcher.

```isabelle
pmatch_value_sound:
  out in set (pmatch fuel r st) ==>
  exists v. pval_trace r st v out
```

This is a real semantic layer, not a wrapper, because it explains every
successful engine path with a structured submatch value.

Checked fragment bridge now present:

```isabelle
pmatch_mon_context_core_run_complete:
  pmonctx_core_supported C ==>
  pcore_supported r ==>
  out in set (pmatch fuel (plug_mon_context C r) st) ==>
  exists v. pval_core_run fuel (plug_mon_context C r) st v out
```

This is the current strongest value-inhabitation theorem. It covers the core
fragment under monotone sequence/alternation/capture contexts, but not yet
ordered repetition values.

Candidate B: value completeness for bounded traces.

```isabelle
pval_trace r st v out ==>
  exists fuel. out in set (pmatch fuel r st)
```

This should be split by fragment first. Lookaround and backreference cases
need care, and possessive/lazy/greedy ordering should not be erased.

Candidate C: capture reconstruction.

```isabelle
pval_trace r st v out ==>
  pcaps out = pcaps_after (pcaps st) v
```

This gives a real bridge between submatch values and engine-observable capture
environments.

Candidate D: possessive subset at the outcome level.

```isabelle
set (qmatch fuel Possessive lo hi r st)
  subseteq set (qmatch fuel Greedy lo hi r st)
```

This is already present in the seed theory as `qmatch_possessive_subset_greedy`.
It is useful infrastructure but probably not enough for a new bounty by itself.
The value version would be more meaningful:

```isabelle
possessive_value_outcomes_subset_greedy:
  possessive value outcomes subset greedy value outcomes
```

where outcomes include consumed string and captures.

Checked adjacent infrastructure now present:

```isabelle
qmatch_possessive_zero_length_le_one:
  length (qmatch fuel Possessive 0 hi r st) <= 1

qtrace_possessive_zero_unique:
  qtrace fuel Possessive 0 hi r st out1 ==>
  qtrace fuel Possessive 0 hi r st out2 ==>
  out1 = out2

qtrace_possessive_zero_first_greedy:
  qtrace fuel Possessive 0 hi r st out ==>
  qmatch fuel Greedy 0 hi r st != [] /\
  hd (qmatch fuel Greedy 0 hi r st) = out
```

This is not enough by itself for the ordered-value bounty, but it captures the
general zero-phase commitment property that the `ababa` smoke test relies on.
The first-greedy theorem is stated only when possessive actually returns a
trace, avoiding the finite-fuel case where possessive can commit to a recursive
path that later exhausts fuel.

Checked value-layer step now present:

```isabelle
pval_possessive_zero_run_sound_qmatch:
  pval_possessive_zero_run fuel hi r st vs out ==>
  out in set (qmatch fuel Possessive 0 hi r st)

qmatch_possessive_zero_core_value_complete:
  pcore_supported r ==>
  out in set (qmatch fuel Possessive 0 hi r st) ==>
  exists vs. pval_possessive_zero_run fuel hi r st vs out

pval_possessive_zero_run_explains_state:
  pval_possessive_zero_run fuel hi r st vs out ==>
  pval_explains_state st (PRepVal Possessive vs) out

pmatch_possessive_zero_core_value_complete:
  pcore_supported r ==>
  out in set (pmatch (Suc fuel) (PQuant Possessive 0 hi r) st) ==>
  exists vs.
    pval_possessive_zero_run fuel hi r st vs out /\
    pval_explains_state st (PRepVal Possessive vs) out
```

This gives possessive zero-phase repetition a structured list-of-values
inhabitation theorem for core-supported repeated bodies, and ties the list back
to consumed text plus capture updates via `PRepVal`.

Candidate E: atomic first-value commitment.

```isabelle
pval_trace (PAtomic r) st v out ==>
  v is the first value produced by r at st
```

This would connect atomic grouping to ordered value semantics and should support
PCRE-003.

Checked state-level infrastructure now present:

```isabelle
ptrace_atomic_first_result:
  ptrace (Suc fuel) (PAtomic r) st out ==>
  exists rest. pmatch fuel r st = out # rest

ptrace_atomic_unique:
  ptrace (Suc fuel) (PAtomic r) st out1 ==>
  ptrace (Suc fuel) (PAtomic r) st out2 ==>
  out1 = out2
```

Checked value-layer infrastructure now present:

```isabelle
pval_ordered_atomic_first_result:
  pval_ordered_run (Suc fuel) (PAtomic r) st v out ==>
  exists rest. pmatch fuel r st = out # rest

pval_ordered_atomic_output_unique:
  pval_ordered_run (Suc fuel) (PAtomic r) st v1 out1 ==>
  pval_ordered_run (Suc fuel) (PAtomic r) st v2 out2 ==>
  out1 = out2
```

The remaining value-layer step is stricter: pair the first output state with
the first structured value for `r`, preserving capture updates and explaining
which inner value was committed.

Candidate F: positive-lookaround capture fidelity gap.

State and prove, for the current simplified kernel, that `PLook` preserves
`pcaps` unchanged. Record separately that official PCRE2 retains captures from
successful positive assertions. This is a useful research result because it
identifies a precise place where the PoC differs from full PCRE2.

Checked current-kernel facts now present:

```isabelle
lookahead_preserves_caps_current_kernel:
  st' in set (pmatch (Suc fuel) (PLook positive r) st) ==>
  pcaps st' = pcaps st

lookbehind_preserves_caps_current_kernel:
  st' in set (pmatch (Suc fuel) (PLookBehind positive r) (PState l s caps)) ==>
  pcaps st' = caps
```

## Next Small Formal Step

The next formal expansion should be greedy/lazy zero-phase value runs, but only
after preserving proof-time headroom. Current clean `PcrePOC` checks are around
18.5 seconds under `-o timeout=20`, so adding another large inductive directly
to `Pcre_Values.thy` is risky.

Proposed shape:

```isabelle
inductive pval_backtracking_zero_run ::
  qkind => nat => nat option => pcre => pstate => pval list => pstate => bool
```

Boundary:

- only `Greedy` and `Lazy`;
- repeated body must be `pcore_supported`;
- constructors should have explicit stop and take cases;
- the take constructor should require
  `mid in set (progress_outputs st (pmatch fuel r st))` plus a core value run
  for `mid`.

Expected theorems:

```isabelle
pval_backtracking_zero_run_sound_qmatch:
  pval_backtracking_zero_run q fuel hi r st vs out ==>
  q in {Greedy, Lazy} ==>
  out in set (qmatch fuel q 0 hi r st)

qmatch_backtracking_zero_core_value_complete:
  q in {Greedy, Lazy} ==>
  pcore_supported r ==>
  out in set (qmatch fuel q 0 hi r st) ==>
  exists vs. pval_backtracking_zero_run q fuel hi r st vs out
```

Proof plan:

- induct on `fuel`, arbitrary `hi st out`;
- split first on `can_take hi`;
- in the take branch, obtain `mid` from the concat-map membership before
  invoking the induction hypothesis;
- use `pmatch_core_run_complete` to inhabit the repeated item;
- introduce `vs` explicitly with `exI`, never with broad witness search.

This would make `pval_ordered_run` ready for ordered greedy/lazy constructors
and would move PCRE-002 from set-level ordering toward ordered value lists.
