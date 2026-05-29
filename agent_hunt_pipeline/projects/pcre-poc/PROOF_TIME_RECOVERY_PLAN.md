# PCRE Proof-Time Recovery Plan

Status: planning note for keeping the PCRE value formalization inside the
fast-check loop.

## Current Boundary

Current session:

```isabelle
session PcrePOC = HOL +
  theories[document = false]
    Pcre_POC
    Pcre_Values
```

Current file sizes:

- `Pcre_POC.thy`: about 2,481 lines.
- `Pcre_Values.thy`: about 1,527 lines after deferring the fullmatch/value
  wrapper.

Current checked boundary:

- `-o timeout=20`: PASS.
- `-o timeout=19`: unstable; some clean runs pass and some hit the session
  timeout boundary.
- `-o timeout=18`: FAILS at the session timeout boundary.

Consequence: the next large inductive relation should not be added directly to
`Pcre_Values.thy`.

## Backref-Values Lesson Applied Here

The POSIX `backref-values` branch recovered from a slow proof script by
changing the shape of value-processing definitions, not by raising the timeout:

- avoid overlapping `fun (sequential)` definitions over many value patterns;
- prefer recursion over the regex structure, with explicit value cases in the
  right-hand side;
- use explicit witnesses for existential constructor goals;
- avoid handing the full matcher and full value relation to broad automation.

The current PCRE value work follows that style, but the file has grown enough
that session-level timing is now the binding constraint.

## Split Target

The value theory should be split before adding greedy/lazy value runs:

1. `Pcre_Value_Base.thy`

   Keep:

   - `pval`;
   - `pflat`;
   - `pcaps_after`;
   - `pval_explains_state`;
   - generic state/capture/spine lemmas.

2. `Pcre_Core_Values.thy`

   Keep:

   - `pcore_supported`;
   - `pmonctx_core_supported`;
   - `pval_core_trace`;
   - `pval_core_run`;
   - core soundness/completeness.

3. `Pcre_Quant_Values.thy`

   Keep:

   - `pval_possessive_zero_run`;
   - possessive zero-phase soundness/completeness;
   - future greedy/lazy zero-phase value runs.

4. `Pcre_Ordered_Values.thy`

   Keep:

   - `pval_ordered_run`;
   - `pordered_supported`;
   - `pordered_supported_atomic`;
   - ordered/fullmatch value bridges.

## Session Shape

Use the existing `PcrePOC` session as the integration target, but add smaller
scoped sessions for development:

```isabelle
session PcreCoreValues = HOL +
  theories[document = false]
    Pcre_POC
    Pcre_Value_Base
    Pcre_Core_Values

session PcreOrderedValues = HOL +
  theories[document = false]
    Pcre_POC
    Pcre_Value_Base
    Pcre_Core_Values
    Pcre_Quant_Values
    Pcre_Ordered_Values
```

Expected use:

- develop base/core lemmas against `PcreCoreValues`;
- develop greedy/lazy quantifier values against `PcreOrderedValues`;
- run `PcrePOC` before commits that affect public integration.

## Safe Migration Order

1. Move base definitions first without changing theorem statements.
2. Move core relations and prove the same exported theorem names.
3. Move possessive quantifier values.
4. Move ordered values.
5. Only after all four moves pass, add greedy/lazy value runs.

Each step should preserve checked theorem names where possible. Avoid combining
the split with semantic changes.

## Timeout Policy

- `-o timeout=20` remains the current public fast-loop verifier.
- Treat `-o timeout=19` only as a trend probe, not as a pass/fail gate.
- Do not accept a new checked increment if it makes `-o timeout=20` flaky or
  fail unless the increment is explicitly about recovering proof-time headroom.
- A greedy/lazy value relation should be developed in a split theory/session
  before it is folded back into `PcrePOC`.

## Immediate Next Formal Candidate

After the split, implement:

```isabelle
pval_backtracking_zero_run
```

for `Greedy` and `Lazy`, restricted to `pcore_supported` repeated bodies.

The intended first bridge is:

```isabelle
qmatch_backtracking_zero_core_value_complete:
  q \<in> {Greedy, Lazy} \<Longrightarrow>
  pcore_supported r \<Longrightarrow>
  out \<in> set (qmatch fuel q 0 hi r st) \<Longrightarrow>
  \<exists>vs. pval_backtracking_zero_run q fuel hi r st vs out
```

This is the shortest route from the current ordered-value infrastructure to a
real PCRE-002 theorem.
