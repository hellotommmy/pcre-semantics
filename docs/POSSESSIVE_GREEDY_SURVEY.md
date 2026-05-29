# Possessive vs Greedy Smoke Test

This note records the external evidence and formalization target for PCRE-001.
It is deliberately separate from the Isabelle theory: the proof should be
small, but the semantic claim must be anchored in real documentation and real
engine behavior.

## Pattern

```text
subject: ababa
possessive: ^(aba|ab|a)*+$  => no
greedy:     ^(aba|ab|a)*$   => yes
```

The example distinguishes two ideas that are often conflated:

- ordinary greedy repetition tries repetition branches in a greedy priority
  order but may still backtrack when the following pattern fails;
- possessive repetition commits to the chosen quantified match and prevents
  later failure from re-entering that quantified item.

## Official PCRE2 Claim

Primary sources:

- `https://pcre.org/current/doc/html/pcre2pattern.html`
- `https://pcre.org/current/doc/html/pcre2matching.html`

Relevant PCRE2 facts to model:

- `pcre2_match()` is the Perl-compatible standard algorithm.
- The standard algorithm is a depth-first search through the pattern tree.
- When a mismatch occurs, it tries alternatives at the current point, then
  backs up to previous branch points.
- Greedy or ungreedy quantifiers control the order in which repetition
  branches are tried.
- Atomic grouping locks the matched subpattern so later failure cannot
  backtrack into it.
- Possessive quantifiers are equivalent in meaning to the corresponding atomic
  grouped form and are always greedy.
- PCRE2 may automatically possessify simple cases such as `A+B` into `A++B`
  when backtracking into the repeat cannot help.

For PCRE-001, the formal target is therefore not "Kleene star chooses the
longest possible list of iterations" as an unordered language fact. The target
is an ordered depth-first engine semantics with a cut/commit boundary around
the possessive quantifier's repeated item.

## Real Engine Transcript

Current local oracle:

```powershell
powershell -ExecutionPolicy Bypass -File tools/run_engine_feedback.ps1
```

Observed output:

```text
== Perl compatibility oracle ==
possessive    no   expected=no
greedy        yes  expected=yes
== PCRE2 pcre2test oracle ==
WARNING: pcre2test is not installed or not on PATH
```

Perl is used only as a temporary compatibility oracle. A PCRE2 `pcre2test`
transcript must be added before claiming PCRE2-specific fidelity.

## Cross-Engine Notes

These are survey targets, not completed claims:

- PCRE2 and Perl: Perl-compatible backtracking semantics for the standard
  matcher; possessive quantifiers act like atomic groups.
- Java `Pattern`: documents greedy, reluctant, and possessive quantifier
  families explicitly.
- Python `re`: supports atomic groups `(?>...)` in recent versions; the
  official documentation describes discarded internal stack points. It does
  not use PCRE's possessive quantifier syntax as the main surface form.
- .NET Regex: official docs emphasize a backtracking NFA engine and identify
  atomic groups/lookarounds as constructs that limit or suppress backtracking.
- JavaScript: MDN documents greedy and non-greedy quantifiers, but current
  standard JavaScript lacks possessive quantifier and atomic-group syntax.
- RE2 and Rust regex: intentionally avoid backtracking features such as
  backreferences and lookaround in favor of predictable-time matching.

The terminology is not globally uniform. "Greedy" can mean "try larger
repetition counts first" inside an ordered search, not "commit to the maximum
possible consumed substring". This distinction should be made explicit in the
formal semantics and any writeup.

## Fuzzing Properties

PCRE-001 suggests construct-directed fuzzing:

- Generate alternatives with shared prefixes, such as `(aba|ab|a)`.
- Wrap them in `*`, `+`, `{m,n}`, and their possessive variants.
- Append suffix anchors or literals that force the engine to decide whether it
  may re-enter the quantified item.
- Compare ordinary greedy, possessive, and atomic rewrites:
  `X*+Y` should agree with `(?>X*)Y` for the relevant PCRE surface subset, but
  may differ from `X*Y`.
- Track search-cost properties separately from language acceptance. A pair can
  have the same denotation but very different backtracking trees.

For ReDoS-oriented tasks, generate nested unlimited repeats and failing suffixes
and measure whether atomic or possessive rewrites collapse the search tree. PCRE2
documents this exact failure mode for nested repeats and recommends atomic
groups/possessive quantifiers to avoid very long failing matches.

## Isabelle Target

The checked proof should eventually provide:

```isabelle
lemma greedy_ababa_accepts:
  "pcre_fullmatch fuel pcre_ex_greedy_ababa ''ababa''"

lemma possessive_ababa_rejects:
  "\<not> pcre_fullmatch fuel pcre_ex_possessive_ababa ''ababa''"
```

The proof must be narrow. Whole-engine `eval`/`normalization` currently trips
over code generation for the general lookbehind equation, and broad `simp`
over the full matcher is too slow. A good next step is a small computation
lemma for the fragment generated by literals, alternation, sequencing, anchors,
and quantifiers.
