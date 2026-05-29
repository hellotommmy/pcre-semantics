# Engine Feedback Workflow

PCRE semantics work must follow a four-way feedback loop:

1. **Official source**: read PCRE2 documentation first, normally
   `pcre2pattern` for syntax/construct semantics and `pcre2matching` for engine
   algorithms.
2. **Real engine**: run PCRE2 `pcre2test` when available. For Perl-compatible
   constructs, Perl may be used as a temporary oracle, but PCRE2 transcripts are
   required before claiming PCRE2-specific fidelity.
3. **Cross-engine survey**: compare popular engines before generalizing a term
   such as greedy, possessive, atomic, non-backtracking, or linear. Track at
   least PCRE2, Perl, Python `re`, Java `Pattern`, .NET Regex, JavaScript, RE2,
   Rust regex, and Oniguruma/Ruby when relevant.
4. **Formalization**: encode the semantic distinction in Isabelle, prove the
   executable/relational bridge, then prove the concrete behavior theorem.

For the motivating example, PCRE2 documents possessive quantifiers as a notation
for atomic grouping: once the quantified item has matched, later failure cannot
backtrack into it. That is different from ordinary greedy repetition, where the
engine may revisit the repeated item to make the rest of the pattern succeed.

Research questions to keep live:

- Does each engine use "greedy" to mean longest repetition count, first-success
  maximum munch, or a backtracking priority discipline?
- Is the term used consistently within PCRE2 across quantifiers, atomic groups,
  lookaround, subroutine calls, and backtracking verbs?
- Which non-backtracking fragments are regular/linear and can be compiled to a
  safe matcher without changing captures or match priority?
- Where do PCRE-compatible features create ReDoS risks, and can the formal
  semantics expose the vulnerable search tree shape?
- How should fuzzing be targeted by construct: grammar-directed generation,
  metamorphic properties, engine-vs-Isabelle agreement, timeout growth, and
  equivalence/non-equivalence of greedy, possessive, and atomic rewrites?