# PCRE Semantics Formalization

Standalone Isabelle/HOL research repo for practical PCRE-style regex semantics.

The project is separate from `hellotommmy/posix`. It may later import or compare
against POSIX/backreference results, but PCRE work should happen here first.

Current seed artifacts:

- `Pcre_POC.thy`: executable and relational proof-of-concept semantics for ordered backtracking, greedy/lazy/possessive/linear repetition, captures, backreferences, atomic groups, lookaround, anchors, conditionals, search, result objects, and a subpattern-call layer.
- `PCRE_BOUNTIES.md`: 50,000 digital USD bounty board for new constructs/options/semantics.
- `agent_hunt_pipeline/projects/pcre-poc/CLAUDE.md`: agent operating profile.
- `tools/run_engine_feedback.ps1`: real-engine validation harness.

First validated smoke test:

```text
subject: ababa
greedy:     ^(aba|ab|a)*$   => yes
possessive: ^(aba|ab|a)*+$  => no
```

The corresponding Isabelle theorems are `greedy_ababa_accepts` and
`possessive_ababa_rejects`.