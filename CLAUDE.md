# Project Agent Entry Point

This repository uses an Agent Hunt style workflow for PCRE-style regex semantics.

Read first:

- `AGENTS.md`
- `agent_hunt_pipeline/projects/pcre-poc/CLAUDE.md`
- `PCRE_BOUNTIES.md`
- `PROGRESS_PCRE.md`

Core loop:

1. Pick a PCRE construct or option from the bounty board.
2. Read the official documentation and record the exact semantic claim.
3. Run real-engine examples with `tools/run_engine_feedback.ps1` or a more specific harness.
4. Formalize executable and relational semantics in Isabelle.
5. Prove the executable/relational bridge and at least one behavior theorem.
6. Re-run engine tests and Isabelle checks.
7. Commit and push.

Proof-performance rules:

- A slow Isabelle command is a proof-engineering bug. Do not respond by only
  increasing the timeout.
- Broad `auto`, `simp`, `force`, `blast`, `metis`, and large `elim!` calls
  should be replaced when they visibly hang. Split the goal, name the local
  facts, and use constructor-specific eliminators or explicit `cases`.
- If a recursive definition itself is slow to process, simplify its shape.
  Prefer `primrec`, `definition`, or one clear structural recursion with
  explicit `case ... of ...` branches over nested overlapping `fun` patterns.
- Import the `backref-values` lesson for PCRE value work: the POSIX pilot
  replaced a slow `fun (sequential)` over many value patterns by a `primrec`
  over the regex with explicit value cases, cutting cold checks from roughly
  200 seconds to roughly 16 seconds.
- For existential/constructor proof obligations, name the local witness fact
  and use explicit `exI`, constructor rules, and `cases`. Do not leave
  schematic witnesses for broad `blast`/`auto`; even short-looking lines can
  push clean checks over the timeout.
- Avoid `by eval`/code-generation proofs for concrete PCRE examples that touch
  `pstate` or captures. The capture environment is function-valued, so code
  generation can introduce equality/enum obligations for functions.
- Defer wrapper theorems that push the clean session to the timeout boundary.
  A theorem that is not a semantic layer should not cost the project its fast
  checker feedback loop.
