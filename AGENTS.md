# Agent Instructions

This is the standalone PCRE semantics repository. Do not do PCRE development
inside the POSIX/backreference repository.

Before editing, read:

- `CLAUDE.md`
- `agent_hunt_pipeline/projects/pcre-poc/CLAUDE.md`
- `PCRE_BOUNTIES.md`
- `PROGRESS_PCRE.md`

Rules:

- Validate semantic claims against official PCRE2 documentation first.
- Run at least one real engine test for every new observable behavior whenever a supporting engine is available.
- Prefer PCRE2 `pcre2test`; Perl is an acceptable compatibility oracle for Perl-compatible features when PCRE2 tools are unavailable.
- Formalize only after recording the external behavior and source references.
- No `sorry`, `oops`, `axiomatization`, `quick_and_dirty`, `oracle`, or hidden assumptions.
- Commit and push small checked increments to avoid losing progress.
- Treat slow Isabelle commands as proof-script bugs, not as normal build time.
  Broad `auto`/`simp`/`force`/`blast`/`metis` search should normally return in
  well under a second on this pilot. If it visibly hangs, stop that proof shape
  and split the goal into explicit cases and helper lemmas.
- Do not fix a timeout by merely raising the timeout and rerunning unchanged.
  Identify the slow source line and replace the resource-intensive command or
  definition. For heavy nested or overlapping recursive definitions, prefer
  `primrec`, simple `definition`, or recursion over one structural argument
  with explicit `case ... of ...` branches.
- Use the `backref-values` lesson: a slow `fun (sequential)` definition with
  many overlapping value patterns was replaced by a `primrec` over the regex
  plus explicit value cases, reducing cold pilot checks from about 200 seconds
  to about 16 seconds. Apply the same discipline here before adding PCRE value
  or submatch inhabitation layers.
- For existential or constructor goals, avoid handing schematic witnesses to
  broad `blast`/`auto`. Name the witness-producing fact, then use explicit
  `proof (intro exI[of _ ...])`, constructor rules, and local `cases` so the
  command checks immediately.
- Avoid `by eval`/code-generation proofs for concrete PCRE examples that touch
  `pstate` or captures: `capenv` is function-valued, so code generation can
  create equality/enum obligations for functions. Prefer structural lemmas,
  explicit witnesses, or an external engine transcript for sanity examples.
- If a wrapper theorem passes once but pushes the clean session to the timeout
  boundary, defer it or move it to a split theory. Do not keep non-core wrappers
  in the hot proof path at the cost of the fast feedback loop.
