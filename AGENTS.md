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