# PCRE Progress

Last updated: 2026-05-29 (standalone repo created)

## Standalone Repo Bootstrap (2026-05-29)

- Repository path: `C:\Users\kaihong\Documents\pcre_semantics`.
- Remote target: `hellotommmy/pcre-semantics`.
- Migrated seed theory `Pcre_POC.thy` out of the POSIX/backreference repo.
- Added standalone `ROOT`, `README.md`, `AGENTS.md`, `CLAUDE.md`, PCRE bounty board, and real-engine feedback harness.
- Seeded AST definitions for the motivating example; the exact checked theorem
  pair remains open as PCRE-001.
- Real-engine baseline: Perl from Isabelle's Cygwin distribution is available and is used as the current compatibility oracle. PCRE2 `pcre2test` is not yet installed on this machine.
- Next smallest safe step: install or vendor PCRE2 tools, then add a PCRE2 transcript for the same smoke test and record exact PCRE2 version.
