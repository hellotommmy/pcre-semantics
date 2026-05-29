# Rules for Working on the PCRE Semantics PoC

This is the project profile for the PCRE-style regex formalization track. It
inherits the repository-wide Agent Hunt discipline from the POSIX
backreference project, but its technical target is different: practical regex
engine behavior rather than only POSIX language recognition.

Read this file before doing PCRE work, then read:

- `PCRE_BOUNTIES.md`
- `PROGRESS_PCRE.md`
- `agent_hunt_pipeline/projects/posix-backref/BOUNTY_PROTOCOL.md`
- `agent_hunt_pipeline/projects/posix-backref/AGENT_ROLES.md`
- `agent_hunt_pipeline/projects/posix-backref/BRANCHING_AND_RUN_MODE.md`
- `agent_hunt_pipeline/projects/posix-backref/DUAL_AGENT_COORDINATION.md`

The public process inspirations are:

- `https://arxiv.org/abs/2601.03298`, which reports a long-running loop
  between LLM agents and a fast proof checker producing a large formalization
  quickly and cheaply.
- `https://arxiv.org/abs/2603.06737`, which describes a bounty-based,
  decentralized multi-agent proof marketplace where agents propose statements,
  attach bounties, compete to prove them, and the proof assistant remains the
  final authority.

## Project Identity

- Project: PCRE-style practical regex semantics in Isabelle/HOL.
- Main branch: `master`.
- Primary board: `PCRE_BOUNTIES.md`.
- Seed theory: `Pcre_POC.thy`.
- Session file: root `ROOT`, session name `PcrePOC`.
- Relationship to POSIX/backref: separate research lane. Do not change the
  frozen POSIX/backreference semantic statements to make PCRE work easier.

## Mission

Formalize industrial regex engine behavior construct by construct:

- ordered backtracking where result order matters;
- greedy, lazy, possessive, atomic, and non-backtracking behavior;
- captures, named captures, branch reset, backreferences, and subroutine calls;
- zero-width assertions, lookaround, anchors, and mode options;
- engine APIs returning spans and capture environments;
- parser/elaboration from PCRE syntax into the formal AST;
- correctness bridges between executable matchers and relational semantics.

Language membership alone is not enough for this track. PCRE behavior is often
observable through the first result, capture values, match start/end offsets,
and committed failure.

## Canonical Smoke Test

Every semantics for possessive quantifiers must explain this behavior:

```text
subject: ababa
greedy:     ^(aba|ab|a)*$   succeeds
possessive: ^(aba|ab|a)*+$  fails
```

The possessive version commits to the first repeated decomposition and does not
backtrack into shorter alternatives to repair the final match. This is a
minimal example of why PCRE-style semantics cannot be reduced to unordered
regular-language denotation.

## Allowed Edit Areas

PCRE workers may edit:

- `Pcre_POC.thy`
- future `Pcre_*.thy` files
- `ROOT`
- `PCRE_BOUNTIES.md`
- `PROGRESS_PCRE.md`
- PCRE-specific project notes under `agent_hunt_pipeline/projects/pcre-poc/`

Do not edit production POSIX/backref files for PCRE work unless the admin
explicitly opens an integration bounty:

- `RegLangs.thy`
- `PosixSpec.thy`
- `Lexer.thy`
- `LexerSimp.thy`
- `Blexer.thy`
- `BlexerSimp.thy`
- `BasicIdentities.thy`
- `GeneralRegexBound.thy`
- `ClosedForms.thy`
- `ClosedFormsBounds.thy`
- `FBound.thy`

## Bounty Rule

Each newly formalized construct, configuration option, or observable semantic
behavior that is absent from the POSIX/backreference example project can be a
PCRE bounty. A bounty must name:

- the PCRE feature or behavior;
- the checked Isabelle artifact;
- the verifier command or session;
- effort estimates;
- dependencies and blockers.

Wrapper-only theorem packages do not count. A paid PCRE bounty must add a new
semantic layer, executable algorithm, parser bridge, or nontrivial correctness
proof.

## Agent Coordination

Use the shared-branch pattern unless the admin explicitly requests a quarantine
branch:

```powershell
git pull --rebase --autostash origin master
git status --short --branch
```

PCRE work should be split into resource lanes:

- Semantics lane: `Pcre_POC.thy` datatype, executable matcher, relational
  semantics, and core correctness.
- Parser lane: future `Pcre_Parser.thy` and syntax elaboration.
- Differential lane: future `Pcre_Differential.thy` fixtures and documented
  PCRE or Perl examples.
- Integration lane: future bridge files comparing PCRE behavior with POSIX
  leftmost-longest semantics.
- Steward lane: mechanical merging, status repair, and guard execution only.

Only one agent should edit the same theory section at a time. Locks in
`PCRE_BOUNTIES.md` must be pushed quickly when multiple agents are active.

## Lessons Imported From 130k Lines

The first paper's main practical lesson is that scale comes from a tight loop:
small proof edits, fast checker feedback, and persistent resume prompts. For
PCRE work this means:

- keep each theorem narrow enough for a scoped load;
- treat slow Isabelle commands as proof-script bugs;
- update progress before context compaction;
- never rely on memory instead of the local project files;
- avoid deleting partially useful work during a reset or merge.

The POSIX/backref project already records a related local rule: never throw
away useful checked work. That rule is especially important here because PCRE
features interact in surprising ways.

## Lessons Imported From Agent Hunt

The second paper's useful lesson is decentralized statement discovery with
market pressure, but still under proof-assistant verification. For PCRE work:

- let agents propose small missing semantic facts as bounty tasks;
- price tasks by feature value and formal difficulty;
- allow competition for open tasks and sub-bounties for helper lemmas;
- require locks, deposits, and visible status to prevent duplicate work;
- reject bounty claims for wrappers that only repackage known facts;
- make Isabelle, not the agent or the ledger, the final correctness authority.

## Proof Integrity

Do not introduce `sorry`, `oops`, `axiomatization`, `quick_and_dirty`,
`oracle`, or hidden assumptions. Do not weaken theorem statements to collect a
bounty. If a PCRE statement is false, record the counterexample and propose a
corrected statement.

Prefer:

- executable definitions with clear fuel or width bounds;
- relational views that state the intended semantics;
- explicit correctness lemmas connecting the two;
- example theorems that pin down tricky engine behavior.

Avoid:

- huge `auto` calls over the full matcher;
- broad global simp rules for recursive matchers;
- conflating unordered language equality with ordered engine equality;
- changing POSIX/backref definitions as a shortcut.

## Proof Performance Budget

The PCRE pilot should stay in the fast-check loop. Slow Isabelle commands are
proof-script bugs, not routine build time.

Use these thresholds:

- about 0.5 seconds for broad proof search (`auto`, `simp`, `force`, `blast`,
  `metis`, large `elim!`): if it visibly hangs, abandon that proof shape and
  split the goal;
- 10 seconds on one command: identify the source line and the facts in scope;
- 30 seconds on one command: replace broad automation with local helper lemmas
  and explicit cases;
- 120 seconds: let the timeout wrapper kill the build and inspect the first
  real slow command;
- 200 seconds: treat this as a definition or proof-structure bug, not a
  tolerable PCRE build.

Preferred repairs:

- replace heavy nested or overlapping `fun` definitions by `primrec`,
  `definition`, or simpler structural recursion with explicit `case ... of ...`
  branches;
- use constructor-specific elimination and introduction rules instead of
  handing automation the whole matcher or value relation;
- prove small named facts such as output shape, consumed substring, capture
  update, and first-result facts before the final theorem;
- when a theorem needs an existential witness, introduce it explicitly with
  `exI[of _ ...]` and a named local fact instead of asking `blast` or `auto` to
  discover schematic witnesses;
- avoid global simp rules for recursive matchers unless termination and rewrite
  direction are clearly harmless.
- avoid `by eval`/code-generation proofs for concrete examples involving
  `pstate` or captures: `capenv` is function-valued, and generated equality can
  require enum/equal instances for functions;
- if a wrapper theorem pushes the clean session to the timeout boundary, defer
  it or move it into a split theory instead of keeping it in the hot path.

Imported `backref-values` lesson: the POSIX backreference pilot had a slow
`fun (sequential)` value-injection definition over many nested, overlapping
patterns. Replacing it with `primrec` over the regex and explicit value cases in
the right-hand side reduced cold pilot checks from about 200 seconds to about 16
seconds. Any PCRE submatch-value or capture-value layer should follow that
shape from the start.

## Validation

Fast scoped check for the seed PCRE theory:

```powershell
$env:USER_HOME='/cygdrive/c/Users/kaihong/Documents/pcre_semantics/.codex/isabelle-home'
& 'C:\Users\kaihong\Desktop\Isabelle2025\contrib\cygwin\bin\bash.exe' -lc 'cd /cygdrive/c/Users/kaihong/Documents/pcre_semantics && /cygdrive/c/Users/kaihong/Desktop/Isabelle2025/bin/isabelle process -l HOL -d . -T Pcre_POC 2>&1'
```

Session target when the local Isabelle heap/log environment permits it:

```powershell
& 'C:\Users\kaihong\Desktop\Isabelle2025\contrib\cygwin\bin\bash.exe' -lc 'cd /cygdrive/c/Users/kaihong/Documents/pcre_semantics && /cygdrive/c/Users/kaihong/Desktop/Isabelle2025/bin/isabelle build -v -j 1 -d . PcrePOC'
```

The raw `isabelle process` command stays interactive after loading the theory,
so use an outer timeout and inspect the output for real Isabelle errors.

## Progress Reporting

After every meaningful PCRE step, update `PROGRESS_PCRE.md` with:

- branch;
- files changed;
- definitions and theorem names;
- verifier command and result;
- whether any Isabelle command was slow;
- next smallest safe step;
- blockers.

When ending a PCRE session, report branch, changed files, checked artifacts,
validation result, and any admin questions.

## Real Engine Feedback Loop

Do not formalize PCRE behavior from intuition alone. For every new construct or
option, follow this loop:

1. Read the official PCRE2 documentation and record the precise claim.
2. Run real examples with PCRE2 `pcre2test` when available; use Perl only as a
   temporary Perl-compatible oracle when PCRE2 tools are missing.
3. Compare popular engines before treating terminology as universal: PCRE2,
   Perl, Python `re`, Java `Pattern`, .NET Regex, JavaScript, RE2/Rust regex,
   and Oniguruma/Ruby are the default survey set.
4. Write the Isabelle semantics and prove at least one executable behavior
   theorem plus a relational correctness bridge.
5. Add a fuzzing or differential-test note if the construct affects search-tree
   size, backtracking, captures, or match priority.

The default validation entry point is:

```powershell
powershell -ExecutionPolicy Bypass -File tools/run_engine_feedback.ps1
```

PCRE2 official anchors for this loop:

- `https://pcre.org/current/doc/html/pcre2pattern.html`
- `https://pcre.org/current/doc/html/pcre2matching.html`

For possessive quantifiers, PCRE2 states that they are equivalent in meaning to
atomic grouping: after a successful match of the quantified item, later failure
cannot backtrack into it. The formal semantics must model that commitment, not
just language membership.
