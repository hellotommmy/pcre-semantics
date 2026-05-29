# PCRE Semantics Bounties

This is the bounty board for the PCRE-style industrial regex formalization
track. It complements, but does not replace, `BACKREF_BOUNTIES.md`.

The rule for this board is intentionally simple: each newly formalized regex
construct, configuration option, engine mode, or observable semantic behavior
that is not already present in the POSIX/backreference example project can be
priced as a bounty. A payout is valid only for checked Isabelle artifacts with
no proof-bypass markers and with progress recorded in `PROGRESS_PCRE.md`.

The total pool is **50,000 digital USD** accounting units. These are project
coordination units, not a real-money representation inside the repository.

See `agent_hunt_pipeline/projects/pcre-poc/CLAUDE.md` for the PCRE track
rules and `agent_hunt_pipeline/projects/posix-backref/BOUNTY_PROTOCOL.md` for
the inherited Agent Hunt mechanics.

## Scope

Eligible work must add at least one of:

- a new executable or relational PCRE construct semantics;
- a new configuration or mode semantics, such as multiline, dotall, ungreedy,
  Unicode, anchored, or newline behavior;
- a new engine-observable behavior, such as ordered captures, match spans,
  possessive commitment, backtracking verbs, or start-offset handling;
- a nontrivial correctness bridge between executable matching and relational
  semantics;
- a verified parser/frontend bridge from PCRE syntax into the formal AST.

Wrapper-only theorem bundles, renamings, `iff` restatements, and theorem
packages that merely summarize existing facts are not bounty-eligible.

Canonical smoke test: on subject `ababa`, ordinary greedy repetition for
`^(aba|ab|a)*$` succeeds, while possessive repetition for
`^(aba|ab|a)*+$` fails because the first repeated branch is committed and no
backtracking into shorter alternatives is allowed.

## Pool

| Category | Amount |
| --- | ---: |
| Total pool | 50,000 |
| Allocated (active + completed) | 50,000 |
| Collected (paid out) | 0 |
| Reserved (unallocated) | 0 |

## Agent Balances

| Agent | Role | Balance | Notes |
| --- | --- | ---: | --- |
| Codex | Admin/Worker | 0 | Current PCRE track setup |
| Opus | Worker | 0 | Optional future worker |
| MergeSteward | Steward | 0 | Mechanical integration only |
| Alice | Worker | 0 | Optional future worker |
| Bob | Worker | 0 | Optional future worker |

## Active

| ID | Task | Bounty | Est. Lines | Difficulty | Est. USD | Status | Owner | Artifact | Verifier | Notes |
| --- | --- | ---: | ---: | ---: | ---: | --- | --- | --- | --- | --- |
| PCRE-001 | Possessive repetition commitment smoke test | 2,000 | 80 | 7 | 2,000 | OPEN | - | Pcre_POC.thy:possessive_ababa_rejects,greedy_ababa_accepts | Isabelle:PcrePOC | Prove the user-supplied Perl behavior as executable and relational facts |
| PCRE-002 | Ordered greedy lazy and possessive quantifier semantics | 2,500 | 110 | 7 | 2,500 | OPEN | - | Pcre_POC.thy:qmatch_order_complete | Isabelle:PcrePOC | Sets are not enough; first-result ordering must be specified and proved |
| PCRE-003 | Atomic-group commitment and capture interaction | 2,500 | 120 | 8 | 2,500 | OPEN | - | Pcre_POC.thy:atomic_capture_commit_sound | Isabelle:PcrePOC | Atomic groups must commit both input and capture choices consistently |
| PCRE-004 | Engine result and capture validity invariants | 2,500 | 120 | 7 | 2,500 | OPEN | - | Pcre_POC.thy:pcre_exec_valid_caps,pcre_exec_span_sound_complete | Isabelle:PcrePOC | Match spans and captures must be tied to the original subject |
| PCRE-005 | Backtracking verbs semantics | 3,500 | 170 | 9 | 3,500 | OPEN | - | Pcre_POC.thy:pcre_verb_trace_sound | Isabelle:PcrePOC | Cover PRUNE SKIP COMMIT ACCEPT FAIL as control effects, not characters |
| PCRE-006 | Keep or reset match-start semantics | 2,500 | 110 | 8 | 2,500 | OPEN | - | Pcre_POC.thy:pcre_keep_resets_start_sound | Isabelle:PcrePOC | Formalize the observable effect of keep on reported start offsets |
| PCRE-007 | Named captures and branch-reset numbering | 3,000 | 140 | 8 | 3,000 | OPEN | - | Pcre_POC.thy:pcre_named_branch_reset_sound | Isabelle:PcrePOC | Capture environments need both numeric and named lookup discipline |
| PCRE-008 | Conditional subpatterns and assertion conditionals | 2,500 | 110 | 7 | 2,500 | OPEN | - | Pcre_POC.thy:pcre_conditional_complete | Isabelle:PcrePOC | Include capture-defined and assertion-based condition forms |
| PCRE-009 | Lookaround semantics with width discipline | 3,000 | 150 | 8 | 3,000 | OPEN | - | Pcre_POC.thy:pcre_lookaround_width_sound | Isabelle:PcrePOC | Fixed-width and bounded-width constraints must be explicit |
| PCRE-010 | Mode-option and anchor matrix | 3,000 | 150 | 8 | 3,000 | OPEN | - | Pcre_POC.thy:pcre_options_anchor_matrix_sound | Isabelle:PcrePOC | Model multiline dotall ungreedy anchored newline and dollar-end variants |
| PCRE-011 | Unicode properties and grapheme clusters | 4,000 | 220 | 9 | 4,000 | OPEN | - | Pcre_POC.thy:pcre_unicode_semantics_sound | Isabelle:PcrePOC | Character-class semantics must be parameterized enough for PCRE data tables |
| PCRE-012 | PCRE syntax frontend to formal AST | 3,000 | 160 | 8 | 3,000 | OPEN | - | Pcre_Parser.thy:pcre_parse_sound | Isabelle:PcrePOC | Verified subset parser or checked elaborator from PCRE syntax |
| PCRE-013 | Subpattern calls recursion and DEFINE blocks | 3,500 | 180 | 9 | 3,500 | OPEN | - | Pcre_POC.thy:pcre_subroutine_complete | Isabelle:PcrePOC | Extend the current fuelled program layer into a complete call semantics |
| PCRE-014 | Linear or non-backtracking fragment theorem | 3,000 | 160 | 8 | 3,000 | OPEN | - | Pcre_POC.thy:pcre_linear_fragment_sound | Isabelle:PcrePOC | Identify a fragment where ordered exploration is equivalent to linear matching |
| PCRE-015 | Differential executable semantics harness | 3,500 | 170 | 8 | 3,500 | OPEN | - | Pcre_Differential.thy:pcre_fixture_sound | Isabelle:PcrePOC | Formal test fixtures against documented PCRE or Perl examples, with checked expected outcomes |
| PCRE-016 | POSIX compatibility and priority comparison | 2,500 | 130 | 8 | 2,500 | OPEN | - | Pcre_Posix_Bridge.thy:pcre_posix_priority_bridge | Isabelle:PcrePOC+BackRefPilot | Compare leftmost-first PCRE behavior with existing POSIX leftmost-longest story |
| PCRE-017 | Full PCRE PoC consolidation theorem | 3,500 | 220 | 10 | 3,500 | OPEN | - | Pcre_POC.thy:pcre_poc_semantics_complete | Isabelle:PcrePOC | One umbrella correctness theorem covering all accepted PCRE bounty constructs |

## Completed

| ID | Task | Bounty | Est. Lines | Difficulty | Est. USD | Status | Owner | Artifact | Verifier | Notes |
| --- | --- | ---: | ---: | ---: | ---: | --- | --- | --- | --- | --- |

## Seed Artifacts

`Pcre_POC.thy` is a seed proof-of-concept kernel containing ordered
backtracking, greedy, lazy, possessive, linear repetition, captures,
backreferences, atomic groups, lookaround, conditionals, word boundaries,
line anchors, search, result objects, and a fuelled subpattern-call layer.

These seed artifacts do not automatically collect bounties from this new board.
To collect, an agent must lock or complete a concrete PCRE task above, name the
checked theorem or definition, pass the verifier, and update the ledger.

## Locks

| Lock ID | Task ID | Agent | Deposit | Branch | Expires UTC | Status |
| --- | --- | --- | ---: | --- | --- | --- |
| - | - | - | 0 | - | - | RELEASED |

## Lock Rules

- Lock deposit: 10% of bounty, rounded up.
- Maximum **10** active locks per agent.
- Locks expire after **24 hours**.
- Push lock/status edits immediately when multiple agents are active.
- Lock-or-lose: if another agent proves a locked task, the bounty goes to the
  locker unless a sub-bounty agreement says otherwise.
- A lock does not authorize changing frozen POSIX/backref statements.

## Ledger

| Time UTC | Agent | Action | Task ID | Amount | Balance After | Notes |
| --- | --- | --- | --- | ---: | ---: | --- |
| 2026-05-29T00:00:00Z | Codex | RESET | PCRE-001 | 0 | 0 | Initialize PCRE board |
| 2026-05-29T00:00:00Z | Opus | RESET | PCRE-001 | 0 | 0 | Initialize PCRE board |
| 2026-05-29T00:00:00Z | MergeSteward | RESET | PCRE-001 | 0 | 0 | Initialize PCRE board |
| 2026-05-29T00:00:00Z | Alice | RESET | PCRE-001 | 0 | 0 | Initialize PCRE board |
| 2026-05-29T00:00:00Z | Bob | RESET | PCRE-001 | 0 | 0 | Initialize PCRE board |

## Completion Rules

A PCRE bounty is complete only when:

- the construct, option, or semantic behavior is not already covered by the
  POSIX/backreference example project;
- the artifact is a checked Isabelle definition, executable algorithm,
  relational semantics, or nontrivial correctness theorem;
- the relevant scoped load or session build succeeds;
- no `sorry`, `oops`, `axiomatization`, `quick_and_dirty`, `oracle`, or hidden
  proof bypass is introduced;
- `PROGRESS_PCRE.md` records the build command, result, theorem names,
  remaining blockers, and next smallest safe step;
- all affected agents can see the lock/status update on the shared branch.

## Sub-Bounties

Agents may split a PCRE task into sub-bounties from their own balance. A
sub-bounty must have a clear artifact name, verifier, and dependency on the
parent task. Sub-bounties cannot pay for wrapper-only facts.

## Early-Finish Bonus

If all allocated PCRE tasks are completed before the admin-set deadline, a 10%
bonus of any future PCRE extension pool may be distributed among agents who
completed at least one PCRE bounty. This board starts with no unallocated
reserve, so the bonus requires an explicit later pool extension.
