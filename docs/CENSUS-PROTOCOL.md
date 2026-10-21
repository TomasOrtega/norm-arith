# Semantic census and source selection

The source universe is every tracked `.lean` file below `Mathlib/` at the pinned
mathlib revision. `MathlibTest`, `Archive`, and external packages are outside the
universe. Record a result for every file, including failures and unprocessed
files. A calibration subset does not establish full-library coverage.

## Observations and eligibility

Elaborate the original source with its actual Lake module setup. Traverse
finalized tactic and term information. Retain source-backed proposition goals,
source positions, declaration names, local contexts, and the declared outcome
for each norm-related observation. A scalar conclusion can qualify through
recognized local norm facts even when the conclusion contains no norm itself.
Record unresolved, synthetic, duplicate, and uneditable observations separately.
Only spans contained in a recognized declaration body can become edits. Proofs
in declaration types, binder defaults, and other statement syntax remain
observations with an exclusion reason. Each proposal records the enclosing
body's UTF-8 byte range.
Honor the module setup's elaboration options and Lean's normal asynchronous
default. Wait for finalized command snapshots before reading information trees;
forcing synchronous elaboration can change private-declaration compatibility.

`NormArith.goalFragment` distinguishes the real core, additive-group extension,
opaque upper-bound extension, and goals outside the fragment. The real core
requires actual real normed-space capabilities, not only norm-shaped syntax.
An arbitrary metric space does not become a real normed space because its goal
mentions `dist`. Opaque scalar products remain outside the complete core.

The built-in preparation normalizes distances in the target and in selected
fact proofs. It preserves the types of the user's local declarations. Local
`let` expressions are reduced definitionally before fact classification and
vector normalization. Bare `norm_arith` selects recognized local bounds;
`norm_arith [facts]` controls norm facts and retains norm-free scalar comparisons.
Vector equalities give checked zero-norm facts. No one-off human lemma is added
to make a census attempt succeed.

## Replay and evidence

Replay requires the tactic import. Elaborate an augmented variant with the fixed
`NormArith` import and match observations to the original by source span,
declaration, and canonical closed context and goal. The added import can affect
elaboration, so an augmented observation alone is not an original-source census.
Read observations with their elaborated environments, so within-command
generated declarations remain available for type inference. For tactic replay
and kernel checking, use the environment from before the enclosing source
command, with the recorded metavariables, local declarations, options, and local
instances. Reject unresolved proofs, admissions, and self references;
kernel-check each successful proposal.
Files in the tactic's own dependency closure receive an explicit import-cycle
outcome. Do not merge independently imported environments.

A successful replay is an isolated proposal. It is not a verified source edit
and contributes no final line saving before the combined source patch compiles.
The run manifest fixes source hashes, executable and implementation hashes,
resource limits, preparation, matching, and the tracked universe. Resuming a run
with changed inputs is forbidden. Keep every attempt and its outcome.
Create `STOP_REQUESTED` in a run directory to drain active work and stop before
launching more files. The stopped run remains incomplete. Remove the marker
explicitly before resuming with unchanged frozen inputs.

The fixed replacement has one code line. A source span confined to one physical
line cannot save a code line, so retain it as `no_line_saving_untried` without a
tactic attempt. This outcome establishes neither tactic success nor failure.
Attempt eligible multiline bodies with the declared per-goal limits. Resource
failures at the file level receive one predeclared larger retry, run serially
after the first tier; proof failures receive no discretionary retry. Preserve
the first attempt and the retry in the ledger.

## Selection

`scripts/select_census.py` converts UTF-8 half-open proposal spans to exact
whole-line edits while preserving surrounding source text. It checks full-file
and span hashes. A fixed one-line replacement is `norm_arith` for a tactic node
or `by norm_arith` for a term node.

Within each file, choose the disjoint whole-line spans with the largest total
reduction in nonblank, noncomment code lines. Equal savings prefer fewer edits,
then source order and stable candidate ids. Equivalent edits count once.
Charge the new import once per file and require positive net saving. Keep
no-saving, duplicate, overlapping, rejected, and unprocessed outcomes in the
selection ledger. Timing never affects selection.

Compile the combined replacement files with actual imports and fresh outputs.
Preserve theorem statements and assumptions. Source-compile rejections require
recorded reasons and deterministic reselection among the remaining candidates.
Only the final compiled nonoverlapping patch enters headline accounting and the
paired affected-file experiment. Its compilation includes actual tactic search.

## Current evidence

The initial two-file calibration and selector checks are development evidence.
They do not establish a complete census or a new compilation speedup. The
prototype's separate archived measurements remain in `benchmarks/results/`.
The final census manifest, file ledger, selection ledger, compiled patch, and
confirmatory analysis must supply the new paper's empirical claims.
