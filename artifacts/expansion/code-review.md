# Read-only review of the first expanded implementation

Scope: the suffix/finalizer changes in `NormArith/Census.lean` and conjunction /
scalar-order preprocessing in `NormArith/Tactic.lean`, compared with the retained
v3 implementation. No production files were changed during this review.

No soundness or explicit-fact-control blocker was found.

- Suffix ranges come from actual parser tactic-sequence child lists. Replay
  matches the exact first child's original source range, uses its pre-tactic
  metavariable/local context, requires a single current goal, and ends at that
  sequence's tail. Nested branches therefore get their own sequence bounds.
  The real integration regression rewrites prepared, nested-branch, and
  `where finally` examples, then compiles their combined source.
- Finalizer body ranges cover the optional finalizer tactic block or named
  subsection's tactic body. They preserve subsection labels and statement text.
  This matches pinned Lean's `Parser.Term.whereFinally` and
  `whereFinallySubsection` syntax.
- Conjunction splitting constructs checked `And.left`/`And.right` projections.
  Explicit fact lists still exclude unselected norm-containing conjuncts;
  norm-free scalar conjuncts remain available, as required by the existing
  explicit-fact policy.
- Added norm nonnegativity, real norm bounds, and min/max inequalities are
  universal checked lemmas derived from the target or selected comparisons.
  They do not derive norm bounds from excluded local hypotheses. Failed
  `linarith` attempts restore tactic state.
- Isolated suffix replay is still only a proposal. The final source compile
  remains mandatory, with pre-command proof checking and parent-reference
  rejection retained. This protects against unusable source spans and effects
  on subsequent proof text.

Nonblocking resource concern: each single-goal tactic-info node currently scans
all suffixes in its command. This can be quadratic in a large command's syntax
size. The declared heartbeat, wall-time, and file memory limits still apply;
a range-indexed suffix map is a possible later optimization.

The composed patch audited in `combined-01-audit.json` is an intermediate,
source-verified result while discovery continues. Its line counts are not a
new compilation-speed claim or the final expanded-study result.

Reviewed production source SHA256:

- `NormArith/Census.lean`: `3759e281a3a6dd72a248dc79599ce3977b614389174a56d7c4f8f679cd7c1dc6`
- `NormArith/Tactic.lean`: `475b7b914004344c7d215e25d830dd4c6275f12b7c6da81c5763f88d871a4616`
