# Review of the isolated generic metric prototype

No soundness or tactic-state blocker was found in the revised prototype. This is
a source review, not a new completeness proof or compilation-speed result.

Reviewed files and SHA256:

- `.lake/metric-prototype/MetricPrototype.lean`:
  `2b35382914e98d4bb5456188789b50ed35c4671536f31ab923ee1ef23004e96a`.
- `.lake/metric-expansion-prototype-v2/MetricPrototype.lean`:
  `40009e0bd5191be3c2f8fa34989158d3335f29b11b02621757a18fc6efea7210`.
- The module-compatible `.olean`:
  `a5a2374ad089ef9d8324e05d957a071f52f3f57244d286659cdcc258504edbf4`.

The namespace engine is byte-identical in both sources: 2,796 bytes, SHA256
`e35ad53224c7805bac2d317f910a361719474343cdeb8378dd68ee3a0aec383c`.
Only the module/import/export wrapper and trailing test examples differ.

The real-comparison check (legacy source lines 9–15) restricts the target and
selected facts. Point collection (17–26) rejects loose bound variables and
metavariables. The proof engine (28–61) instantiates `dist_self`, `dist_nonneg`,
`dist_comm`, and `dist_triangle`, then invokes `linarith` with `only_on = true`.
All supplied facts are proof terms; no unchecked certificate or admission is
introduced. Failed lemma construction restores its saved state, including the
pair of nonnegativity/symmetry facts as one unit.

Pinned Lean's `Lean/Elab/Tactic/Basic.lean:381–387` also implements ordinary
`TacticM` exception handling with `Tactic.tryCatchRestore`. Therefore a prior
concern about the original scratch code lacking explicit per-lemma restores was
conservative, not a demonstrated state-leak bug. The revised explicit guards are
clear. A production fallback still needs normal backtracking around a failed
whole attempt and the existing final goal-closure checks.

The scratch explicit list (65–76) passes exactly the listed proofs. Production
`norm_arith [facts]` intentionally retains norm-free scalar local comparisons.
Integration should pass the already-selected fact array to the metric engine;
it should not rescan local declarations and recover excluded distance/norm
hypotheses. Preserve negative explicit-fact controls when integrating.

The global eight-point cap permits at most 400 generated facts: eight self
equalities, 56 pair facts, and 336 ordered distinct-point triangle inequalities.
It does not cap the number or size of input facts, expression traversal, or
`linarith` work. Use this as a fallback after cheaper norm paths and retain the
declared heartbeat/time/memory budgets. Multiple spaces and structurally distinct
aliases can consume the quota; target points are visited first. A failed bounded
search is incomplete, not evidence that the estimate is mathematically invalid.

At review time, trial 02 whole-file compilation verifies Bounded and Kuratowski;
ArzelaAscoli fails. Trial 01's module packaging failure is retained. These are
scratch trials, not final production patch evidence. All preparation and imports
must be counted again after production integration and combined compilation.

The metric extension supports generic pseudometric spaces and lies outside the
original real normed-space completeness statement. Its classification and
bounded-search limits need separate reporting. The 906-file follow-up discovery
also has a different tactic/extractor version from the original 8,637-file census;
it cannot replace that census's denominator or silently improve its coverage.

The current expanded milestone saves 157 net lines but is untimed. The preserved
41-line study's 1.105× ratio belongs to its own frozen implementation and ten-file
workload. A paper may report these as separately labelled studies, or freeze and
measure the final expanded workload. It must not present 157 lines and 1.105× as
one matched experiment. A new paper bundle, source-cost table, and portable build
audit are required if the paper changes; the existing bundle remains unchanged.
