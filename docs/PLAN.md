# Implementation plan

This is the completed prototype plan. The current research implementation follows
[PAPER-PLAN.md](PAPER-PLAN.md), which requires a broader tactic, a semantic census,
and a verified compilation speedup over existing mathlib proofs.

Build a useful norm-arithmetic tactic and a reproducible mathlib replacement
patch. Proof simplification is the primary goal; compilation speed is measured
and reported even when it regresses.

The initial implementation and evaluation are complete. See
[the measured results](../benchmarks/RESULTS.md) and the reproducible local patch.

## Initial scope

- Explicit source bounds: `norm_arith [h₁, ..., hₙ]`.
- Upper-bound goals of the form `‖v‖ ≤ B`, with counted preparation steps.
- Additive norm arguments without assuming a real vector-space structure.
- Retain rational-real scalar support and Lean-checked certificates.
- Add capabilities as actual mathlib examples justify them; Isabelle feature
  parity is not the initial milestone.

See [the scope decision](adr/0002-initial-tactic-fragment.md).

## Work sequence

1. Establish a reproducible baseline using the repository's pinned Lean and
   mathlib revisions. Verify the build and existing tests before treating the
   starter's validation claims as evidence.
2. Inventory candidate proof blocks in `Analysis/Convex/Uniform.lean` and
   `Analysis/Calculus/FDeriv/Measurable.lean`. Record their original source,
   theorem, assumptions, and outcome. The two telescoping blocks in the
   `FDerivMeasurableAux` and `RightDerivMeasurableAux` namespaces are promising
   first candidates, not established replacements.
3. Add regression examples for additive proofs without a real vector-space
   instance, confirm the current limitation, and implement additive certificate
   construction. Preserve the existing rational-real examples and failure tests.
4. Compile useful pilot replacements without changing theorem statements or
   assumptions. Expand through a documented mathlib search, retaining a record
   of failures and replacements with no benefit. Freeze the final evaluation
   set before collecting headline results.
5. Count net proof-line reduction and repeatedly compile the full affected files
   in the original and replacement variants. Preserve actual imports, include
   regressions, and report variability and tactic setup costs.
6. Deliver the local replacement patch, candidate manifest, reproduction commands,
   raw measurements, and a report with claims limited to the evidence obtained.

## Evaluation and claims

Compare existing mathlib proofs only with the `norm_arith` replacements. Count
nonblank, noncomment proof lines, charge added helper proofs and setup, and
report tactic implementation size separately. Measure compilation speed as total
baseline time divided by total replacement time over the same affected files.
When a replacement invokes `norm_arith`, its search and proof construction are
part of the measured compilation.

Follow [EVALUATION.md](EVALUATION.md) for the measurement rules. Describe line
savings as proposed until the patch merges upstream; do not infer mathlib-wide
compilation gains from affected-file measurements.
