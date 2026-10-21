# Human review of combined selection 05

I reviewed the 53 selected replacements in 32 files for proof clarity and
preparation risks. This is a source review of the selected manifest, not a new
compiler or timing result. The manifest hash and a representative source span
are recorded in `human-review-05.json`. Combined verification remains separate.

No proof-clarity blocker or clearly dead preparation was found. The replacements
retain bounds that use the surrounding mathematical argument. Sum estimates,
operator-norm bounds, scalar-product monotonicity, and local-radius conversions
remain explicit. The tactic then closes a finite comparison. This supports the
description “shorter proof fragments with preparation counted”; it does not
support describing every replacement as a one-line proof of its whole theorem.

The main points for the final compiler review are:

- Some prepared facts are consumed through automatic local-fact selection.
  Examples are `hp` and `hq` in `manual-lprojection-product`, the scaled bounds
  in the four Akra–Bazzi fragments, and `hsum` in `manual-strong-law-sums`.
  Their names need not occur in the final tactic text to be used. Compiler
  diagnostics and the checked proof, rather than textual name counts, determine
  whether preparation is unused.
- `manual-uniform-upper` retains `hδδ` while passing an explicit norm-fact list.
  This matches the API: explicit lists control norm facts while local scalar
  comparisons remain available. A report should not describe that list as the
  complete set of scalar premises.
- The exponential and logarithmic estimates explicitly retain nonlinear scalar
  steps using `mul_le_mul`, `linarith`, or `nlinarith`. The expanded norm tactic
  does not acquire a general nonlinear decision procedure from these examples.
- The Arzelà–Ascoli fragment has visible radius normalization, a discrete-image
  equality, and four applied distance bounds. All seven replacement lines count.
  It uses a generic pseudometric space and demonstrates the metric extension.
- The CompleteCopy metric-instance fragment first unfolds the new distance and
  rewrites absolute differences as real distances. The tactic then uses already
  existing ambient and real metric structures. It does not invoke the triangle
  axiom of the instance under construction.
- The zero-saving PiNat approximation variant is excluded. Only its shorter
  surjectivity estimate is selected, preserving the existing approximation proof.

Useful scenario labels for the eventual report are below. They describe proof
work, and are not disjoint statistical categories.

| Scenario | Selected examples | What remains explicit |
| --- | --- | --- |
| Telescoping norm differences | FDeriv Measurable, operator estimates | Existing endpoint bounds |
| Restricted quantified estimates | `quantified-fderiv-map` | `simp only [map_sub]`; membership premises come from the existing context |
| Sum and scalar normalization | Analytic partial sums, Strong Law, ControlledClosure | Finite/infinite-sum bounds and homogeneity |
| Real absolute-value comparisons | Akra–Bazzi bounds | Product monotonicity with known signs |
| Nonlinear preparation followed by a norm comparison | Exp, Complex LogBounds | Quadratic/product bounds |
| Generic metric chains | Arzelà–Ascoli, bounded continuous limits, closed balls | Applied continuity, boundedness, or membership facts |
| Metric and coordinate-norm estimates | Kuratowski embedding | The coordinate norm bound |
| A metric construction reduced to existing metrics | CompleteCopy in MetricSpace/Polish | Unfolding its distance definition |

`representative-example-05.md` shows the complete Strong Law before/after source
fragment with all preparation and the added import accounted for. It separates
the analytic bound from the algebraic step that `norm_arith` discharges.
