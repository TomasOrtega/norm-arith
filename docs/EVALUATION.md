# Evaluating mathlib replacements

The comparison is existing mathlib proofs versus `norm_arith` replacements at a
pinned revision. Alternate manual proofs and other tactics are not evaluation
baselines. This measures improvements to the existing library without claiming
an advantage over every available proof technique.

## Candidate selection

The pilot uses explicitly supplied norm bounds and upper-bound goals of the form
`‖v‖ ≤ B`. Additive arguments must not require a real vector-space structure.
Short preparation steps are allowed and counted; broader goal forms and
automatic context search are deferred until examples justify them.

Begin with `Analysis/Convex/Uniform.lean` and
`Analysis/Calculus/FDeriv/Measurable.lean`, then expand through a documented
mathlib search. Record attempted candidates, including unsupported cases,
unsuccessful attempts, and replacements that offer no benefit. Freeze the final
evaluation set before collecting headline measurements and publish the outcomes
alongside successful replacements.

## Proof-line reduction

Count nonblank, noncomment proof lines using normal mathlib formatting. Include
preparation steps and subtract added helper proofs and setup from the savings;
charge shared additions once. Keep theorem statements and assumptions unchanged.
Report the tactic's implementation size separately. Proof-line reduction is not
a claim of net repository line reduction.

## Affected-file compilation

Compare the original files with their original imports against the replacement
files with their actual imports. Compile the same affected-file set in each
variant, including files whose compilation becomes slower. Each measured run
must actually compile those files; a cached build that performs no compilation
does not qualify.

When the replacement invokes `norm_arith`, the measured compilation includes
its search and proof construction.

Use repeated runs with matching dependency-cache conditions and report
variability. The aggregate speedup is total baseline compilation time divided by
total replacement compilation time for the same files. Preserve the individual
measurements and report tactic build/setup costs separately. Individual proof
timings are supplementary evidence, not a whole-file compilation claim.

## Reporting

Report the pinned revision, candidate and replacement counts, proof lines before
and after, net proof-line reduction, and affected-file compilation times and
ratio. Report regressions as well as improvements. Describe an unmerged patch as
proposed savings; claim accepted mathlib savings only after the changes merge.

The first frozen evaluation has five verified replacements across three files.
See [the results](../benchmarks/RESULTS.md) for line counts, compilation timings,
raw evidence, and reproduction instructions.
