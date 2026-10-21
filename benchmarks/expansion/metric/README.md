# Generic metric expansion

The frozen scratch extension proves real comparisons from distance nonnegativity,
symmetry, and triangle inequalities. It uses at most eight syntactically collected
points and Lean's checked `linarith` backend. It does not claim complete metric
arithmetic, nonlinear arithmetic, or new timing results.

`production-v2.json` contains nine proposed edits in seven Mathlib files. Exact
copied files compiled with the frozen scratch extension, with fresh nonempty
compiler outputs and no warnings. They replace 61 proof-code lines with 30,
including all preparation. Seven imports give 24 net lines saved when this set
stands alone. The two PiNat edits are useful together; one alone saves no proof
lines after its preparation. Imports shared with a larger patch must be counted
only once.

The production manifest changes the checked `metric_arith` spelling to
`norm_arith` and imports `NormArith`. Those substitutions still require combined
whole-source verification against the integrated production implementation.
`scratch-confirmed-v2.json` preserves the exact tested source strings;
`scratch-confirmed-v2-accounting.json` preserves their accounting. Earlier v1
snapshots remain unchanged.

Production verification 05 rejected `metric-bounded-closed-ball` and
`metric-diameter-closed-ball` before compilation: `NormArith` already imports
`Mathlib/Topology/MetricSpace/Bounded.lean`, so adding `import NormArith` to that
file creates an import cycle. The narrower scratch import did not expose this
dependency. These two candidates are excluded through
`artifacts/expansion/source-exclusions-05.json`; their scratch proofs remain valid,
but they contribute no production savings. The immutable v2 snapshots retain the
original proposal set. Final production accounting belongs to the reselected,
combined verified patch.

Production compilation 06 also rejected `metric-contracting-tail` in
`Mathlib/Topology/MetricSpace/Contracting.lean`. Its target contains the variable
coefficient product `K * dist x y`, outside the production metric frontend's
affine comparison fragment. The scratch prototype accepted a broader set of
real comparisons, so its successful trial did not establish production support.
`artifacts/expansion/source-exclusions-06.json` and `combined-06-failure.json`
preserve the exclusion and compiler diagnostic. This candidate contributes no
production savings. No preparation variant or frontend change is proposed.

The source engine is preserved in `MetricPrototype.snapshot.lean` (SHA256
`40009e0bd5191be3c2f8fa34989158d3335f29b11b02621757a18fc6efea7210`).
Its namespace engine matches the root prototype byte for byte. The copy adds
Lean module/public export declarations and omits its standalone examples.
The compiled scratch module lives in `.lake/metric-expansion-prototype-v2`.

`trial.py` preserves original census build options, adds explicit scratch import
artifacts, and compiles complete copied modules. It does not register or rebuild a
production Lake module, and does not establish native-runtime equivalence.
`confirmed.py` checks source identity, compiler artifact hashes, nonempty outputs,
and diagnostics before including a file. Existing Mathlib sources stay untouched.

`reviewed.json` records discovery queries, unsuccessful sites, and every trial
report. Three proposed spans in two other files remain failed and are excluded.
Trial 01 failed module packaging. Trials 02–09 include failed proof variants;
trial 04 repeated the prior manifest after manifest generation failed. Successful
current sources come from trials 05, 06, and 10. Preparation for local scalar
definitions and vector/coercion aliases is charged explicitly. No unsuccessful
attempt is classified as a proof of unsupported mathematics.

Regenerate the mutable proposal inventory with `python3
benchmarks/expansion/metric/prepare.py`. Run a new scratch trial with `python3
benchmarks/expansion/metric/trial.py --output .lake/NEW-DIRECTORY`; the output
directory must not already exist. Immutable production snapshots do not change
when the mutable inventory changes.
