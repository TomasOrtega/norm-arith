# Expanded Mathlib patch: 310 net code lines saved

**Combined source verification, independent accounting, and confirmatory timing: PASSED.**
The local patch saves **310 net code lines** across **87 replacements in 46 files**.
Every affected file compiled with fresh outputs; an independent audit rechecked
the literal patch and all **322 compilation artifacts**. Warm compilation of all
affected files is **1.072× faster**, with a conditional 95% interval of
**1.067–1.081×**. The patch has not merged into Mathlib.

The study retains Lean `4.36.0-rc1` and Mathlib revision
`2f3c7c8a8949b04a32f9303f59163acffb766996`.

## Verified source accounting

| Quantity | Verified selection 09 |
| --- | ---: |
| Disjoint replacements | 87 |
| Affected files | 46 |
| Original proof code lines | 582 |
| Replacement proof code lines, including preparation | 226 |
| Proof code lines saved | 356 |
| Added import code lines | 46 |
| Added helper code lines | 0 |
| **Net code lines saved** | **310** |

Counts exclude blank lines and comments. Every preparatory bound, normalization,
and continuation line counts; each file import is charged once. Source guards
preserve statements and all source outside the recorded proof-body edits.
The longest replacement line has 99 Unicode characters, within the fixed
100-character formatting limit.
Selection uses line savings rather than timing. Overlapping, duplicate,
non-saving, import-offset, and failed candidates remain in the selection ledger.
Two cyclic imports and one combined-source failure are explicitly
[excluded](../../artifacts/expansion/source-exclusions-final.json).

Implementation cost is separate: **850 tactic code lines** and **470 census code
lines**, with [source hashes](../../artifacts/expansion/implementation-costs-v4.json).
These are implementation totals, not additional Mathlib proof savings or a
whole-repository line reduction.

The preserved [manifest](verified-05/manifest.json), [patch](verified-05/mathlib.patch),
[verification receipt](verified-05/verification-receipt.json), and
[independent audit](verified-05/independent-audit.json) bind the selected edits,
frozen project sources, original and changed files, and compilation evidence.
The earlier [232-line](verified-03/manifest.json) and
[304-line](verified-04/manifest.json) milestones remain preserved.

## Search scope and capabilities

The latest targeted scan processed 885 files selected from the earlier census:
875 completed and 10 remain incomplete. Its frozen-input integrity check passed.
It produced 158 isolated kernel-checked proposals. Selected proposals and
reviewed manual candidates then passed separate combined whole-file verification.
The final patch contains 50 census-generated replacements and 37 composed outside
the census with assistance from AI coding agents. Some of the latter need only
explicit facts, without extra preparation.
These sources do not establish all possible uses across Mathlib.
The [targeted archive receipt](../../artifacts/expansion/discovery-v4-archive/archive.json)
binds outcomes and raw observations, including incomplete files. Complete raw
discovery and intermediate verification archives remain local and Git-ignored.
Tracked receipts and inventories identify them; see
[evidence packaging](../../docs/CENSUS-ARCHIVE.md).

The expanded tactic projects conjunctions and supplies real norm and min/max
order bounds. Bounded specialization matches local quantified norm estimates to
observed vectors and checks their premises. It permits 12 templates, 12 binders,
32 observed vectors, 32 new bounds, and 128 attempts with at most 8 patterns each.
Explicit fact lists still control norm and distance premises.

A separate pseudometric extension checks distance nonnegativity, symmetry,
self-distance, and triangle constraints on at most 8 observed points. Failed
metric attempts restore state before the norm pipeline continues. The
[regression receipt](../../artifacts/expansion/next/production-regressions/receipt.json)
retains source snapshots and build evidence. These bounded extensions leave the
paper's quantifier-free real-core theorem unchanged.

Finite-sum estimates, operator bounds, variable-coefficient monotonicity, and
nonlinear scalar steps can remain explicit preparation. The tactic does not
prove analytic convergence hypotheses or provide a general nonlinear decision
procedure. The [Strong Law example](../../artifacts/expansion/representative-example-07.md)
shows all preparation: 20 proof code lines become five, before charging its import.
The [earlier source review](../../artifacts/expansion/human-review-07.md) covers
the 74-fragment milestone; the
[tactic and preparation review](../../artifacts/expansion/next/final-source-review.md)
covers the implementation changes and ten further preparation candidates. The
[final patch review](../../artifacts/expansion/next/final-patch-clarity-review.md)
checks the additions and revisions in the 87-replacement patch. These clarity
reviews are separate from compilation and independent accounting.

## Confirmatory warm compilation result

The [predeclared protocol](../../artifacts/expansion/expanded-study-protocol.md)
compares the existing proofs with the complete 46-file replacement patch.
The code, native artifacts, selection, and analysis rules were frozen before the
pilot. A speed-level-blinded 24-pair pilot review retained the predeclared
four-pair blocks and fixed 40-pair confirmation. The pilot was not pooled with
confirmation. All files and samples remain in the analysis.

| Quantity | Final expanded study |
| --- | ---: |
| Original mean total seconds per 46-file pass | 131.188455 |
| Replacement mean total seconds per 46-file pass | 122.333093 |
| Mean-total ratio, original / replacement | **1.072387×** |
| Conditional paired 95% block BCa interval | **1.066942–1.081410×** |
| Compiler time reduction | 6.750% |
| Measured paired passes | 40 |
| Blocks / adjacent paired passes per block | 10 / 4 |
| Bootstrap draws / seed | 10,000 / 20261020 |
| Descriptively faster / slower files by mean | 39 / 7 |

The lower interval endpoint exceeds one, satisfying the fixed success criterion.
[Independent recomputation](study-final/independent-statistics.json) agrees with
the raw samples and frozen analysis. The
[actual-byte audit](study-final/timed-output-byte-audit.json) rehashed all
**42,504 fresh outputs** across pilot and confirmation, plus frozen source,
compiler, import, setup, and native-library inputs. Every compiler call has unique
output paths and a successful process receipt. Source and runtime inventories
matched throughout both runs.

Each repetition compiles the whole file with cached dependencies and one Lean
thread, using actual variant headers, original Lake build options, dependency
order, and alternating original/replacement passes. Import loading, tactic search,
proof construction, kernel checking, serialization, IR, and C generation are
inside compiler time. Native C object compilation, Lake dispatch, source-header
setup, and Python bookkeeping are excluded. Each run records 100 setup
subprocesses; no cold native-build cost was measured.

The native imports differ between variants. The replacement import can load
Mathlib and tactic native libraries for unchanged tactics, so the measured ratio
includes that runtime configuration. It is an affected-file compilation result,
not a full Mathlib build result or an isolated algorithm comparison.

The BCa interval assumes independent representative blocks. The pilot showed
nonzero differential drift, and calibration does not prove independence or cure
nonstationarity. The recorded power snapshots showed AC power and low-power mode
zero, but the battery changed from 80% AC-attached before sampling to 41% and
discharging afterward. Thermal-status queries were unavailable. These snapshots
do not establish continuous power or stable thermal conditions. Ordinary
background activity was uncontrolled.

The [study transport and restoration instructions](study-final/README.md) retain
exact reports, raw times, frozen plans, all calibration versions and decision
receipts, implementation sources, independent checkers, and power metadata.
Complete raw compiler outputs and logs are also archived locally; their tracked
byte index and archive receipt identify every file.

### Per-file results

These are descriptive arithmetic means over all 40 measured calls per variant.
Positive time changes are slowdowns; they remain included in the aggregate.
Per-file ratios have no separate confidence claim.

| File | Original mean s | Replacement mean s | Original / replacement | Time change |
| --- | ---: | ---: | ---: | ---: |
| `Analysis/Normed/Module/Multilinear/Basic.lean` | 8.264 | 7.739 | 1.068× | -6.3% |
| `Analysis/Normed/Order/Lattice.lean` | 1.320 | 1.340 | 0.985× | +1.5% |
| `Analysis/Analytic/Basic.lean` | 5.114 | 4.555 | 1.123× | -10.9% |
| `Analysis/Asymptotics/AsymptoticEquivalent.lean` | 1.906 | 1.711 | 1.114× | -10.3% |
| `Analysis/SpecialFunctions/Exp.lean` | 1.949 | 1.678 | 1.161× | -13.9% |
| `Analysis/Asymptotics/SpecificAsymptotics.lean` | 1.659 | 1.538 | 1.079× | -7.3% |
| `Analysis/Calculus/FDeriv/Basic.lean` | 3.283 | 2.890 | 1.136× | -12.0% |
| `Topology/MetricSpace/Gluing.lean` | 1.804 | 1.744 | 1.035× | -3.4% |
| `Analysis/Normed/Operator/Banach.lean` | 3.972 | 3.881 | 1.023× | -2.3% |
| `Topology/MetricSpace/PiNat.lean` | 2.825 | 2.526 | 1.118× | -10.6% |
| `Topology/MetricSpace/Polish.lean` | 1.313 | 1.552 | 0.846× | +18.3% |
| `MeasureTheory/Function/L1Space/Integrable.lean` | 4.264 | 3.632 | 1.174× | -14.8% |
| `MeasureTheory/Integral/FinMeasAdditive.lean` | 3.182 | 2.854 | 1.115× | -10.3% |
| `Topology/Bornology/BoundedOperation.lean` | 1.279 | 1.206 | 1.061× | -5.7% |
| `Topology/ContinuousMap/Bounded/Basic.lean` | 2.578 | 2.325 | 1.109× | -9.8% |
| `Topology/ContinuousMap/Bounded/Normed.lean` | 3.469 | 3.188 | 1.088× | -8.1% |
| `MeasureTheory/Integral/DominatedConvergence.lean` | 2.912 | 2.511 | 1.160× | -13.8% |
| `Analysis/Calculus/BumpFunction/FiniteDimension.lean` | 3.036 | 2.715 | 1.118× | -10.6% |
| `Analysis/Calculus/FDeriv/Measurable.lean` | 4.400 | 4.185 | 1.051× | -4.9% |
| `Analysis/Convex/Uniform.lean` | 1.288 | 1.738 | 0.741× | +34.9% |
| `Analysis/Complex/OpenMapping.lean` | 2.170 | 2.014 | 1.078× | -7.2% |
| `Analysis/Fourier/RiemannLebesgueLemma.lean` | 2.260 | 2.180 | 1.036× | -3.5% |
| `Analysis/LocallyConvex/Polar.lean` | 1.726 | 1.651 | 1.045× | -4.3% |
| `Analysis/Normed/Algebra/Spectrum.lean` | 4.085 | 3.723 | 1.097× | -8.9% |
| `Analysis/Normed/Algebra/Unitization.lean` | 2.629 | 2.586 | 1.016× | -1.6% |
| `Analysis/Normed/Field/Approximation.lean` | 1.585 | 1.571 | 1.009× | -0.8% |
| `Analysis/Normed/Group/ControlledClosure.lean` | 1.235 | 1.275 | 0.969× | +3.2% |
| `Analysis/Normed/Module/MStructure.lean` | 1.549 | 1.663 | 0.931× | +7.4% |
| `MeasureTheory/Covering/BesicovitchVectorSpace.lean` | 2.594 | 2.452 | 1.058× | -5.5% |
| `MeasureTheory/Function/Jacobian.lean` | 4.147 | 3.669 | 1.130× | -11.5% |
| `Analysis/SpecialFunctions/Complex/LogBounds.lean` | 3.207 | 2.995 | 1.071× | -6.6% |
| `Analysis/SpecialFunctions/Elliptic/Weierstrass.lean` | 9.987 | 9.200 | 1.086× | -7.9% |
| `Analysis/SpecialFunctions/FrullaniIntegral.lean` | 1.978 | 1.831 | 1.081× | -7.5% |
| `Computability/AkraBazzi/GrowsPolynomially.lean` | 3.483 | 3.128 | 1.114× | -10.2% |
| `MeasureTheory/Constructions/HaarToSphere.lean` | 2.572 | 2.544 | 1.011× | -1.1% |
| `MeasureTheory/Function/AEEqOfIntegral.lean` | 1.933 | 1.771 | 1.092× | -8.4% |
| `MeasureTheory/Function/ConvergenceInDistribution.lean` | 2.140 | 1.951 | 1.097× | -8.8% |
| `MeasureTheory/Integral/PeakFunction.lean` | 2.574 | 2.353 | 1.094× | -8.6% |
| `MeasureTheory/Measure/IntegralCharFun.lean` | 1.766 | 1.618 | 1.092× | -8.4% |
| `MeasureTheory/Measure/SeparableMeasure.lean` | 2.237 | 2.191 | 1.021× | -2.0% |
| `NumberTheory/Padics/PadicNumbers.lean` | 3.785 | 3.381 | 1.119× | -10.7% |
| `Probability/StrongLaw.lean` | 3.850 | 3.441 | 1.119× | -10.6% |
| `Topology/ContinuousMap/Bounded/ArzelaAscoli.lean` | 1.117 | 1.273 | 0.878× | +14.0% |
| `Topology/MetricSpace/GromovHausdorffRealized.lean` | 2.208 | 2.007 | 1.100× | -9.1% |
| `Topology/MetricSpace/Kuratowski.lean` | 1.302 | 1.346 | 0.967× | +3.4% |
| `Topology/MetricSpace/GromovHausdorff.lean` | 3.251 | 3.012 | 1.079× | -7.3% |

## Historical study

The [original result](../FINAL-RESULTS.md) saves **41 net lines** in 16 replacements
across 10 files. Its 40-pair study measured **1.105×** warm affected-file speedup
with a conditional 95% interval of **1.095–1.112×**. That result applies only to
its frozen implementation and workload. The
[historical paper and portable evidence](../../artifacts/paper-baseline-41line/README.md)
remain preserved separately.
