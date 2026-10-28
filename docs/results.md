# Results

## Current mathlib corpus

The corpus contains **65 paired snippets** from 49 mathlib modules: 48 complete
theorem copies, 14 extracted blocks, and three adapted estimates. The latest
24 additions contribute 20 complete theorems and four extracted blocks from
24 previously unused source modules. Statements, baseline proofs, source spans,
and attribution are recorded in [the manifest](../Benchmarks/manifest.json).

New coverage includes asymptotics, Gaussian integrals, Weierstrass estimates,
derivative slopes, multilinear composition, tensor products, completion,
dominated convergence for series, characteristic functions, contractions,
Gromov products, metric gluing, and the Kuratowski embedding.

Proof bodies decrease from **460 to 360 lines**, and whole snippets from
**923 to 888 lines**, including imports and preparation: 100 proof lines and
35 net code lines saved. Longer tactic replacements remain in the corpus.
All **130 files compile with warnings treated as errors**. This expansion was
checked for correctness; the repeated timing reports below cover the earlier
20-case and 41-case subsets, not the full 65-case corpus.

## Measured 41-case expansion

This measured workload contains **41 paired snippets** from 25 source modules:
28 complete theorem copies, 10 extracted local blocks, and three adapted
estimates. The 21 additions include 20 complete theorems and one pointwise
estimate for normed group homomorphisms. They retain the pinned source statements,
baseline proofs, and attribution in
[the frozen manifest](../Benchmarks/expanded-41.json).

The new cases cover normed rings, affine spaces, bounded linear maps, convexity,
circle maps, Gaussian cutoffs, logarithmic series and infinite products, metric
chains and balls, and dominated finitely additive maps. Short source proofs and
cases with longer tactic replacements are included.

Across all 41 cases, proof bodies decrease from **235 to 143 lines** and whole
snippets from **512 to 461 lines**, including the extra tactic import in each
pair. These are 92 proof lines and 51 net code lines saved. The additions broaden
coverage; their aggregate whole-snippet cost is five lines larger than their
baselines.

All **328 compilations passed**: one warmup and three measured passes of both
variants. Median corpus totals are **106.918 s baseline** and **119.564 s tactic**,
or 11.8% slower with the tactic. These descriptive measurements use the
`fefd724` implementation and the expanded benchmark sources; recorded hashes
match the files checked after the run.

The expanded measurements are stored separately in
[the report](../Benchmarks/expanded-results.md) and
[raw samples](../Benchmarks/expanded-results.json). The original 20-case report
and its measurements below are preserved.

## Roadmap implementation

The roadmap measurements use implementation `cd9083f` and the unchanged Lean and
mathlib pins. Source hashes are stored with every report. The timings below are
small descriptive samples, not a general speed claim.

### Analytic composition

All 40 compilations passed: five pairs, one warmup, and three measured runs.
Proof bodies decrease from 44 to 5 lines. Whole snippets decrease from 94 to 55
lines, including imports, assumptions, and local exponent instances.
The [report](../Benchmarks/analytic-results.md) and
[raw samples](../Benchmarks/analytic-results.json) contain every case.

| Case | Manual compile | Tactic compile | Proof lines, manual → tactic |
| --- | ---: | ---: | ---: |
| Interpolation, held out | 2.940 s | 2.895 s | 7 → 1 |
| Product | 2.986 s | 3.553 s | 17 → 1 |
| Elliptic | 2.981 s | 2.964 s | 10 → 1 |
| Mixed norms, held out | 3.048 s | 5.982 s | 3 → 1 |
| Fixed point | 2.870 s | 2.977 s | 7 → 1 |

The median corpus totals are 14.836 s manually and 18.356 s with the tactics:
**23.7% slower overall**. The mixed-norm case is about twice as slow. It remains
in the report, and no rules were tuned on these held-out results.

The 39 saved lines are savings per use after shared primitive lemmas are
available. They are not a net reduction in repository code. The reusable
`Parameters`, `FunctionSpace`, and `FixedPoint` modules contain 67, 223, and 143
code lines respectively: 433 total. The `NormArith/` implementation grew from 1,455
to 2,801 code lines, excluding blanks and comments. That total includes the
realization proofs, rule infrastructure, and replay checker. These costs must
remain visible when deciding how many uses justify an adapter.

### Core phases and replay

Two cases compare the reference backend, forced LP, and saved proof replay.
Each variant has one warmup and three measured samples in fresh processes.
All 24 samples and both replay captures passed. The source did not change during
the run. The [raw report](../artifacts/core-profile/results.json) contains the
samples, memory counters, proof data sizes, and source hashes.

| Case | Reference compile | LP compile | Replay compile | LP search | Reconstruction |
| --- | ---: | ---: | ---: | ---: | ---: |
| RationalChain4 | 2.628 s | 2.667 s | 2.476 s | 8.263 ms | 115.448 ms |
| CoupledErrors | 2.621 s | 2.555 s | 2.467 s | 12.914 ms | 50.536 ms |

Values are medians. Reconstruction includes vector proofs and the final scalar
proof. Whole compilation includes process startup, imports, checking, and output.
Replay includes graph decoding and kernel checking; it does not isolate kernel
time. The LP measurements also include trace and proof-size collection.

| Case | Replay data | Shared graph nodes |
| --- | ---: | ---: |
| RationalChain4 | 93,950 bytes | 6,328 |
| CoupledErrors | 53,561 bytes | 3,545 |

Peak process memory was about 2.37–2.39 GB, including imports and process overhead.
The files contain anonymous examples, so exported `.olean` size is not a useful
measure of their proof size. Stored replay is much larger than a tactic call.
It avoids search; it is not a source-size reduction technique.

Earlier failed trials are retained: [host counter access](../artifacts/core-profile-sandbox-failure/results.json),
[runner and build interference](../artifacts/core-profile-runner-failure/results.json),
[local-name replay](../artifacts/core-profile-replay-failure/results.json), and
[generated-lemma replay](../artifacts/core-profile-auxiliary-failure/results.json).
They are excluded from the table. Their runner and replay defects were fixed and
covered by regression tests before the successful run.

## Earlier workloads and accounting

The original measured implementation has two separate workloads:

- **20 mathlib-derived pairs** compare original standalone proof blocks with the
  public tactic. Eight are complete theorem copies, nine are extracted local
  blocks, and three are explicit adaptations. All are pinned and attributed in
  [the current, expanded manifest](../Benchmarks/manifest.json).
- **Five synthetic backend pairs** compare the retained reference path with a
  forced LP call on identical statements. They are defined in
  [their own manifest](../Benchmarks/backends.json) and make no source-line-saving
  claim about mathlib.

The source workload has **128 baseline proof-body lines and 52 replacement lines**:
76 fewer lines, or 59.4%. Charging one extra tactic import in each standalone file
leaves **56 net code lines saved**. Statements and all local preparation are
included in whole-snippet accounting. The runner checks equality of the paired
statements and rejects direct reuse of the theorem being replaced.

## Measured source and compilation costs

| Metric | Original proofs | Tactic proofs | Change |
| --- | ---: | ---: | --- |
| Proof-body code lines | 128 | 52 | 76 fewer (59.4%) |
| Whole-snippet code lines | 266 | 210 | 56 fewer (21.1%) |
| Median aggregate compilation time | 51.098 s | 57.040 s | Tactic takes 11.6% longer |

The baseline/tactic time ratio is **0.896×**. Nineteen of twenty individual case
medians were slower with the tactic. All **240 compilations succeeded**: 40
warmup compilations and 200 recorded samples. This workload establishes shorter
source with an observed fresh-process compilation cost, not a runtime speedup.

## Isolated backend comparison

The retained reference path took **16.709 s** and forced LP took **16.739 s**
per median aggregate pass, a reference/LP ratio of **0.998×**. All **60 backend
compilations succeeded**, including warmups. No aggregate speedup was observed
on these five cases; the approximately 0.18% difference is not evidence of a
meaningful performance distinction in this small run.

| Synthetic case | Reference median | LP median | Reference / LP |
| --- | ---: | ---: | ---: |
| Four-source rational chain | 3.076 s | 3.159 s | 0.974× |
| Six-source rational chain | 3.292 s | 3.284 s | 1.002× |
| Eight-source rational chain | 3.507 s | 3.647 s | 0.962× |
| Coupled error bounds | 2.938 s | 2.863 s | 1.026× |
| Dense eight-source observations | 3.536 s | 3.684 s | 0.960× |

Aggregate figures are medians of the per-pair totals; individual case medians
need not sum to the aggregate median. The formulation avoids enumerating all
supports, but a compact formulation alone does not establish a runtime benefit.
These baseline reports predate the separate phase and replay measurements above.
No tuning was performed on that measured implementation after observing its
results.

## Measurements

The checked-in benchmark reports contain the actual timing results and all
samples: [mathlib snippets](../Benchmarks/results.md),
[raw snippet data](../Benchmarks/results.json),
[backend comparison](../Benchmarks/backend_results.md), and
[raw backend data](../Benchmarks/backend_results.json).

These original reports use five recorded pairs after one warmup pass. Each sample
launches Lean afresh with new output files. Compilation order alternates. Times include
startup, imports, elaboration, tactic execution, checking, and writing outputs.
Dependencies are already built. The package uses its ordinary default build,
without requesting native precompilation of all mathlib.

The reports retain slow cases and failures. Aggregate timing ratios are withheld
if required recorded compilations fail. Medians are descriptive; uncontrolled
machine load and this small selected workload do not support claims of general
or statistically significant speedup.

## Interpretation

The main corpus measures end-to-end proof replacement. Many examples close in
the tactic's cheap paths, so these timings do not isolate the new LP. The
synthetic workload deliberately tests backend behavior separately, including
larger support sizes and dense observations. It is a diagnostic workload, not
an estimate of how often such goals occur in real PDE formalizations.

Neither corpus measures whole-paper proof reduction, an upstream mathlib patch,
or an entire PDE theorem. Extracted snippets retain their mathematical
hypotheses, but their import/startup balance differs from full source files.
The analytic template tests establish working functionality; their synthetic
one-line proofs are not counted as mathlib source savings.

Earlier full-file census and paper results remain linked from
[history](history.md). They concern different implementations and workloads and
are not combined with this branch's measurements.

## Reproduce

```sh
lake exe cache get
lake build --wfail NormArith NormArithTest
python3 -m unittest discover -s scripts
python3 scripts/benchmark_snippets.py --pairs 3 --warmups 1 \
  --output Benchmarks/results/local/current.json
python3 scripts/benchmark_snippets.py --manifest Benchmarks/backends.json \
  --pairs 5 --warmups 1 --output Benchmarks/backend_results.json
```

The snippet command measures the current mathlib corpus. To reproduce the
41-case expansion, add `--manifest Benchmarks/expanded-41.json`. To select cases
from other earlier reports, pass their identifiers with `--only`.

The original 20-case and backend reports measured implementation
[`0e35741a42c721537674a0a1c8bd9334f787c70d`](https://github.com/TomasOrtega/norm-arith/commit/0e35741a42c721537674a0a1c8bd9334f787c70d),
with Lean 4.36.0-rc1 and the pinned mathlib revision. The stored source hashes
identify that implementation. Later roadmap changes use separate reports and
must not be attributed to these earlier timings.

Record hardware, toolchain, source revision, and all samples when comparing runs.
The JSON includes the implementation and snippet hashes so later changes can be
distinguished from measurement noise.
