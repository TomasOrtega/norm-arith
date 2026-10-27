# Results

## Workloads and accounting

The feature branch has two separate workloads:

- **20 mathlib-derived pairs** compare original standalone proof blocks with the
  public tactic. Eight are complete theorem copies, nine are extracted local
  blocks, and three are explicit adaptations. All are pinned and attributed in
  [the manifest](../Benchmarks/manifest.json).
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
The next performance work is profiling search and proof reconstruction, followed
by larger workloads selected before measurement. No tuning was performed on the
measured implementation after observing these results.

## Measurements

The checked-in benchmark reports contain the actual timing results and all
samples: [mathlib snippets](../Benchmarks/results.md),
[raw snippet data](../Benchmarks/results.json),
[backend comparison](../Benchmarks/backend_results.md), and
[raw backend data](../Benchmarks/backend_results.json).

Each report uses five recorded pairs after one warmup pass. Each sample launches
Lean afresh with new output files. Compilation order alternates. Times include
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
python3 scripts/benchmark_snippets.py --pairs 5 --warmups 1
python3 scripts/benchmark_snippets.py --manifest Benchmarks/backends.json \
  --pairs 5 --warmups 1 --output Benchmarks/backend_results.json
```

The implementation measured here is
[`0e35741a42c721537674a0a1c8bd9334f787c70d`](https://github.com/TomasOrtega/norm-arith/commit/0e35741a42c721537674a0a1c8bd9334f787c70d),
with Lean 4.36.0-rc1 and the pinned mathlib revision. Both reports' implementation
and snippet hashes were checked against the final source files. Documentation
and report additions after that commit do not change the measured Lean code.

Record hardware, toolchain, source revision, and all samples when comparing runs.
The JSON includes the implementation and snippet hashes so later changes can be
distinguished from measurement noise.
