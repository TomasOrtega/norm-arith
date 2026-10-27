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

Record hardware, toolchain, source revision, and all samples when comparing runs.
The JSON includes the implementation and snippet hashes so later changes can be
distinguished from measurement noise.
