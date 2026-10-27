# Progress

This page describes the implemented feature branch. The larger proposal lives in
[roadmap.md](roadmap.md); a design in that document is not automatically an
implemented feature.

## Working and checked

| Area | Current implementation | Evidence |
| --- | --- | --- |
| Independent package | Pinned mathlib dependency; no mathlib patches; core and optional analysis imports | `lakefile.toml`, public modules |
| Rational norm arithmetic | Existing structural, short-search, metric, and finite-reference paths retained | Core, Expansion, Metric, Tactic tests |
| Compact LP | Typed support blocks, exact sparse simplex, strict/equality branches, rational extraction, checked reconstruction | LP tests, including forced backend calls |
| Backend controls | `norm_arith.useLP`, `norm_arith.forceLP`, `trace.norm_arith.lp` | LP tests and synthetic benchmark pairs |
| Explicit seminorms | Triangle, reverse triangle, homogeneity, multiple seminorms, supplied comparison bounds | Seminorm tests |
| Analytic frontend | Structural facts, linear/bilinear operator bounds, bilinear perturbations, scalar finishing | Analysis tests |
| Analytic templates | Young, energy absorption, coupled bounds, elliptic scalar absorption, quadratic ball/contraction estimates | Analysis lemmas and direct tactic examples |
| Function-space bridges | Finite `eLpNorm`/`lpNorm` conversion, raw-function triangle, bundled Hölder examples | Analysis tests with explicit membership/exponent assumptions |
| Real-source benchmarks | 20 paired standalone mathlib snippets, provenance, matching statements, accounting | `Benchmarks/manifest.json` and both proof directories |
| Isolated backend workload | Five synthetic reference-versus-LP pairs, separate from source savings | `Benchmarks/backends.json` |
| Measurement infrastructure | Fresh outputs, warmups, alternating order, retained failures and samples | Python runner and accounting tests |
| Documentation | Brief README plus mathematics, proofs, design, results, history, full roadmap | This directory |

The central build checks ten regression modules containing 146 `example`
declarations, 55 `#guard` assertions, and 34 expected-failure checks. Those counts
describe source constructs, not independent mathematical coverage percentages.
The new analytic/seminorm modules contribute 29 examples, including five expected
rejections. The LP module includes direct encoder/oracle tests and forced frontend
tests so a successful fallback cannot hide a broken LP integration.

## Verification snapshot (27 October 2026)

- `lake build --wfail NormArith NormArithTest` completed successfully.
- All ten Python benchmark-accounting tests passed.
- All 240 mathlib-snippet and 60 backend timing samples compiled successfully.
- A separate temporary Lake project fetched the published Git package and
  compiled all three README examples with the core and analytic imports.
- The clean GitHub [CI run for the measured implementation](https://github.com/TomasOrtega/norm-arith/actions/runs/40534845298)
  passed its build, regression, accounting, snippet, and README checks.

The measured Lean implementation is commit
`0e35741a42c721537674a0a1c8bd9334f787c70d`. Subsequent report, documentation, and
consumer-check changes do not alter those Lean sources. Raw reports retain
the source hashes. CI also checks the synthetic backends and downstream Git
consumer on future runs.

## Explicit limits

The LP defaults bound observations to 48, vector atoms to 64, support rows to
6000, and scalar/function variable slots to 4096. Lean's heartbeat limit also
applies. These are implementation budgets, not mathematical restrictions on the
semantic reduction. Search failure means unknown.

Explicit seminorm automation uses bounded structural facts; it is not yet an
exact multiple-seminorm LP frontend. Analytic automation uses a fixed set of
templates and scalar tactics. It does not discover the analytic hypotheses of
a PDE theorem. The current quadratic templates establish estimates, not a
fixed-point existence theorem. The full semantic realization argument is written
out in Markdown; only certificate reconstruction and its applications are
machine-checked here.

## Next milestones

| Priority | Work | Completion criterion |
| --- | --- | --- |
| 1 | Evaluate and tune LP scheduling | More source workloads; sparse and dense stress cases; measure proof reconstruction separately from search |
| 2 | Shared norm/seminorm observation frontend | Exact seminorm blocks with common vector relations; expected-failure coverage for incompatible norm assumptions |
| 3 | Analytic rule registration and search | Explicit side-condition obligations, bounded composition, reproducible proof explanations |
| 4 | Hölder and interpolation exponent planning | Exact rational witness search; theorem-backed endpoint and membership checks |
| 5 | Mixed-norm and integral adapters | Correct norm order, measurability and finiteness; genuine function-space benchmark examples |
| 6 | Larger PDE estimate blocks | Formal analytic premises and checked elliptic/fixed-point applications, with measured surrounding proof costs |
| 7 | Optional Hilbert quadratic certificates | Rational Gram/PSD certificates, checked independently of LP search |
| 8 | Formal semantic completeness and countermodels | Lean realization theorem and verified model extraction; distinguish relaxation witnesses from genuine counterexamples |
| Later | mathlib contribution | API/dependency review and agreement on upstream scope; no port is underway on this branch |

The aim is fewer routine proof lines with predictable checking costs. A feature
is promoted from the roadmap only after its actual API and examples compile.
Runtime claims belong on the [results page](results.md), with the corresponding
raw data and workload definition.
