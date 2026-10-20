# Mathlib replacement results

Five verified local replacements remove **39 proof lines**, or **36 lines after
charging three new imports**, at mathlib revision
`2f3c7c8a8949b04a32f9303f59163acffb766996`. The replaced proof blocks shrink
from 57 nonblank, noncomment lines to 18, including all preparation.
Theorem statements and assumptions are unchanged. These savings are proposed;
the patch has not merged into mathlib.

Compilation is **6.3% slower** in the final run: median total time rises
from 10.757 s to 11.435 s, a before/after ratio of
0.941×. This result does not support a compilation-speedup claim.

## Compilation measurements

The final run uses Lean 4.36.0-rc1 on macOS arm64 with one Lean thread, cached
dependencies, one unmeasured warmup per variant, and ten measured pairs.
Original-first and replacement-first order alternate. Each measurement compiles
a complete file to fresh Lean artifacts and C, using its actual imports and
Lake library options. Search and proof construction are included; native C
object compilation and Lake dispatch are excluded. No samples were discarded.

| File | Existing median (s) | Replacement median (s) | Before / after |
| --- | ---: | ---: | ---: |
| Convex/Uniform.lean | 1.295 | 1.552 | 0.835× |
| Calculus/FDeriv/Measurable.lean | 4.409 | 4.695 | 0.939× |
| Analytic/Basic.lean | 5.074 | 5.203 | 0.975× |
| **Total per pass** | **10.757** | **11.435** | **0.941×** |

The total is the median of per-pass sums, rather than the sum of file medians.
Original totals range from 10.553 to 11.350 s;
replacement totals range from 11.316 to 12.057 s.
All ten paired replacement totals are slower. These are measurements of three
affected files on one machine, not a whole-mathlib build.

A separate rebuild of the tactic with mathlib dependencies already cached took
5.185 s. The complete tactic library contains
295 nonblank, noncomment code lines. Its implementation, tests, and benchmark
infrastructure are reported separately from proof-line savings.

## Candidate outcomes

The frozen ledger contains 14 reviewed sites: five replacements, seven deferred
exclusions, and two unchanged examples. One unchanged replacement was compiled
but saved no proof lines; another was retained after static review of its
existing one-line proof. Deferred sites are not counted as failed compilations.
[SELECTION.md](SELECTION.md) records discovery queries, unsuccessful development
attempts, and the limits of the lexical mathlib-wide search.

## Reproduction and retained evidence

Run the commands in the [project README](../README.md#mathlib-evaluation).
The harness generates copied full sources, a reviewable patch, exact compiler
commands, logs, setup JSON, raw times, and source hashes. The patch imports this
project's `NormArith` library; the reproduction uses the project Lake environment.

- [Verified mathlib patch](results/mathlib.patch)
- [Final generated report](results/report.md) and [raw result JSON](results/report.json)
- [Every final measurement](results/measurements.jsonl)
- [Frozen manifest](candidates.json) and [exact measured implementation patch](results/implementation.patch)

The first complete run, before the certificate-only scalar fast path, measured
11.480 s before and 12.650 s after (0.907×). It is retained in
[the initial report](results/initial/report.md), with
[raw measurements](results/initial/measurements.jsonl) and
[the exact initial implementation patch](results/initial/implementation.patch).
Both runs use the same frozen candidate set; no timing samples were removed.
Host timings drift between runs, so compare variants within each paired run.

Full local compiler artifacts and logs remain under `.lake/benchmark-optimized`
and `.lake/benchmark-final`. Reproduction creates fresh copies in its chosen
output directory.
