# Standalone snippet benchmark

Measured at 2026-10-27T18:23:54.299246+00:00. 5 paired snippets, 1 warmup pass(es), 3 recorded pairs.

**Workload:** analytic composition and parameter planning.

Five standalone pairs compare manual composition with public tactics using the same checked analytic primitives. These are new examples, not extracted mathlib proofs or full PDE formalizations. Shared library lemmas are available to both variants. All local setup, side-condition instances, and imports are included in line counts. Interpolation and Mixed were held out until their generic rules were complete; the other three are development examples. No rules were tuned on the held-out cases.

Case definitions: [analytic.json](analytic.json). This is not a census, a whole-file compilation study, or a claim about all PDE proofs.

## Source size

| Metric | Baseline | Tactic | Saved |
| --- | ---: | ---: | ---: |
| Proof-body code lines | 44 | 5 | 39 |
| Whole-snippet code lines | 94 | 55 | 39 |

Counts exclude blank and comment-only lines. Proof bodies are delimited in every file. Whole-snippet counts include imports, statements, and all preparation. Imports and local preparation are counted in each file.

## Compilation

Median total time per corpus pass: **14.836 s baseline**, **18.356 s tactic**. Their ratio is **0.808×** (baseline/tactic; above one favors the tactic).

Each sample launches `lake env lean -DwarningAsError=true` with fresh `.olean` and `.ilean` outputs. Recorded pairs alternate compilation order. Dependencies are already built and imports are warmed. Times include process startup, imports, tactic execution, checking, and output writing. They exclude the separately recorded dependency-build/setup step. Background machine load is uncontrolled. These descriptive medians do not establish statistical significance.

| Snippet | Kind | Proof lines (old → new) | Net code saved | Baseline median (s) | Tactic median (s) | Ratio |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| [Interpolation](Analytic/Interpolation.lean) | held-out composition | 7 → 1 | 6 | 2.940 | 2.895 | 1.016× |
| [Product](Analytic/Product.lean) | development example | 17 → 1 | 16 | 2.986 | 3.553 | 0.840× |
| [Elliptic](Analytic/Elliptic.lean) | development example | 10 → 1 | 9 | 2.981 | 2.964 | 1.006× |
| [Mixed](Analytic/Mixed.lean) | held-out composition | 3 → 1 | 2 | 3.048 | 5.982 | 0.510× |
| [FixedPoint](Analytic/FixedPoint.lean) | development example | 7 → 1 | 6 | 2.870 | 2.977 | 0.964× |

Raw samples, failures, source hashes, versions, and timing order are retained in [analytic-results.json](analytic-results.json).
