# Standalone snippet benchmark

Measured at 2026-10-27T16:00:55.736461+00:00. 5 paired snippets, 1 warmup pass(es), 5 recorded pairs.

**Workload:** synthetic backend comparison.

Same checked statements under the retained reference path and forced compact LP. These cases are separate from the mathlib extraction corpus; no source-line savings are claimed. All cases, including failures and timeouts, remain in the report.

Case definitions: [backends.json](backends.json). This is not a census, a whole-file compilation study, or a claim about all PDE proofs.

The two variants run the same proof with different solver settings. Their line counts are not included in the mathlib proof-savings total.

## Compilation

Median total time per corpus pass: **16.709 s baseline**, **16.739 s tactic**. Their ratio is **0.998×** (baseline/tactic; above one favors the tactic).

Each sample launches `lake env lean -DwarningAsError=true` with fresh `.olean` and `.ilean` outputs. Recorded pairs alternate compilation order. Dependencies are already built and imports are warmed. Times include process startup, imports, tactic execution, checking, and output writing. They exclude the separately recorded dependency-build/setup step. Background machine load is uncontrolled. These descriptive medians do not establish statistical significance.

| Snippet | Kind | Proof lines (old → new) | Net code saved | Baseline median (s) | Tactic median (s) | Ratio |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| [RationalChain4](BackendLP/RationalChain4.lean) | synthetic | 1 → 1 | 0 | 3.076 | 3.159 | 0.974× |
| [RationalChain6](BackendLP/RationalChain6.lean) | synthetic | 1 → 1 | 0 | 3.292 | 3.284 | 1.002× |
| [RationalChain8](BackendLP/RationalChain8.lean) | synthetic | 1 → 1 | 0 | 3.507 | 3.647 | 0.962× |
| [CoupledErrors](BackendLP/CoupledErrors.lean) | synthetic | 1 → 1 | 0 | 2.938 | 2.863 | 1.026× |
| [DenseEight](BackendLP/DenseEight.lean) | synthetic | 1 → 1 | 0 | 3.536 | 3.684 | 0.960× |

Raw samples, failures, source hashes, versions, and timing order are retained in [backend_results.json](backend_results.json).
