# Historical 41-line patch and compilation result

This is the completed earlier study. The [expanded study](expansion/RESULTS.md)
uses a different implementation and workload. The historical
[paper and portable evidence](../artifacts/paper-baseline-41line/README.md)
remain preserved.

The final patch saves **41 net code lines** in **10 files**, using **16**
replacements. Warm Lean compilation of those files has a measured **1.105×**
speedup over their existing mathlib proofs. The paired 95% interval is
**1.095–1.112×**, conditional on independent, representative timing blocks.

The study pins mathlib `2f3c7c8a8949b04a32f9303f59163acffb766996`
and Lean `4.36.0-rc1`. The patch is local and has not merged into mathlib.

## Source accounting and coverage

| Quantity | Result |
| --- | ---: |
| Tracked `Mathlib/` Lean files processed | 8,637 |
| Complete file outcomes | 8,610 |
| Incomplete file outcomes | 27 |
| Isolated kernel-checked proposals | 40 |
| Selected disjoint replacements | 16 |
| Affected files | 10 |
| Original proof code lines | 67 |
| Replacement proof code lines | 16 |
| Proof code lines saved | 51 |
| Added import code lines | 10 |
| Added helper code lines | 0 |
| **Net code lines saved** | **41** |

Counts exclude blank lines and comments. The fixed formatting rule limits
replacement lines to 100 Unicode characters and charges continuation lines.
The selected replacements have a maximum line length of 89 characters. Every
affected file compiled with fresh outputs; verification produced 70 nonempty
artifacts and no long-line diagnostics.

The selector maximizes savings over disjoint proposal spans, charges each
file's import, and requires positive net savings per file. Its ledger contains
16 selected proposals, 12 overlaps, 9 import-offset cases, and 3 cases without
formatted line savings. Timing never selects proposals.

Processing every file does not establish complete goal extraction. The census
retains 27 incomplete outcomes and 99 known eligible observations without
terminal outcomes; further unseen populations in incomplete files are unknown.
Original single-line proofs are retained as untried, rather than counted as
tactic successes. See the [census report](../docs/research/mathlib-census.md)
and [archive documentation](../docs/CENSUS-ARCHIVE.md).

## Confirmatory timing

| Quantity | Result |
| --- | ---: |
| Mean original full-pass time | 34.823072 s |
| Mean replacement full-pass time | 31.510198 s |
| Ratio of mean pass times | 1.105136568 |
| Paired 95% BCa interval | [1.095315117, 1.112425279] |
| Measured paired passes | 40 |
| Warmup paired passes | 1 |
| Raw compiler records, including warmup | 820 |
| Failed compiler records | 0 |
| Pairs per block / resampling blocks | 4 / 10 |
| Bootstrap draws / seed | 10,000 / 20261020 |

A separate 24-pair pilot preceded calibration. The block-length review used
serial dependence, order effects, and drift without absolute times or average
speed levels. Four-pair blocks retain two AB/BA cycles. The final sample count,
workload, statistic, interval method, and success rule were frozen before the
confirmatory run. The lower endpoint exceeds one, satisfying the declared gate.
Every affected file and every measured pair is retained.

The Uniform file becomes slower: mean time increases from 1.300343 to
1.478620 seconds. The other nine files improve by both mean and median time.
The selected example in that file illustrates proof compression without a
per-file speed guarantee. The [per-file review](../artifacts/style-confirmatory-statistics-review.json)
retains both summaries for every file.

The machine was an Apple M4 Max MacBook Pro with 36 GB memory, on AC power with
low-power mode disabled. Lean used one thread. Ordinary system background
activity was uncontrolled. The interval assumes independent, representative
blocks; the pilot does not prove independence or coverage under arbitrary drift
or dependence.

The result concerns warm compilation of the ten modified files. It includes
actual tactic search, imports, proof construction, kernel validation,
serialization, and C generation. It excludes native C object compilation and
Lake dispatch. The changed import/native-library environment contributes to
the measured effect, so this is not an isolated algorithm comparison. Cold
native-build cost was not fully recorded. These data do not establish a speedup
for an entire mathlib build or another machine.

## Evidence and reproduction

- [Readable patch and complete selection ledger](final/README.md).
- [Independent statistics check](../artifacts/style-confirmatory-statistics.json).
- [Independent line-count audit](../artifacts/independent-line-count.json).
- [Post-run frozen-input check](../artifacts/style-confirmatory-postcheck.json).
- [Source verification and freeze receipt](../artifacts/style-correction-result.json).
- [Calibration decision](../artifacts/calibration-style-v4-decision.json) and
  [blinded diagnostic review](../artifacts/style-pilot-calibration-review.json).
- [Validated paper evidence transport](../artifacts/paper-baseline-41line/evidence-transport/transport.json).
- [Independent clean portable rebuild](../artifacts/portable-paper-build.json).
- [Historical paper, PDF, language audit, and rebuild instructions](../artifacts/paper-baseline-41line/README.md).

Use the archived paper sources and restored bundle to rebuild this historical
paper with Python 3.15.0. The current paper build targets the expanded study.

The [harness documentation](../scripts/README.md) describes fresh source
verification and timing runs. Setup, imported binaries, compiler options,
sources, raw samples, and analysis are bound by hash inventories. A separate
implementation checks the actual statistical result without importing the
benchmark or paper code.

## Preserved earlier studies

A style check found that one replacement in the earlier 18-edit, 11-file patch
exceeded mathlib's line limit. Formatting it removed that file's net saving.
The correction was recorded before inspecting that study's confirmatory
result. The original fixed run completed and is preserved under
[`artifacts/superseded-style-study/`](../artifacts/superseded-style-study/).
The revised patch received fresh source verification, calibration, and timing.

The [prototype pilot](RESULTS.md) also remains unchanged. It used five
replacements in three files, saved 36 net lines, and compiled 6.3% slower.
