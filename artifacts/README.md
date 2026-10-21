# Research evidence

The current local patch has 87 replacements in 46 files and saves 310 net code
lines. Combined source verification and independent accounting passed. Forty
predeclared pairs give a 1.072× warm affected-file compilation ratio, with
conditional 95% block-BCa interval [1.067, 1.081]. Mean pass time decreases from
131.19 to 122.33 seconds. All 46 files remain in the result. See the
[current results](../benchmarks/expansion/RESULTS.md) for scope and limits.

## Current study

| Artifact | Purpose |
| --- | --- |
| [verified-05](../benchmarks/expansion/verified-05/milestone.json) | Final 310-line patch and verification milestone |
| [independent audit](../benchmarks/expansion/verified-05/independent-audit.json) | Literal source recount, diff application, and 322 fresh output checks |
| [discovery-v4 archive](expansion/discovery-v4-archive/archive.json) | Final targeted scan: 885 files, 875 complete, 10 incomplete, 158 proposals |
| [implementation costs](expansion/implementation-costs-v4.json) | Separate 850-line tactic and 470-line census totals |
| [timing protocol](expansion/expanded-study-protocol.md) | Frozen original-versus-replacement study and analysis rules |
| [machine profile](expansion/machine-profile-before-study.json) | Hardware, software, and power snapshot before measurement |
| [post-study power snapshot](expansion/machine-profile-after-study.json) | Observed power settings after all 40 pairs, before analysis/export |
| [quiet-start receipt](expansion/quiet-start.json) | Final freeze and stopped competing workloads |
| [portable study](../benchmarks/expansion/study-final/README.md) | Exact timing records, analysis plans, calibration, and checked transport restoration |
| [study archive receipt](../benchmarks/expansion/study-final/archive.json) | Checked compressed transport and local archive of all compiler outputs and logs |
| [independent statistics](../benchmarks/expansion/study-final/independent-statistics.json) | Separate recomputation of the mean ratio and conditional block-BCa interval |
| [actual-byte audit](../benchmarks/expansion/study-final/timed-output-byte-audit.json) | Rehashed frozen inputs and all 42,504 fresh pilot and confirmation outputs |
| [independent review](expansion/final-review/independent-recomputation.json) | Further raw-data, patch-accounting, and provenance checks |
| [restored-study review](expansion/final-review/restored-study-recomputation.json) | Independent numerical checks from the restored compact study |
| [final claims review](expansion/final-review/final-claims.json) | Manuscript and PDF claims bound to the final sources and numerical evidence |
| [paper transport](paper-expanded-transport/transport.json) | Checked evidence parts for the default [paper rebuild](../paper/README.md) |
| [paper release](paper-expanded-validation/release.json) | Final manuscript, language, test, and all-page visual checks |
| [offline default build](paper-expanded-validation/offline-default-build-receipt.json) | Fresh transport restoration with no dependency cache or Lean launch and identical rendered pages |

## Historical 41-line study

The original study has 16 replacements in 10 files and saves 41 net code lines.
Its measured warm affected-file compilation speedup is 1.105×, with a conditional
95% block-BCa interval of 1.095–1.112×. That result applies only to the historical
implementation and workload. The [result summary](../benchmarks/FINAL-RESULTS.md)
and [archived paper](paper-baseline-41line/README.md) preserve its scope and limits.
The latter includes instructions to restore the historical portable bundle from
its tracked compressed transport.

| Artifact | Purpose |
| --- | --- |
| [paper-evidence/bundle.json](paper-evidence/bundle.json) | Portable validated source, census, timing, and analysis evidence |
| [portable-paper-build.json](portable-paper-build.json) | Independent clean rebuild, guarded file access, copied-data analysis, and final source/text agreement |
| [style-correction-result.json](style-correction-result.json) | Combined source verification and frozen patch hashes |
| [independent-line-count.json](independent-line-count.json) | Independent source/diff recount of all 41 net saved lines |
| [independent-line-count.py](independent-line-count.py) | Separate nested-comment/string lexer and patch checker |
| [style-confirmatory-postcheck.json](style-confirmatory-postcheck.json) | Post-run source, compiler-artifact, and raw-data checks |
| [style-confirmatory-statistics.json](style-confirmatory-statistics.json) | Independent recomputation of the actual final estimate and interval |
| [style-confirmatory-statistics-review.json](style-confirmatory-statistics-review.json) | All ten files' mean and median times, including the Uniform slowdown |
| [verify_style_statistics.py](verify_style_statistics.py) | Independent statistics implementation |
| [style-statistics-test-receipt.json](style-statistics-test-receipt.json) | Pre-pilot synthetic verification and source hashes |
| [calibration-style-v4-decision.json](calibration-style-v4-decision.json) | Dated four-pair block choice before final sampling |
| [style-pilot-calibration-review.json](style-pilot-calibration-review.json) | Serial, order, and drift review without average speed levels |
| [pilot-style-v4-serial-diagnostics.json](pilot-style-v4-serial-diagnostics.json) | Complete descriptive pilot diagnostics |
| [census-v3/archives.json](census-v3/archives.json) | Compact and full raw census archive receipts |
| [machine-profile.json](machine-profile.json) | Recorded hardware profile |
| [style-correction-tests/inventory.json](style-correction-tests/inventory.json) | Failing regressions followed by passing formatting/verification checks |

Deep raw census and intermediate verification archives remain local and
Git-ignored. Tracked receipts and inventories bind those archives; they are not
part of a clone. Portable paper bundles use checked compressed transports and do
not need the full raw archives or the original `.lake` dependency cache. They
retain runtime hash inventories and export-time validation attestations.
Rebuilding a paper is distinct from running new Lean compilation experiments.
See [evidence packaging](../docs/CENSUS-ARCHIVE.md).

## Earlier studies

[`superseded-style-study/`](superseded-style-study/) preserves the completed
18-edit, 11-file study and its original tools. A source-style correction changed
the workload before the historical 41-line study above. The
[pre-result decision](style-correction-decision.json) records the reason.

The root `calibration-decision.json`, `pilot-serial-diagnostics.json`, and
`verify_confirmatory_statistics.py` belong to that earlier 11-file study.
They do not define the current patch's result. The
[prototype pilot](../benchmarks/RESULTS.md) is older still and uses a different
implementation and workload.
