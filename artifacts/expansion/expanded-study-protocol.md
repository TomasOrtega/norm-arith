# Fresh expanded compilation study

This protocol is fixed before the new pilot. The final source patch is pending;
the preserved 232-line patch is a scheduling reference, not the new frozen study.
No expanded pilot or confirmatory measurements have started.

Use the existing proofs as the only baseline. Measure all files in the final
deterministically selected, freshly verified patch, including every preparation,
import and slowdown. No timing-based file selection or transfer of the historical
1.105× result is permitted.

## Freeze and coordination

Before sampling, finish candidate selection and final combined verification,
independently recount the literal patch, and copy its exact manifest to
`.lake/expanded-study-20261021/frozen/manifest.json` with selection status `frozen`.
The candidate set must exceed 232 net lines for the new goal. Preserve the source
verification receipt, original/patched files, project sources and all hashes.

Build the final tactic and its native library before final source verification.
Keep those same bytes through pilot and confirmation. If a separate one-time
rebuild cost is desired, record it before that verification; do not rebuild
between pilot and confirmation. Warm source-header setup remains separately
recorded by each run. No cold-native-build claim follows from an up-to-date check.

Freeze every `NormArith*.lean`, `NormArith/**/*.lean` and
`NormArithTest/**/*.lean`, including paper examples; Lean/Lake/Python binaries;
Lake configuration; benchmark source; selected Mathlib sources; actual parsed
variant headers/options; import artifacts and native libraries. Tests or source
files added during a run invalidate it. Stop discovery, native builds, compression,
archive export, TeX rendering and other agent CPU/disk workloads. Paper prose may
be edited without building. Keep the actual tool session handle and `launch.json`.

## Commands after the owner authorizes the final freeze

Run from the project root, with Python 3.15.0 and unique new output directories:

```sh
python3 artifacts/expansion/freeze_study.py FINAL_VERIFICATION FINAL_INDEPENDENT_AUDIT \
  --output .lake/expanded-study-20261021/frozen

python3 scripts/benchmark.py .lake/expanded-study-20261021/frozen/manifest.json \
  --skip-setup --threads 1 --repetitions 24 --warmups 1 \
  --output .lake/expanded-study-20261021/pilot \
  > .lake/expanded-study-20261021/pilot-run.log 2>&1

python3 artifacts/expansion/calibration_review.py \
  .lake/expanded-study-20261021/pilot/report.json \
  --output .lake/expanded-study-20261021/pilot-calibration-review.json
```

The freeze helper checks exact patch reconstruction, independent source counts,
all recorded fresh outputs and the current source/configuration/runtime inputs.
It changes only the manifest's selection status. Its receipt binds the machine
and power snapshot in `artifacts/expansion/machine-profile-before-study.json`
and the protocol and independent analysis helpers. `--check-only` validates a
verification without creating the frozen study. The untimed verified-08 milestone
has passed this preflight; the final merged verification must pass again.

Read only the blinded calibration review before choosing the block length. It
omits absolute durations, average speed effects, intervals and significance;
its numerical diagnostics are invariant to multiplying either variant's times
by a constant. Inspect serial correlation, relative AB/BA order differences and
relative half-run drift. Four-pair blocks and 40 confirmatory pairs are the
default. Use eight-pair blocks and 80 pairs only with a written dependence
rationale. Both designs retain ten whole blocks. With 24 pilot pairs, correlations
at four/eight-pair resolution use only six/three blocks and are noisy. If neither
choice is defensible, retain the pilot without a confirmatory claim.
Monitor pilot progress using completed-row counts and process status, not the
per-file durations in the redirected log or the report's unblinded summary.

Write dated `calibration.json` with schema 1, the chosen `block_pairs`, rationale,
and exact pilot-report/measurements paths and SHA256 hashes. Freeze that decision
before reading the effect or starting confirmation. Do not pool pilot samples.

```sh
python3 scripts/benchmark.py .lake/expanded-study-20261021/frozen/manifest.json \
  --skip-setup --threads 1 --warmups 1 --repetitions 40 \
  --confirmatory --calibration .lake/expanded-study-20261021/calibration.json \
  --bootstrap-resamples 10000 --bootstrap-seed 20261020 \
  --output .lake/expanded-study-20261021/confirmation \
  > .lake/expanded-study-20261021/confirmation-run.log 2>&1
```

Use `--repetitions 80` for the predeclared eight-pair design. No sample-count
change, outlier deletion or stopping for significance is allowed after the
confirmatory plan is frozen. If interrupted, send SIGINT to the coordinator PID
in `launch.json`; the active compiler group is reaped, completed evidence is
retained, and the run exits 130. Preserve the interrupted run; restart only as a
new separately labelled study and output directory.

## Outcome and evidence

The primary ratio is mean original full-pass seconds / mean replacement full-pass
seconds. Resample whole paired nonoverlapping blocks, retaining all affected
files and both variants, using the existing 95% BCa procedure, 10,000 draws,
seed 20261020 and whole-block jackknife. Success requires a valid calibrated lower
endpoint strictly above one. An undefined interval or failed gate is not a speed
improvement; publish its observed ratio/interval and all file regressions honestly.
Calibration supports a block rationale but does not prove independence or
guarantee coverage under arbitrary drift or dependence.

Each repetition genuinely compiles complete files to fresh `.olean`, `.ilean`,
module sidecars, IR and C with actual imports, native plugins, original Lake build
options, one Lean thread, common dependency order and alternating AB/BA passes.
Dependency artifacts are warm. Import loading, tactic search, kernel checking,
serialization and C generation are inside compiler time; output hashing follows
the timer. Lake dispatch, setup and native C object compilation are separate.
This is an affected-file Lean compilation claim, not all-Mathlib build speed.

Retain immutable plans, calibration and blinded review, all raw times/logs and
per-output hashes, runtime/executable lineage, source verification, source-count
audit and independent recomputation of statistics. Paper evidence must bind the
final patch and tactic to these new measurements; keep the old full census as
historical coverage background and the 885-file follow-up as targeted evidence.
Do not relabel the follow-up as full coverage or reuse old implementation costs.

After sampling ends, independently recompute the report's statistics:

```sh
python3 artifacts/expansion/verify_expanded_statistics.py \
  .lake/expanded-study-20261021/confirmation/report.json \
  --output .lake/expanded-study-20261021/independent-statistics.json
```

The standalone checker imports neither benchmark nor paper code. It checks the
exact final file set, both predeclared designs, all recorded rows and the BCa
arithmetic; output hash inventories are checked as metadata here, with byte
validation performed separately against the retained raw outputs.

## Capacity and packaging

The 40-file scheduling reference has a 101.489-second one-off replacement pass.
Adding its 30 new-file durations to the old original pass gives a rough
204.330-second pair allowance. This is not a speed estimate. The 24+40 measured
pairs plus two warmups need about 225 minutes of compiler work; the 80-pair design
needs about 361 minutes. Reserve five/seven hours respectively and recompute if
the final file set changes. Retaining all fresh outputs and per-pass setups needs
roughly 14/22 GiB; reserve 20/30 GiB plus final archives. No timed work has begun.

Commit source, compact portable evidence, manifests, reports and checksums. Store
each portable bundle as checked compressed parts of at most 32 MiB. Verify a full
restore before publication. The complete census and intermediate verification
raw archives remain locally preserved and ignored by Git; their receipts and
inventories remain tracked. Document that a clone lacks those deep audit payloads.
Splitting parts bounds individual file size, not total clone size. Publication
follows the finished evidence and paper checks.
