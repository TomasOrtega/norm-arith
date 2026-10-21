# Final expanded compilation study

The 310-line patch uses 87 replacements in 46 Mathlib files. The fixed 40-pair
confirmation measured **1.072387×** warm affected-file speedup, with a conditional
95% paired block BCa interval of **1.066942–1.081410×**. Mean total compiler time
decreased from **131.188455 to 122.333093 seconds**. All files and samples remain,
including seven files with slower replacement means.

See the [results and per-file table](../RESULTS.md),
[independent statistics](independent-statistics.json),
[actual-output byte audit](timed-output-byte-audit.json), and
[archive receipt](archive.json). The interval assumes independent representative
blocks. Calibration and power snapshots do not establish that assumption or
continuous stable machine conditions.

## Restore the compact evidence

The checked transport contains exact reports, raw measurement rows, frozen plans,
source variants, implementation sources, analysis helpers, all calibration
versions and decisions, and machine/power metadata. Large JSON files are retained
inside five compressed parts, each at most 32 MiB. No Lean build is needed to
recompute the statistics. Choose an output directory that does not exist:

```sh
python3 paper/evidence_transport.py unpack \
  benchmarks/expansion/study-final/transport/transport.json \
  --output /private/tmp/norm-arith-study-restored \
  --receipt-sha256 87a6604f1637e33ab4b32159ae282e26601164655a816aabf4487f3e16dc88ec \
  --bundle-sha256 6908e00755a24a3447f68ac222628756a316f5a4f3ea1825cba0d1b2c01d7875

python3 /private/tmp/norm-arith-study-restored/audit-tools/verify_expanded_statistics.py \
  /private/tmp/norm-arith-study-restored/confirmation/report.json \
  --output /private/tmp/norm-arith-study-statistics.json
```

Use Python 3.15.0 for exact numerical reproduction. The resulting statistics
SHA256 is `348735896280396b276e9e4540c1fcdcff79cb9b7d2e041ce4c22c7218395bc2`.
The [roundtrip receipt](roundtrip-integrity.json) records an actual restore into
`/private/tmp` and identical recomputation with a Python audit hook denying reads
of the original project. Frozen reports retain their original path strings;
statistical replay uses adjacent restored files and does not read those paths.

The transport includes the superseded, unlaunched relative-path calibration and
both decision receipts. Only the review-path representation changed before
confirmation; the selected four-pair blocks and 40-pair sample count did not.
The final [calibration](calibration.json) and
[owner check](calibration-root-check.json) identify the version used.

## Raw outputs and scope

The byte audit rehashed 56,103 unique files, including all **42,504 fresh compiler
outputs** from pilot and confirmation. It checked distinct per-call output paths,
process receipts, frozen source and configuration, actual headers/imports/native
libraries, compiler executable hashes, the clean Mathlib pin, and equal resolved
runtime provenance across runs.

Complete compiler outputs and logs are preserved in a local, Git-ignored raw
archive. The [archive receipt](archive.json) gives its path and hash; the
[raw byte index](raw-study-index.json) identifies every member. Compact transport
retains the observations and byte-audit attestations, but does not ship those
raw compiler outputs. Rehashing the original outputs requires the deep archive;
statistical replay does not.

Compiler time includes imports, tactic search, proof construction and checking,
serialization, IR, and C generation with cached dependencies. It excludes native
C object compilation, Lake dispatch, and harness setup/bookkeeping. Different
native imports are part of the measured variants, so this is neither an isolated
algorithm comparison nor a full Mathlib build result. The manuscript's checked
paper bundle remains the default path for rebuilding the paper.
