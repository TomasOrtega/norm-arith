# Superseded source-style study

This directory preserves the fixed timing study for the original 18-edit,
11-file patch. One generated proof line exceeds mathlib's 100-character limit.
Formatting that line removes the affected file's net saving. The corrected patch
requires its own selection, source verification, calibration, and timing study.
These historical timings are not results for that corrected patch.

`evidence/` passed strict live validation before the selector or verifier changed.
Its receipt and byte inventory preserve reports, all raw timing samples, plans,
calibration inputs, source patch, proof outputs, original source, and old tools.
Runtime/import bytes were inspected at export; their hashes are retained without
shipping the full dependency cache. Portable recomputation checked the copied
evidence and proof outputs. It does not rerun timing or prove the timing model's
independence assumption.

`status.live.json` preserves the exact historical configuration. The separate
`status.portable.json` selects the copied bundle and has `claim_speedup=false`.
`export.json` binds both statuses, the bundle receipt, old tool snapshots, and
historical siblings. The independent statistics checker is preserved with its
original 11-file workload, alongside its result, pilot diagnostic sources,
calibration decision, post-run input checks, and the pre-result style decision.

The main paper configuration is separate and must bind the corrected study.

The unpacked `evidence/` directory is ignored by Git. Its complete portable
bundle is published in `evidence-transport/`. From the repository root, restore
it into an absent destination with:

```sh
python3 paper/evidence_transport.py unpack \
  artifacts/superseded-style-study/evidence-transport/transport.json \
  --output artifacts/superseded-style-study/evidence \
  --receipt-sha256 fa6cc922890a22cb4b694187054268b154b684f82884fe779c2e822447711979 \
  --bundle-sha256 de9e8a9d0c738a6c366cc46fc3a60f54695a30319f01ac3723cd7960ab845b85
```

The restore checks every compressed part and payload file. The separate
`evidence-transport-check.json` records a successful round trip.
