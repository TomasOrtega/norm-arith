# Expanded Mathlib replacements

The combined expansion is source-verified: **310 net code lines saved** across
**87 replacements in 46 files**. The original proofs use 582 code lines; the
replacements use 226, including every preparation step. Forty-six added imports
reduce the 356 proof-line saving to 310. There are no helper declarations.

The [patch](verified-05/mathlib.patch), [manifest](verified-05/manifest.json), and
[verification receipt](verified-05/verification-receipt.json) belong to the pinned
Mathlib revision `2f3c7c8a8949b04a32f9303f59163acffb766996`. All affected files
compiled together, with fresh outputs and affected dependencies ordered first.
The patch also passes `git apply --check`. It has not been applied upstream.

The [independent audit](verified-05/independent-audit.json) recounts literal proof
spans, preparation and imports, applies the unified diff independently, and checks
all 322 fresh compilation-output hashes. The [final receipt](verified-05/milestone.json)
records the source-verified stage before timing; it supersedes the generic audit's
earlier stage label. The milestone includes original and patched sources, frozen
project sources, input manifests, and body evidence. Its complete raw verification
archive is preserved locally and Git-ignored; tracked receipts bind its bytes.
The [first milestone](verified-01/manifest.json) remains preserved at 109 net lines,
29 replacements and 16 files; the [second](verified-02/manifest.json) preserves
157 net lines, 37 replacements and 21 files. Later milestones preserve
[232 lines](verified-03/manifest.json) and [304 lines](verified-04/manifest.json).

The final targeted follow-up processed 885 selected files: 875 complete and ten
incomplete, with 158 isolated checked proposals. Its
[archive receipt](../../artifacts/expansion/discovery-v4-archive/archive.json) binds
all raw records, including failures; the raw archive is retained locally.
Earlier discovery versions and failed combined
trials remain available. This targeted search does not establish full Mathlib
coverage or find every possible replacement. The final patch combines 50
census-generated replacements with 37 composed outside the census. AI coding
agents helped develop the latter; some entries need only explicit facts.
The selection excludes
unsupported or cyclic imports.

The new confirmatory study measured **1.072× warm affected-file compilation
speedup**, with a conditional paired 95% BCa interval of **1.067–1.081×**.
Mean total compilation time for all 46 files decreased from 131.188 to 122.333
seconds. All 40 pairs and seven per-file mean slowdowns remain in the result.
The [results and scope](RESULTS.md) include independent statistics, output-byte
checks, power observations, and [portable study evidence](study-final/README.md).
The earlier 1.105× result applies only to the
[original 41-line patch](../FINAL-RESULTS.md), its implementation and its workload.

`manual/` retains proposed preparations, full-file trials, and a confirmed subset.
Proposals contribute no savings until the combined source patch compiles.
`scripts/select_expansion.py` merges proposals, removes overlapping spans, and
charges imports once per file. The preparation verifier checks each exact edit
against an original declaration-body observation and preserves all source outside
the recorded proof span.
