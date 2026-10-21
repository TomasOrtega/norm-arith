# Norm and metric arithmetic paper

The expanded manuscript has a four-page main body, followed
by references and technical appendices, in the unchanged official NeurIPS 2026
preprint style. Anonymous author information does not assert workshop submission
or acceptance.

The paper explains the finite real-space core, bounded quantified specialization,
and a checked pseudometric extension. Its new patch and timings must come from
one final frozen study. It reports 87 verified proof replacements in 46 files,
with 310 net code lines saved after preparation and imports. The ratio of mean
original and replacement compilation times is 1.0724×, with a conditional paired
95% interval of [1.0669, 1.0814]. All 40 paired passes and seven slower files
remain in the analysis. The earlier 41-line, 1.105× study remains historical;
its measurements do not transfer to the expanded implementation.

## Build

From the repository root, a completed portable release builds with:

```sh
python3 paper/build.py --render
```

This command restores the configured local evidence transport if needed, checks
its payload, regenerates the tables, runs XeLaTeX and BibTeX through latexmk,
and checks the log and four-page main-body limit. It launches no Lean or native
build. Portable status uses its checked examples by default; the explicit
`--reuse-checked-examples` alias remains available. The PDF is
`paper/output/pdf/paper.pdf`. Inspect every rendered page under
`paper/tmp/pdfs/` before delivery.

For unfinished changes to the manuscript, use:

```sh
python3 paper/build.py --draft --render
```

A draft has visible unfinished-evidence labels. It does not establish a final
patch, fresh example check, or timing result. A release must build without
`--draft`.

An explicit `--fresh-examples` build compiles `NormArith` and freshly checks
`NormArithTest/Paper.lean`. Do this before final source verification and timing,
or in a separate replay checkout. A build or relink after verification can
invalidate the frozen runtime fingerprints.

The six snippet markers are `hidden`, `reverse`, `mathlib`, `boundary`,
`quantified`, and `metric`, delimited by `-- paper:begin NAME` and
`-- paper:end NAME`. Each block includes its statement and proof. Shared section
variables can remain outside the displayed block; Lean checks the whole module.

The build requires XeLaTeX, latexmk, BibTeX, `kpsewhich`, and Poppler's `pdfinfo`,
`pdffonts`, `pdftotext`, and `pdftoppm`. The fonts are TeX Gyre Termes, TeX Gyre
Heros, and JuliaMono, with explicit regular, bold, italic, and bold-italic faces.
No shell escape is required. `paper/output/toolchain.json` records tool versions,
font and TeX-input hashes, embedded font names, and build logs. Different TeX or
font versions can change PDF bytes and layout.

The checked numerical runtime is CPython 3.15.0. Use that version for exact
bootstrap-hash replay, for example `uv run --python 3.15.0 python paper/build.py
--render`. Different numerical runtimes have not been checked for identical
statistical hashes.

The style archive came from the [official NeurIPS 2026 instructions](https://media.neurips.cc/Conferences/NeurIPS2026/Formatting_Instructions_For_NeurIPS_2026.zip),
SHA-256 `82473931e3ef710fcd3f4a8cd4119b9de32e56825f90f9e5a6d55f2d01b817d9`.
The [Math-AI workshop call](https://mathai-2026.github.io/cfp/) supplies the format
reference; this repository makes no venue-status claim.

## Evidence chain

`status.json` is the active configuration. The expanded live configuration uses
`study_mode: "composed_expansion"`. Its five validated stages are:

| Stage | Inputs |
| --- | --- |
| Historical full census | `census_manifest`, `census_summary`, `census_integrity`, `census_outcomes`, `census_archive` |
| Targeted follow-up | `targeted_archive` and its compact inventory, outcomes, proposals, raw index, and frozen implementation |
| Composed selection | `selector_manifest`, `selector_summary`, `selector_ledger`, and hashed input-manifest snapshots |
| Compiled frozen patch | `source_verification_report`, `source_verified_manifest`, `frozen_manifest` |
| Confirmatory timing | `confirmatory_report`, `confirmatory_analysis_plan`, `confirmatory_measurements`, and their calibration/runtime lineage |

The full census supplies the pinned 8,637-file universe and its recorded gaps.
The follow-up uses a fixed 885-file subset with earlier norm observations. Its
outcomes do not establish a new full-mathlib census. Finished runs can retain
explicit failed-file outcomes; pending or unprocessed files are rejected.
Known eligible observations without terminal outcomes in an incomplete file
remain `unknown_due_incomplete_file`.

The adapter recomputes targeted outcome counts and deterministic selection from
the archived input manifests. Each selected source span must belong to an
original observed declaration body. The complete patched files compile together
with fresh artifacts. The latest targeted Lean and configuration hashes must
match that verification; the historical census can have an older implementation.

Line accounting uses nonblank, noncomment code lines in the formatted source.
It charges all preparation, helpers, and added imports. Rejected, overlapping,
and no-saving candidates remain in the ledgers. Implementation and extractor
costs are separate figures. Proof savings are not total-repository savings.

The timing adapter retains every affected file, warmup, and measured paired
pass. It checks exact headers, setup inputs, native plugins, compiler executable
hashes, Python version, calibration, and frozen analysis. It recomputes the ratio
of mean full-pass times and whole-block paired BCa interval from raw records.
Fresh expanded-study rows require verified compiler outputs and their hashes.
Portable evidence retains these timed-output hashes; the separate live audit
checks the actual output bytes before archival.

`claim_speedup` defaults to false. Enabling it requires a valid paired 95%
interval wholly above one. A complete negative result remains reportable. Native
import differences belong to the actual original-versus-patch comparison; the
ratio does not isolate the tactic's algorithm.

The expanded calibration metadata uses `calibration_review`,
`calibration_decision`, `calibration_review_source`, and `diagnostics_source`.
The review contains dependence, order, and drift diagnostics without absolute
times or average speed levels. The adapter binds its pilot and source hashes
to the frozen decision and the 40/4 or 80/8 confirmatory design. It does not need
the earlier unblinded `pilot_diagnostics` artifact. Portable mode restores these
metadata specifications from its frozen configuration.

`example_candidate_id` selects a literal source replacement from the verified
patch. The generator checks its ID, declaration body, span hash, patch, complete
file check, and compiler artifacts. All preparation stays visible in the
selected example. No anticipated count or historical timing fills missing data.

## Portable release

After complete live validation, export to a new directory:

```sh
python3 paper/evidence.py --status paper/status.json \
  --export artifacts/paper-evidence-expanded
python3 paper/evidence_transport.py pack artifacts/paper-evidence-expanded \
  --output artifacts/paper-expanded-transport
```

The first command exports the complete validated chain and checks the portable
form before publication. The second creates deterministic gzip/tar transport
parts, each at most 32 MiB. Both destinations must be new. Record the printed
bundle and transport receipt hashes in the release configuration:

```json
{
  "study_mode": "composed_expansion",
  "evidence_bundle": "artifacts/paper-evidence-expanded",
  "evidence_bundle_sha256": "SHA256_OF_BUNDLE_JSON",
  "evidence_transport": "artifacts/paper-expanded-transport/transport.json",
  "evidence_transport_sha256": "SHA256_OF_TRANSPORT_JSON"
}
```

Keep the selected example ID and metadata specifications. Set live stage paths
to null; live and portable stage inputs cannot mix. When the unpacked directory
is absent, the build restores it from the configured tracked parts. Restoration
checks part order and hashes, archive bytes, regular member paths, expansion
size, and the complete bundle inventory before an atomic directory rename.
It rejects symlinks, duplicate members, extra files, and existing destinations.
It needs no network or original absolute `.lake` paths.

The payload includes all reported evidence: full and targeted compact ledgers,
selection inputs, source guards, original and patched source, complete raw timing
records, plans, calibration, runtime fingerprints, validator snapshots, one
fresh proof-output set, and the six checked examples. Dependency/native binaries
and every timed-pass binary are not copied. Their export-time hash checks are
recorded explicitly. Portable validation is not a new Lean check, a timing rerun,
or an independent signature. Deep raw extraction archives remain separate;
compact evidence does not recreate all original elaboration observations.

The historical manuscript/PDF and its source state are preserved in
`artifacts/paper-baseline-41line/paper.tar.gz` with a byte receipt. Its evidence
transport is under `artifacts/paper-baseline-41line/evidence-transport/`.
Rebuild that study with its preserved manuscript and validator snapshots. The
expanded manuscript must use the separate expanded bundle.

## Language and checks

The explanatory prose has a 53-rule applicability matrix in `language-audit.md`,
a vocabulary/POS/sense ledger in `vocabulary-review.tsv`, and a corpus-bound
review in `language-review.json`. Mathematical and research-format exceptions
are explicit. This is STE-based writing, without unqualified ASD-STE100
conformance or external certification. The official dictionary is not bundled.

After changing prose or generated results, inspect the complete affected contexts
and language requirements. Resolve `paper/output/language-candidates.json`, then
record the contextual review with `python3 paper/audit.py --record-review`.
A release build rejects unresolved candidates, unreviewed words, or a stale
review record. Vocabulary coverage alone cannot establish contextual correctness.

Run the focused paper, transport, and real-font checks with:

```sh
python3 -m unittest discover -s paper -p 'test_*.py'
```

Synthetic fixture tests do not contribute proof checks, observations, savings,
or timing data. The font integration tests compile every selected font face and
skip only when XeLaTeX or `pdffonts` is unavailable.
