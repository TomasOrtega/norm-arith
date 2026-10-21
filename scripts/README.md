# Reproduce a mathlib replacement measurement

The harness uses Python's standard library and the project's pinned Lean/Lake.
It compares original mathlib source with the proposed replacements; no alternate
tactic or manual-proof baseline is included.

From the project root, after fetching mathlib's dependency cache:

```sh
python3 scripts/benchmark.py benchmarks/candidates.json \
  --output /private/tmp/norm-arith-evaluation --rebuild-tactic
```

The output directory must be empty. The default is one warmup and ten measured
pairs, alternating original/replacement and replacement/original order. Use
`--threads N` to fix Lean's thread count; the default preserves Lean's default.
`--timeout SECONDS` applies to each compiler or setup process.

`--rebuild-tactic` removes only generated `NormArith` artifacts in the project's
`.lake/build/lib/lean` and `.lake/build/ir` directories, plus its own native
shared/static libraries and sidecars under `.lake/build/lib`. It preserves sources,
test artifacts, and dependency caches, then records a separate
`lake --no-cache build NormArith` duration. Without that flag, setup performs a
normal possibly cached tactic build. Edited-header setup also records any native
compilation/linking required by the installation. `--skip-setup` instead checks that the tactic
is already up to date. Module dependency preparation and setup queries still run.
Finish all builds and relinks before final source verification. After verification
freezes import and native-library bytes, use `--skip-setup` for both the pilot and
confirmatory run; rebuilding can invalidate that evidence.

For a quick source/patch review without compiling:

```sh
python3 scripts/benchmark.py benchmarks/candidates.json \
  --prepare-only --output /private/tmp/norm-arith-proposed
```

The mathlib dependency must be a clean checkout at the exact manifest revision.
The harness never edits its source. `--mathlib` can make that path explicit but
must resolve to the project's `.lake/packages/mathlib` when compiling.

## What is timed

Every trial directly invokes the pinned Lean compiler on complete copied source
files with their real variant imports. Lean's `--deps-json` parses each complete
variant's import header. `lake setup-file` receives that header and the original
module path, so Lake resolves the correct package identity, imports, plugins and
native libraries. Compiler options come from the original Lake build setup;
editor-only options returned by `setup-file` are excluded. The raw headers,
raw edited setups and effective compiler setups are retained with hashes.
The copied setup leaves `imports` unset so the source header controls imports. Affected dependencies compile before their
importers, whose setup points to those fresh outputs while preserving exactly the
artifact parts requested by Lake. Ordinary imports do not gain private data or
full IR. The two variants share an order valid for both import graphs. Added-import cycles
are rejected.

Each compiler command requests `.olean`, `.ilean` and C output. Module-system
`.olean.server`, `.olean.private`, `.ir` and `.ir.sig` outputs are also required.
Every pass writes into a new empty directory, so a cached no-op cannot count as a
compilation. A nonzero exit, JSON error diagnostic, admitted `sorry`, timeout or
missing output prevents a successful report. Separate `leanir` compilation is not
supported when `compiler.postponeCompile` is enabled.

The measured work includes process startup, import loading, tactic search, proof
construction/checking, artifact serialization and C generation. It excludes
dependency builds, Lake dispatch and native C object compilation. Setup costs are
recorded separately. This measures warm affected-file Lean compilation, not a
whole-mathlib build.

Native compilation is part of the recorded installation. A replacement import can
load native tactic code and native code for its dependencies, while the original
keeps the libraries selected by its actual original imports. Both library lists
and hashes are recorded. The primary ratio therefore includes installation and
import effects; it does not isolate the norm algorithm. Native build/link costs
can occur during edited-header setup and remain outside compile totals.

The same files compile in both variants, including regressions. Each aggregate
sample sums every affected file in one pass. The exploratory report preserves the
pilot statistic: median original total / median replacement total. Ratios below
one indicate a slowdown. All samples are retained; JSON includes per-file and
aggregate ranges and raw samples. A manifest whose `selection_status` is not
`frozen` produces a report explicitly labelled as an integration trial.

## Confirmatory analysis

Freeze the patch and candidate selection, then collect a separate pilot on that
exact workload and tactic source. Use pilot serial diagnostics to select the
block length and explain why dependence between blocks is acceptably small.
The earlier three-file prototype pilot cannot calibrate a new census or tactic.
Pilot measurements are excluded from the confirmatory sample.

Write a calibration artifact before the confirmatory run:

```json
{
  "schema_version": 1,
  "date": "2026-10-20",
  "block_pairs": 2,
  "rationale": "Describe the pilot serial diagnostics and block-length choice.",
  "pilot_report": {
    "path": "pilot/report.json",
    "sha256": "SHA256 of the complete frozen-selection pilot report"
  },
  "pilot_measurements": {
    "path": "pilot/measurements.jsonl",
    "sha256": "SHA256 of the pilot raw measurements"
  }
}
```

Reference paths resolve from the calibration file. The harness checks both hashes,
report/raw-data agreement, complete paired observations, the affected-file set,
and agreement with the current manifest, patch, Lean source/configuration hashes,
toolchain, threads, warmups and machine. After setup and before any warmup, it
also matches both variants' parsed headers, effective build options, import
artifact bytes, native plugin paths/initializers/bytes, and Lean/loader environment
settings (including `LEAN_IMPORT_WORKERS`). Only run-output paths are normalized;
editor-only raw options are excluded from this compiler-runtime comparison. The pilot must contain at least three
complete blocks of the selected size. Calibration requires a dated rationale;
these checks do not establish independence. A hash of the compiler/setup protocol
functions must also match. Both full harness hashes remain in provenance;
analysis-only edits outside those functions do not require a new pilot. Review
any harness change that could affect measurement conditions even if that hash
matches.

Fresh studies also bind the actual Lean, Lake, Python and Lake-launcher executable
bytes, and require the same Python version. Each successful measurement records
`compilation_status: "verified"` and SHA256 hashes of every fresh output; failed
validation rows remain failed even when the compiler exits zero. Output hashing
occurs after the compiler timer stops.

```sh
python3 scripts/benchmark.py benchmarks/candidates.json \
  --confirmatory --calibration benchmarks/calibration.json \
  --repetitions 40 --bootstrap-resamples 10000 --bootstrap-seed 20261020 \
  --threads 1 --output /private/tmp/norm-arith-confirmatory --skip-setup
```

Confirmatory mode defaults to 40 measured pairs and one warmup pair. The pair
count is fixed before setup. A `--block-pairs` override must match calibration.
Block size must be positive and even, divide the measured pair count, and leave
at least three blocks. Each nonoverlapping block retains adjacent AB/BA pairs,
all affected files and their paired original/replacement totals. Three blocks is
an algorithmic minimum, not evidence of adequate power or reliable coverage.
Neither the default count nor default seed justifies an independence assumption.

The primary statistic is mean original full-pass time / mean replacement
full-pass time. Resampling selects whole paired blocks with replacement, never
individual files or separate variants. The 95% bias-corrected and accelerated
(BCa) interval uses at least 10,000 resamples, a fixed recorded seed, half-weighted
bias-correction ties, linear empirical-quantile interpolation, and deletion of
one whole block at a time for jackknife acceleration. Equal block sizes preserve
the ratio of pass means. The success criterion is a valid calibrated interval
whose lower endpoint is strictly greater than one. All slowdowns remain in the
aggregate. Medians are descriptive in this mode.

The [primary-source methods note](../docs/research/benchmark-statistics.md)
documents the BCa transformation, jackknife formula, and numerical conventions.
Its interpretation here assumes independent, representative blocks. Pilot
calibration supports the block-length choice but does not establish those
assumptions or guarantee coverage under arbitrary dependence or drift.
A degenerate bootstrap or jackknife, nonfinite correction, acceleration pole or
endpoint beyond the resample resolution yields an undefined interval and a false
success gate. A completed compilation run can therefore fail the improvement
criterion. Exploratory runs have no confirmatory success gate.

Every run writes `analysis-plan.json` before setup or compilation. It records the
sample count, ordering, workload, analysis settings, calibration references and
input hashes. Changes to the plan, manifest, tactic/configuration sources,
calibration or pilot evidence, copied source/patch, or original mathlib sources
invalidate the run. Resolved module setups are also checked after creation.
The output directory must remain unique: the harness cannot append samples or
silently revise a plan. Predeclare another run if the design changes; report the
original outcome. Historical pilot reports keep their original median statistic.

`launch.json` records the coordinator PID, command and start time. Keep the shell
or tool session handle when starting a long run. If interruption is necessary,
send SIGINT to that recorded coordinator: it terminates and reaps its active
compiler process group, retains completed rows and logs, writes an interrupted
report, and exits 130. An interrupted run is not resumable or a successful study;
retain it and use a new output directory for another predeclared run.

## Run the semantic census

```sh
lake build norm_arith_census
python3 scripts/census.py --output .lake/census-run --workers 4
```

The default universe is every tracked Lean source below `Mathlib/` at the pinned
revision. The run records original tactic and term observations, declaration-body
ranges, bounded replay outcomes, per-file failures, and checked proposals. It
freezes its extractor, source/configuration hashes, and resource rules. A
`--file Mathlib/Some/File.lean` or `--limit N` run is calibration, not full coverage.
Use `--resume` with the same output and arguments only when frozen inputs match.

One-line spans cannot save a line with the fixed replacement, so their outcome
is `no_line_saving_untried`. Isolated checked proposals contribute no final line
savings until the selected source patch compiles. See the
[census protocol](../docs/CENSUS-PROTOCOL.md) for matching, exclusions, budgets,
and deterministic selection.

## Verify a selected census patch

```sh
python3 scripts/select_census.py /path/to/census --output /private/tmp/selection
python3 scripts/verify_selection.py /private/tmp/selection/manifest.json \
  --census /path/to/census --output /private/tmp/source-verification --threads 1
```

The verifier checks each selected edit against its original declaration proof-body
range and checked census proposal. It reuses hash-checked census build setups,
resolves the actual patched headers, and compiles each selected file once with
fresh outputs. Affected dependencies feed their fresh artifacts to importers.
No source in the mathlib checkout is edited.

The selector formats proofs before counting savings. A long `by norm_arith`
uses an indented two-line block, with both lines charged. Fixed replacements
must fit 100 Unicode characters per line; a file must retain positive savings
after its import cost. The verifier rejects `linter.style.longLine` diagnostics
even when Lean exits successfully. Other ordinary warnings remain recorded.

Only complete combined-patch success writes a `source-verified-trial`
`manifest.json`. `verification.json` records hashes, commands and results.
A failed file rejects its selected edits as one set; this does not prove every
individual edit is invalid. `exclusions.json` records candidate ids, source hashes
and reasons. Reselect with `select_census.py --exclude exclusions.json`, then verify
the new whole patch in a fresh directory. Blocked dependents are not classified
as failed proof candidates. Timings never choose candidates or exclusions.

## Manifest schema

```json
{
  "schema_version": 1,
  "selection_status": "frozen",
  "mathlib_revision": "40-character commit hash",
  "files": [{
    "path": "Mathlib/Some/File.lean",
    "source_sha256": "SHA256 of exact file bytes",
    "imports": ["NormArith"],
    "helpers": []
  }],
  "candidates": [{
    "id": "stable-candidate-id",
    "path": "Mathlib/Some/File.lean",
    "declaration": "theorem_name",
    "status": "replace",
    "reason": "why this candidate belongs in the evaluation",
    "start_line": 100,
    "end_line": 106,
    "original_sha256": "SHA256 of exact inclusive source span bytes",
    "replacement": "  norm_arith [h₁, h₂]\n"
  }]
}
```

Line numbers are one-based and inclusive. Replacement text ends with a newline
and includes all preparation. Hashes prevent a shifted or changed source from
silently patching another proof. Replacement spans may not overlap. Preserve the
theorem's statement and assumptions when choosing spans; review the generated
patch to check this.

Other candidate statuses are `unsupported`, `failed` and `unchanged`. These stay
in the report but do not modify source or contribute savings. Optional exact spans
on excluded candidates are also hash-checked. Only files with active `replace`
candidates belong to the affected-file timing set.

An optional helper entry is
`{"id": "helper-name", "before_line": 100, "text": "...\n"}`. Its position refers
to the original source. Each helper's complete declaration is charged once
against proof savings. Candidate preparation is already charged through the
replacement text. Imports are reported separately, including a net figure that
also charges imports. Nested comments and comment markers inside literals are
handled when counting nonblank, noncomment lines. Tactic implementation lines are
recorded separately; `NormArith/Census.lean` instrumentation has a separate
extractor cost. Proof savings do not assert net repository line reduction.

## Artifacts and checks

`report.md` and `report.json` contain the result, candidate outcomes and provenance:
the mathlib revision, manifest and patch hashes, platform, Lean/Lake versions,
threads, and hashes of the working project Lean sources. Inputs changing after
the analysis plan is frozen invalidate the run. `mathlib.patch`, copied full
sources, command arguments, setup JSON, stdout/stderr and `measurements.jsonl`
make it reviewable.

Run the harness checks without Lean or downloads:

```sh
python3 -m unittest discover -s scripts -p 'test_*.py'
```
