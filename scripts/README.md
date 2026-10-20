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
`.lake/build/lib/lean` and `.lake/build/ir` directories. It preserves sources,
test artifacts, and dependency caches, then records a separate
`lake --no-cache build NormArith` duration. Without that flag, setup performs a
normal possibly cached tactic build. `--skip-setup` instead checks that the tactic
is already up to date. Module dependency preparation and setup queries still run.

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
files with their real variant imports. It reuses Lake's queried module setup,
including library options, package identity, plugins, dynamic libraries and
resolved dependency artifacts. The copied setup leaves `imports` unset so the
source header controls imports. Affected dependencies compile before their
importers, whose setup points to those fresh outputs while preserving exactly the
artifact parts requested by Lake. Ordinary imports do not gain private data or
full IR. Added-import cycles are rejected.

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

The same files compile in both variants, including regressions. Aggregate samples
sum the file times in each pass; the reported ratio divides the median original
total by the median replacement total. Ratios below one indicate a slowdown.
All samples are retained; JSON includes per-file and aggregate ranges and raw
samples. A manifest whose `selection_status` is not `frozen` produces a report
explicitly labelled as an integration trial.

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
recorded separately; proof savings do not assert net repository line reduction.

## Artifacts and checks

`report.md` and `report.json` contain the result, candidate outcomes and provenance:
the mathlib revision, manifest and patch hashes, platform, Lean/Lake versions,
threads, and hashes of the working project Lean sources. Sources changing during
measurement invalidate the run. `mathlib.patch`, copied full sources, command
arguments, setup JSON, stdout/stderr and `measurements.jsonl` make it reviewable.

Run the harness checks without Lean or downloads:

```sh
python3 -m unittest discover -s scripts -p 'test_*.py'
```
