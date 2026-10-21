# Census evidence archive

Run the archive command after the full semantic census has ended:

```sh
python3 scripts/archive_census.py .lake/census-full-v3 \
  --output artifacts/census-full-v3
```

The output directory must not exist. The command writes to a temporary sibling
directory and publishes the bundle by renaming that directory after validation.
It does not upload files or change the census run.

Add `--full-raw` to create `raw.tar.gz` as well. This archive can be large. It
contains every regular file in the source run under `run/`, including raw event
ledgers, logs, setup data, retry histories, and the frozen implementation. It
does not follow paths in requests or cache-origin metadata to other directories.
The command accepts only the census file layout. It refuses symlinks, special
files, build outputs, and extra files such as environment dumps. It does not
collect the process environment. Paths already recorded by the census remain
in its metadata and logs.

## Required checks

The archive command obtains the census output lock. It refuses an active run,
pending or invalid integrity, a calibration scope, a selected subset of the
manifest universe, or any missing file outcome. It checks the manifest protocol
hash, every declared implementation and configuration snapshot, and setup-cache
origin hashes. The origin source and the current run must have the same Mathlib
source universe, revision, and configuration hashes.

For each recorded attempt, the command checks its evidence hashes with
`census.verify_evidence`. The latest result must match its attempt ledger. A
completed attempt must also match its raw event ledger, and its proposals must
match the checked successful events. The command recomputes the summary from
the latest per-file outcomes and requires exact agreement with the saved summary.
It checks that the run files did not change before it publishes the archive.

An `orchestrator_exception` can have no extractor evidence. It is retained only
when `orchestrator_error.json` matches the file outcome. The archive lists these
files under `files_without_extractor_evidence`. If a proposal file has no matching
attempt result, its rows are retained as unattributed evidence. They receive no
successful-proposal credit. Archive-time hashes do not establish kernel checking
for these rows.

All manifest files must have been processed. Some may have failed. The archive
preserves the failure counts and reasons and keeps `full_universe_processed`
separate from `full_universe_completed`. A valid archive does not establish
successful elaboration of failed files, complete goal coverage within them,
correctness of a combined source patch, line savings, or compilation speedup.

## Bundle contents

The directory and `compact.tar.gz` contain:

- The exact census manifest, summary, integrity record, and optional launch and
  setup-cache origin records. A resumed run also retains its interruption
  records, checked against the same protocol and universe size.
- `file-outcomes.jsonl`: every latest file result, including failures.
- `attempt-outcomes.jsonl`: every saved attempt result. `current_attempt` marks
  the result that supplied the final file outcome.
- `proposals.jsonl`: all saved proposal rows, with their result and source
  proposal-file paths. Historical and unattributed rows remain distinct from
  current successful proposals.
- `frozen-implementation/`: the source and configuration snapshots recorded by
  the census manifest.
- `source-inventory.json`: the byte length and SHA-256 hash of every raw run file.
  Raw event, log, and setup bytes are indexed here but are only included in the
  optional raw archive.
- `archive.json`: coverage counts, failure counts, archive scope, and tool hashes.
- `archive-tools/`: the exact archiver and validation-helper sources used.
- `inventory.json`: the byte length and SHA-256 hash of each compact payload file.
  It excludes itself to avoid a circular hash.

The compact archive stores its payload below `census-evidence/`. The output
directory also contains `archives.json` and a `.sha256` file for each archive.
These give the archive byte lengths and SHA-256 hashes. They sit outside the
archives to avoid circular hashes. For example:

```sh
cd artifacts/census-full-v3
shasum -a 256 -c compact.tar.gz.sha256
shasum -a 256 -c raw.tar.gz.sha256  # when --full-raw was used
```

Keep the complete raw archive for independent reinspection of observations and
attempts. The compact bundle supports review of accounting and provenance. It
does not replace raw evidence for reanalysis. These hashes detect byte changes;
they are not a signature or an external record of publication.

## Repository packaging

The repository publishes compact census records and portable paper evidence.
The portable bundles use checked compressed parts of at most 32 MiB; the paper
build restores the configured bundle when its unpacked directory is absent.
Historical bundles have explicit restore commands beside their transports.

The complete `artifacts/census-v3/raw.tar.gz`, targeted discovery raw archives,
and intermediate verification raw archives remain in the local research
workspace and are ignored by Git. Their archive receipts and byte inventories
remain tracked. A clone does not contain these deep audit payloads, and the
paper rebuild does not require them. The tracked portable evidence contains the
selected proof outputs, source patch, complete timing samples, and compact
census ledgers needed for the published numerical analysis.

Re-running the census and archive commands creates a new experiment; it does
not recreate the original raw observations or their hashes.

The [expanded timing study](../benchmarks/expansion/study-final/README.md) has its
own checked transport and restoration instructions. Its full compiler outputs
and logs remain in the local `.lake/expanded-study-20261021-archive/` archive.
The tracked archive receipt and member index bind those bytes. Statistical
replay uses the compact transport and does not need that deep archive.
