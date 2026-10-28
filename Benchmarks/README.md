# Standalone proof benchmarks

This directory measures a selected workload of actual mathlib proof fragments.
It is an independently compilable corpus, not a patch to the dependency and
not a complete census of mathlib.

## Read a pair

`Baseline/Foo.lean` and `Tactic/Foo.lean` contain the same theorem statement.
The first keeps the source proof or an explicitly described extraction; the
second replaces the relevant arithmetic with this package. Both retain the
context needed to compile outside the source file.

[`manifest.json`](manifest.json) pins mathlib, identifies the source declaration
and line span, and records adaptations. Cases distinguish complete theorems,
literal local estimate blocks, and adapted estimates. Source authorship and
Apache-2.0 attribution are retained. A proof may use its source module's lemmas,
but may not solve the benchmark by invoking the theorem it is meant to replace.

The mathlib corpus contains **52 pairs** from 39 source modules: 36 complete
theorem copies, 13 extracted blocks, and three adapted estimates. In 38 pairs the
tactic proof is shorter; the other 14 have equal proof-body line counts. Imports
do not count toward savings. Thirteen pairs with longer tactic proofs were
removed. Coverage includes asymptotics, Weierstrass estimates, multilinear
composition, normed rings, affine spaces, characteristic functions, contractions,
and metric constructions.

## Run

From the repository root, after `lake build --wfail NormArith NormArithTest`:

```sh
python3 scripts/benchmark_snippets.py --check
python3 scripts/benchmark_snippets.py --pairs 3 --warmups 1 \
  --output Benchmarks/results/local/current.json
```

Use `--only` with case identifiers for a subset, `--timeout` for each Lean
invocation, `--lake` for an explicit Lake executable, and `--output` to keep a
separate result. The command above keeps new timings in an ignored local
directory and preserves the checked-in reports. The unfiltered 41-case run is
archived in [Git history](https://github.com/TomasOrtega/norm-arith/tree/3c71795846c9d183a2dd1adc819ca53314088eb1/Benchmarks).
It includes five subsequently removed pairs and does not measure the current
corpus. The original 20-case reports are [`results.json`](results.json) and
[`results.md`](results.md), which remain the runner's default output paths.
Reports include all samples and failure outcomes.

## What is measured

Proof-body counts use explicit markers, exclude blanks and comments, and include
all local preparation. Imports are outside those markers and do not affect
reported savings. Raw JSON retains whole-file counts as diagnostic metadata.
The runner checks matching statements, unique markers, and source-theorem reuse.

Each timed sample starts a new `lake env lean -DwarningAsError=true` process and writes fresh
`.olean` and `.ilean` files. Warmups precede recorded pairs, and the baseline/tactic
order alternates. Times include process startup, imports, elaboration, tactic
search, kernel checking, and output writing. They exclude dependency builds and
initial native setup. Machine load remains uncontrolled. The report gives
descriptive medians, not a statistical significance claim.

The suite measures the public tactic against original proofs. Easy examples
may use structural or short search without reaching the LP. These measurements
therefore do not isolate the LP's effect. Synthetic backend comparisons, when
reported, have their own manifest, directories, and results.

## Compare the backends

The five synthetic cases use the same statements and heartbeat limits. The
baseline sets `norm_arith.useLP` to false; the LP version sets
`norm_arith.forceLP` to true. Shared preprocessing remains enabled. These goals
exercise the backend, including four-, six-, and eight-source decompositions and
a dense eight-source example.

```sh
python3 scripts/benchmark_snippets.py --manifest Benchmarks/backends.json --check
python3 scripts/benchmark_snippets.py --manifest Benchmarks/backends.json \
  --pairs 5 --warmups 1 --output Benchmarks/backend_results.json
```

See [backend_results.md](backend_results.md) for timings. These are synthetic
algorithm comparisons, and their code-line counts are excluded from the mathlib
source-savings headline.

## Add a case

1. Choose a real proof block in the pinned source and record the theorem, span,
   author, and exact revision.
2. Copy its statement and necessary context into the baseline. Preserve every
   mathematical hypothesis; describe abstractions or changed names.
3. Copy the same statement into the tactic version and replace only the estimate
   proof. Include all setup and extra imports in that file.
4. Keep the pair only if its tactic proof uses no more proof-body lines than the
   baseline, excluding imports. Add the manifest entry and forbidden source-theorem
   identifier. Run accounting tests and compile both versions before recording timings.
5. Retain slower examples and failed runs. Explain exclusions before computing a
   summary; do not silently select only favorable results.

Synthetic tests belong in a separate workload. A short generic vector analogue
is useful, but should never be called an unchanged formalization of a PDE theorem.

## Analytic composition

The five pairs in [analytic.json](analytic.json) compare manual composition with
public tactics. Both variants can use the same checked primitive lemmas. Counts
include imports, membership assumptions, and local exponent instances.
Interpolation and mixed-norm exponents were held out until the generic rules
were complete. The other cases are development examples.

```sh
python3 scripts/benchmark_snippets.py --manifest Benchmarks/analytic.json --check
python3 scripts/benchmark_snippets.py --manifest Benchmarks/analytic.json \
  --pairs 3 --warmups 1 --output Benchmarks/analytic-results.json
```

These are per-use proof savings. The reusable rule implementation is additional
source. Report its cost separately. These examples do not count as mathlib source
replacements or as a complete PDE formalization.

## Search, reconstruction, and replay

```sh
python3 scripts/profile_core.py --pairs 3 --warmups 1
```

The runner compares the reference backend, forced LP, and saved proof replay.
It rotates order and starts a fresh Lean process for each sample. LP traces give
oracle search and proof reconstruction time. Reconstruction includes the final
scalar proof. Replay time includes decoding and checking; it is not isolated
kernel time. Whole compilation includes imports and output writing.

Reports also record proof graph bytes, graph nodes, output size, peak process
memory when available, source hashes, and all failed samples. A changed-source
run is rejected. Build first and pass `--no-build` when measuring an already
checked version. Do not edit or build the same modules during a timing run.
