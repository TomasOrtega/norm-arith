# A systematic mathlib census for norm arithmetic

Research and implementation date: 20 October 2026. The semantic extractor is
[NormArith/Census.lean](../../NormArith/Census.lean); the bounded coordinator is
[scripts/census.py](../../scripts/census.py). Small calibration runs are distinct
from a completed full-corpus census and its later compilation experiment.

## A finite claim that can be checked

The current [discovery script](../../benchmarks/discover.py) records three lexical
queries. Its [selection ledger](../../benchmarks/SELECTION.md) explicitly limits
the resulting 31 matching lines; these are not every possible use of norm
arithmetic. The completed experiment has five replacements across three files,
39 fewer proof lines, and a 6.3% compilation slowdown.
[Current results](../../benchmarks/RESULTS.md)

A defensible broader claim would be: “At revision R, extraction completed on
every file in the declared source universe. We attempted every source-backed
goal satisfying predicate P, using preparation grammar G, source-selection rule
S, and fixed resource budget B. The resulting compiling, nonoverlapping patch
reduced proof code by X lines.” The extraction ledger must list files that did
not complete; otherwise the denominator is incomplete.

This is an exhaustive experiment over a finite, declared procedure. It does not
establish that no other norm-arithmetic replacement exists. Unbounded helper
invention, preprocessing, changed proof structure, and future tactic features
leave that larger question open. A completeness claim would need a formal
fragment and a completeness argument in addition to corpus results.

## Available extraction layers

Lean's `TacticInfo` records goal identifiers and metavariable contexts before and
after a tactic, along with its syntax. `TermInfo` also carries its elaborated
expression, local context, expected type, and syntax. The surrounding context
records the parent declaration. These are the ingredients needed to inspect
actual goal expressions and map successful proposals back to source spans.
[Lean InfoTree types](https://lean-lang.org/doc/api/Lean/Elab/InfoTree/Types.html)

The frontend's command snapshots expose their completed info trees. The installed
4.36.0-rc1 source collects top-level command trees after their tasks complete;
trees can contain deferred assignments, so an extractor must wait for finalized
results rather than sample an editor while elaboration is in progress.
[Lean frontend source](https://github.com/leanprover/lean4/blob/v4.36.0-rc1/src/Lean/Elab/Frontend.lean),
[InfoTree traversal API](https://lean-lang.org/doc/api/Lean/Elab/InfoTree/Util.html)

Cached `.ilean` files are useful for a cheaper first pass. Their schema stores
module identity, direct imports, identifier references, and declarations, rather
than reusable proof states. This can enumerate references to a fixed family of
triangle, norm, and distance lemmas without depending on textual spelling or
line layout. It cannot recover every intermediate norm goal.
[Lean reference-index schema](https://lean-lang.org/doc/api/Lean/Server/References.html)

The community REPL already documents file mode with `allTactics: true`, returning
tactic spans, displayed goals, and reusable proof-state identifiers. Its JSON
API also exposes an `infotree` request. Its inspected `master` toolchain matches
this project's 4.36.0-rc1. These are promising starting points, not a validated
integration: pin a REPL revision and verify module identity, private imports,
Lake options, and state replay before using it for the census.
[REPL usage](https://github.com/leanprover-community/repl),
[REPL JSON API](https://raw.githubusercontent.com/leanprover-community/repl/master/REPL/JSON.lean),
[REPL toolchain](https://raw.githubusercontent.com/leanprover-community/repl/master/lean-toolchain)

LeanDojo's own extractor is another concrete reference: its trace schema records
command ASTs, tactic states before/after, tactic spans, and premise references.
It demonstrates that the extraction pipeline is implementable. It does not
establish compatibility with this pinned Lean version or replace the need for
an explicit eligibility and replacement protocol.
[LeanDojo extractor](https://raw.githubusercontent.com/lean-dojo/LeanDojo/main/src/lean_dojo/data_extraction/ExtractData.lean)

## Implemented census protocol

1. Freeze the mathlib/Lean/extractor revisions and source universe. The default
   universe is tracked `Mathlib/**/*.lean`; untracked files, `MathlibTest`,
   `Archive`, and dependencies are outside it. Every tracked file appears in
   `manifest.json` with its source hash. `--file` and `--limit` explicitly label
   a run `calibration`, even if all selected files succeed.
2. Extract both tactic-goal and proof-term expected-type information. A
   tactic-only census misses term-style proofs and some `calc` steps. Filter
   actual expressions by the declared supported norm-inequality fragment rather
   than pretty-printed strings. Keep raw counts before filtering.
3. Deduplicate macro-generated and nested observations using original source
   ranges, declaration identity, and goal fingerprints. Exclude observations
   from abandoned elaboration alternatives. Preserve unresolved/generated
   ranges as an explicit noneditable category, rather than inventing source
   positions. Unresolved contexts and missing or synthetic ranges have explicit
   `node_exclusion` events; unexpected extraction errors produce `node_error`
   and a partial-file result. The core retains some information while backtracking, so merely
   traversing every node does not identify distinct source obligations.
   [InfoTree backtracking behavior](https://github.com/leanprover/lean4/blob/v4.36.0-rc1/src/Lean/Elab/InfoTree/Basic.lean)
4. Try the same tactic procedure everywhere: declared norm-bound selection,
   deterministic source order, fixed preprocessing grammar, and heartbeat/time
   limits. The census invokes bare `norm_arith`, including its fixed distance
   normalization and automatic local-fact selection, without ad hoc preparation
   or invented helpers. Eligibility and fragment labels come from the tactic's
   expression-level APIs; scalar syntax alone does not establish a real vector
   space capability. Norm-free real conclusions are retained when the same
   classifier recognizes useful local norm facts.
   An eligible span confined to one physical source line receives
   `no_line_saving_untried`: replacing it with the fixed one-line tactic cannot
   reduce code lines. It remains in the denominator and is not a proved success.
5. For each promising state, reconstruct a source replacement and compile the
   complete module. A REPL state solved in isolation is a proposal, not a verified
   source patch. Preserve statements, assumptions, necessary surrounding goals,
   import visibility, and downstream use of local facts.
6. Select nonoverlapping replacements and compile the complete combined patch.
   Nested states must not yield duplicated line savings. Charge all preparation,
   shared helper declarations, and imports once. Report unsuccessful attempts,
   compiling no-saving results, and import-cycle exclusions alongside successes.

The original mathlib proofs remain the evaluation baseline, as already agreed
in [EVALUATION.md](../EVALUATION.md). A semantic census does not require reopening
alternate-tactic comparisons. Examples chosen to explain the algorithm should
come from verified entries and be linked to their exact source/manifest records.

## What is needed for a credible speed claim

The [current harness](../../scripts/README.md) already checks fresh outputs,
uses actual per-variant imports and Lake options, retains all repeated paired
samples, and separates a tactic rebuild. Those properties should remain. The
existing result supports proof compression, not faster compilation; shortening
a proof does not ensure that proof search and certificate checking cost less.

Before optimizing, profile representative successes and expensive failures.
Lean's nested trace profiler can measure elapsed time or heartbeats and export
Firefox Profiler data. Measure reification, candidate search, vector-identity
checking, certificate construction, scalar arithmetic, and import loading in
separate diagnostic runs. Instrumentation is not part of headline timings.
[Lean trace profiler](https://lean-lang.org/doc/api/Lean/Util/Trace.html)

For the broader experiment, freeze the candidate protocol and final implementation
before measuring again. Report per-file distributions and paired total ratios,
with uncertainty estimates when making a statistical speed claim. Keep earlier
runs and unsuccessful optimization trials. Do not select just the faster files.
The existing affected-file scope remains the default; a whole-mathlib speed claim
requires a separate actual whole-build comparison, including new tactic imports
and their downstream effects.

A broader patch may contain dependent affected files. Their remapped artifacts
must preserve each importer's requested `.olean`/private/server and IR parts.
The current harness fixes that existing-edge case, but an affected dependency
introduced only through a new import needs additional setup handling or explicit
rejection before such a case is measured. The current three-file pilot has no
affected-file dependency edges and is unaffected by that limitation.
[Harness implementation](../../scripts/benchmark.py)

## Scope preservation and replay

The original source is elaborated first with its actual module name, package,
Lake options, import artifact shape, plugins, and dynamic libraries. A second
pass adds `NormArith` to that same header without moving source positions. It
attempts only observations that match the original kind, half-open UTF-8 byte
range, parent declaration, and exact canonical expression of the goal closed
over **all** local declarations, including let values. Binder names and metadata
are removed for comparison; unresolved metavariables are exclusions, not guessed
substitutions. Hashes index observations; exact expression equality guards
matching. Failed elaboration alternatives are skipped.

The extractor uses finalized command snapshots in order. Type inference,
classification, and canonicalization use the node's original environment,
metavariable context, local context, options, namespace, and restored local
instances. Generated matchers and declarations created within one command must
remain available during observation; the pinned `Submodule.smul_induction_on'`
proof is a regression for this distinction. Replay and certificate checking use
a separate environment from before the command. An integration regression found
that ordinary `ContextInfo.env` can already contain the enclosing theorem, so
using it for replay would admit self leakage. Later declarations and the
enclosing theorem are not replay facts. A context that actually requires a
within-command constant may therefore be observed but fail safe replay.
Elaboration honors the setup's `Elab.async` option, defaulting to `true` as the
pinned CLI does. Forcing synchronous elaboration changes private-in-public
compatibility: the pinned `Group/End` and `Ext/ExtClass` sources compile normally
but fail with `-DElab.async=false`. Both are extraction regressions.
[Pinned command snapshot implementation](https://github.com/leanprover/lean4/blob/v4.36.0-rc1/src/Lean/Elab/Frontend.lean),
[Context replay implementation](https://github.com/leanprover/lean4/blob/v4.36.0-rc1/src/Lean/Elab/InfoTree/Main.lean)

A replay uses a fresh goal, restores local instances, rejects remaining goals,
metavariables, `sorry`, and references to its enclosing declaration, closes the
proof over its local context, and submits a temporary theorem to `addDecl` with
`debug.skipKernelTC = false`. The self-reference check also runs after closure,
so a let value cannot hide it. A successful replay is an isolated checked
proposal; only recompiling its source replacement establishes patch validity.
The second pass is excluded for modules in the tactic's import closure, with
an `import_cycle` outcome for every eligible original observation.
[Kernel-checking entry point](https://github.com/leanprover/lean4/blob/v4.36.0-rc1/src/Lean/AddDecl.lean)

Only recognized declaration value bodies can supply editable spans. Parser
syntax identifies simple RHS terms, equation RHS terms, and structure-instance
field values. A proof appearing inside a declaration's statement or assumptions
remains an observation with `outside_decl_body`; it cannot become a replacement.
Each proposal includes its containing body bounds so selection can validate this
restriction independently. Unknown declaration forms are conservative exclusions.
Synthetic/unlocated info nodes are counted before attempting type inference.

The replay finishes pending synthetic metavariables **inside** `Tactic.run`'s
action, with tactic recovery and error-to-`sorry` disabled. Pinned `Tactic.run`
restores the pending list when its action returns, so synthesizing afterward
loses deferred `by module` proof obligations. A real vector-rearrangement
regression exercises this path. The checked proof closure retains used let
values; full-context matching still preserves every let value.
[Pinned tactic runner](https://github.com/leanprover/lean4/blob/v4.36.0-rc1/src/Lean/Elab/Tactic/Basic.lean)

The default bounds are four worker processes, one Lean thread per worker,
600 seconds per file, 4 GiB of Lean runtime allocation allowance,
`maxHeartbeats = 200000` and 2 seconds per replay, and 10,000 replay attempts per file.
The coordinator enforces the file wall limit and reaps its process group. A
cooperative cancellation token enforces replay wall limits, backed by the outer
file deadline. The Lean memory allowance is not a hard operating-system RSS
limit; actual peak RSS is recorded with `wait4`. Every process retains its
command, exit status, elapsed/user/system time, peak RSS, and raw logs.

Creating `STOP_REQUESTED` in the run directory stops new setup batches and file
submissions. Active files finish; interrupted integrity and remaining-file counts
are retained, and the coordinator exits with status 130. Remove the marker
explicitly before resuming. Only the configured worker count of files is queued.

After the initial worker pool finishes, an incomplete file with `file_timeout`
or `process_failed` receives at most one serial retry with 1,800 seconds and
8 GiB. Its first attempt remains on disk. The goal budgets do not change;
ordinary tactic failures and completed-file unknowns do not trigger retries.
Resuming an exhausted second tier does not add a third attempt.

Lake setup queries are batched in bounded groups of 32. Pinned Lake documents
ordered, newline-delimited JSON results for multiple query targets; the
coordinator verifies each module name and count before using them. A failed
batch falls back to separately logged individual queries. Setup JSON is retained
compressed, with hashes. Setup time belongs to extraction setup, not the later
affected-file compilation headline.
[Pinned Lake query implementation](https://github.com/leanprover/lean4/blob/v4.36.0-rc1/src/lake/Lake/CLI/Main.lean)

`summary.json` distinguishes the full universe, selected files, processed files,
completed files, failures, and unprocessed files. “Full universe processed”
means every tracked file received an outcome; “full universe completed” also
requires successful extraction and a complete outcome ledger. Neither means
every mathematically possible proof replacement was found. Node exclusions,
import cycles, unsupported shapes, failed search, and exhausted budgets remain
visible. Resume refuses changed protocol/source hashes and changed raw evidence;
new attempts retain earlier attempt directories.
Attempt events retain the original fragment label and record the augmented
label separately, because the extra import can add typeclass capabilities.
Summary fragment denominators and outcome counts use the original observations.
Implementation/configuration source snapshots are retained in
`frozen-implementation/`. An explicit `lake --no-build --no-cache --rehash build`
preflight requires a fresh executable. Source and binary hashes are checked
again after extraction; `integrity.json` is `valid` only after those checks.
Changed implementation/configuration/source inputs invalidate the run's frozen
claim. Concurrent coordinators cannot share an output directory.

Run the extractor after building its native executable:

```sh
lake build norm_arith_census
python3 scripts/census.py --output .lake/census-full --workers 4
python3 scripts/census.py --output .lake/census-full --workers 4 --resume
```

The executable requires `supportInterpreter = true`, and initializer execution
must be enabled separately for each imported header. Compacted header regions
remain alive across both passes as required by Lean's initializer API.
[Initializer execution requirements](https://github.com/leanprover/lean4/blob/v4.36.0-rc1/src/Lean/ImportingFlag.lean)

The agreed speed criterion is a frozen, combined patch whose affected-file ratio
of mean original/replacement pass totals has a valid calibrated paired 95% BCa
interval strictly above one. The benchmark retains slow files and all measured
pairs. A positive result is required for that claim; the experiment cannot
promise a particular factor or guarantee that the requirement will be met.

## Observed v3 metadata gaps

The frozen v3 run records `partial_extraction` when type inference on a source
`TermInfo` raises `unknown metavariable`. The following inspected cases have no
observed norm goals or eligible replacements. They remain explicit unknowns;
zero observed goals does not prove that a failed file contains no opportunities.
Byte spans are zero-based, half-open UTF-8 offsets at the pinned mathlib revision.
Their complete events remain under `.lake/census-full-v3/files/<module>/attempt-01/events.jsonl`.

| Mathlib source and declaration | Source spans | Failed metadata |
| --- | --- | --- |
| `Combinatorics/Graph/Lattice.lean:68`, `Graph.edgeSet_inf` | `[2408,2412)`, `[2417,2421)`, `[2408,2421)` | `E(G)`, `E(H)`, and intersection in the theorem statement; missing `?_uniq.3644` |
| `Combinatorics/SimpleGraph/Clique.lean:927`, `IsIndepSet.nonempty_mem_compl_mem_edge` | `[37204,37205)` twice, `[37204,37208)` | `s` and complement in the theorem statement; missing `?_uniq.21706` |
| `Combinatorics/SimpleGraph/Walk/Operations.lean:298`, `Walk.concatRec_concat` | `[10820,10824)`, `[10819,10824)` | `Hnil` and `@Hnil` in a dependent-recursion proof; missing `?_uniq.7376.536` |
| `Computability/NFA.lean:225`, `mem_acceptsFrom_sep_fact` | `[7598,7599)` twice | `p` in a local set-comprehension statement; missing `?_uniq.3355.1881` |
| `Data/Fin/Tuple/Basic.lean:971`, `Fin.insertNth_last` | `[39543,39554)`, `[39555,39590)`, `[39592,39593)`, `[39592,39595)`, `[39591,39596)`, `[39543,39596)`, `[39533,39596)`, `[39532,39597)` | A dependent cast/congruence term; missing `?_uniq.29272.160` or `?_uniq.29272.165` |

The five cases above have the same missing-metavariable family, rather than
an unavailable declaration or a proof replay failure. The set terms in the
first two rows lie outside declaration bodies. The remaining rows show that
the family can also occur inside dependent proofs; those gaps stay unknown.

A separate metadata family occurs inside Qq pattern quotations:
`Tactic/FieldSimp/Discharger.lean:76`, span `[2792,2802)`, reports unknown free
variable `_fvar.853` in `~q(($e : $α) ≠ $b)`;
`Tactic/Positivity/Core.lean:540`, span `[24098,24119)`, reports unknown free
variable `_fvar.49765` in `~q($a ≠ ($b : ($α : Type _)))`.
Both are type-ascription fragments in quoted metaprogram patterns, and both
files have zero observed norm goals or eligible replacements. Their exact
missing-context cause has not been established. They remain partial extraction
outcomes rather than being treated as checked proof goals.

This is consistent with retained elaboration metadata from backtracking, but
the exact cause of these nodes has **not** been proved. The pinned local Lean
sources, relative to the toolchain's `src/lean/`, support that inference:

- `Lean/Elab/InfoTree/Main.lean:84–95`: `TermInfo.runMetaM` uses the supplied
  context and local context, as the census does; Lean's own formatter catches
  type-inference failure and displays `<failed-to-infer-type>`.
  [Pinned source](https://github.com/leanprover/lean4/blob/v4.36.0-rc1/src/Lean/Elab/InfoTree/Main.lean#L84-L95)
- `Lean/Elab/Term/TermElabM.lean:420–427`: `SavedState.restore` defaults to
  retaining info nodes while restoring the metavariable state.
  [Pinned source](https://github.com/leanprover/lean4/blob/v4.36.0-rc1/src/Lean/Elab/Term/TermElabM.lean#L420-L427)
- `Lean/Elab/InfoTree/Util.lean:44–73` and `InfoTree/Basic.lean:30–40`:
  the standard visitor merges nested contexts before visiting nodes. The census
  uses this visitor rather than substituting a final global metavariable context.
  [Visitor](https://github.com/leanprover/lean4/blob/v4.36.0-rc1/src/Lean/Elab/InfoTree/Util.lean#L44-L73),
  [context merge](https://github.com/leanprover/lean4/blob/v4.36.0-rc1/src/Lean/Elab/InfoTree/Basic.lean#L30-L40)

## Extractor-host initialization gap

`Mathlib/Data/Finset/Attr.lean:21` fails the v3 original pass with
`rule set 'finsetNonempty' already exists`, before any proof observations.
A normal fresh Lean CLI compilation with the same cached original setup
succeeds and emits fresh `.olean`, `.ilean`, and `.c` outputs. The command,
exit status, and logs are retained in
`.lake/census-finset-attr-diagnosis/cli-default/`; no dependency or production
outputs were changed. This is an extractor-host limitation, not a failure of
the pinned mathlib source.

The census executable imports `NormArith`, whose dependency closure already
contains this module. Aesop's rule-set declarations use process-global state:
`Aesop/Frontend/Extension/Init.lean:41–48` defines `declaredRuleSetsRef`;
`Frontend/Extension.lean:24–50` registers a rule set there and rejects duplicates;
`Frontend/Command.lean:25–31` performs that check before generating its
`meta initialize` command. These local sources are pinned at Aesop revision
`cbdde3aa2665915fb286c48bcd4cdf885c629511`.
[Registry](https://github.com/leanprover-community/aesop/blob/cbdde3aa2665915fb286c48bcd4cdf885c629511/Aesop/Frontend/Extension/Init.lean#L41-L48),
[duplicate check](https://github.com/leanprover-community/aesop/blob/cbdde3aa2665915fb286c48bcd4cdf885c629511/Aesop/Frontend/Extension.lean#L24-L50),
[command](https://github.com/leanprover-community/aesop/blob/cbdde3aa2665915fb286c48bcd4cdf885c629511/Aesop/Frontend/Command.lean#L25-L31)

Together, the source and CLI comparison support a collision with previously
initialized host state. The frozen run retains `original_elaboration_failed`;
it does not silently waive the declaration or count this file as extracted.

## Observed file deadline

The first-tier `Condensed/Light/Sequence.lean` process reached its 600-second
deadline after 600.05 seconds of wall time, 592.34 seconds of user CPU, and
3.01 seconds of system CPU, with 1.29 GB peak RSS. This shows CPU-active work;
it does not establish which elaboration or inspection step consumed the time.
The event ledger contains only `file_start`, so its proof-goal population is
unknown, rather than known to be empty. The recorded `file_timeout` receives
the predeclared serial 1,800-second retry. Final first-tier and retry outcomes,
not this intermediate observation, govern the census counts. Evidence remains
in `.lake/census-full-v3/files/Mathlib.Condensed.Light.Sequence/attempt-01/`.
The retained second attempt also times out: 1,800.075 seconds of wall time,
1,796.49 seconds of user CPU, and 1.284 GB peak RSS. Its ledger still contains
only `file_start`, so the file's goal population remains unknown.

## Final v3 evidence

The finished frozen run processed all 8,637 tracked files: 8,610 completed and
27 retained incomplete outcomes. All 19 scheduled second-tier attempts finished,
and final input verification is valid. This is a full file-attempt census, with
explicit gaps; it is not complete extraction from every file. It retains 40
isolated checked proposals from completed files, before combined source-patch
verification. The protocol hash is
`4750509079f8a5b198338b671451d09f4889b0210fe9d91b9bca331d24a2202e`.

The validated archive is `.lake/census-archive-final/`. Its compact payload is
10,869,293 bytes, and its full raw payload is 273,473,357 bytes. The full raw
archive preserves all 78,406 indexed files, including observations and failed
attempts. `archives.json` and the adjacent `.sha256` files record their hashes.
Independent inspection verified both archive hashes, every raw member name and
size against the source inventory, representative raw content hashes, all 8,637
unique file outcomes, and all 8,656 attempt records. No proposal was unattributed
and no file lacked extractor evidence.

The three remaining memory failures hit the 8 GiB runtime allowance. Their
known eligible observations leave 99 missing attempt outcomes: 75 in
`Analysis/Calculus/ContDiff/Bounds`, 21 in
`Analysis/Normed/Module/PiTensorProduct/InjectiveSeminorm`, and 3 in
`Probability/Distributions/Gaussian/HasGaussianLaw/Independence`. These are
unknown due to incomplete files, not solver failures. Other failed files may
have an unknown goal population even when their known eligible count is zero.

Every final incomplete source is listed below; paths are relative to `Mathlib/`.
The archived `file-outcomes.jsonl` contains their exact limits, process results,
and raw-evidence hashes.

| Final outcome | Source |
| --- | --- |
| `augmented_elaboration_failed` | `Analysis/Asymptotics/Arith.lean` |
| `augmented_elaboration_failed` | `Analysis/Asymptotics/Ring.lean` |
| `augmented_elaboration_failed` | `Analysis/LocallyConvex/Basic.lean` |
| `augmented_elaboration_failed` | `Analysis/Normed/Module/Seminorm/Basic.lean` |
| `file_timeout` | `Condensed/Light/Sequence.lean` |
| `original_elaboration_failed` | `Data/Finset/Attr.lean` |
| `original_elaboration_failed` | `Tactic/Bound/Init.lean` |
| `original_elaboration_failed` | `Tactic/Continuity/Init.lean` |
| `original_elaboration_failed` | `Tactic/Finiteness/Attr.lean` |
| `original_elaboration_failed` | `Tactic/SetLike.lean` |
| `partial_extraction` | `Combinatorics/Graph/Lattice.lean` |
| `partial_extraction` | `Combinatorics/SimpleGraph/Clique.lean` |
| `partial_extraction` | `Combinatorics/SimpleGraph/Walk/Operations.lean` |
| `partial_extraction` | `Computability/NFA.lean` |
| `partial_extraction` | `Data/Fin/Tuple/Basic.lean` |
| `partial_extraction` | `Data/Set/Sups.lean` |
| `partial_extraction` | `MeasureTheory/Integral/IntervalIntegral/AbsolutelyContinuousFun.lean` |
| `partial_extraction` | `RingTheory/DividedPowers/Padic.lean` |
| `partial_extraction` | `RingTheory/Localization/FractionRing.lean` |
| `partial_extraction` | `Tactic/FieldSimp/Discharger.lean` |
| `partial_extraction` | `Tactic/Positivity/Core.lean` |
| `partial_extraction` | `Topology/DiscreteSubset.lean` |
| `partial_extraction` | `Topology/Order/IntermediateValue.lean` |
| `partial_extraction` | `Topology/Order/IsLUB.lean` |
| `process_failed` | `Analysis/Calculus/ContDiff/Bounds.lean` |
| `process_failed` | `Analysis/Normed/Module/PiTensorProduct/InjectiveSeminorm.lean` |
| `process_failed` | `Probability/Distributions/Gaussian/HasGaussianLaw/Independence.lean` |
