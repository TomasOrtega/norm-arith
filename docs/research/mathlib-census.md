# A systematic mathlib census for norm arithmetic

Research date: 20 October 2026. This note uses primary Lean/REPL sources and the
local pinned project. No extraction pass, compiler experiment, or new benchmark
was run for this investigation.

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

## Recommended census protocol

1. Freeze the mathlib/Lean/extractor revisions and source universe. The default
   universe should be tracked `Mathlib/**/*.lean`; list whether generated files,
   `MathlibTest`, `Archive`, and dependencies are outside it. Record one outcome
   for every file, including extraction errors and resource exhaustion.
2. Extract both tactic-goal and proof-term expected-type information. A
   tactic-only census misses term-style proofs and some `calc` steps. Filter
   actual expressions by the declared supported norm-inequality fragment rather
   than pretty-printed strings. Keep raw counts before filtering.
3. Deduplicate macro-generated and nested observations using original source
   ranges, declaration identity, and goal fingerprints. Exclude observations
   from abandoned elaboration alternatives. Preserve unresolved/generated
   ranges as an explicit noneditable category, rather than inventing source
   positions. The core retains some information while backtracking, so merely
   traversing every node does not identify distinct source obligations.
   [InfoTree backtracking behavior](https://github.com/leanprover/lean4/blob/v4.36.0-rc1/src/Lean/Elab/InfoTree/Basic.lean)
4. Try the same tactic procedure everywhere: declared norm-bound selection,
   deterministic source order, fixed preprocessing grammar, and heartbeat/time
   limits. The existing explicit-bound interface and counted preparation remain
   compatible with this approach. Separate direct successes from successes that
   require the permitted preparation.
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

## Decisions for the expanded project

- Choose the coverage claim: a full semantic census of eligible source-backed
  obligations, or a narrower census of all resolved references to a declared
  lemma family. The former better supports a broad “all mathlib” ambition and
  requires processing the entire source universe.
- Define which new mathematical fragments and deterministic preparation rules
  belong to the procedure. A manual preparation allowance can be retained, but
  it must have a finite protocol if the paper claims exhaustive attempts.
- Decide whether the paper requires a positive compilation-speed result, or
  treats speed as a measured outcome while proof simplification remains primary.
  The latter was the prior agreement; a positive ratio cannot be guaranteed in
  advance.
