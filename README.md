# norm-arith

A Lean tactic for norm estimates whose useful vector decomposition is hidden.
Search proposes rational coefficients; Lean checks the vector identity and norm
certificate before exact scalar arithmetic closes the goal.

```lean
module

import NormArith

example {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (x y : E) (a b : ℝ)
    (h₁ : ‖x + y‖ ≤ a) (h₂ : ‖x - y‖ ≤ b) :
    ‖x‖ ≤ (a + b) / 2 := by
  norm_arith

example {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (x y : E) : ‖x‖ - ‖y‖ ≤ ‖x - y‖ := by
  norm_arith
```

Use `norm_arith [facts]` to select norm facts explicitly. Local scalar
comparisons remain available. Omitted norm or distance premises are excluded
when specializing quantified facts. `norm_arith?` reports successful search.

## Build and check

With [elan](https://github.com/leanprover/elan) installed:

```sh
lake exe cache get
lake build --wfail
python3 -m unittest discover -s scripts
```

The project pins Lean **4.36.0-rc1** and mathlib commit
`2f3c7c8a8949b04a32f9303f59163acffb766996`.
`lake-manifest.json` also pins transitive dependencies.
The Lean checks cover exact search, certificate lemmas, successful proofs,
expected failures, and all six paper examples.
The library enables native metaprogram compilation. Its first native build can
also compile and link mathlib's native library; retain that setup cost separately
from warm file-compilation measurements.

## Supported fragment

The real-space core recognizes rational vector combinations and affine real
comparisons involving norms. It handles `≤`, `<`, `=`, distances, and local
vector equalities. Vector expressions that it cannot normalize remain opaque
atoms. Recognized rational scalar syntax uses real scalar multiplication, such
as `(2 : ℝ) • x`.

Structural certificates and a short decomposition search run first. The
reference fallback enumerates independent supports among every observed norm
argument, through the exact column rank. Its default per-target limits are
10000 subset attempts and 10000 results. Exhaustion is unknown. The paper proves
completeness of the mathematical reduction; it does not claim that a bounded
program always completes the enumeration.

Integer certificates also work in seminormed additive commutative groups.
A bounded signed-pair search supplies some dependent integer decompositions.
This extension has weaker guarantees; real homogeneity must not be assumed for
an arbitrary group. A separate upper-bound extension accepts opaque scalar
right sides. Products of norms and normalization of variable vector coefficients
are outside the complete real core.

Fact processing projects conjunctions, supplies real norm and min/max order
bounds, and specializes local quantified norm estimates. Specialization uses
observed vector terms and checked local, conjunction, or scalar-linear premises.
A fixed rewrite set normalizes distances, balls, closed balls, and the four
bounded interval types. It preserves scalar let names used as opaque products.
This heuristic permits at most 12 templates, 12 binders per template, 32 observed
vectors, 32 new bounds, and 128 attempts with at most 8 additive patterns each.
Premise construction has depth 4. Explicit-fact alias filtering conservatively
excludes expressions beyond depth 8 or 256 visited nodes.

A separate metric extension uses distance nonnegativity, symmetry, self-distance,
and triangle inequalities in pseudometric spaces. It collects at most 8 points total
from the goal and selected comparisons, then checks scalar consequences with
`linarith`. Space instances and recognized comparisons determine routing. If a
metric attempt fails, it restores the proof state and continues through the norm
pipeline. Both extensions are bounded heuristics; the paper's real-core theorem
is unchanged.

Norm decompositions use the same certificate builder and proved lemmas; the
metric path uses proved distance lemmas and checked scalar arithmetic.
No additional axioms, `sorry`, `unsafe`, or `native_decide` are used in the tactic.

## Paper and evaluation

The [paper source and build instructions](paper/README.md) produce a short
NeurIPS workshop-style PDF, with checked Lean examples and technical appendices.
The [paper plan](docs/PAPER-PLAN.md) states the agreed scope and success criteria.

Expansion work has a [verified local patch](benchmarks/expansion/README.md)
that saves **310 net code lines** across **87 replacements in 46 files**.
The original proof blocks use 582 code lines; replacements use 226, and 46
added imports are charged. The final targeted follow-up processed 885 files:
875 completed, ten remain incomplete, and 158 isolated proposals were checked.
The patch combines census proposals with replacements composed outside the census.
AI coding agents helped develop and review the source edits.
Forty predeclared paired measurements give a **1.072× speedup** in warm Lean
compilation across all 46 affected files, with a conditional 95% block-BCa
interval of **1.067–1.081×**. Mean pass time decreases from **131.19 to 122.33
seconds**, including tactic search, imports, and fresh compiler outputs.
Seven files became slower and remain in the aggregate.
The interval assumes independent, representative four-pair blocks. Machine
conditions were observed through snapshots; ordinary background activity was
uncontrolled. Native-library setup is recorded separately.

The historical local mathlib patch has **16 replacements in 10 files**. It removes
**41 net code lines**: 67 proof lines become 16, with 10 added imports and no
helpers. The census processed all 8,637 tracked files; 27 file outcomes remain
incomplete. These are local patch savings; the patch has not merged into mathlib.

For that historical patch, forty predeclared paired measurements give a **1.105× speedup** in warm Lean
compilation of the affected files (95% block-bootstrap interval
**1.095–1.112×**). Mean pass time decreases from 34.82 to 31.51 seconds. Timing
includes tactic search and every affected file. It includes the effect of native
imports; cold native-build cost was not fully recorded. The interval assumes
independent, representative timing blocks.

See [the current source results and scope](benchmarks/expansion/RESULTS.md),
[the historical results](benchmarks/FINAL-RESULTS.md),
[the expanded paper](paper/output/pdf/paper.pdf), and
[harness documentation](scripts/README.md). The
[earlier prototype pilot](benchmarks/RESULTS.md) remains archived: it saved
36 net lines and compiled 6.3% slower. It uses an earlier implementation and
workload.

The release keeps compact evidence and checked compressed transports in Git.
Deep raw census and intermediate verification archives remain local and are
Git-ignored; see [evidence packaging](docs/CENSUS-ARCHIVE.md).

## Project files

| File | Role |
| --- | --- |
| `NormArith/Search.lean` | Exact rational elimination, short search, and finite reference enumeration |
| `NormArith/Certificate.lean` | Proved norm-certificate lemmas |
| `NormArith/Metric.lean` | Checked distance constraints on a bounded set of points |
| `NormArith/Tactic.lean` | Recognition, local facts, normalization, search, and checked proof construction |
| `NormArithTest/` | Search, certificate, integration, and paper checks |
| `benchmarks/` | Final result summary and archived prototype measurements |
| `artifacts/` | Validated census archives, timing evidence, and independent checks |
| `scripts/` | Census and paired full-file measurement tools |
| `paper/` | LaTeX, bibliography, generated evidence, language audit, and PDF build |
| `docs/adr/` | Scope and evaluation decisions |

[UPSTREAM.md](docs/UPSTREAM.md) describes the route to a mathlib contribution.
This is an independent implementation informed by existing norm-arithmetic
methods; Isabelle ML code is not bundled. License: Apache-2.0.
