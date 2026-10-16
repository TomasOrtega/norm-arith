# Developing this into a mathlib contribution

This is a standalone prototype. Build confidence in a small, useful fragment before
proposing a new mathlib tactic. This guide follows the official contribution pages
linked below, checked on 16 October 2026; recheck them before submitting.

## 1. Finish and measure the prototype

Keep rational vector normalization, certificate search, and Lean proof construction
separate. Search may fail or time out; every successful result must produce a proof
checked by Lean. Explain the supported fragment and failure cases in the tactic's
docstring. Do not claim completeness from a collection of successful examples.

Add examples where the useful vector decomposition is absent from the goal syntax.
Include negative coefficients, dependent generators, zero vectors, rational bounds,
and expected failures. Make the search limit predictable and failure messages useful.
Keep unsupported symbolic coefficients outside the initial promise.

## 2. Demonstrate value on actual mathlib proofs

Start with the norm estimates in `Analysis/Convex/Uniform.lean` and
`Analysis/Calculus/FDeriv/Measurable.lean`; links are in [REFERENCES.md](REFERENCES.md).
These are candidate benchmarks, not claims that the starter already replaces them.
For each example, record the mathlib revision, theorem, original proof, replacement,
and elapsed time or heartbeats. Compile both versions in the same checkout.

Compare with a short manual proof and current `bound`, `grind`, and existing lemmas.
Show a benefit from discovering decompositions, beyond renaming existing automation.
Retain the examples that expose that benefit as regression tests.

## 3. Discuss scope, then prepare a small PR

Discuss the working prototype in the Lean Zulip `#mathlib` channel. Explain, in your
own words, the supported fragment, certificate strategy, examples, timings, and
relationship to existing tactics. Ask for feedback on placement and maintenance.
Mathlib's [contribution guide][contribute] recommends discussion of unfamiliar work
and explicitly recognizes standalone projects as a useful development route.

On a branch of a current mathlib fork, a plausible initial layout is:

- `Mathlib/Tactic/NormArith.lean`: user-facing syntax and implementation entry point.
- `Mathlib/Tactic/NormArith/`: supporting files if the implementation needs splitting.
- `MathlibTest/norm_arith.lean`: positive, negative, and regression examples.

Use focused imports. A tactic importing normed-space theory should not be added to
`Mathlib/Tactic/Common.lean`, whose purpose is to avoid substantial theory imports.
Follow existing tactic files for module structure and mathlib's [style guide][style]
for headers, docstrings, namespaces, and formatting. Update the tactic import index
as appropriate and run `lake exe mk_all` to regenerate `Mathlib.lean`.

Build the affected modules and tests, resolve linter warnings, and let mathlib CI
validate integration. Follow the [PR workflow][workflow]. Keep a first PR focused on
one usable fragment; broad proof replacements and further features can follow.

## AI assistance and attribution

This starter was generated with ChatGPT. Before contributing it, understand and be
able to justify all code and design decisions yourself. Mathlib's current
[AI policy][ai] requires the PR description to disclose the tools used and how they
were used. Substantial LLM-generated code also needs the `LLM-generated` label,
which contributors can request with a comment containing `LLM-generated`.
The policy prohibits using an LLM to write GitHub or Zulip comments: write those
yourself. This document is a development guide, not a discussion or PR template.

Credit Isabelle's `norm` procedure as an algorithmic reference. The intended Lean
implementation is independent; Isabelle ML code is not included in this starter.
See [REFERENCES.md](REFERENCES.md) for the implementation and historical sources.

[contribute]: https://leanprover-community.github.io/contribute/index.html
[workflow]: https://leanprover-community.github.io/contribute/how-to-contribute.html
[style]: https://leanprover-community.github.io/contribute/style.html
[ai]: https://leanprover-community.github.io/contribute/index.html#use-of-ai
