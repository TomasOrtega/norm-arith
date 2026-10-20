# Base the paper on a general tactic and a semantic mathlib census

The paper targets proof-assistant researchers. Its contributions are a general
Lean tactic, a precise supported fragment and correctness arguments, and a
systematic mathlib evaluation; algorithmic novelty requires evidence from the
related-work review.

Coverage means every eligible source-backed goal found during complete
elaboration of a pinned mathlib revision, under published preparation and
resource limits. Record extraction failures, tactic failures, overlapping
replacements, and no-saving outcomes. The existing mathlib proofs remain the
comparison baseline.

For the paper phase, an aggregate affected-file compilation speedup over the
existing proofs is a required success criterion. Improving only the prototype
does not meet it. This raises the prototype-phase criterion in
[ADR-0001](0001-measure-real-mathlib-replacements.md); the existing slowdown
remains valid evidence and must be reported.

The required speedup includes search by actual `norm_arith` calls. If implemented,
generated-certificate replay is a separate mode and a separate efficiency result.

Use a predeclared confirmatory paired experiment for the speedup claim. The
primary measure is original mean total affected-file compilation time divided
by replacement mean total time. Its paired 95% confidence interval must lie
entirely above one. Freeze code, patch, sample count, and analysis first; do not
extend the run until significance appears. Retain medians and per-file results
as descriptive evidence. This replaces the pilot's median ratio as the primary
paper metric without changing the recorded pilot results.
