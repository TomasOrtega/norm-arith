# Measure real mathlib replacements before expanding the tactic

Develop the tactic around actual mathlib proof replacements, adding capabilities
as those examples require rather than making Isabelle feature parity the first
milestone. Proof simplification is the primary goal; compilation speed is a
measured secondary goal, and a useful replacement may compile more slowly.

The first deliverable is a reproducible replacement patch against a pinned mathlib
revision. Describe its proof-line savings as proposed until the changes merge
upstream. Initial speed claims concern compilation of affected files; individual
proof timings are separate evidence, and any claim about all of mathlib requires
a whole-build measurement. Report measured slowdowns as well as speedups.
