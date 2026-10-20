# Share normalized input and checked certificates across solver paths

Use one normalized rational representation and one checked certificate layer
for the real norm-arithmetic core. Implement a complete finite-constraint
reference algorithm and reuse existing mathlib scalar arithmetic. Its
mathematical completeness obligation remains the one in
[ADR-0007](0007-paper-completeness-and-checked-soundness.md).

Optimized paths use the same interface and retain the reference fallback.
Check them against the reference and accept performance changes through
whole-file measurements. This keeps one correctness boundary while allowing
search and certificate generation to improve independently.

The additive-group extension remains sound with weaker guarantees, as specified
in [ADR-0005](0005-core-fragment-and-group-extension.md).
