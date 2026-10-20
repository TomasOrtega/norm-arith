# Put automatic bound discovery behind the default tactic interface

The paper's tactic defaults to bare `norm_arith`, selecting relevant local bounds
automatically. Retain `norm_arith [facts]` for explicit control. Normalization,
bound selection, search, and certificate construction belong behind this small
interface rather than in repeated preparation by callers.

This extends the explicit-only initial interface in
[ADR-0002](0002-initial-tactic-fragment.md). The exact supported fragment and
preparation rules still need to be settled before implementation.
