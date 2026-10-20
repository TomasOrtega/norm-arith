# Prove soundness in Lean and mathematical completeness in the paper

Require Lean-checked normalization and certificate soundness, plus a mathematical
completeness proof for the declared real norm-arithmetic fragment. An end-to-end
Lean formalization of search completeness is outside the first paper's required
deliverables. Resource exhaustion returns unknown, not a mathematical rejection.

The core can use vector-equality assumptions, but its advertised conclusions
remain scalar comparisons involving norms. Do not infer vector equality from
zero norm in a seminormed space. State completeness relative to the declared
grammar and recognized assumptions rather than hidden properties of opaque
expressions.
