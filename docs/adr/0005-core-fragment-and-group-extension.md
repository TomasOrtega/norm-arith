# Separate the real norm-arithmetic core from the additive-group extension

The paper's core handles rational vector combinations and linear arithmetic
involving norms and scalar variables, including equalities, strict inequalities,
and distances. Products of norms and normalization of variable vector
coefficients remain outside the core.

Retain arbitrary seminormed additive groups as a sound extension with explicitly
weaker guarantees. Real homogeneity and rational averaging are not valid rules
for arbitrary normed groups, so one completeness claim cannot silently cover
both settings. [ADR-0007](0007-paper-completeness-and-checked-soundness.md)
specifies the paper's completeness obligation and treatment of vector equalities.
