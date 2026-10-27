# From norm arithmetic to automated analytic estimates

**Design proposal for norm-arith**  
**Date:** 27 October 2026  
**Status:** Implemented for the bounded APIs recorded in [progress.md](progress.md). See [results.md](results.md) for measurements. This document keeps the original design and its open research questions. The baseline below is the pre-feature-branch implementation; proposed names are mapped to the actual public modules on the progress page.

## 1. Objective

Extend `norm_arith` into a system that can compose analytic estimates, choose useful intermediate norms and admissible parameters, absorb error terms, and produce short Lean proofs with explicit constants.

The intended input is a target estimate together with the analytic facts that make it true. These facts may include boundedness of an operator, a Sobolev embedding, a product estimate, an energy inequality, or a smallness assumption. The system should determine how to combine them. It should also establish routine side conditions when the local context and registered theorems provide the necessary information.

The long-term target is substantial estimate blocks in analysis and PDE formalizations. Examples include an elliptic energy estimate with a lower-order perturbation, a contraction argument for a nonlinear integral equation, and stability or residual bounds for its solution.

The proposal has three mathematical components:

1. An exact linear programming core for rational-linear norm and seminorm arithmetic.
2. A theorem-guided layer for products, operators, integrals, interpolation, and absorption.
3. An optional quadratic-certificate layer for Hilbert-space estimates.

A second use of linear programming selects Hölder exponents and interpolation weights within explicitly defined parameter fragments. The analytic theorems themselves remain proved library results.

Success means that a user can express the mathematical ingredients of an estimate and let the tactic supply the routine composition. Every successful invocation must produce a proof checked by Lean. The implementation must retain control over constants, hypotheses, and search cost.

## 2. Starting point and compatibility

The baseline is repository commit [`177a21d`][repo-commit], which pins mathlib commit `2f3c7c8a8949b04a32f9303f59163acffb766996`.

The current architecture already separates the essential responsibilities:

| Existing component | Role |
| --- | --- |
| `NormArith/Search.lean` | Exact rational elimination, short decomposition search, and bounded independent-support enumeration |
| `NormArith/Certificate.lean` | Proved triangle, homogeneity, and finite linear-combination certificates |
| `NormArith/Tactic.lean` | Recognition, normalization, local facts, search orchestration, and proof construction |
| `NormArith/Metric.lean` | A separate bounded metric-arithmetic path |
| `NormArithTest/` and `benchmarks/` | Correctness checks and evaluation infrastructure |

The real-space core recognizes rational vector combinations and affine scalar comparisons involving norms. Its fallback enumerates decompositions for observed norm arguments, builds their proofs, and passes the resulting inequalities to `linarith`. The implementation also has separately bounded extensions for additive groups, metrics, and local fact specialization. [Search][repo-search], [Tactic][repo-tactic], and [Certificate][repo-certificate] are the relevant source files.

The proposed LP backend replaces decomposition enumeration within the real-space core. The existing certificate boundary remains useful. The current inexpensive structural path should run before the more general solver.

Preserve the public forms:

```lean
norm_arith
norm_arith [h₁, h₂]
norm_arith?
norm_arith? [h₁, h₂]
```

Preserve their established fact-selection semantics. In particular, a norm hypothesis omitted from an explicit fact list must not re-enter through analytic rule specialization. Local scalar comparisons may remain available according to the current contract.

Use a separate frontend, provisionally called `analytic_estimate`, for the broader search over analytic lemmas. This frontend should invoke the same arithmetic core. Heavy analytic rule packs should be optional imports.

The initial performance comparison should retain the pinned mathlib version. A simultaneous dependency upgrade would obscure the effect of the new solver.

## 3. The compact linear programming core

### 3.1 The mathematical fragment

Fix vector atoms $x_1,\ldots,x_d$ in a real seminormed vector space. Normalize every observed vector expression into

$$
v_i=\sum_{k=1}^{d} a_{ik}x_k,
\qquad a_i\in\mathbb Q^d,
\qquad 1\le i\le m.
$$

The coefficients $a_{ik}$ are known rational numbers. The atoms need not be linearly independent. The underlying vector space can be infinite-dimensional.

The scalar hypotheses and target are affine comparisons involving the values $\|v_i\|$ and additional scalar variables, with rational coefficients. Equality and strict inequality are allowed. For an inequality goal, prove inconsistency of its hypotheses and its negation. Split an equality goal into its two weak inequalities and certify each separately. Equality hypotheses can be represented by two opposite weak inequalities.

This fragment includes

$$
2\|u+v\|-\|u-v\|\le A,
\qquad
B\le\|u\|,
$$

with symbolic scalar bounds $A,B$. A product of two varying scalar quantities, such as $C\|u\|$, lies outside this linear fragment. It may be treated as an opaque scalar atom for sound, incomplete reasoning, or handled using additional proved relations. The completeness and countermodel guarantees apply only when the encoding omits no relationships required by the interpretation of its atoms.

Known rational-linear vector equalities are handled explicitly as described in Section 3.4. Vector disequalities and arbitrary Boolean combinations require additional preprocessing and are outside the first implementation target.

### 3.2 An extended LP for finite norm observations

Introduce real variables

$$
r_i\in\mathbb R,
\qquad
f_i\in\mathbb R^d,
\qquad 1\le i\le m.
$$

The variable $r_i$ represents $\|v_i\|$. Impose

$$
r_i\ge0,
\qquad
f_i\cdot a_i=r_i,
\qquad
-r_j\le f_i\cdot a_j\le r_j
\quad\text{for all }i,j.
$$

All coefficients are rational constants. The additional variables $f_i$ represent supporting linear functionals on the formal coordinate space.

Replace observed norms in the scalar formulas by the corresponding $r_i$, append those formulas, and search for a certificate of inconsistency.

The norm portion has $m(d+1)$ variables and $O(m^2)$ constraints. A dense representation has up to $O(m^2d)$ coefficient entries. This is a bound on the formulation size. It is not a runtime bound for simplex or for Lean proof reconstruction.

### 3.3 Finite realization theorem

**Proposition.** Let $m\ge1$ and $a_1,\ldots,a_m\in\mathbb Q^d$. For real numbers $r_1,\ldots,r_m$, the following are equivalent:

1. There exist a real normed vector space $E$ and vectors $x_1,\ldots,x_d\in E$ such that
   $$
   \left\|\sum_k a_{ik}x_k\right\|=r_i
   \quad\text{for every }i.
   $$
2. There exist $f_1,\ldots,f_m\in\mathbb R^d$ satisfying the LP constraints above.

The same finite norm values can be realized in the concrete space $\ell_\infty^m$.

**Proof of 1 implies 2.** For each $v_i=\sum_k a_{ik}x_k$, choose a real linear functional $\phi_i$ with

$$
|\phi_i(x)|\le\|x\|,
\qquad
\phi_i(v_i)=\|v_i\|.
$$

Set $(f_i)_k=\phi_i(x_k)$. Linearity gives the constraints. The required supporting-functional result is a Hahn–Banach consequence. Mathlib has `exists_dual_vector''` for seminormed spaces, including the zero case. [Hahn–Banach][hahn-banach]

**Proof of 2 implies 1.** Define the vector $x_k\in\mathbb R^m$ by

$$
(x_k)_i=(f_i)_k,
$$

and equip $\mathbb R^m$ with the sup norm. The $i$-th coordinate of $v_j=\sum_k a_{jk}x_k$ is $f_i\cdot a_j$. Every coordinate has absolute value at most $r_j$, and the $j$-th coordinate equals $r_j$. Therefore $\|v_j\|_\infty=r_j$.

This explicit realization avoids a quotient construction and is a convenient target for a Lean formalization.

An equivalent seminorm construction on $\mathbb R^d$ is

$$
p(z)=\max_i |f_i\cdot z|.
$$

It satisfies $p(a_j)=r_j$. Both descriptions explain why the finite norm constraints are sufficient.

**Consequence.** For a conjunction of scalar linear comparisons in this fragment, LP feasibility is equivalent to realizability in some real normed space. Unsatisfiability of the hypotheses and negated goal characterizes the implications that follow from generic normed-space structure.

A prescribed space may have additional properties. For example, this theorem does not make the generic solver complete for Euclidean geometry or for a particular function norm. Those properties enter through additional rules.

### 3.4 Local vector equalities

Suppose the context also provides

$$
\sum_k e_{hk}x_k=0,
\qquad e_h\in\mathbb Q^d.
$$

There are two sound implementations:

- Normalize the formal coordinate space modulo the rational span of the relation rows $e_h$.
- Keep the original coordinates and add $f_i\cdot e_h=0$ for every supporting functional and every relation.

The second implementation directly preserves the concrete realization theorem: the constructed sup-norm vectors satisfy every supplied vector equality.

Certificate reconstruction must retain the proofs of these relations. A coordinate identity modulo the relation span becomes a true vector identity by substituting the corresponding Lean equalities.

For explicit seminorms, do not infer $x=y$ merely from $p(x-y)=0$. A seminorm can have a nontrivial kernel.

### 3.5 Several seminorms

For seminorms $p_1,\ldots,p_s$ on the same vector space, use a separate supporting-functional family for each $p_\ell$. All families share the normalization of the vector expressions and the exact vector relations.

The construction

$$
p_\ell(z)=\max_i |f_{\ell,i}\cdot z|
$$

realizes the finite observations for arbitrary seminorm families on a common formal vector space. With vector relations present, assign $x_k$ to the column $(f_{\ell,i,k})_{\ell,i}$ in the common product coordinate space, and let $p_\ell$ be the sup seminorm on its $\ell$-th block. Every functional annihilates the relation rows, so the assigned vectors satisfy the actual vector equalities. Consequently, the generic finite-seminorm fragment admits the same kind of exact encoding.

Instantiated comparisons such as

$$
p_1(u)\le 3p_2(u)+B
$$

become scalar rows. A universally quantified analytic comparison must first be instantiated through a checked theorem application. A feasible assignment to a finite set of such instances does not establish a model satisfying the original universal analytic theorem.

If several functionals must each be genuine norms on the same space, their kernels must be compatible. Independent seminorm blocks remain a sound proof-search relaxation, but a completeness claim for that stronger class requires further work.

### 3.6 Complex spaces

Real or rational coefficient combinations can be handled in complex normed spaces by restriction of scalars. Their generic finite realization also works in $\mathbb C^m$ with the sup norm, using the same real coordinate values.

A broader fragment with arbitrary complex coefficients requires additional structure. For complex-linear supporting functionals, constraints involving a complex modulus are generally second-order cone constraints rather than linear constraints. Simple phase and modulus identities can be added as certified rules, but the rational LP completeness theorem should retain its stated coefficient fragment.

## 4. Reconstructing elementary certificates

The supporting-functional variables are search data. The generated Lean proof can use vector identities, triangle inequality, scalar homogeneity, and scalar arithmetic.

### 4.1 A certificate with nonnegative multipliers

Use the equivalent weak inequalities

$$
r_i-f_i\cdot a_i\le0,
$$

$$
f_i\cdot a_j-r_j\le0,
\qquad
-f_i\cdot a_j-r_j\le0.
$$

The first inequality becomes equality because the second family includes $j=i$.

Let an LP contradiction certificate use nonnegative rational multipliers $\alpha_i$, $\beta_{ij}^{+}$, and $\beta_{ij}^{-}$ for these rows. Elimination of every coordinate of $f_i$ gives

$$
\alpha_i a_i
=
\sum_j(\beta_{ij}^{+}-\beta_{ij}^{-})a_j.
$$

With vector relation rows present, this identity may include an additional rational combination of the $e_h$. Those terms vanish by the supplied vector equalities.

Lean checks the corresponding vector identity

$$
\alpha_i v_i
=
\sum_j(\beta_{ij}^{+}-\beta_{ij}^{-})v_j
$$

and then proves

$$
\begin{aligned}
\alpha_i\|v_i\|
&\le \sum_j|\beta_{ij}^{+}-\beta_{ij}^{-}|\|v_j\|\\
&\le \sum_j(\beta_{ij}^{+}+\beta_{ij}^{-})\|v_j\|.
\end{aligned}
$$

The second step uses $\beta_{ij}^{+},\beta_{ij}^{-}\ge0$. There is no division by $\alpha_i$, so the zero case is included.

This is precisely the scalar contribution of the eliminated functional block. Combining these inequalities with the input scalar rows yields the final contradiction.

### 4.2 Soundness theorem to formalize first

Formalize a finite certificate lemma with these inputs:

- A family of real seminorms and vector expressions.
- Rational coefficients for vector combinations.
- Proofs of the relevant vector identities.
- Nonnegative rational row multipliers.
- Proved scalar premises.
- A checked arithmetic identity yielding a contradiction, with its strictness information.

Its conclusion is the requested scalar comparison.

The proof should not depend on the optimizer, its pivot rule, the supporting-functional existence theorem, or a numerical tolerance. Search may fail or produce invalid output. Invalid output must fail certificate checking.

The finite realization theorem establishes the mathematical completeness of the encoding. The elementary certificate theorem establishes the soundness of accepted output. These are separate deliverables.

### 4.3 Reusing the existing simplex oracle

Mathlib already exposes an exact certificate oracle for `linarith`. The pinned implementation uses integer-coefficient comparison rows and a simplex-based search for a nonnegative combination yielding a contradiction. [Linarith interface][linarith-data], [Simplex oracle][simplex]

The adapter should:

1. Encode the norm problem as data.
2. Clear rational denominators using positive factors and retain those factors in row provenance. A multiplier on a scaled integer row must be translated back to the original rational row with its scale.
3. Expand equality rows into two weak inequalities when needed.
4. Preserve strict comparisons from the input and the negated goal.
5. Respect the oracle's constant coordinate and include the true row $-1<0$, or an explicitly equivalent construction. This permits a contradiction involving only weak input inequalities to become a zero linear combination with a positively weighted strict row.
6. Obtain row multipliers.
7. Check the identities exactly and extract norm certificates.
8. Elaborate only the selected proof.

Do not pass fictitious supporting-functional inequalities to `linarith` as though they were established Lean hypotheses. Either reconstruct the elementary certificates as above or separately prove and instantiate legitimate supporting witnesses.

The existing oracle reports contradiction certificates. Its failure interface does not provide a feasible assignment. Countermodel diagnostics therefore require a separate extension.

### 4.4 Replay

A successful `norm_arith?` should emit a proof or explicit certificate that can be replayed without repeating LP or analytic search.

Replay should store exact rational data and refer to stable source facts. It must recheck vector identities and scalar combinations. It should not silently fall back to search.

A stale certificate may legitimately fail after the theorem or its premises change. For unchanged source, replay should give predictable checking cost. Search, reconstruction, and replay must be measured separately.

## 5. A common interface for norms and seminorms

### 5.1 Reuse the mathematical hierarchy

Mathlib already provides `Seminorm`, `SeminormClass`, composition with linear maps, sums, and suprema. Use these structures where appropriate. [Seminorms][seminorms]

An internal adapter can package expressions and proof-producing operations without introducing a competing hierarchy of mathematical objects.

For each observed norm family, retain:

- The actual functional or norm instance.
- The domain and scalar field.
- Every relevant parameter, including measure, set, exponent, weight, or derivative order.
- The codomain of the functional.
- The applicable nonnegativity, subadditivity, and homogeneity laws.
- The domain or finiteness conditions under which those laws apply.

The key identifies a mathematical expression, not merely its ambient Lean type. In particular, $L^p(\mu)$, $L^q(\mu)$, and $L^p(\nu)$ observations must remain separate.

### 5.2 First supported families

The first adapters should cover:

- Ordinary `Norm.norm` expressions.
- Explicit real seminorms.
- Seminorms pulled back along certified linear maps.
- Finite sums and maxima of seminorms.
- Bundled `Lp` norms for $1\le p\le\infty$.
- Raw `lpNorm` and `eLpNorm` observations when their required domain conditions have been proved.

A derivative seminorm such as $u\mapsto\|D^\alpha u\|_p$ should be introduced on a suitable vector space of functions or through local theorems that establish the required derivative identities. The notation alone does not establish linearity.

Generic arithmetic over a bundled normed space should not unfold the definition of the norm into integrals, suprema, or Fourier coefficients.

### 5.3 Finiteness and extended values

`eLpNorm` is extended-nonnegative-real valued. Real `lpNorm` is its `toReal` conversion, and mathlib proves `lpNorm_of_not_memLp`. Thus raw `lpNorm` is not a global seminorm on unrestricted functions. [Real-valued Lp norms][lp-norm]

An adapter should establish and cache relevant `MemLp`, measurability, and finiteness facts. It may apply suitable inequalities in `ENNReal` before converting a finite arithmetic problem to real scalars.

Support the endpoint $p=\infty$ explicitly. Handle zero functions and zero measures according to the actual library theorems. Below $p=1$, use a separate quasi-norm rule family rather than ordinary triangle certificates.

## 6. The analytic rule layer

A registered analytic rule is a proved theorem together with enough indexing information to identify useful instances. Its application produces an ordinary Lean theorem application and explicit premise obligations.

Initial rule families should include:

| Family | Typical conclusion |
| --- | --- |
| Bounded linear maps | $\|Tu\|_Y\le C\|u\|_X$ |
| Bounded bilinear maps | $\|B(u,v)\|_Z\le C\|u\|_X\|v\|_Y$ |
| Finite sums and integrals | A norm bounded by a sum or integral of norms |
| Hölder | A product or pairing bounded by suitable function norms |
| Young | A product bounded by weighted powers |
| Interpolation | An intermediate norm bounded by powers of endpoint norms |
| Embeddings | A supplied Sobolev, Poincaré, or other comparison |
| Monotonicity | Replacement of nonnegative factors by proved bounds |

Mathlib already supplies operator-norm and bilinear Hölder infrastructure. [Operators][operators], [Hölder][holder]

### 6.1 Controlled term generation

The broad frontend should be goal-directed:

1. Inspect the target and selected hypotheses.
2. Identify which rule conclusions can match the required expressions.
3. Generate a bounded collection of useful intermediate expressions.
4. Prove rule premises from established facts and side-condition procedures.
5. Add the resulting certified inequalities to the arithmetic problem.
6. Stop when a complete proof is found or a documented budget is exhausted.

Useful expansions include

$$
B(u,v)-B(u',v')
=
B(u-u',v)+B(u',v-v')
$$

and distribution of certified linear maps through sums. These transformations should be registered with their proofs and selected deliberately. Unrestricted algebraic expansion can make both search and proof terms unnecessarily large.

### 6.2 Scope and proof dependencies

Cache facts within their actual local context. Deduplicate equivalent expressions and repeated theorem instances. Record which facts justify each new fact.

The justification graph must be acyclic. A rule cannot use its own intended conclusion to discharge a premise. The graph of mathematical inequalities can contain cycles: inequalities such as $p(u)\le Cq(u)$ and $q(u)\le Dp(u)$ can legitimately coexist.

Explicit fact selection must constrain this layer as well as the final solver. Diagnostics should identify an unmet analytic premise instead of silently strengthening the assumptions.

### 6.3 Existing tactics as components and baselines

Use `positivity`, `gcongr`, algebraic normalization, and appropriate existing search machinery for their established roles. Mathlib's `bound` tactic already applies registered inequalities and uses arithmetic at its leaves. [Bound][bound]

The new system should add joint norm reasoning, parameter selection, and reusable certificates while cooperating with that infrastructure.

## 7. Symbolic constants and nonlinear scalar expressions

PDE estimates contain products and powers even when the final bookkeeping is linear. A practical implementation should distinguish three cases.

**Linear scalar consequences.** Expressions such as $2A-3B\le C$ go directly to the LP core.

**Nonlinear expressions with an available relationship.** After proving Young's inequality, an expression such as $\nu D^2$ can be a scalar atom. The final linear combination can use it without solving general nonlinear arithmetic.

**Relationships that still need proof.** From $0\le C\le C_0$ and $0\le A\le A_0$, the inequality $CA\le C_0A_0$ requires monotonicity. Merely naming $CA$ and $C_0A_0$ as independent atoms loses that implication.

Use sign-aware rewriting, monotonicity, multiplication of proved inequalities, and a bounded nonlinear-arithmetic fallback where appropriate. Keep symbolic vector coefficients outside the complete rational-vector core unless a dedicated rule reduces them.

### 7.1 Young and a single absorption

Given

$$
E+\nu D^2\le FD,
\qquad \nu>0,
$$

a rule supplies

$$
FD\le\frac{\nu}{2}D^2+\frac{F^2}{2\nu}.
$$

The arithmetic core concludes

$$
E+\frac{\nu}{2}D^2\le\frac{F^2}{2\nu}.
$$

For this final step, use scalar atoms $E$, $X=\nu D^2$, and $Y=F^2/\nu$. Mathlib has Young inequalities in several scalar domains. A convenient parameterized wrapper can expose the form used by this rule. [Young inequalities][young]

Parameter selection should initially use explicit templates, such as spending one half of an available positive coefficient. For several error terms, rational fractions can satisfy an absorption budget. Joint optimization over arbitrary symbolic powers or denominators is a larger problem.

### 7.2 Coupled absorption

The LP core is particularly useful when several estimates depend on one another. For example,

$$
A\le F+\frac14B,
\qquad
B\le G+\frac12A
$$

imply

$$
A\le\frac87F+\frac27G,
\qquad
B\le\frac47F+\frac87G.
$$

For the first conclusion, combine the first input inequality with one quarter of the second. For the second, combine one half of the first with the second.

This is a useful benchmark because the solver must combine available estimates jointly. The constants are sharp relative to these two scalar constraints. They need not be sharp for the underlying PDE, whose additional structure may supply stronger information.

## 8. Selecting exponents and interpolation parameters

### 8.1 Linear parameter fragments

For Hölder,

$$
\frac1r=\frac1p+\frac1q.
$$

For interpolation between fixed endpoint exponents,

$$
\frac1p=\sum_i\frac{\theta_i}{p_i},
\qquad
\theta_i\ge0,
\qquad
\sum_i\theta_i=1.
$$

These constraints are linear in reciprocal exponents and weights when the endpoint exponents are fixed. The solver can find exact rational parameters and instantiate the corresponding analytic theorem.

Its search must also include every side condition of that theorem, such as admissible ranges and excluded endpoints. An arithmetic solution to the exponent equations is not enough by itself.

If both a weight and its endpoint reciprocal exponent vary, their product is not automatically linear. The first version should choose among a finite inventory of available endpoint estimates and theorem patterns.

### 8.2 A basic interpolation benchmark

Given $u,v\in L^2\cap L^6$, seek an $L^2$ estimate on $uv$. One admissible choice is

$$
\|uv\|_2\le\|u\|_4\|v\|_4.
$$

The equation

$$
\frac14=\frac{\theta}{2}+\frac{1-\theta}{6}
$$

gives $\theta=1/4$. Interpolation then yields

$$
\|uv\|_2
\le
\|u\|_2^{1/4}\|u\|_6^{3/4}
\|v\|_2^{1/4}\|v\|_6^{3/4}.
$$

The tactic should report the chosen exponents and the theorem instances used. It need not claim that this symmetric choice is the unique or optimal route.

### 8.3 Mixed norms

A later adapter should compose inner and outer Hölder rules. A benchmark is

$$
\|fg\|_{L_t^2L_x^2}
\le
\|f\|_{L_t^\infty L_x^3}
\|g\|_{L_t^2L_x^6}.
$$

The spatial constraint is $1/2=1/3+1/6$. The temporal constraint is $1/2=0+1/2$. The proof also needs the measurability and representation facts required by the chosen mixed-norm construction.

Keep the order of the iterated norms in the expression identity. Exchanging $L_t^qL_x^p$ with $L_x^pL_t^q$ requires a separate applicable theorem.

## 9. Showcase one: a small-drift elliptic estimate

This benchmark combines exponent selection, several function norms, a Sobolev bridge, absorption, and uniform constants.

### 9.1 Supplied mathematical inputs

Let $u$ be a real-valued compactly supported smooth function on $\mathbb R^3$. Assume $f\in L^{6/5}(\mathbb R^3)$ and $b\in L^3(\mathbb R^3;\mathbb R^3)$ with respect to Lebesgue measure, using the Euclidean pointwise norm for vector-valued functions. These are membership hypotheses, including measurability. Smooth compact support supplies the relevant membership facts for $u$ and its gradient, and Hölder establishes integrability of the displayed products.

Supply an energy inequality

$$
\nu\|\nabla u\|_2^2
\le
\left|\int fu\right|
+
\left|\int(b\cdot\nabla u)u\right|,
\qquad \nu>0.
$$

Supply an applicable Sobolev estimate

$$
\|u\|_6\le S\|\nabla u\|_2,
\qquad S\ge0,
$$

and the smallness condition

$$
S\|b\|_3\le\frac{\nu}{2}.
$$

The target conclusions are

$$
\|\nabla u\|_2\le\frac{2S}{\nu}\|f\|_{6/5},
\qquad
\|u\|_6\le\frac{2S^2}{\nu}\|f\|_{6/5}.
$$

The constants are uniform in $u$, $f$, and the admissible $b$, with dependence on the structural data already contained in $S$ and $\nu$.

### 9.2 Intended automated argument

Choose the Hölder relations

$$
\frac{1}{6/5}+\frac16=1,
\qquad
\frac13+\frac12+\frac16=1.
$$

Use the scalar product bound and Hölder to derive

$$
\left|\int fu\right|
\le \|f\|_{6/5}\|u\|_6,
$$

$$
\left|\int(b\cdot\nabla u)u\right|
\le \|b\|_3\|\nabla u\|_2\|u\|_6.
$$

Write $G=\|\nabla u\|_2$, $F=\|f\|_{6/5}$, and $B=\|b\|_3$. Substitute the Sobolev estimate and use nonnegativity:

$$
\nu G^2
\le SFG+SBG^2
\le SFG+\frac{\nu}{2}G^2.
$$

Absorb to obtain

$$
\frac{\nu}{2}G^2\le SFG.
$$

Handle $G=0$ directly. When $G>0$, cancel the positive factor and obtain $G\le2SF/\nu$. The Sobolev estimate gives the second conclusion.

A checked scalar lemma can package this final cancellation and its zero case. The tactic must not divide by an unproved nonzero norm.

### 9.3 Implementation sequence

First prove the abstract scalar-and-norm estimate from explicitly supplied Hölder bounds. Then automate the Hölder instances. Finally instantiate the chosen function-space and Sobolev representation.

Mathlib has compactly supported $C^1$ Gagliardo–Nirenberg–Sobolev results under explicit dimensional and codomain conditions. Select a theorem whose assumptions match the benchmark, or accept the desired bridge as an input. [Sobolev inequality][sobolev]

The energy inequality is a supplied analytic input. Deriving it from a differential equation, including integration by parts, is a separate formalization task.

## 10. Showcase two: a nonlinear fixed-point argument

This benchmark targets the estimate bookkeeping in a local existence argument and produces stability and residual bounds from the same rules.

### 10.1 Supplied mathematical inputs

Let $X$ be a Banach space. Let $B:X\times X\to X$ be bilinear, with

$$
\|B(u,v)\|\le K\|u\|\|v\|,
\qquad K\ge0.
$$

Let $a\in X$ satisfy

$$
\|a\|\le A,
\qquad A\ge0,
\qquad 8KA\le1.
$$

Define

$$
\Phi(u)=a+B(u,u).
$$

Select the radius template $R=2A$. The target is to prove invariance of the closed ball of radius $R$ and a Lipschitz constant at most $1/2$ there.

The choice of $R$ is a checked template. The unrestricted constraint $A+KR^2\le R$ is nonlinear in $R$, so this example does not assert arbitrary LP synthesis of radii.

### 10.2 Ball invariance

For $\|u\|\le2A$,

$$
\begin{aligned}
\|\Phi(u)\|
&\le A+K(2A)^2\\
&=A+4KA^2\\
&\le A+\frac12A\\
&\le2A.
\end{aligned}
$$

The proof uses triangle inequality, the bilinear bound, monotonicity, and the smallness assumption.

### 10.3 Contraction

Generate the bilinear identity

$$
B(u,u)-B(v,v)
=
B(u-v,u)+B(v,u-v).
$$

For $\|u\|,\|v\|\le2A$,

$$
\begin{aligned}
\|\Phi(u)-\Phi(v)\|
&\le K(\|u\|+\|v\|)\|u-v\|\\
&\le4KA\|u-v\|\\
&\le\frac12\|u-v\|.
\end{aligned}
$$

The closed ball is complete and nonempty. A wrapper can apply an existing Banach fixed-point theorem to the restricted self-map and obtain a unique fixed point in that ball. Mathlib supplies the underlying contraction and fixed-point theory. [Contracting maps][contracting]

The conclusion is uniqueness within the specified ball. Global uniqueness would need further information.

### 10.4 Stability and residual control

Suppose $a,a'$ satisfy the common radius assumptions and $u,u'$ are their fixed points in the ball. The same perturbation estimate gives

$$
\|u-u'\|
\le \|a-a'\|+\frac12\|u-u'\|,
$$

hence

$$
\|u-u'\|\le2\|a-a'\|.
$$

For an approximate solution $w$ in the ball,

$$
\|u-w\|
\le \frac12\|u-w\|+\|\Phi(w)-w\|,
$$

so

$$
\|u-w\|\le2\|w-\Phi(w)\|.
$$

The desired implementation should reuse the contraction certificate for these additional conclusions.

### 10.5 A PDE interpretation

A PDE application can supply

$$
a=S(t)u_0,
\qquad
\|a\|_X\le C_0\|u_0\|_Y,
$$

and a bilinear integral estimate

$$
\|B(u,v)\|_X
\le C_1T^\alpha\|u\|_X\|v\|_X.
$$

Assume $C_0,C_1,M\ge0$, $T>0$, and $\|u_0\|_Y\le M$. Substitute $A=C_0M$ and $K=C_1T^\alpha$, with their nonnegativity proved. The estimate portion reduces to the explicit condition

$$
8C_0C_1T^\alpha M\le1.
$$

The spaces and propagator estimates remain supplied. If the intended argument makes this condition hold by taking time sufficiently small, also assume $\alpha>0$. Solving for a time $T$ involving arbitrary symbolic powers is a later parameter-synthesis feature.

## 11. Uniform constants and explanations

Constant dependencies must be enforced by the theorem statement and Lean's scoping discipline.

For a goal

$$
\exists C,\ \forall u,\ P(u)\Longrightarrow N(u)\le C\,M(u),
$$

construct $C$ before introducing $u$. The metavariable for $C$ then has a context that excludes $u$. Dependency metadata can help explain the result, but cannot replace this logical discipline.

An explanation mode should present:

- The chosen constant or parameter.
- Its permitted dependencies.
- The analytic theorem instances used.
- The exact absorption or smallness conditions.
- The norm decompositions and final scalar combination.

For the elliptic example, it could report $C=2S/\nu$, the chosen Hölder exponents, and the condition $S\|b\|_3\le\nu/2$.

Include a negative regression distinguishing $\forall u\,\exists C$ from $\exists C\,\forall u$. Individually available bounds do not by themselves provide a uniform constant.

## 12. A separate Hilbert quadratic extension

Generic norm axioms do not capture all identities of inner-product spaces. A later plugin should normalize finite quadratic expressions in vectors.

For a real symmetric rational matrix $Q$, consider

$$
\sum_{i,j}Q_{ij}\langle x_i,x_j\rangle.
$$

A rational factorization

$$
Q=R^{\mathsf T}DR,
\qquad D\text{ diagonal},\quad D_{kk}\ge0,
$$

certifies nonnegativity because the expression equals

$$
\sum_k D_{kk}\left\|\sum_jR_{kj}x_j\right\|^2.
$$

For complex Hilbert spaces, use the corresponding real-valued expression involving real parts of inner products.

A small benchmark is

$$
\|x+y\|^2\le\frac32\|x\|^2+3\|y\|^2,
$$

with the certificate

$$
\frac32\|x\|^2+3\|y\|^2-\|x+y\|^2
=
\frac12\|x-2y\|^2\ge0.
$$

For a fixed rational matrix, exact rational elimination and an LDL-style certificate are a reasonable first implementation. Searching over combinations of hypotheses to obtain a positive-semidefinite matrix is a larger semidefinite-certificate problem.

This plugin should share expression handling, rule application, replay, and explanation facilities with the LP core. Its mathematical certificates remain distinct.

## 13. Proposed implementation structure

The boundaries below are more important than the exact filenames.

| Proposed module | Responsibility |
| --- | --- |
| `NormArith/Reify.lean` | Rational vector forms, norm-family identities, scalar atoms, and normalization proofs |
| `NormArith/Problem.lean` | Solver-independent observations, scalar rows, vector relations, and source proofs |
| `NormArith/LP/Encode.lean` | Compact supporting-functional encoding |
| `NormArith/LP/Oracle.lean` | Adapter to an exact contradiction-certificate oracle |
| `NormArith/LP/Extract.lean` | Eliminate auxiliary variables and recover elementary certificates |
| `NormArith/Certificate.lean` | Generalized checked certificate lemmas |
| `NormArith/Realization.lean` | Finite-realization and completeness theorems, separate from the runtime imports |
| `NormArith/Replay.lean` | Deterministic certificate checking and proof suggestions |
| `NormArith/Estimate.lean` | Bounded analytic rule search and premise management |
| `NormArith/Rules/` | Optional seminorm, operator, Lp, Hölder, Young, and interpolation adapters |
| `NormArith/Hilbert/` | Optional quadratic normalization and exact certificates |

Use sparse rational data and canonical expression tables. Delay Lean proof construction until search selects a useful certificate. Preserve source proofs so that extraction never needs to re-prove an analytic assumption. The runtime tactic and elementary checker need not import `Realization.lean` or its Hahn–Banach dependencies.

Candidate surface syntax is:

```lean
-- Existing interface, with the new backend behind it.
norm_arith [h₁, h₂]

-- Proposed broader interface.
analytic_estimate [h_energy, h_sobolev, h_small]

-- Proposed explanation and replay output.
analytic_estimate? [h_energy, h_sobolev, h_small]
```

These last two commands are proposed APIs. Their implementations and exact configuration syntax are part of the roadmap.

Completeness belongs to the mathematical reduction with an exact terminating solver on the stated fragment. An implementation with finite search or resource budgets can return unknown on a valid goal.

Keep outcomes distinct: a proof, unsupported syntax, an unmet premise, resource exhaustion, or failure to find a certificate. Only an independently checked feasible model warrants a model-based diagnostic.

For the pure generic fragment, a rational feasible LP point can give a concrete rational sup-norm counterexample. With opaque nonlinear scalar expressions, structured vector atoms, specific analytic rules, or fixed-space assumptions, an assignment satisfying only the finite relaxation is a diagnostic about the selected constraints, not a counterexample to the full theorem.

## 14. Development milestones and acceptance gates

### M0. Freeze the baseline

Record the current repository and dependency versions. Preserve existing successful examples, expected failures, explicit-fact tests, and benchmark inputs.

**Gate:** the baseline results are reproducible sufficiently to compare solver changes without changing the surrounding dependency stack.

### M1. Formalize the certificate and realization interfaces

Prove the generalized elementary certificate lemma. Formalize the finite sup-norm realization theorem and its extension to supplied rational vector relations. State the exact supported fragment.

**Gate:** soundness is independent of the optimizer. Zero vectors, zero seminorms, dependent atoms, and strict scalar comparisons are covered by the appropriate theorem or preprocessing contract.

### M2. Implement the compact LP backend

Add encoding, exact oracle integration, extraction, and replay. Retain the structural fast path and the existing enumeration as a small-instance comparison tool during migration.

**Gate:** existing positive tests continue to succeed, and expected failures that enforce the soundness boundary continue to fail. Documented failures caused only by resource limits or incomplete search may become successes. Small problems agree with exhaustive enumeration when it completes. Deliberately damaged coefficients, signs, identities, and strictness flags are rejected.

### M3. Support explicit seminorms and several families

Add adapters, exact family identities, linear-map pullbacks, and supplied affine bridges.

A benchmark is: from $p(u)\le A$, $q(v)\le B$, and $\forall w,\ p(w)\le3q(w)$, prove

$$
p(2u-v)\le2A+3B.
$$

**Gate:** one certificate backend supports ordinary norms, explicit seminorms, and a derivative-seminorm adapter. Distinct measures and exponents are never silently identified.

### M4. Support finite function-norm representations

Connect bundled `Lp`, real `lpNorm`, and extended `eLpNorm` through checked domain and finiteness facts.

**Gate:** equivalent finite estimates work in the supported representations, including $p=\infty$. An invalid conversion involving an infinite extended norm cannot enter the real core without a valid proof.

### M5. Add products, operators, and absorption

Implement selected analytic rules, bilinear perturbation normalization, Young templates, and coupled linear estimates.

**Gate:** the product perturbation, scalar energy, and coupled-absorption benchmarks close at the public frontend. Symbolic positive coefficients and zero-factor cases are handled explicitly.

### M6. Select exponents and build the elliptic showcase

Implement rational reciprocal-exponent constraints and fixed-endpoint interpolation. Complete the small-drift example, first from abstract input inequalities and then in an applicable function-space representation.

**Gate:** inferred parameters instantiate proved theorems with every side condition discharged. The output constant has the intended dependencies.

### M7. Complete the fixed-point showcase

Prove ball invariance and contraction from the supplied bilinear estimate. Connect these outputs to the existing fixed-point theorem. Reuse the result for stability and residual bounds.

**Gate:** uniqueness is stated on the certified ball, the zero-radius case is handled, and all parameter templates produce checked obligations.

### M8. Extend according to the analytic corpus

Add mixed norms, selected additional embeddings, and Hilbert quadratic certificates where real proof blocks justify them. Consider quasi-norm rules as a separate family.

**Gate:** each extension demonstrates improvement on examples held out from its rule development, while preserving the core's predictable behavior.

These are dependency milestones. They do not impose a calendar schedule or assume that every later component is needed for the first useful release.

## 15. Evaluation

Evaluate core performance separately from analytic coverage.

### 15.1 Solver comparison

Compare:

1. Existing frontend and enumeration.
2. Existing frontend with the compact LP and reconstruction of its selected certificates.
3. Explicit certificate replay.

An optional additional comparison can defer proof construction in the existing enumeration backend, reconstructing only the inequalities selected by scalar search. That isolates delayed construction from the change in norm-constraint encoding.

Use both the existing corpus and generated rational problems. Vary the number of observed norm terms, vector rank, sparsity, coefficient bit lengths, and dependency patterns. Include goals that fail as well as goals that succeed.

Measure search time, proof construction, kernel checking, memory, certificate size, and total affected-file compilation. Keep small-goal regressions and timeouts in the reported aggregate.

A polynomial-size encoding does not by itself establish faster execution. Rational coefficient growth and proof elaboration may dominate some cases.

### 15.2 Analytic coverage

Use complete estimate blocks from real analysis and PDE formalizations. Keep a portion of the corpus held out while developing rule packs.

Compare the baseline proof with:

- The new core only.
- The core plus explicit seminorm adapters.
- The analytic frontend with supplied intermediate estimates.
- The analytic frontend with parameter selection and intermediate-rule search.
- Certificate replay.

Report successful replacements and net source reduction. Charge new helper facts, required side-condition proofs, and imports to the replacement. Moving bookkeeping elsewhere should remain visible in the accounting.

Also record which obstacle caused each failure: a missing analytic theorem, an unsupported representation, an unresolved domain condition, a poor parameter choice, an arithmetic limitation, or exhausted search.

### 15.3 Correctness regressions

The regression corpus should include:

- Reversed triangle directions and incorrect scalar signs.
- Strict versus weak inequalities.
- Zero seminorm values without vector equality.
- Different norm instances on the same type.
- Different measures, sets, exponents, and derivative orders.
- Infinite `eLpNorm` values and missing membership facts.
- Derivative identities lacking their regularity assumptions.
- Symbolic coefficients that cannot be treated as rational constants.
- Nonuniform constants presented as uniform bounds.
- Circular rule justification.
- Stale or altered replay certificates.

These cases check the stated mathematical boundary and the behavior of the frontend.

## 16. Research contributions and open questions

The use of linear programming in norm arithmetic has established precedent. Solovay, Arthan, and Harrison studied the decidability of normed-space theories, and Arthan describes a parametrized LP procedure for additive formulas implemented in HOL Light. [Decidability][decidability], [Mechanized reasoning][arthan]

The project should establish and evaluate its own precise contributions:

1. A compact supporting-functional encoding with a formal finite-realization theorem.
2. Extraction of ordinary seminorm certificates from the LP certificate.
3. An implementation that reuses Lean's proof infrastructure and supports deterministic replay.
4. A common interface for several finite seminorms and certified comparisons.
5. Controlled composition of analytic estimates, including parameter selection.
6. Demonstrated reductions in complete formal estimate blocks.

The specific supporting-functional formulation is a design proposed here. A publication claiming novelty for that formulation should first investigate the optimization and automated-reasoning literature more thoroughly.

Useful research questions include:

- When does the compact LP outperform independent-support enumeration?
- How much of the improvement comes from delayed proof construction and replay?
- Can block structure reduce rational simplex costs?
- When is lazy generation of supporting constraints preferable to the full $O(m^2)$ formulation?
- Which small analytic rule inventory covers the largest fraction of real estimate blocks?
- Can proof search use failed arithmetic attempts to choose the next useful analytic lemma?
- Which parameter choices yield short certificates with manageable constants?
- How often can failure in the generic fragment produce an informative checked sup-norm counterexample?

A lazy method that needs feasible LP assignments requires a suitable solver interface. The existing contradiction-only oracle does not supply those assignments.

The first release should deliver a rigorous LP core, several seminorms, finite function-norm adapters, and a small collection of effective analytic rules. The larger objective is to make formal proofs of analytic estimates follow the level of detail at which mathematicians communicate those estimates, while preserving every hypothesis and constant dependency in the checked proof.

## References

- [Repository baseline][repo-commit], including the current [README][repo-readme].
- [Current rational decomposition search][repo-search].
- [Current tactic frontend][repo-tactic].
- [Current certificate lemmas][repo-certificate].
- [Pinned mathlib linarith datatypes and oracle interface][linarith-data].
- [Pinned mathlib simplex oracle][simplex].
- [Mathlib Hahn–Banach and norming functionals][hahn-banach].
- [Mathlib seminorm structures][seminorms].
- [Mathlib operator norms][operators].
- [Mathlib real-valued Lp norms][lp-norm].
- [Mathlib bundled Lp spaces][lp-spaces].
- [Mathlib Hölder for continuous bilinear maps][holder].
- [Mathlib comparison and product estimates for Lp expressions][compare-exp].
- [Mathlib Young inequalities][young].
- [Mathlib Sobolev inequality][sobolev].
- [Mathlib contracting maps and Banach fixed points][contracting].
- [Mathlib bound tactic][bound].
- [Solovay, Arthan, and Harrison, Some new results on decidability for elementary algebra and geometry][decidability].
- [Arthan, Mechanized Reasoning for Continuous Problem Domains][arthan].

[repo-commit]: https://github.com/TomasOrtega/norm-arith/commit/177a21dfd81ef0e9be9188f91e8a39bea44fe4e4
[repo-readme]: https://github.com/TomasOrtega/norm-arith/blob/177a21dfd81ef0e9be9188f91e8a39bea44fe4e4/README.md
[repo-search]: https://github.com/TomasOrtega/norm-arith/blob/177a21dfd81ef0e9be9188f91e8a39bea44fe4e4/NormArith/Search.lean
[repo-tactic]: https://github.com/TomasOrtega/norm-arith/blob/177a21dfd81ef0e9be9188f91e8a39bea44fe4e4/NormArith/Tactic.lean
[repo-certificate]: https://github.com/TomasOrtega/norm-arith/blob/177a21dfd81ef0e9be9188f91e8a39bea44fe4e4/NormArith/Certificate.lean
[linarith-data]: https://github.com/leanprover-community/mathlib4/blob/2f3c7c8a8949b04a32f9303f59163acffb766996/Mathlib/Tactic/Linarith/Datatypes.lean
[simplex]: https://github.com/leanprover-community/mathlib4/blob/2f3c7c8a8949b04a32f9303f59163acffb766996/Mathlib/Tactic/Linarith/Oracle/SimplexAlgorithm.lean
[hahn-banach]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Normed/Module/HahnBanach.html
[seminorms]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Normed/Module/Seminorm/Basic.html
[operators]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Normed/Operator/Basic.html
[lp-norm]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Function/LpSeminorm/LpNorm.html
[lp-spaces]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Function/LpSpace/Basic.html
[holder]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Function/Holder.html
[compare-exp]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Function/LpSeminorm/CompareExp.html
[young]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/MeanInequalities.html
[sobolev]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/FunctionalSpaces/SobolevInequality.html
[contracting]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/MetricSpace/Contracting.html
[bound]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Bound.html
[decidability]: https://arxiv.org/abs/0904.3482
[arthan]: https://www.lemma-one.com/papers/70.pdf

