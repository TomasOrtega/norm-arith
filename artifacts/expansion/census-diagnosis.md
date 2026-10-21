# Expansion diagnosis from the retained v3 census

This is a read-only audit of `.lake/census-full-v3`, at mathlib revision
`2f3c7c8a8949b04a32f9303f59163acffb766996`. It proposes experiments, not new
verified replacements or savings. `index_census.py` and `index_suffixes.py`
reproduce the counts and source excerpts in the neighboring JSON/JSONL files.

## What the failure count means

There are 2,753 failed replay records across 388 files, covering 2,752 distinct
source spans. They overlap: 939 are whole `by` terms, 950 are complete indented
tactic sequences, and 276 are `calc`/`calcTactic` nodes. This is not a count of
2,753 independent missed proofs. Median failed replay time is 6 ms; maximum is
872 ms. No replay reached the heartbeat or goal-time limit. Increasing those
limits alone does not address the observed failures.

| Exact failure family | Records |
|---|---:|
| No certificate for recognized scalar/norm constraints | 1,989 |
| Opaque upper-bound extension found no certificate | 708 |
| Tactic no longer recognizes a real norm comparison in replay | 50 |
| Within-command private matcher absent from the pre-command environment | 3 |
| Certificate identity normalization fails in `Analytic/Basic` | 2 |
| Missing `Norm (E → G)` during structural-bound construction | 1 |

The first message mentions additive incompleteness even for core-labelled
records; it is not a reliable fragment classifier. Original fragment labels
partition failures as 1,077 core, 958 additive, and 718 upper-bound-extension.

Nonexclusive source-text indicators among failed records: 683 introduce or
specialize local facts; 2,395 rewrite or simplify; 381 normalize products,
quotients, or scalar multiples of norms; 199 use nonlinear arithmetic; and 439
mention sums, integrals, continuity, or related semantic bounds. These are
lexical indicators, not proofs that those operations are necessary.

The largest failed span is `Analysis/Complex/PhragmenLindelof.lean:117–220`.
Its analytic argument establishes the bound; the initial context does not
already imply it by affine norm arithmetic. Treating its 104 physical lines as
available savings would be misleading. Similar large failures occur in
`Analysis/Fourier/FourierTransformDeriv.lean:348–427` and
`Analysis/BoxIntegral/DivergenceTheorem.lean:72–135`.

## The larger collector opportunity: tails after preparation

Whole sequences are present: 4,129 indented tactic-sequence observations,
21 bracketed sequences, 368 `calcTactic`, and 182 `calc` observations. The gap
is *suffixes*, not wholesale absence of these syntax kinds.

The frozen collector only marks a tactic replaceable when `goalsBefore` has
length one and `goalsAfter` is empty (`frozen-implementation/NormArith/Census.lean:242`
inside `.lake/census-archive-final`). Thus intermediate `have`, `rw`, `simp`,
`apply`, and branch tactics do not expose a replaceable tail even when prior
steps have prepared enough bounds. There are 1,091 multiline recognized-goal
observations excluded as `multi_goal_tactic`.

A source-containment scan finds 1,752 previously unobserved tail candidates in
293 files, mainly starting at `rw` (432), `have` (414), `refine` (161), `simp`
(149), and `apply` (135). This heuristic sometimes crosses sibling `calc`
steps or branches. Use syntax-parent child lists to delimit real tails; do not
accept this JSONL as a proposal manifest. Replay each tail against the original
pre-tactic goal/context, keep kernel checking, and compile the combined source.

There is a separate opportunity in multi-step `calc` tails after a semantic
first step. The remaining individual step proof terms do not represent the
combined tail goal. A tail proposal must construct the relation from its
previous endpoint to the final endpoint and emit a valid final `calc` step.

## Concrete smaller investigations

- `Analysis/SpecialFunctions/Log/Summable.lean:209–212`: reverse triangle
  estimate `‖‖1 + f i‖ - 1‖ ≤ ‖f i‖`; investigate nested real norms and constants.
- `Analysis/Analytic/Basic.lean:661–664`: the identity needs unfolding
  `FormalMultilinearSeries.partialSum` before `abel`. Both retained attempts
  fail during certificate normalization. This is a concrete atom-normalization
  or fixed-preparation experiment.
- `Analysis/Normed/Module/Multilinear/Basic.lean:231–241`: the final estimate has
  prepared induction and local bounds; the remaining finite-sum identity is
  additional semantic preparation, not a bare norm-arithmetic consequence.
- `MeasureTheory/Covering/BesicovitchVectorSpace.lean:383–394`: triangle
  arithmetic follows a normalized variable-scalar norm bound. Keep that bound's
  preparation and account for it before estimating savings.

## Bodies, definitions, and conservative gaps

The collector tests whether each *target* is a proposition; it does not require
the containing declaration to be a theorem (`Census.lean:155`). Proof subterms
of non-Prop definitions and structure fields are therefore already in scope.

All 11 multiline recognized observations excluded as `outside_decl_body` occur
in `Analysis/Distribution/ContDiffMapSupportedIn.lean:1069–1088`, under
`noncomputable def bilinLeftCLM` and its `where finally` proof cases (1057).
The body-range collector handles simple/equation/structure bodies but omits
this attached finalizer. Extend that exact proof-body syntax; do not broaden
the guard to whole commands, which could alter theorem statement text.

The 50 replay grammar rejections include normed-instance constructions such as
`Analysis/Normed/Lp/lpSpace.lean:550–572`. The observation environment can contain
the resulting instance while the required pre-command replay environment
cannot assume the very norm axiom being proved. Preserve that protection.
The three private-matcher failures in `Topology/MetricSpace/GromovHausdorff.lean:304–314`
also reflect pre-command availability; do not solve them by exposing the parent
theorem to replay.

Other recorded barriers are 54 import-cycle skips in eight foundational normed
files, 15 augmentation failures in four files, and four exact-context mismatches
in `Normed/Group/Hom` and `InfiniteSum`. Import cycles need a genuine dependency
refactor before a source import is valid. Exact-context mismatches should stay
unknown unless an equally strong matching method is introduced.

The 27 incomplete file outcomes and 99 known eligible observations with no
attempt remain coverage gaps. Neither the proposed suffix scan nor these
diagnostic counts establish new complete coverage or larger line savings.
