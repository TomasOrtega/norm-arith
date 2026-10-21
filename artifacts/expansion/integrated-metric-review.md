# Integrated metric source review

Reviewed snapshots:

- `NormArith/Metric.lean`:
  `4987a96a314ef53daa83868c5a772e133899efbb81b80e9d88792581629deb0f`.
- `NormArith/Tactic.lean`:
  `dd0e8481c69ed87e89a8f2344f68a653c17ba48b87124d9167c1b93ef71e7c61`.
- `NormArithTest/Metric.lean`:
  `541c62f8239ea64976cb325ef3861d42e1eef68badffa394eb8985714da23c99`.

No kernel-soundness or selected-fact leakage issue was found. `Metric.constraints`
returns ordinary lemma applications in `MetaM`; the tactic wrapper passes exactly
`selectedFacts` and uses the existing backtracking `tryLinear`. It does not rescan
local declarations for proof premises. `linarith true` restricts its search to
the supplied proofs, as documented by pinned Mathlib's
`Mathlib/Tactic/Linarith/Frontend.lean:341–406`. Outer `focusAndDone` and
`withoutRecover` remain in place.

The engine retains the reviewed eight-point/400-generated-fact bounds. Points
with loose bound variables or metavariables are excluded. Each failed lemma
application restores its `MetaM` state; pair facts are appended together. Input
fact count and traversal remain subject to Lean/file budgets rather than an
additional explicit cap. The tests cover explicit norm/distance exclusion,
retained scalar hypotheses, scalar conclusions, strict failure and mixed spaces.

One source-derived routing gap was reported to the implementation owner before
this review was completed. This example should follow distance nonnegativity:

```lean
example {X : Type*} [PseudoMetricSpace X] (a b : X) (r x : ℝ)
    (hm : dist a b ≤ r) (hn : ‖x‖ ≤ 1) : 0 ≤ r := by
  norm_arith [hm]
```

At the reviewed snapshot, `goalFragment` scans the full local context
(`Tactic.lean:247–249`), finds the excluded unrelated `hn`, and returns `core`
before checking `metricFacts` (255–257). The exclusive branch at 552 then skips
the metric engine; the additive norm path does not supply generic distance
nonnegativity. This is a coverage/routing issue, not an invalid proof or fact
leak. No compiler run was started during the owner's build to confirm the case.

Simply giving metric facts priority has the symmetric problem when a norm bound
proves the scalar target and a metric fact is unrelated. A backtracking alternate
engine attempt on the same selected facts preserves both possibilities. The
owner was asked to record a red regression before changing production routing.
This note records the pre-fix snapshot and must not be treated as a review of
later changed routing bytes.

The owner reproduced this case in
`artifacts/expansion/regressions/metric-routing-red.log` and added both asymmetric
regressions. The routing fix was reviewed at Tactic SHA256
`27b311a82a893e3857b0d4bdeffbe8bb8b0ae323580f284d171f8d2e1e9d18ba`
and Metric-test SHA256
`6509dd0e51d8893bb27e2b012d3959e26d40f7523c28932f05c8e31d6dcb0ba5`.
The Metric module bytes are unchanged. The fix gives generic metric facts a
conservative extension classification, attempts `tryMetric` on selected facts,
and falls through to the existing norm path when it fails. `tryMetric` saves
before constraint generation and restores on both false and exception. Both
engine choices therefore remain available without recovering excluded premises.
This delta has no source-review blocker; a green owner build is required before
the new frozen scan. Classification can conservatively exclude some core-shaped
goals from the core count when metric facts are present; it does not extend the
completeness claim.

`metric_extension` remains separate from `core` in the classifier and Core tests.
The metric extension has no completeness claim. Final line counts require the
eventual combined literal patch and fresh whole-file compilation; the preserved
41-line speed study remains specific to its old implementation and workload.
