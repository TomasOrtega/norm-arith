# Further proof replacements

`confirmed-v2.json` freezes nine reviewed replacements in five Mathlib files.
Their exact complete copied files compiled against the current production tactic
in `.lake/expansion-next-05`. Strict extraction checked source identity, every
fresh nonempty compiler artifact hash, and the absence of warnings or errors.
The snapshot records original body observations, exact source spans, replacement
strings, trial-report hashes, and the production source hashes at extraction.
The combined verifier must still bind the full compiler and runtime inputs.

The replacements use 57 proof-code lines in place of 117, with all preparation
included. Five imports and no helpers give 55 net lines saved for this set alone.
This is not an additional 55-line claim on top of a prior patch: the union must
account for shared imports and overlap with the old multilinear substep. This
batch has no timing result.

| File | Replacements | Preparation retained |
| --- | --- | --- |
| Calculus/FDeriv/Measurable | Right-derivative error and operator shell estimates | Pointwise bounds, interval membership, scalar positivity |
| Normed/Module/Multilinear/Basic | The inserted-sum induction tail | The finite-sum rewrite and both induction estimates |
| Normed/Order/Lattice | Norm contraction estimates for infimum and supremum | Two existing order contraction bounds in each proof |
| Constructions/HaarToSphere | Two radial-normalization estimates | Scaled unit-vector norm and distance identities |
| Covering/BesicovitchVectorSpace | Separation and radial-error tails | Reciprocal scalar estimate and the normalized radial bound |

The nonlinear scalar steps remain explicit. For example, Besicovitch's reciprocal
bound is proved by `nlinarith only` before `norm_arith` combines the separation
cases. The tactic does not gain a general nonlinear solver from these examples.

`confirmed-v1.json` and its accounting preserve the earlier four-edit trial on
the preceding production version. They are historical and are superseded by v2
for proposed integration. The immutable v2 hashes are:

- Manifest: `890edcce6e079bc461f8bd04de84f00a33e25e573374d4db6ef6fb40642f63b1`
- Accounting: `b32d9bf6ef446310f011a336a582da03eff3ef1621af634ad1bb0c07b5b9e049`

`failed-tail-index.jsonl` ranks 594 multiline attempts from discovery v3. The
filter retained failed 5–50-line tails containing at least two norm, triangle,
or arithmetic steps, excluding the old verified spans. Larger enclosing tails
were then reviewed separately where the old patch shortened only a substep.
This was local postprocessing, not another Mathlib census. `reviewed.json`
preserves trial outcomes and rejected variants. Two prepared Polish-space tails
remain failed and are excluded. An overlarge Besicovitch span initially omitted
an old helper; the corrected proof uses the original structure field directly.
A deprecated lemma warning in the shell preparation was fixed before v2.

`prepare.py` regenerates the mutable inventory, which includes unsuccessful
proposals. To replay the checked set, pass the immutable manifest explicitly:

```sh
python3 benchmarks/expansion/next/trial.py \
  --manifest benchmarks/expansion/next/confirmed-v2.json \
  --output .lake/expansion-next-NEW
```

The output directory must not exist. Trials use actual edited import headers
with `lake --no-build setup-file` and original census build options. They do not
rebuild production dependencies or edit the original Mathlib checkout.
