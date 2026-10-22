# Additional Mathlib proof replacements

The follow-up verifies **46 additional net code lines saved** in **30 replacements
across 17 new files**. All **63 complete edited files** passed combined compilation,
using fresh outputs for affected dependencies. The compiler produced 441 nonempty
artifacts; their hashes were checked, and no warnings or errors remained.

The combined selection saves **356 net lines in 117 replacements across 63 files**.
It retains all 87 published replacements without changing their text. The tactic,
Mathlib checkout, timing harness, published paper, and published timing results are
unchanged. This follow-up has no new timing result.

## Savings by file

Paths are relative to `Mathlib/`. Each file pays for one added `NormArith` import.
Preparation is included in the replacement column; no helper declarations are added.

| File | Replacements | Proof code lines | Net lines saved |
|---|---:|---:|---:|
| `Analysis/ODE/PicardLindelof.lean` | 2 | 25 → 13 | 11 |
| `Analysis/Distribution/SchwartzSpace/Basic.lean` | 3 | 11 → 5 | 5 |
| `Geometry/Euclidean/Sphere/Tangent.lean` | 3 | 14 → 8 | 5 |
| `MeasureTheory/Measure/ResolventTransform.lean` | 1 | 10 → 4 | 5 |
| `Analysis/Calculus/UniformLimitsDeriv.lean` | 2 | 7 → 3 | 3 |
| `Analysis/Normed/Module/FiniteDimension.lean` | 2 | 7 → 3 | 3 |
| `Analysis/Calculus/ContDiff/Convolution.lean` | 2 | 5 → 2 | 2 |
| `Topology/MetricSpace/CauSeqFilter.lean` | 2 | 6 → 3 | 2 |
| `Topology/UrysohnsLemma.lean` | 2 | 5 → 2 | 2 |
| `Analysis/Complex/ValueDistribution/SecondMainTheorem.lean` | 1 | 6 → 4 | 1 |
| `Analysis/Convolution.lean` | 2 | 4 → 2 | 1 |
| `Analysis/Normed/Lp/SmoothApprox.lean` | 1 | 3 → 1 | 1 |
| `Analysis/Normed/Unbundled/SmoothingSeminorm.lean` | 1 | 3 → 1 | 1 |
| `MeasureTheory/Covering/Besicovitch.lean` | 2 | 5 → 3 | 1 |
| `NumberTheory/Padics/Measure/AmiceTransform.lean` | 1 | 4 → 2 | 1 |
| `Probability/Moments/ComplexMGF.lean` | 1 | 3 → 1 | 1 |
| `Topology/MetricSpace/HausdorffDimension.lean` | 2 | 5 → 3 | 1 |
| **Total** | **30** | **123 → 60** | **46** |

These are newly selected replacements. Some combine new proof fragments with
previously found census successes that did not cover an import on their own.
This is a targeted follow-up, not an exhaustive search of all Mathlib proofs.

## Example

In `MeasureTheory.hasDerivAt_resolventTransform`, a ten-line distance calculation
becomes the following four lines. The two preparatory facts are included in the count.
After the import, this file saves five lines.

```lean
    have hx' := infDist_le_dist_of_mem (x := a) (s := algebraMap 𝕜 A '' μ.support)
      (y := algebraMap 𝕜 A x) ⟨x, hx, rfl⟩
    change dist w a < infDist a (algebraMap 𝕜 A '' μ.support) / 2 at hw
    norm_arith [hx', hw]
```

## Evidence and limits

The source pin is Mathlib `2f3c7c8a8949b04a32f9303f59163acffb766996`, with
Lean `4.36.0-rc1`. Counts exclude blank lines and comments. Each replacement keeps
the recorded text outside its proof span; every replacement line is at most 100
Unicode characters. Original declaration-body observations bind each edit to its
source. Failed and revised attempts remain in the four group directories.

- [New replacements only](verified/additional.patch)
- [Complete combined patch](verified/mathlib.patch)
- [Machine-readable counts](verified/summary.json)
- [Independent source and count audit](independent-audit.json)
- [Final manifest](verified/manifest.json)
- [Compressed verification receipt](verified/verification.json.gz)
- [Archived source, setups, and logs](verified/raw-verification.tar.gz)

The existing speedup applies to the earlier 46-file workload. A new paired timing
study is needed to report a speedup for this 63-file workload. The published paper
has not been updated with these follow-up counts.

## Reproduction

The four `confirmed.json` files are the inputs to the selection, together with
`../verified-05/manifest.json`. Their snapshots and hashes are in `selection/inputs/`
and `selection/manifest.json`. Run from the repository root with the pinned toolchain,
the original body-census evidence, and the existing built dependencies:

```sh
python3 scripts/verify_selection.py \
  benchmarks/expansion/followup-20261021/selection/manifest.json \
  --allow-preparation \
  --body-census .lake/census-full-v3 \
  --body-census .lake/expansion-preprocessing-calibration-01 \
  --body-census .lake/expansion-discovery-v2 \
  --body-census .lake/expansion-discovery-v3 \
  --body-census .lake/expansion-discovery-v4 \
  --output .lake/followup-recheck-new-directory \
  --threads 1 \
  --lake benchmarks/expansion/followup-20261021/lake-no-build
```

The wrapper requires existing dependencies and prevents Lake from rebuilding them.
The verifier writes fresh compiler outputs to the supplied new directory.
