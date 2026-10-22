# Checked analysis follow-up

Four additional replacements compile together in complete copied Mathlib files at
`2f3c7c8a8949b04a32f9303f59163acffb766996`. They use the current tactic without a
rebuild. The published paper and timing workload are unchanged.

| File | Original lines | Replacement lines | Import cost | Net saving |
| --- | ---: | ---: | ---: | ---: |
| `Analysis/Complex/ValueDistribution/SecondMainTheorem.lean` | 6 | 4 | 1 | 1 |
| `NumberTheory/Padics/Measure/AmiceTransform.lean` | 4 | 2 | 1 | 1 |
| `Probability/Moments/ComplexMGF.lean` | 3 | 1 | 1 | 1 |
| `Analysis/Normed/Unbundled/SmoothingSeminorm.lean` | 3 | 1 | 1 | 1 |
| **Total** | **16** | **8** | **4** | **4** |

Counts exclude blank and comment lines, include all preparation, and add no helper
lemmas. The four files are outside the published 46-file workload. The longest new
replacement line has 88 Unicode characters.

- [manifest.json](manifest.json) binds exact original source and proof spans.
- [mathlib.patch](mathlib.patch) shows all four edits and imports.
- [body-evidence.json](body-evidence.json) records four matched declaration-body
  observations from the final targeted discovery. These observations certify the
  original body ranges; they are not census-generated replacement proposals.
- [verification-receipt.json](verification-receipt.json) records the combined
  full-file check, source hashes, and 28 nonempty fresh output hashes.
- [trials/final-01/report.json](trials/final-01/report.json) and its adjacent logs,
  copied sources, and actual edited-header setups retain the exploratory run.

The combined check uses `warningAsError=true` and rejects `style.longLine`
diagnostics. All four files passed. Root's combined release verifier must still
check the union with other new candidates before a new workload is frozen.

[attempts.json](attempts.json) and `trials/` retain unsuccessful trials too. The
second finite-sum lower-bound attempt in SecondMainTheorem did not produce a
certificate. The Units attempt had a parenthesis error and a certificate failure;
it is excluded. The Hensel telescope attempt reached the existing 200,000-heartbeat
limit; no budget was increased. No failed fragment is included in the final
manifest.

`trial.py` repeats the copied-file experiment using existing cached source setups
and `lake --no-build setup-file`. Its output must be a new directory. For example:

```sh
python3 benchmarks/expansion/followup-20261021/analysis/trial.py \
  --manifest benchmarks/expansion/followup-20261021/analysis/manifest.json \
  --output .lake/followup-analysis-repeat
```
