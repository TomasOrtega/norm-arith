# Calculus and analysis follow-up

`confirmed.json` contains 13 checked edits in six files outside the published
46-file workload. They replace 59 proof-code lines with 28 lines. Six new
`NormArith` imports leave **25 net lines saved**. Explicit preparation counts
as replacement code. Every replacement line has at most 100 Unicode characters.

| Mathlib file | Edits | Before | After | Net after import |
| --- | ---: | ---: | ---: | ---: |
| `Analysis/Calculus/ContDiff/Convolution.lean` | 2 | 5 | 2 | 2 |
| `Analysis/Calculus/UniformLimitsDeriv.lean` | 2 | 7 | 3 | 3 |
| `Analysis/Convolution.lean` | 2 | 4 | 2 | 1 |
| `Analysis/Distribution/SchwartzSpace/Basic.lean` | 3 | 11 | 5 | 5 |
| `Analysis/Normed/Module/FiniteDimension.lean` | 2 | 7 | 3 | 3 |
| `Analysis/ODE/PicardLindelof.lean` | 2 | 25 | 13 | 11 |

The edits use the existing tactic. The Picard–Lindelöf proofs retain explicit
scalar multiplication and domain-membership steps. The Schwartz-space edits
retain scalar monotonicity. An earlier isolated success in `norm_toZeroAtInfty`
now contributes a saving because the other edits pay for its file's import.

All six complete copied files compiled with their actual `NormArith` import,
fresh outputs, and `-DwarningAsError=true`. The first three successful files
are bound to trial `04`; the other three are bound to `final-05`.
`verified-summary.json` checks that each reported replacement-source hash
matches the source generated from the final manifest. This is a proof and
line-count result; it provides no additional compilation-speed measurement.
The published paper and timing workload remain unchanged.

`body-validation.json` records source and original declaration-body evidence.
`selected/` records a successful run of `scripts/select_expansion.py` on this
batch. `trial-index.json` and `trials/` preserve all seven attempts, including
failed candidates and compiler diagnostics. The bounded-convolution candidate
at original lines 781–782 was dropped after its prepared domain check failed.
Other failures were corrected with explicit typed facts, explicit scalar
composition, or removal of an unused simp argument. No failed edit appears
in `confirmed.json`.

`prepare.py` reconstructs the exploratory manifest from the pinned Mathlib
sources and the original census observations. `trial.py` reuses the existing
trial helpers, adds warnings-as-errors, and uses `lake --no-build setup-file`.
For example, choose a new output directory and run:

```sh
python3 benchmarks/expansion/followup-20261021/calculus/trial.py \
  --manifest benchmarks/expansion/followup-20261021/calculus/confirmed.json \
  --output .lake/followup-calculus-recheck
```

`confirmed.json` is frozen. Later combined verification can check these edits
with the other follow-up batches without changing this trial record.
