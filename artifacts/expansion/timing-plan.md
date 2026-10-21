# Capacity estimate and proposed expanded compilation study

This is a premeasurement proposal. No new measurements were run. The final
expanded implementation and source patch are still changing, so this is not yet
an input-frozen analysis plan.

## Scheduling evidence

The completed 41-line study used ten files, one Lean thread, one warmup pair and
40 measured pairs. Its original/replacement mean pass totals are 34.823/31.510 s:
66.333 s per pair, 44.22 minutes of measured compilation, 45.35 minutes including
warmup, and 68.89 s of separately recorded setup. Its independent 24-pair pilot
used the same workload and is excluded from those 40 pairs.

The 21-file expanded verification's replacement compilation sums to 62.597 s.
Eleven files are new relative to the timed baseline and contribute 29.795 s.
Using their one-off replacement durations as a rough allowance for original
compilation gives 34.823 + 29.795 + 62.597 = 127.215 s per pair. This is a capacity
estimate only: verification ran during discovery, has no paired baseline, and
uses a different tactic. Dividing these estimates would not estimate speedup.

At that scale, 24 pilot pairs, 40 confirmatory pairs, and two warmup pairs require
about 140 minutes of compiler work. Forty extra confirmatory pairs add about
85 minutes. Reserve roughly three hours for the default design or five hours
for the longer design, plus any final tactic/native rebuild before the pilot.
Recompute this allowance when the final affected-file set changes.

The old confirmatory raw runs occupy about 2.36 GiB for 41 pairs. The expanded
verification has 30.37 MiB of fresh artifacts and about 27.50 MiB of per-file
setups for one variant. Retaining both variants for 66 pairs therefore needs
roughly 7.5 GiB before reports/setup duplication; reserve at least 10 GiB for the
default study or 15 GiB for 106 pairs. Keep all artifacts and raw timings.

## Proposed fixed protocol

1. Finish discovery and integration; freeze the complete deterministic net-saving
   patch, all preparation/imports, source hashes, config, native libraries, and
   harness. Fresh-compile all affected files and independently recount that exact
   patch. Include every selected file, including regressions. Stop census workers,
   native builds, compression and other experiment workloads before sampling.
2. Collect a new 24-pair calibration pilot and one warmup pair on that exact frozen
   workload. Use one Lean thread, serial whole-file compilation, alternating
   original/replacement order, common dependency order, real variant headers and
   native imports, warm dependencies, and fresh outputs every repetition. Record
   source/header/setup cost separately. The outcome measures warm Lean module
   compilation and generated C/IR, not C object compilation or all of Mathlib.
3. Review only speed-level-blinded serial/order/drift diagnostics from that pilot:
   centered variant durations, centered paired log ratios, lag correlations,
   AB-versus-BA differences, and half-run drift. Use four-pair blocks by default;
   choose eight only with a written dependence rationale. Do not expose average
   speed, confidence intervals or significance to this decision. If neither size
   is defensible, retain the pilot and do not declare a confirmatory result.
4. Freeze the dated calibration and final plan before confirmatory setup. Use
   exactly 40 measured pairs for four-pair blocks, or exactly 80 for eight-pair
   blocks, giving ten whole blocks in either case. Collect one fresh warmup pair.
   Do not pool pilot samples, drop outliers, stop for significance, or increase the
   sample count after inspecting the effect. Ten blocks are limited evidence;
   calibration does not prove independence or guarantee interval coverage.
5. Primary statistic: mean original full-pass total / mean replacement full-pass
   total. Use the existing paired whole-block BCa implementation, 95% interval,
   10,000 resamples, seed 20261020, whole-block jackknife and all affected files.
   A speed claim requires a valid calibrated lower endpoint strictly above one.
   Report all file regressions and the ratio/interval if this gate fails. An
   undefined interval is not a successful speed result.
6. Retain the full pilot, calibration decision, immutable pre-sampling plan,
   compiler commands/logs, fresh output hashes, raw pairs and independent
   statistics check. If code or patch changes after calibration, preserve that
   study and start a separately labelled study with new calibration.

The original 41-line timing study and portable paper evidence remain intact.
Only a successful new matched study can attach a compilation ratio to the final
expanded line count. If speed does not improve, the expanded source simplification
can still be reported honestly with its observed compilation cost.
