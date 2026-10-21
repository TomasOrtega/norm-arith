#!/usr/bin/env python3
"""Independently check the fixed 40-pair, four-pair-block BCa analysis.

Run only after timing ends. This checks arithmetic and recorded rows, not proof
artifacts, runtime provenance, or the independent representative-block assumption.
It imports no benchmark or paper code.
"""

import argparse
import hashlib
import json
import math
from pathlib import Path
import platform
import random
from statistics import NormalDist
import sys

FILES = (
    "Mathlib/Analysis/Calculus/FDeriv/Basic.lean",
    "Mathlib/Analysis/Normed/Module/Multilinear/Basic.lean",
    "Mathlib/Analysis/Calculus/FDeriv/Measurable.lean",
    "Mathlib/Analysis/Convex/Uniform.lean",
    "Mathlib/Analysis/Normed/Field/Approximation.lean",
    "Mathlib/Computability/AkraBazzi/GrowsPolynomially.lean",
    "Mathlib/MeasureTheory/Function/L1Space/Integrable.lean",
    "Mathlib/MeasureTheory/Integral/DominatedConvergence.lean",
    "Mathlib/MeasureTheory/Measure/SeparableMeasure.lean",
    "Mathlib/NumberTheory/Padics/Hensel.lean",
    "Mathlib/Topology/MetricSpace/GromovHausdorff.lean",
)
PAIRS, BLOCK_PAIRS, RESAMPLES, SEED, TOLERANCE = 40, 4, 10000, 20261020, 1e-12


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def compare(actual, expected, label):
    if isinstance(expected, bool) or expected is None or isinstance(expected, str):
        require(type(actual) is type(expected) and actual == expected, f"{label}: metadata mismatch")
    elif isinstance(expected, (int, float)):
        require(type(actual) in (int, float) and math.isfinite(actual)
                and abs(actual - expected) <= TOLERANCE, f"{label}: {actual!r} != {expected!r}")
    elif isinstance(expected, list):
        require(isinstance(actual, list) and len(actual) == len(expected), f"{label}: length mismatch")
        for index, value in enumerate(expected):
            compare(actual[index], value, f"{label}[{index}]")
    else:
        require(isinstance(actual, dict), f"{label}: expected object")
        for key, value in expected.items():
            require(key in actual, f"{label}: missing {key}")
            compare(actual[key], value, f"{label}.{key}")


def read_passes(rows):
    expected = []
    for phase, count in [("warmup", 1), ("measured", PAIRS)]:
        for pair in range(count):
            order = ("original", "replacement") if pair % 2 == 0 else ("replacement", "original")
            expected.extend((phase, pair, variant, path) for variant in order for path in FILES)
    require(len(rows) == len(expected), "missing or extra raw records")
    measured = {"original": [[] for _ in range(PAIRS)], "replacement": [[] for _ in range(PAIRS)]}
    for index, (row, key) in enumerate(zip(rows, expected)):
        require(isinstance(row, dict), f"raw row {index}: expected object")
        actual = (row.get("phase"), row.get("pair"), row.get("variant"), row.get("path"))
        require(type(row.get("pair")) is int and actual == key, f"raw row {index}: wrong key/order")
        require(type(row.get("returncode")) is int and row["returncode"] == 0
                and row.get("timed_out") is False, f"raw row {index}: failed/missing compiler result")
        seconds = row.get("seconds")
        require(type(seconds) in (int, float) and math.isfinite(seconds) and seconds > 0,
                f"raw row {index}: invalid duration")
        if row["phase"] == "measured":
            measured[row["variant"]][row["pair"]].append(seconds)
    return {variant: [math.fsum(values) for values in passes] for variant, passes in measured.items()}


def analyze(totals):
    blocks = [
        {"pairs": list(range(start, start + BLOCK_PAIRS)),
         "original_seconds": math.fsum(totals["original"][start:start + BLOCK_PAIRS]),
         "replacement_seconds": math.fsum(totals["replacement"][start:start + BLOCK_PAIRS])}
        for start in range(0, PAIRS, BLOCK_PAIRS)
    ]
    count = len(blocks)

    def ratio(indices):
        return math.fsum(blocks[i]["original_seconds"] for i in indices) / math.fsum(
            blocks[i]["replacement_seconds"] for i in indices)

    estimate = ratio(range(count))
    rng = random.Random(SEED)
    draws = []
    for _ in range(RESAMPLES):
        indices = [rng.randrange(count) for _ in range(count)]
        draws.append(ratio(indices))
    below = sum(value < estimate for value in draws)
    tied = sum(value == estimate for value in draws)
    probability = (below + tied / 2) / RESAMPLES
    require(min(draws) != max(draws) and 0 < probability < 1, "undefined BCa bias correction")
    normal = NormalDist()
    z0 = normal.inv_cdf(probability)
    jackknife = [ratio([i for i in range(count) if i != omitted]) for omitted in range(count)]
    center = math.fsum(jackknife) / count
    deviations = [center - value for value in jackknife]
    squared = math.fsum(value ** 2 for value in deviations)
    require(squared > 0, "undefined BCa jackknife acceleration")
    acceleration = math.fsum(value ** 3 for value in deviations) / (6 * squared ** 1.5)
    adjusted, endpoints, interpolation = [], [], []
    draws.sort()
    for tail in [0.025, 0.975]:
        shifted = z0 + normal.inv_cdf(tail)
        denominator = 1 - acceleration * shifted
        require(denominator > 0, "BCa acceleration pole")
        q = normal.cdf(z0 + shifted / denominator)
        require(1 / RESAMPLES <= q <= 1 - 1 / RESAMPLES, "BCa endpoint beyond Monte Carlo resolution")
        position = (RESAMPLES - 1) * q
        low = math.floor(position)
        fraction = position - low
        high = min(low + 1, RESAMPLES - 1)
        endpoints.append((1 - fraction) * draws[low] + fraction * draws[high])
        adjusted.append(q)
        interpolation.append({"tail": tail, "position": position, "lower_index": low,
                              "upper_index": high, "fraction": fraction})
    require(all(math.isfinite(x) for x in endpoints) and endpoints[0] <= endpoints[1], "invalid BCa endpoints")
    means = {variant: math.fsum(values) / PAIRS for variant, values in totals.items()}
    compare(means["original"] / means["replacement"], estimate, "ratio of means versus block sums")
    inference = {
        "primary_statistic": "ratio_of_mean_pass_totals",
        "original_mean_seconds": means["original"], "replacement_mean_seconds": means["replacement"],
        "estimate": estimate,
        "interval": {"status": "valid", "confidence_level": 0.95,
                     "lower": endpoints[0], "upper": endpoints[1], "bias_correction": z0,
                     "acceleration": acceleration, "adjusted_quantiles": adjusted,
                     "bootstrap_distribution_sha256": digest(json.dumps(draws).encode())},
        "block_pairs": BLOCK_PAIRS, "block_count": count, "blocks": blocks,
        "bootstrap_resamples": RESAMPLES, "bootstrap_seed": SEED,
        "success_criterion_met": endpoints[0] > 1,
    }
    derivation = {
        "raw_record_count": 2 * len(FILES) * (PAIRS + 1), "warmup_record_count": 2 * len(FILES),
        "measured_record_count": 2 * len(FILES) * PAIRS, "affected_file_count": len(FILES),
        "paired_passes": PAIRS, "variant_passes": PAIRS * 2, "block_pairs": BLOCK_PAIRS,
        "blocks": count, "bootstrap_replicates": RESAMPLES, "indices_per_replicate": count,
        "bootstrap_below_estimate": below, "bootstrap_tied_estimate": tied,
        "bias_probability": probability, "whole_block_jackknife_estimates": jackknife,
        "jackknife_center": center, "jackknife_sum_squared_deviations": squared,
        "endpoint_interpolation": interpolation,
    }
    return inference, derivation


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("report", type=Path)
    parser.add_argument("--measurements", type=Path)
    parser.add_argument("--plan", type=Path)
    parser.add_argument("--output", type=Path, help="new output JSON; default stdout")
    args = parser.parse_args()
    raw_path = args.measurements or args.report.parent / "measurements.jsonl"
    plan_path = args.plan or args.report.parent / "analysis-plan.json"
    try:
        report_bytes, raw_bytes, plan_bytes = args.report.read_bytes(), raw_path.read_bytes(), plan_path.read_bytes()
        report, plan = json.loads(report_bytes), json.loads(plan_bytes)
        rows = [json.loads(line) for line in raw_bytes.splitlines() if line.strip()]
        compare(report, {"schema_version": 1, "status": "complete", "compilation_order": list(FILES),
                         "provenance": {"repetitions": PAIRS, "warmups": 1},
                         "resolved_calibration_match": True,
                         "inference": {"mode": "confirmatory", "calibration_validated": True, "inputs_unchanged": True}}, "report")
        compare(plan, {"schema_version": 1, "mode": "confirmatory", "measured_pairs": PAIRS,
                       "warmup_pairs": 1, "selection_status": "frozen",
                       "pair_order": "even: original then replacement; odd: replacement then original",
                       "all_affected_files_and_pairs_retained": True,
                       "primary_statistic": "ratio_of_mean_pass_totals",
                       "interval": {"method": "paired_nonoverlapping_equal_block_BCa", "confidence_level": 0.95,
                                    "block_pairs": BLOCK_PAIRS, "resamples": RESAMPLES, "seed": SEED,
                                    "bias_ties": "half_weight", "quantile": "linear_interpolation_at_p_times_n_minus_one",
                                    "acceleration": "delete_one_whole_block_jackknife",
                                    "success": "valid calibrated interval with lower endpoint strictly greater than one"},
                       "calibration": {"block_pairs": BLOCK_PAIRS}}, "plan")
        require(len(plan["affected_files"]) == len(FILES) and set(plan["affected_files"]) == set(FILES), "plan affected-file mismatch")
        require(report["analysis_plan"]["sha256"] == digest(plan_bytes), "report analysis-plan hash mismatch")
        require(rows == report["measurements"], "raw rows differ from report measurements")
        totals = read_passes(rows)
        expected, derivation = analyze(totals)
        compare(report["inference"], expected, "inference")
        for variant in ["original", "replacement"]:
            compare(report["summary"]["aggregate"][variant]["seconds"], totals[variant], f"summary.{variant}.passes")
        result = {
            "schema_version": 1, "status": "verified", "absolute_numeric_tolerance": TOLERANCE,
            "input_sha256": {"report": digest(report_bytes), "measurements": digest(raw_bytes),
                             "analysis_plan": digest(plan_bytes), "verifier": digest(Path(__file__).read_bytes())},
            "python": {"implementation": platform.python_implementation(), "version": platform.python_version()},
            "methods": {
                "estimate": "sum original full-pass times / sum replacement full-pass times",
                "sampling_unit": "one contiguous four-pair block; all11 files and both variants stay together",
                "PRNG": "random.Random(20261020); 10000 replicates;10 successive randrange(10) calls per replicate",
                "bias": "Phi^-1((count(draw<estimate)+0.5*count(draw==estimate))/10000)",
                "acceleration": "sum((mean(jackknife)-jackknife_i)^3)/(6*sum((mean(jackknife)-jackknife_i)^2)^1.5)",
                "adjustment": "Phi(z0+(z0+Phi^-1(alpha))/(1-a*(z0+Phi^-1(alpha)))) at alpha=.025,.975",
                "quantile": "linear interpolation at q*(10000-1) in sorted bootstrap ratios",
                "references": ["https://doi.org/10.1080/01621459.1987.10478410", "https://doi.org/10.1214/ss/1032280214"],
                "implementation_conventions": "half-weight ties, CPython PRNG calls and empirical interpolation are recorded choices",
            },
            "derivation": derivation, "recomputed_inference": expected,
            "limitations": "Arithmetic agreement does not validate independent representative blocks, empirical coverage, proof correctness or live runtime provenance.",
        }
        output = json.dumps(result, indent=2, allow_nan=False) + "\n"
        if args.output:
            with args.output.open("x") as stream:
                stream.write(output)
        else:
            print(output, end="")
        return 0
    except (ValueError, KeyError, TypeError, OSError, OverflowError) as error:
        print(f"independent confirmatory verification failed: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
