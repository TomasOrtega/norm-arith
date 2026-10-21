#!/usr/bin/env python3
"""Descriptive serial diagnostics for a completed 24-pair benchmark pilot."""

import argparse
import hashlib
import json
import math
from pathlib import Path
import statistics
import sys

PROJECT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(PROJECT / "scripts"))
from benchmark import BenchmarkError, paired_blocks, paired_totals


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def autocorrelations(values):
    center = statistics.fmean(values)
    denominator = math.fsum((value - center) ** 2 for value in values)
    return {
        str(lag): (
            math.fsum((values[t] - center) * (values[t - lag] - center)
                      for t in range(lag, len(values))) / denominator
            if lag < len(values) and denominator > 0 else None
        )
        for lag in range(1, 5)
    }


def describe(original, replacement):
    logs = [math.log(a / b) for a, b in zip(original, replacement)]
    return {
        "pairs_or_blocks": len(original),
        "original_mean_seconds": statistics.fmean(original),
        "replacement_mean_seconds": statistics.fmean(replacement),
        "ratio_of_means": math.fsum(original) / math.fsum(replacement),
        "mean_log_paired_ratio": statistics.fmean(logs),
        "sample_sd_log_paired_ratio": statistics.stdev(logs) if len(logs) > 1 else None,
    }


def diagnostics(report, measurements):
    if report.get("schema_version") != 1 or report.get("status") != "complete":
        raise ValueError("requires a completed schema-version 1 benchmark report")
    repetitions = report["provenance"]["repetitions"]
    if repetitions != 24:
        raise ValueError("this pre-pilot diagnostic plan requires exactly 24 measured pairs")
    if report.get("measurements") != measurements:
        raise ValueError("raw measurements differ from the report measurements")
    paths = report["compilation_order"]
    totals = paired_totals(measurements, paths, repetitions)
    paired_blocks(measurements, paths, repetitions, 2)
    original, replacement = totals["original"], totals["replacement"]
    logs = [math.log(a / b) for a, b in zip(original, replacement)]
    series = {"original_seconds": original, "replacement_seconds": replacement,
              "log_paired_ratio": logs}
    sequence = {}
    for parity, label in [(0, "AB"), (1, "BA")]:
        sequence[label] = describe(original[parity::2], replacement[parity::2])
    first = describe(original[:12], replacement[:12])
    second = describe(original[12:], replacement[12:])
    blocks = {}
    for length in [2, 4, 8]:
        rows = paired_blocks(measurements, paths, repetitions, length)
        o = [row["original_seconds"] / length for row in rows]
        r = [row["replacement_seconds"] / length for row in rows]
        block_logs = [math.log(a / b) for a, b in zip(o, r)]
        blocks[str(length)] = {
            "pilot_blocks": len(rows), "confirmatory_blocks_at_40_pairs": 40 // length,
            "block_rows": [
                {"block_index": index, **row,
                 "AB_pairs": length // 2, "BA_pairs": length // 2,
                 "original_mean_seconds_per_pair": o[index],
                 "replacement_mean_seconds_per_pair": r[index],
                 "ratio_of_totals": o[index] / r[index],
                 "log_ratio_of_totals": block_logs[index],
                 "mean_log_paired_ratio": statistics.fmean(logs[row["pairs"][0]:row["pairs"][-1] + 1])}
                for index, row in enumerate(rows)
            ],
            "summary_of_block_pair_means": describe(o, r),
            "lag_autocorrelations": {
                "original_mean_seconds_per_pair": autocorrelations(o),
                "replacement_mean_seconds_per_pair": autocorrelations(r),
                "log_ratio_of_block_totals": autocorrelations(block_logs),
            },
        }
    return {
        "schema_version": 1,
        "scope": "descriptive diagnostics only; no block selection, significance test or confidence interval",
        "repetitions": repetitions, "affected_file_count": len(paths), "affected_files": paths,
        "sequence_definition": {"A": "original", "B": "replacement",
                                "even_zero_based_pair": "AB", "odd_zero_based_pair": "BA"},
        "log_ratio_definition": "natural log(original full-pass seconds / replacement full-pass seconds)",
        "autocorrelation_definition": "sum_{t=k}^{n-1} (x[t]-mean(x))*(x[t-k]-mean(x)) / sum_{t=0}^{n-1} (x[t]-mean(x))^2",
        "undefined_autocorrelations": "null when lag>=series length or centered sum of squares is zero",
        "chronological_pairs": [
            {"pair_index": i, "pair_number": i + 1, "sequence": "AB" if i % 2 == 0 else "BA",
             "original_seconds": original[i], "replacement_seconds": replacement[i],
             "ratio": original[i] / replacement[i], "log_paired_ratio": logs[i]}
            for i in range(repetitions)
        ],
        "all_pairs": describe(original, replacement),
        "lag_autocorrelations": {key: autocorrelations(values) for key, values in series.items()},
        "sequence_means": sequence,
        "AB_minus_BA": {
            key: sequence["AB"][key] - sequence["BA"][key]
            for key in ["original_mean_seconds", "replacement_mean_seconds", "mean_log_paired_ratio"]
        },
        "half_run_drift": {
            "first_half_pair_indices": [0, 11], "second_half_pair_indices": [12, 23],
            "first_half": first, "second_half": second,
            "original_relative_mean_change": second["original_mean_seconds"] / first["original_mean_seconds"] - 1,
            "replacement_relative_mean_change": second["replacement_mean_seconds"] / first["replacement_mean_seconds"] - 1,
            "change_in_mean_log_paired_ratio": second["mean_log_paired_ratio"] - first["mean_log_paired_ratio"],
        },
        "compatible_block_diagnostics": blocks,
        "limitations": [
            "Warmups are retained in input hashes but excluded from these summaries.",
            "Only full-pass totals are analyzed; files are not sampling units.",
            "AB/BA differences are descriptive and can mix sequence effects with time drift.",
            "Half-run drift is descriptive, not a fitted drift correction or a stationarity test.",
            "With 24 pairs, candidate block lengths 2,4,8 leave 12,6,3 pilot blocks; autocorrelations are noisy.",
            "An absent or small sample autocorrelation does not establish block independence or representativeness.",
            "These diagnostics do not justify coverage under arbitrary dependence or choose a calibration rationale.",
            "Ratios of means and means of log ratios are different summaries; neither replaces the frozen confirmatory statistic.",
            "Input hashes bind recorded bytes; this script does not revalidate compiler outputs or live runtime inputs.",
        ],
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("report", type=Path)
    parser.add_argument("--measurements", type=Path)
    parser.add_argument("--output", type=Path, help="new JSON file; default stdout")
    args = parser.parse_args()
    raw = args.measurements or args.report.parent / "measurements.jsonl"
    try:
        report_bytes, raw_bytes = args.report.read_bytes(), raw.read_bytes()
        report = json.loads(report_bytes)
        measurements = [json.loads(line) for line in raw_bytes.splitlines() if line.strip()]
        result = diagnostics(report, measurements)
        result["input_sha256"] = {
            "report": {"path": str(args.report.resolve()), "sha256": hashlib.sha256(report_bytes).hexdigest()},
            "measurements": {"path": str(raw.resolve()), "sha256": hashlib.sha256(raw_bytes).hexdigest()},
            "diagnostic_script": {"path": str(Path(__file__).resolve()), "sha256": sha256(Path(__file__))},
            "benchmark_script": {"path": str(PROJECT / "scripts/benchmark.py"), "sha256": sha256(PROJECT / "scripts/benchmark.py")},
        }
        plan = args.report.parent / "analysis-plan.json"
        if plan.is_file():
            result["input_sha256"]["analysis_plan"] = {"path": str(plan.resolve()), "sha256": sha256(plan)}
        result["recorded_measurement_protocol_sha256"] = report["provenance"].get("measurement_protocol_sha256")
        text = json.dumps(result, indent=2, allow_nan=False) + "\n"
        if args.output:
            with args.output.open("x") as stream:
                stream.write(text)
        else:
            print(text, end="")
        return 0
    except (BenchmarkError, ValueError, KeyError, TypeError, OSError) as error:
        print(f"pilot diagnostics failed: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
