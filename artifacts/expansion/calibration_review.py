#!/usr/bin/env python3
"""Emit pilot dependence diagnostics without exposing the average speed effect."""

import argparse
import hashlib
import importlib.util
import json
from pathlib import Path


SOURCE = Path(__file__).resolve().parents[1] / "pilot_serial_diagnostics.py"
SPEC = importlib.util.spec_from_file_location("pilot_serial_diagnostics", SOURCE)
PILOT = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(PILOT)


def blinded_review(report, measurements):
    diagnostics = PILOT.diagnostics(report, measurements)
    overall = diagnostics["all_pairs"]
    order = diagnostics["AB_minus_BA"]
    drift = diagnostics["half_run_drift"]
    return {
        "schema_version": 1,
        "scope": "Speed-level-blinded calibration; no absolute durations, mean speed ratio, confidence interval or significance.",
        "measured_pairs": diagnostics["repetitions"],
        "affected_files": diagnostics["affected_file_count"],
        "pair_series_autocorrelations": diagnostics["lag_autocorrelations"],
        "AB_minus_BA": {
            "original_relative_duration_difference": order["original_mean_seconds"] / overall["original_mean_seconds"],
            "replacement_relative_duration_difference": order["replacement_mean_seconds"] / overall["replacement_mean_seconds"],
            "mean_log_paired_ratio_difference": order["mean_log_paired_ratio"],
        },
        "half_run_drift": {key: drift[key] for key in [
            "original_relative_mean_change", "replacement_relative_mean_change", "change_in_mean_log_paired_ratio"]},
        "candidate_blocks": {
            str(length): {
                "pilot_blocks": diagnostics["compatible_block_diagnostics"][str(length)]["pilot_blocks"],
                "confirmatory_pairs": 10 * length,
                "confirmatory_blocks": 10,
                "lag_autocorrelations": diagnostics["compatible_block_diagnostics"][str(length)]["lag_autocorrelations"],
            } for length in [4, 8]
        },
        "limits": "Pilot autocorrelations are noisy: six blocks of four or three blocks of eight. Independence is assumed, not proved. Neither candidate being defensible means retain the pilot without a confirmatory claim.",
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("report", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    raw_path = args.report.parent / "measurements.jsonl"
    report_bytes, raw_bytes = args.report.read_bytes(), raw_path.read_bytes()
    report = json.loads(report_bytes)
    measurements = [json.loads(line) for line in raw_bytes.splitlines() if line.strip()]
    result = blinded_review(report, measurements)
    result["input_sha256"] = {
        "pilot_report": hashlib.sha256(report_bytes).hexdigest(),
        "pilot_measurements": hashlib.sha256(raw_bytes).hexdigest(),
        "diagnostic_source": hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
        "review_source": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    }
    with args.output.open("x") as stream:
        stream.write(json.dumps(result, indent=2, allow_nan=False) + "\n")


if __name__ == "__main__":
    main()
