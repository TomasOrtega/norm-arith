#!/usr/bin/env python3
"""Independently check the recorded expanded study without project imports."""

import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
import math
from pathlib import Path
import random
import statistics
import sys


ROOT = Path(__file__).resolve().parents[3]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path):
    return json.loads(path.read_text())


def code_lines(source):
    count, depth, index = 0, 0, 0
    code = quoted = escaped = False
    while index < len(source):
        char, pair = source[index], source[index:index + 2]
        if char == "\n":
            count += code
            code = False
            index += 1
            continue
        if depth:
            if pair == "/-":
                depth += 1
                index += 2
            elif pair == "-/":
                depth -= 1
                index += 2
            else:
                index += 1
            continue
        if quoted:
            code |= not char.isspace()
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                quoted = False
            index += 1
            continue
        if pair == "--":
            newline = source.find("\n", index)
            index = len(source) if newline < 0 else newline
            continue
        if pair == "/-":
            depth = 1
            index += 2
            continue
        if char == '"':
            quoted = True
        code |= not char.isspace()
        index += 1
    assert depth == 0 and not quoted
    return count + code


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--study", type=Path,
                        default=ROOT / ".lake/expanded-study-20261021")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    study = args.study.resolve()
    paths = {
        "report": study / "confirmation/report.json",
        "measurements": study / "confirmation/measurements.jsonl",
        "analysis_plan": study / "confirmation/analysis-plan.json",
        "frozen_manifest": study / "frozen/manifest.json",
        "patch": study / "confirmation/mathlib.patch",
        "calibration": study / "calibration.json",
        "blinded_review": study / "pilot-calibration-review.json",
        "calibration_decision": study / "calibration-decision-receipt-v2.json",
        "calibration_root_check": study / "calibration-root-check.json",
        "verified_manifest": ROOT / "benchmarks/expansion/verified-05/manifest.json",
        "source_audit": ROOT / "benchmarks/expansion/verified-05/independent-audit.json",
        "source_verification": ROOT / "benchmarks/expansion/verified-05/verification-receipt.json",
        "output_byte_audit": study / "timed-output-byte-audit.json",
        "output_byte_audit_script": ROOT / "artifacts/expansion/audit_study_bytes.py",
        "power_before": ROOT / "artifacts/expansion/machine-profile-before-study.json",
        "power_after": ROOT / "artifacts/expansion/machine-profile-after-study.json",
        "review_script": Path(__file__).resolve(),
    }
    report = read(paths["report"])
    plan = read(paths["analysis_plan"])
    frozen = read(paths["frozen_manifest"])
    verified = read(paths["verified_manifest"])
    audit = read(paths["source_audit"])
    calibration = read(paths["calibration"])
    decision = read(paths["calibration_decision"])
    root_check = read(paths["calibration_root_check"])
    rows = [json.loads(line) for line in paths["measurements"].read_text().splitlines()
            if line.strip()]
    assert report["status"] == "complete" and rows == report["measurements"]
    selected = [c for c in frozen["candidates"] if c["status"] == "replace"]
    assert selected == [c for c in verified["candidates"] if c["status"] == "replace"]
    files = {c["path"] for c in selected}
    assert files == set(plan["affected_files"]) == set(report["compilation_order"])
    assert len(files) == 46 and len(selected) == 87
    assert digest(paths["frozen_manifest"]) == report["provenance"]["manifest_sha256"]
    assert digest(paths["patch"]) == audit["patch_sha256"]
    assert digest(paths["patch"]) == report["provenance"]["proposed_patch_sha256"]
    assert digest(paths["calibration"]) == report["inference"]["calibration_sha256"]
    assert digest(paths["analysis_plan"]) == report["analysis_plan"]["sha256"]
    assert digest(paths["calibration"]) == decision["input_sha256"]["calibration"]
    assert digest(paths["blinded_review"]) == decision["input_sha256"]["blinded_review"]
    assert digest(paths["calibration"]) == root_check["calibration_sha256"]
    assert digest(paths["blinded_review"]) == root_check["blinded_review_sha256"]
    assert decision["decided_at_utc"] < root_check["checked_at_utc"] < plan["frozen_at_utc"]
    assert decision["speed_level_blinded"] and not decision["pilot_or_confirmatory_speed_effect_inspected"]
    assert not root_check["speed_effect_inspected"]
    assert plan["measured_pairs"] == 40 and plan["warmup_pairs"] == 1
    assert plan["interval"]["block_pairs"] == calibration["block_pairs"] == 4
    assert calibration["predeclared_confirmatory_pairs"] == 40
    assert report["resolved_calibration_match"]
    assert read(paths["source_verification"])["project_lean_sources"] == report["provenance"]["project_lean_sources"]
    byte_audit = read(paths["output_byte_audit"])
    assert byte_audit["status"] == "all_live_timing_outputs_and_frozen_inputs_rehashed"
    assert byte_audit["helper_sha256"] == digest(paths["output_byte_audit_script"])
    assert byte_audit["frozen_manifest_sha256"] == digest(paths["frozen_manifest"])
    assert byte_audit["pilot_confirmation_resolved_runtime_equal"]
    for name, key in [("report", "report_sha256"), ("measurements", "raw_measurements_sha256"),
                      ("analysis_plan", "analysis_plan_sha256")]:
        assert digest(paths[name]) == byte_audit["runs"]["confirmation"][key]
    expected = {(phase, pair, variant, file)
                for phase, count in [("warmup", 1), ("measured", 40)]
                for pair in range(count) for variant in ("original", "replacement")
                for file in files}
    actual = [(r["phase"], r["pair"], r["variant"], r["path"]) for r in rows]
    assert len(actual) == len(set(actual)) and set(actual) == expected
    assert all(r["returncode"] == 0 and not r["timed_out"]
               and r["compilation_status"] == "verified"
               and math.isfinite(r["seconds"]) and r["seconds"] > 0
               and len(r["artifact_sha256"]) == 7 for r in rows)
    assert all(r["returncode"] == 0 for r in report["setup"])
    output_paths = [path for row in rows for path in row["artifact_sha256"]]
    assert len(output_paths) == len(set(output_paths)) == 26404
    recorded_study = Path(report["analysis_plan"]["path"]).parent.parent
    for row in rows:
        for path, expected_hash in row["artifact_sha256"].items():
            relative = str(Path(path).relative_to(recorded_study))
            entry = byte_audit["output_inventory"][relative]
            assert entry["sha256"] == expected_hash and entry["bytes"] > 0
    for phase, count in [("warmup", 1), ("measured", 40)]:
        for pair in range(count):
            pair_rows = [r for r in rows if r["phase"] == phase and r["pair"] == pair]
            order = ["original", "replacement"] if pair % 2 == 0 else ["replacement", "original"]
            assert [r["variant"] for r in pair_rows] == [v for v in order for _ in files]
            assert [r["path"] for r in pair_rows[:46]] == report["compilation_order"]
            assert [r["path"] for r in pair_rows[46:]] == report["compilation_order"]
    totals = {variant: [sum(r["seconds"] for r in rows if r["phase"] == "measured"
                           and r["pair"] == pair and r["variant"] == variant)
                        for pair in range(40)] for variant in ("original", "replacement")}
    blocks = [(sum(totals["original"][i:i + 4]), sum(totals["replacement"][i:i + 4]))
              for i in range(0, 40, 4)]
    estimate = sum(totals["original"]) / sum(totals["replacement"])
    generator = random.Random(plan["interval"]["seed"])
    draws = []
    for _ in range(plan["interval"]["resamples"]):
        sample = [blocks[generator.randrange(10)] for _ in range(10)]
        draws.append(sum(b[0] for b in sample) / sum(b[1] for b in sample))
    normal = statistics.NormalDist()
    bias = normal.inv_cdf((sum(value < estimate for value in draws)
                          + 0.5 * sum(value == estimate for value in draws)) / len(draws))
    jackknife = [sum(b[0] for j, b in enumerate(blocks) if j != i)
                 / sum(b[1] for j, b in enumerate(blocks) if j != i) for i in range(10)]
    jack_mean = sum(jackknife) / len(jackknife)
    differences = [jack_mean - value for value in jackknife]
    acceleration = sum(d ** 3 for d in differences) / (6 * sum(d * d for d in differences) ** 1.5)
    probabilities = [normal.cdf(bias + (bias + normal.inv_cdf(p))
                                / (1 - acceleration * (bias + normal.inv_cdf(p))))
                     for p in (0.025, 0.975)]
    draws.sort()
    interval = []
    for probability in probabilities:
        position = probability * (len(draws) - 1)
        lower, upper = math.floor(position), math.ceil(position)
        interval.append(draws[lower] + (position - lower) * (draws[upper] - draws[lower]))
    inference = report["inference"]
    assert math.isclose(estimate, inference["estimate"], abs_tol=1e-12)
    for value, key in zip(interval, ("lower", "upper")):
        assert abs(value - inference["interval"][key]) < 1e-12
    original_lines = replacement_lines = 0
    source_hashes = {}
    expected_sources = {file["path"]: file["source_sha256"] for file in frozen["files"]}
    for candidate in selected:
        path = ROOT / ".lake/packages/mathlib" / candidate["path"]
        data = path.read_bytes()
        source_hashes[candidate["path"]] = hashlib.sha256(data).hexdigest()
        assert source_hashes[candidate["path"]] == expected_sources[candidate["path"]]
        span = b"".join(data.splitlines(keepends=True)[candidate["start_line"] - 1:candidate["end_line"]])
        assert hashlib.sha256(span).hexdigest() == candidate["original_sha256"]
        before, after = code_lines(span.decode()), code_lines(candidate["replacement"])
        assert before == candidate["original_proof_lines"] and after == candidate["replacement_proof_lines"]
        original_lines += before
        replacement_lines += after
    imports = sum(len(f["imports"]) for f in frozen["files"] if f["path"] in files)
    assert not any(f["helpers"] for f in frozen["files"] if f["path"] in files)
    assert (original_lines, replacement_lines, imports) == (582, 226, 46)
    assert report["accounting"]["original_proof_lines"] == original_lines
    assert report["accounting"]["replacement_proof_lines"] == replacement_lines
    assert report["accounting"]["added_import_lines"] == imports
    assert report["accounting"]["net_lines_saved_including_imports"] == original_lines - replacement_lines - imports
    census_generated = sum(c["id"].startswith("census-") for c in selected)
    assert census_generated == 50
    measured = [r for r in rows if r["phase"] == "measured"]
    per_file = {file: {variant: sum(r["seconds"] for r in measured
                                  if r["path"] == file and r["variant"] == variant) / 40
                       for variant in ("original", "replacement")} for file in sorted(files)}
    slower = [file for file, means in per_file.items() if means["replacement"] > means["original"]]
    output = {
        "schema_version": 1,
        "status": "independent_raw_retention_statistics_and_source_accounting_passed",
        "created_at_utc": datetime.now(timezone.utc).isoformat(),
        "runtime": sys.version,
        "scope": "Independent stdlib computation, with no imports from the benchmark, paper, or other audit code. Output-file hash metadata is checked here; actual output bytes require the separate byte audit.",
        "input_files": {key: {"path": str(path), "sha256": digest(path)} for key, path in paths.items()},
        "source_sha256": source_hashes,
        "retention": {"measured_pairs": 40, "warmup_pairs": 1, "affected_files": 46,
                      "measured_rows": 3680, "warmup_rows": 92, "unique_output_hash_entries": 26404,
                      "setup_successes": len(report["setup"]), "slower_files_retained": slower,
                      "all_rows_equal_report": True, "complete_unique_cartesian_product": True,
                      "alternating_order_and_common_file_order": True},
        "accounting": {"replacements": 87, "files": 46, "original_proof_lines": original_lines,
                       "replacement_proof_lines": replacement_lines, "added_import_lines": imports,
                       "added_helper_lines": 0, "net_lines_saved": original_lines - replacement_lines - imports,
                       "census_generated_ids": census_generated,
                       "outside_census_ids": len(selected) - census_generated,
                       "manual_review_flags": dict(Counter(str(c.get("manual_review", False)) for c in selected))},
        "timing": {"original_mean_seconds": sum(totals["original"]) / 40,
                   "replacement_mean_seconds": sum(totals["replacement"]) / 40,
                   "ratio": estimate, "elapsed_time_reduction_fraction": 1 - 1 / estimate,
                   "block_pairs": 4, "block_count": 10, "bootstrap_resamples": len(draws),
                   "bootstrap_seed": plan["interval"]["seed"], "conditional_95_percent_BCa": interval,
                   "bias_correction": bias, "acceleration": acceleration,
                   "maximum_endpoint_difference_from_report": max(abs(interval[i] - inference["interval"][key])
                                                                  for i, key in enumerate(("lower", "upper"))),
                   "half_run_relative_duration_changes": {variant: sum(values[20:]) / sum(values[:20]) - 1
                                                          for variant, values in totals.items()}},
        "limitations": ["Independent, representative blocks remain assumptions, not established facts.",
                        "The calibration pilot had relative drift; doubling block length would not establish stationarity.",
                        "This is warm affected-file Lean compilation against the existing proofs, including actual import differences.",
                        "The result does not measure whole-Mathlib, cold-build, or isolated algorithm performance.",
                        "Before/after power snapshots do not establish continuous AC operation; the final battery state says discharging and thermal status is unavailable.",
                        "The source lexer recount is scoped to these observed proof spans, not a general Lean lexer certification."],
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(output, indent=2) + "\n")
    print(json.dumps({"status": output["status"], "receipt": str(args.output),
                      "receipt_sha256": digest(args.output), "accounting": output["accounting"],
                      "timing": output["timing"], "slower_files_retained": len(slower)}, indent=2))


if __name__ == "__main__":
    main()
