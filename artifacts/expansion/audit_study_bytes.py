#!/usr/bin/env python3
"""Recheck live expanded-study inputs and every fresh compiler output."""

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import subprocess


ROOT = Path(__file__).resolve().parents[2]


def require(value, message):
    if not value:
        raise ValueError(message)


def sha(path):
    value = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            value.update(block)
    return value.hexdigest()


def audit(study):
    study = study.resolve()
    checked, artifacts, summaries, reports = {}, {}, {}, {}

    def check(name, expected):
        path = Path(name).resolve(strict=True)
        require(path.is_file() and not Path(name).is_symlink(), "missing or linked evidence: " + name)
        actual = checked.get(str(path))
        if actual is None:
            actual = checked[str(path)] = sha(path)
        require(actual == expected, "changed bytes: " + name)
        return path

    frozen = study / "frozen/manifest.json"
    manifest_sha = sha(frozen)
    source_inventory = {str(p.relative_to(ROOT)): sha(p) for p in
                        sorted(set(ROOT.glob("NormArith*.lean")) |
                               set((ROOT / "NormArith").rglob("*.lean")) |
                               set((ROOT / "NormArithTest").rglob("*.lean")))}
    for label, pairs in [("pilot", 24), ("confirmation", 40)]:
        run = study / label
        report = reports[label] = json.loads((run / "report.json").read_bytes())
        plan_bytes = (run / "analysis-plan.json").read_bytes()
        plan = json.loads(plan_bytes)
        require(report["status"] == "complete" and report["selection_status"] == "frozen", "incomplete " + label)
        require(report["provenance"]["repetitions"] == pairs and report["provenance"]["warmups"] == 1,
                "wrong sample count: " + label)
        require(report["provenance"]["manifest_sha256"] == manifest_sha == sha(run / "manifest.json"),
                "different selected source patch: " + label)
        require(report["provenance"]["project_lean_sources"] == source_inventory, "changed Lean inventory")
        require(report["analysis_plan"]["sha256"] == hashlib.sha256(plan_bytes).hexdigest(), "changed plan")
        require(plan["provenance"] == {k: report["provenance"][k] for k in plan["provenance"]},
                "plan provenance changed")
        for mapping in [plan["input_sha256"], report["resolved_setup_sha256"],
                        report["provenance"]["compiler_executables"]]:
            for name, expected in mapping.items():
                check(name, expected)
        raw = [json.loads(line) for line in (run / "measurements.jsonl").read_text().splitlines() if line.strip()]
        require(raw == report["measurements"], "raw/report disagreement")
        paths = report["compilation_order"]
        require(len(paths) == 46 and len(set(paths)) == 46, "wrong affected-file universe")
        require(len(raw) == 2 * 46 * (pairs + 1), "missing measured rows")
        suffixes = {".c", ".ilean", ".ir", ".ir.sig", ".olean", ".olean.private", ".olean.server"}
        for row in raw:
            require(row["compilation_status"] == "verified" and row["returncode"] == 0 and
                    row["timed_out"] is False, "failed compiler row")
            trial = run / "runs" / row["phase"] / f"{row['pair']:03d}" / row["variant"]
            stem = trial / "artifacts" / row["path"][:-5]
            expected_paths = {str(stem) + suffix for suffix in suffixes}
            require(set(row["artifact_sha256"]) == expected_paths, "cached, shared, or missing output paths")
            log = Path(row["log_dir"])
            command = json.loads((log / "command.json").read_bytes())["argv"]
            process = json.loads((log / "process.json").read_bytes())
            require(process["returncode"] == 0 and process["timed_out"] is False and
                    process["seconds"] == row["seconds"], "compiler process receipt differs")
            for option, destination in [("-o", str(stem) + ".olean"),
                                        ("-i", str(stem) + ".ilean"), ("-c", str(stem) + ".c")]:
                require(command.count(option) == 1 and command[command.index(option) + 1] == destination,
                        "compiler did not request fresh output: " + option)
            require(command[command.index("-j") + 1] == "1", "different compiler thread count")
            check(command[0], report["provenance"]["compiler_executables"][command[0]])
            for name, expected in row["artifact_sha256"].items():
                require(name not in artifacts, "output reused across compiler calls")
                path = check(name, expected)
                artifacts[name] = {"sha256": expected, "bytes": path.stat().st_size}
        summaries[label] = {"rows": len(raw), "warmup_rows": 92, "measured_rows": 92 * pairs,
                            "pairs": pairs, "compiler_outputs": len(raw) * 7,
                            "setup_processes": len(report["setup"]),
                            "report_sha256": sha(run / "report.json"),
                            "raw_measurements_sha256": sha(run / "measurements.jsonl"),
                            "analysis_plan_sha256": sha(run / "analysis-plan.json")}
    require(reports["pilot"]["resolved_runtime"] == reports["confirmation"]["resolved_runtime"],
            "pilot/confirmation runtime, native imports or headers differ")
    require(reports["confirmation"]["resolved_calibration_match"] is True, "runtime match not recorded")
    mathlib = ROOT / ".lake/packages/mathlib"
    revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=mathlib, text=True).strip()
    require(revision == reports["confirmation"]["provenance"]["mathlib_revision"], "different Mathlib pin")
    require(not subprocess.check_output(["git", "status", "--porcelain", "--untracked-files=no"],
                                        cwd=mathlib, text=True).strip(), "Mathlib tracked files changed")
    return {"schema_version": 1, "status": "all_live_timing_outputs_and_frozen_inputs_rehashed",
            "created_at_utc": datetime.now(timezone.utc).isoformat(), "helper_sha256": sha(Path(__file__)),
            "frozen_manifest_sha256": manifest_sha, "runs": summaries,
            "unique_files_rehashed": len(checked), "fresh_outputs_rehashed": len(artifacts),
            "fresh_output_bytes": sum(x["bytes"] for x in artifacts.values()),
            "project_lean_sources": source_inventory, "mathlib_revision": revision,
            "pilot_confirmation_resolved_runtime_equal": True,
            "output_inventory": {str(Path(name).relative_to(study)): value for name, value in artifacts.items()},
            "limitation": "Byte agreement and fresh output paths do not establish timing-model assumptions or stable power."}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("study", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    result = audit(args.study)
    with args.output.open("x") as stream:
        json.dump(result, stream, indent=2)
        stream.write("\n")
    print(json.dumps({k: v for k, v in result.items() if k not in ["output_inventory", "project_lean_sources"]}, indent=2))


if __name__ == "__main__":
    main()
