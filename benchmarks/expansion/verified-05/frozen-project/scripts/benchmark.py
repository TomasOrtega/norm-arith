#!/usr/bin/env python3
"""Compile original and proposed mathlib files against one pinned environment."""

import argparse
from collections import Counter
from datetime import datetime, timezone
import difflib
import hashlib
import inspect
import json
import math
import os
from pathlib import Path
import platform
import random
import re
import shutil
import signal
import statistics
import subprocess
import sys
import threading
import time


class BenchmarkError(Exception):
    pass


def sha256(text):
    data = text.encode("utf-8") if isinstance(text, str) else text
    return hashlib.sha256(data).hexdigest()


def without_comments(text):
    """Preserve lines and literals while removing nested Lean comments."""
    result = []
    i, depth = 0, 0
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1
                result.extend("  ")
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                result.extend("  ")
                i += 2
            else:
                result.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif text.startswith("--", i):
            end = text.find("\n", i)
            end = len(text) if end < 0 else end
            result.append(" " * (end - i))
            i = end
        elif text.startswith("/-", i):
            depth = 1
            result.extend("  ")
            i += 2
        elif text[i] == "«":
            end = text.find("»", i + 1)
            if end < 0:
                raise BenchmarkError("unterminated quoted identifier")
            result.append(text[i:end + 1])
            i = end + 1
        elif match := re.match(r'r(#+)?"', text[i:]):
            close = '"' + (match[1] or "")
            end = text.find(close, i + len(match[0]))
            if end < 0:
                raise BenchmarkError("unterminated raw string")
            end += len(close)
            result.append(text[i:end])
            i = end
        elif text[i] == '"':
            end = i + 1
            while end < len(text):
                if text[end] == "\\":
                    end += 2
                elif text[end] == '"':
                    end += 1
                    break
                else:
                    end += 1
            result.append(text[i:end])
            i = end
        elif match := re.match(r"'(?:\\.|[^'\\\n])'", text[i:]):
            result.append(match[0])
            i += len(match[0])
        else:
            result.append(text[i])
            i += 1
    if depth:
        raise BenchmarkError("unterminated block comment")
    return "".join(result)


def code_line_count(text):
    return sum(bool(line.strip()) for line in without_comments(text).splitlines())


def safe_source_path(path):
    value = Path(path)
    if value.is_absolute() or ".." in value.parts or value.suffix != ".lean":
        raise BenchmarkError(f"invalid relative Lean source path: {path}")
    return value


def prepare_sources(manifest, mathlib):
    if manifest.get("schema_version") != 1:
        raise BenchmarkError("expected manifest schema_version 1")
    if not re.fullmatch(r"[0-9a-f]{40}", manifest.get("mathlib_revision", "")):
        raise BenchmarkError("mathlib_revision must be a full Git commit")
    candidates = manifest.get("candidates", [])
    ids = [candidate["id"] for candidate in candidates]
    if len(set(ids)) != len(ids):
        raise BenchmarkError("candidate ids must be unique")
    statuses = {"replace", "unsupported", "failed", "unchanged"}
    if any(candidate.get("status") not in statuses for candidate in candidates):
        raise BenchmarkError(f"candidate status must be one of {sorted(statuses)}")
    specifications = manifest.get("files", [])
    names = [item["path"] for item in specifications]
    if len(set(names)) != len(names):
        raise BenchmarkError("file paths must be unique")
    if any(candidate["path"] not in names for candidate in candidates):
        raise BenchmarkError("every candidate path must appear in files")
    accounting = {
        "candidate_count": len(candidates),
        "candidate_status_counts": dict(Counter(candidate["status"] for candidate in candidates)),
        "proposed_replacements": sum(candidate["status"] == "replace" for candidate in candidates),
        "original_proof_lines": 0,
        "replacement_proof_lines": 0,
        "added_helper_lines": 0,
        "added_import_lines": 0,
        "candidates": [],
    }
    prepared = []
    for specification in specifications:
        path = specification["path"]
        relative = safe_source_path(path)
        source_bytes = (mathlib / relative).read_bytes()
        if sha256(source_bytes) != specification.get("source_sha256"):
            raise BenchmarkError(f"source hash mismatch: {path}")
        source = source_bytes.decode("utf-8")
        lines = source.splitlines(keepends=True)
        code_lines = without_comments(source).splitlines()
        edits, intervals = [], []
        for candidate in [item for item in candidates if item["path"] == path]:
            row = {key: value for key, value in candidate.items() if key != "replacement"}
            if "start_line" in candidate:
                start, end = candidate["start_line"], candidate["end_line"]
                if not isinstance(start, int) or not isinstance(end, int) or not 1 <= start <= end <= len(lines):
                    raise BenchmarkError(f"invalid source span: {candidate['id']}")
                original = "".join(lines[start - 1:end])
                if sha256(original) != candidate.get("original_sha256"):
                    raise BenchmarkError(f"span hash mismatch: {candidate['id']}")
                row["original_proof_lines"] = sum(bool(line.strip()) for line in code_lines[start - 1:end])
            elif candidate["status"] == "replace":
                raise BenchmarkError(f"replacement has no exact span: {candidate['id']}")
            if candidate["status"] == "replace":
                replacement = candidate["replacement"]
                if not replacement.endswith("\n"):
                    raise BenchmarkError(f"replacement must end with newline: {candidate['id']}")
                if any(start <= old_end and old_start <= end for old_start, old_end in intervals):
                    raise BenchmarkError(f"overlapping replacement spans: {candidate['id']}")
                intervals.append((start, end))
                edits.append((start - 1, end, replacement))
                row["replacement_proof_lines"] = code_line_count(replacement)
                accounting["original_proof_lines"] += row["original_proof_lines"]
                accounting["replacement_proof_lines"] += row["replacement_proof_lines"]
            accounting["candidates"].append(row)
        if not edits:
            continue
        helper_ids = set()
        for helper in specification.get("helpers", []):
            if helper["id"] in helper_ids:
                raise BenchmarkError(f"duplicate helper id: {helper['id']}")
            helper_ids.add(helper["id"])
            before = helper["before_line"]
            if not 1 <= before <= len(lines) + 1:
                raise BenchmarkError(f"invalid helper position: {helper['id']}")
            if any(start < before <= end for start, end in intervals):
                raise BenchmarkError(f"helper inserted inside replacement: {helper['id']}")
            text = helper["text"]
            if not text.endswith("\n"):
                raise BenchmarkError(f"helper must end with newline: {helper['id']}")
            edits.append((before - 1, before - 1, text))
            accounting["added_helper_lines"] += code_line_count(text)
        # Replacement edits precede insertions at the same position.
        for start, end, replacement in sorted(edits, key=lambda edit: (edit[0], edit[1]), reverse=True):
            lines[start:end] = [replacement]
        replacement = "".join(lines)
        imports = specification.get("imports", [])
        for module in imports:
            if not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9.]*(?:\.[A-Za-z_0-9]+)*", module):
                raise BenchmarkError(f"invalid added import: {module}")
        if imports:
            first = re.search(r"^(?:(?:public|meta) )*import\b", replacement, re.MULTILINE)
            if not first:
                raise BenchmarkError(f"cannot locate import header: {path}")
            replacement = replacement[:first.start()] + "".join(f"import {module}\n" for module in imports) + replacement[first.start():]
            accounting["added_import_lines"] += len(imports)
        prepared.append({"path": path, "original": source, "replacement": replacement})
    accounting["net_proof_lines_saved"] = accounting["original_proof_lines"] - accounting["replacement_proof_lines"] - accounting["added_helper_lines"]
    accounting["net_lines_saved_including_imports"] = accounting["net_proof_lines_saved"] - accounting["added_import_lines"]
    return prepared, accounting


def run_process(command, cwd, log_dir, timeout, env=None):
    log_dir.mkdir(parents=True, exist_ok=True)
    (log_dir / "command.json").write_text(json.dumps({"argv": [str(arg) for arg in command], "cwd": str(cwd)}, indent=2) + "\n")
    started = time.perf_counter()
    expired = threading.Event()
    with (log_dir / "stdout.log").open("w") as stdout, (log_dir / "stderr.log").open("w") as stderr:
        process = subprocess.Popen(command, cwd=cwd, env=env, stdout=stdout, stderr=stderr, start_new_session=True)

        def terminate():
            if process.poll() is None:
                try:
                    os.killpg(process.pid, signal.SIGKILL)
                    expired.set()
                except ProcessLookupError:
                    pass

        timer = threading.Timer(timeout, terminate)
        timer.daemon = True
        timer.start()
        try:
            returncode = process.wait()
        except BaseException:
            if process.poll() is None:
                try:
                    os.killpg(process.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
            process.wait()
            interrupted = {"seconds": time.perf_counter() - started, "returncode": process.returncode,
                           "timed_out": expired.is_set(), "interrupted": True, "log_dir": str(log_dir)}
            (log_dir / "process.json").write_text(json.dumps(interrupted, indent=2) + "\n")
            raise
        finally:
            timer.cancel()
    result = {
        "seconds": time.perf_counter() - started,
        "returncode": returncode,
        "timed_out": expired.is_set(),
        "log_dir": str(log_dir),
    }
    (log_dir / "process.json").write_text(json.dumps(result, indent=2) + "\n")
    return result


def require_success(result):
    if result["timed_out"]:
        raise BenchmarkError(f"command timed out; logs: {result['log_dir']}")
    if result["returncode"]:
        raise BenchmarkError(f"command returned exit code {result['returncode']}; logs: {result['log_dir']}")


def validate_compilation(result, outputs):
    require_success(result)
    for name in ["stdout.log", "stderr.log"]:
        for line in (Path(result["log_dir"]) / name).read_text().splitlines():
            try:
                message = json.loads(line)
            except json.JSONDecodeError:
                continue
            if isinstance(message, dict) and message.get("severity") == "error":
                raise BenchmarkError(f"compiler emitted an error diagnostic; logs: {result['log_dir']}")
            if isinstance(message, dict) and "declaration uses 'sorry'" in str(message.get("data", "")):
                raise BenchmarkError(f"compiler admitted a proof with sorry; logs: {result['log_dir']}")
    for output in outputs:
        if not output.is_file() or output.stat().st_size == 0:
            raise BenchmarkError(f"missing compilation output: {output}")
    return fingerprint_inputs(outputs)


def paired_totals(measurements, paths, repetitions):
    if not paths or len(set(paths)) != len(paths):
        raise BenchmarkError("affected-file paths must be nonempty and unique")
    measured = [row for row in measurements if row["phase"] == "measured"]
    expected = {(pair, variant, path) for pair in range(repetitions) for variant in ["original", "replacement"] for path in paths}
    actual = [(row["pair"], row["variant"], row["path"]) for row in measured]
    if len(set(actual)) != len(actual) or set(actual) != expected:
        raise BenchmarkError("incomplete or duplicated paired measurements")
    for row in measured:
        if not isinstance(row["seconds"], (int, float)) or not math.isfinite(row["seconds"]) or row["seconds"] <= 0:
            raise BenchmarkError("paired measurements must have finite positive durations")
        if row.get("returncode", 0) != 0 or row.get("timed_out", False) or row.get("compilation_status", "verified") != "verified":
            raise BenchmarkError("failed or timed-out compilation in paired measurements")
    return {
        variant: [math.fsum(row["seconds"] for row in measured if row["variant"] == variant and row["pair"] == pair)
                  for pair in range(repetitions)]
        for variant in ["original", "replacement"]
    }


def paired_blocks(measurements, paths, repetitions, block_pairs):
    if not isinstance(block_pairs, int) or block_pairs < 2 or block_pairs % 2:
        raise BenchmarkError("block_pairs must be positive and even, retaining adjacent AB/BA pairs")
    if repetitions % block_pairs or repetitions // block_pairs < 3:
        raise BenchmarkError("confirmatory pairs must form at least three complete equal-size blocks")
    totals = paired_totals(measurements, paths, repetitions)
    actual_order = [(row["pair"], row["variant"]) for row in measurements if row["phase"] == "measured"]
    expected_order = [(pair, variant) for pair in range(repetitions)
                      for variant in (["original", "replacement"] if pair % 2 == 0 else ["replacement", "original"])
                      for _ in paths]
    if actual_order != expected_order:
        raise BenchmarkError("paired block rows do not follow the predeclared adjacent AB/BA order")
    return [
        {"pairs": list(range(start, start + block_pairs)),
         "original_seconds": math.fsum(totals["original"][start:start + block_pairs]),
         "replacement_seconds": math.fsum(totals["replacement"][start:start + block_pairs])}
        for start in range(0, repetitions, block_pairs)
    ]


def ratio_of_totals(blocks):
    return math.fsum(block["original_seconds"] for block in blocks) / math.fsum(
        block["replacement_seconds"] for block in blocks
    )


def bootstrap_ratios(blocks, resamples, seed):
    if not blocks or resamples < 1:
        raise BenchmarkError("bootstrap requires blocks and a positive resample count")
    rng = random.Random(seed)
    return [ratio_of_totals([blocks[rng.randrange(len(blocks))] for _ in blocks])
            for _ in range(resamples)]


def bca_interval(blocks, resamples=10000, seed=20261020):
    if len(blocks) < 3:
        raise BenchmarkError("BCa acceleration requires at least three blocks")
    estimate = ratio_of_totals(blocks)
    draws = bootstrap_ratios(blocks, resamples, seed)
    if min(draws) == max(draws):
        raise BenchmarkError("BCa is undefined for a degenerate bootstrap distribution")
    probability = (sum(value < estimate for value in draws)
                   + 0.5 * sum(value == estimate for value in draws)) / resamples
    if not 0 < probability < 1:
        raise BenchmarkError("BCa bias correction is not finite")
    normal = statistics.NormalDist()
    bias = normal.inv_cdf(probability)
    jackknife = [ratio_of_totals(blocks[:index] + blocks[index + 1:]) for index in range(len(blocks))]
    center = statistics.mean(jackknife)
    deviations = [center - value for value in jackknife]
    squared = math.fsum(value * value for value in deviations)
    if squared == 0:
        raise BenchmarkError("BCa acceleration is undefined for a degenerate block jackknife")
    acceleration = math.fsum(value ** 3 for value in deviations) / (6 * squared ** 1.5)
    quantiles = []
    for probability in [0.025, 0.975]:
        z = bias + normal.inv_cdf(probability)
        denominator = 1 - acceleration * z
        if denominator <= 0:
            raise BenchmarkError("BCa adjustment crosses an acceleration pole")
        adjusted = normal.cdf(bias + z / denominator)
        if not 1 / resamples <= adjusted <= 1 - 1 / resamples:
            raise BenchmarkError("BCa endpoint exceeds the bootstrap Monte Carlo resolution")
        quantiles.append(adjusted)
    draws.sort()

    def quantile(probability):
        position = probability * (len(draws) - 1)
        lower = math.floor(position)
        fraction = position - lower
        return draws[lower] * (1 - fraction) + draws[min(lower + 1, len(draws) - 1)] * fraction

    lower, upper = map(quantile, quantiles)
    if not math.isfinite(lower) or not math.isfinite(upper) or lower > upper:
        raise BenchmarkError("invalid BCa interval endpoints")
    return {
        "status": "valid", "confidence_level": 0.95, "lower": lower, "upper": upper,
        "bias_correction": bias, "acceleration": acceleration,
        "adjusted_quantiles": quantiles,
        "bootstrap_distribution_sha256": sha256(json.dumps(draws)),
    }


def confidence_gate(interval):
    return interval.get("status") == "valid" and interval["lower"] > 1


def confirmatory_statistics(measurements, paths, repetitions, block_pairs, resamples, seed):
    blocks = paired_blocks(measurements, paths, repetitions, block_pairs)
    totals = paired_totals(measurements, paths, repetitions)
    try:
        interval = bca_interval(blocks, resamples, seed)
    except BenchmarkError as error:
        interval = {"status": "undefined", "reason": str(error)}
    return {
        "primary_statistic": "ratio_of_mean_pass_totals",
        "original_mean_seconds": statistics.mean(totals["original"]),
        "replacement_mean_seconds": statistics.mean(totals["replacement"]),
        "estimate": ratio_of_totals(blocks), "interval": interval,
        "block_pairs": block_pairs, "block_count": len(blocks), "blocks": blocks,
        "bootstrap_resamples": resamples, "bootstrap_seed": seed,
        "success_criterion_met": confidence_gate(interval),
    }


def summarize(measurements, paths, repetitions):
    totals = paired_totals(measurements, paths, repetitions)
    measured = [row for row in measurements if row["phase"] == "measured"]

    def distribution(values):
        return {"median_seconds": statistics.median(values), "min_seconds": min(values), "max_seconds": max(values), "seconds": values}

    def comparison(original, replacement):
        return {"original": distribution(original), "replacement": distribution(replacement), "speedup": statistics.median(original) / statistics.median(replacement)}

    per_file = []
    for path in paths:
        values = {variant: [next(row["seconds"] for row in measured if row["path"] == path and row["variant"] == variant and row["pair"] == pair) for pair in range(repetitions)] for variant in ["original", "replacement"]}
        per_file.append({"path": path, **comparison(values["original"], values["replacement"])})
    return {"files": per_file, "aggregate": comparison(totals["original"], totals["replacement"])}


def write_report(output, report):
    (output / "report.json").write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n")
    lines = ["# Proposed mathlib replacements", "", f"Status: **{report['status']}**.", ""]
    if "error" in report:
        lines.extend([report["error"], "", "No successful benchmark claim is available from this run.", ""])
    provenance = report.get("provenance", {})
    lines.extend([f"Mathlib revision: `{provenance.get('mathlib_revision', 'unverified')}`.", f"Manifest SHA256: `{provenance.get('manifest_sha256', 'unverified')}`.", ""])
    if report.get("selection_status") != "frozen":
        lines.extend(["The candidate selection is not frozen. This is an integration trial, not a final evaluation.", ""])
    if report.get("analysis_plan"):
        lines.extend([f"Analysis plan: `{report['analysis_plan']['sha256']}` ({report['analysis_plan']['mode']}); frozen before setup or sampling.", ""])
    if report["status"] == "complete":
        inference = report.get("inference", {"mode": "exploratory"})
        if inference["mode"] == "confirmatory":
            interval = inference["interval"]
            lines.extend([
                f"Primary ratio of mean full-pass totals: **{inference['estimate']:.4f}×** "
                f"({inference['original_mean_seconds']:.3f} s original / {inference['replacement_mean_seconds']:.3f} s replacement).",
                f"Paired block BCa: {inference['block_count']} blocks of {inference['block_pairs']} adjacent AB/BA pairs; "
                f"{inference['bootstrap_resamples']} resamples, seed {inference['bootstrap_seed']}.",
            ])
            if interval["status"] == "valid":
                lines.append(f"95% interval: **[{interval['lower']:.4f}, {interval['upper']:.4f}]×**.")
            else:
                lines.append(f"95% interval undefined: {interval['reason']}.")
            passed = "met" if inference["success_criterion_met"] else "not met"
            lines.extend([f"Predeclared improvement criterion (valid lower endpoint > 1): **{passed}**.",
                          inference["coverage_condition"], "The medians below are descriptive.", ""])
        else:
            lines.extend(["Exploratory measurement: the median ratio below has no calibrated confidence interval or confirmatory success claim.", ""])
        count = report["accounting"]
        lines.extend([
            f"{count['proposed_replacements']} verified replacements from {count['candidate_count']} catalogued candidates in {len(report['summary']['files'])} affected files.",
            f"Proof code: {count['original_proof_lines']} → {count['replacement_proof_lines']} lines, plus {count['added_helper_lines']} added helper lines: **{count['net_proof_lines_saved']} net proof lines saved**.",
            f"Added imports: {count['added_import_lines']} lines; savings including imports: {count['net_lines_saved_including_imports']} lines.",
            "Helper declarations are charged in full once. Preparation is included in replacement spans. Tactic implementation and tests are separate from proof savings.", "",
            "Warm whole-file Lean compilation emits `.olean`, `.ilean`, module sidecars and C. Every trial uses fresh outputs and actual variant imports. Dependencies are already built; import loading, search, proof construction, checking, serialization and C generation occur within each measurement. Native C object compilation and Lake dispatch are excluded.", "",
            "| File | Original median (s) | Replacement median (s) | Before / after |", "| --- | ---: | ---: | ---: |",
        ])
        for row in report["summary"]["files"] + [{"path": "**Total**", **report["summary"]["aggregate"]}]:
            lines.append(f"| {row['path']} | {row['original']['median_seconds']:.3f} | {row['replacement']['median_seconds']:.3f} | {row['speedup']:.3f}× |")
        lines.extend(["", "Ratios below 1 indicate a slowdown. Totals are per-pass sums before taking medians. Raw times and minimum/maximum values are in `report.json`; no samples are discarded.", ""])
    if report.get("setup"):
        seconds = sum(row["seconds"] for row in report["setup"])
        lines.extend([f"Recorded setup/build/query processes: {seconds:.3f} s. These depend on the starting cache state; individual commands and logs are under `setup/` and are excluded from warm compile totals.", ""])
        for row in report["setup"]:
            if row["label"] == "tactic-rebuild" and row["returncode"] == 0:
                lines.extend([f"The separate NormArith Lean-artifact rebuild after invalidating its own generated/native artifacts took **{row['seconds']:.3f} s** with dependency artifacts retained and artifact-cache retrieval disabled. Native compilation/linking can also occur in the edited-header setup commands included above.", ""])
    if report.get("accounting"):
        lines.extend(["| Candidate | Status | Reason |", "| --- | --- | --- |"])
        for row in report["accounting"]["candidates"]:
            reason = str(row.get("reason", "")).replace("|", "\\|").replace("\n", " ")
            status = "verified replacement" if report["status"] == "complete" and row["status"] == "replace" else row["status"]
            lines.append(f"| {row['id']} | {status} | {reason} |")
    (output / "report.md").write_text("\n".join(lines) + "\n")


def capture(command, cwd):
    result = subprocess.run(command, cwd=cwd, text=True, capture_output=True, check=False)
    if result.returncode:
        raise BenchmarkError(f"{' '.join(map(str, command))}: {result.stderr.strip()}")
    return result.stdout.strip()


def source_setup(setup, compiled):
    result = json.loads(json.dumps(setup))
    result["imports"] = None
    suffixes = [".olean.private", ".olean.server", ".ir.sig", ".olean", ".ir"]

    def artifact_suffix(path):
        for suffix in suffixes:
            if path.endswith(suffix):
                return suffix
        raise BenchmarkError(f"unrecognized dependency artifact: {path}")

    for module, requested in result.setdefault("importArts", {}).items():
        if module not in compiled:
            continue
        fresh = {artifact_suffix(path): path for part in compiled[module] for path in part}
        try:
            result["importArts"][module] = [
                [fresh[artifact_suffix(path)] for path in part] for part in requested
            ]
        except KeyError as error:
            raise BenchmarkError(f"fresh dependency lacks requested artifact {error.args[0]}: {module}") from error
    return result


def dependency_order(setups):
    modules = {path[:-5].replace("/", "."): path for path in setups}
    done, visiting, order = set(), set(), []

    def visit(path):
        if path in visiting:
            raise BenchmarkError(f"affected-file import cycle: {path}")
        if path in done:
            return
        visiting.add(path)
        for module in setups[path].get("importArts", {}):
            if module in modules:
                visit(modules[module])
        visiting.remove(path)
        done.add(path)
        order.append(path)

    for path in setups:
        visit(path)
    return order


def invalidate_tactic_artifacts(project):
    invalidated = []
    for directory in [project / ".lake/build/lib/lean", project / ".lake/build/ir"]:
        for target in [directory / "NormArith", *sorted(directory.glob("NormArith.*"))]:
            if not target.exists() and not target.is_symlink():
                continue
            if target.is_symlink():
                raise BenchmarkError(f"refusing to invalidate a symlink: {target}")
            invalidated.append(str(target.relative_to(project)))
            if target.is_dir():
                shutil.rmtree(target)
            else:
                target.unlink()
    native = project / ".lake/build/lib"
    pattern = re.compile(r"^(?:lib)?(?:[A-Za-z0-9_]+_)?NormArith\.(?:dylib|so|dll|a|lib)(?:\..*)?$")
    for target in sorted(native.iterdir() if native.exists() else []):
        if not pattern.fullmatch(target.name):
            continue
        if target.is_symlink() or not target.is_file():
            raise BenchmarkError(f"refusing to invalidate a non-regular native artifact: {target}")
        invalidated.append(str(target.relative_to(project)))
        target.unlink()
    return invalidated


def parse_build_setups(text, modules):
    try:
        values = [json.loads(line) for line in text.splitlines() if line.strip()]
    except json.JSONDecodeError as error:
        raise BenchmarkError("invalid batched Lake build setup JSONL") from error
    if len(values) != len(modules) or any(not isinstance(value, dict) or value.get("name") != module
                                         for module, value in zip(modules, values)):
        raise BenchmarkError("batched Lake build setup module order/count mismatch")
    return values


def edited_source_setups(source_files, *, mathlib, lean, lake, command, output, label, build_setups):
    output.mkdir(parents=True, exist_ok=True)
    paths = list(source_files)
    headers = {}
    for start in range(0, len(paths), 128):
        batch = paths[start:start + 128]
        text = command(f"{label}-headers-{start:06d}", [lean, "--deps-json", *[str(source_files[path]) for path in batch]])
        parsed = json.loads(text).get("imports", [])
        if len(parsed) != len(batch):
            raise BenchmarkError("Lean header parser returned an unexpected result count")
        for path, item in zip(batch, parsed):
            header = item.get("result")
            if item.get("errors") or not isinstance(header, dict) or not isinstance(header.get("imports"), list):
                raise BenchmarkError(f"Lean could not parse source imports: {path}: {item.get('errors')}")
            headers[path] = header
    setups, records = {}, {}
    for path in paths:
        module = path[:-5].replace("/", ".")
        header = headers[path]
        header_path = output / f"{module}.header.json"
        header_path.write_text(json.dumps(header, indent=2) + "\n")
        text = command(f"{label}-edited-{module}",
                       [lake, "setup-file", str(mathlib / path), json.dumps(header, separators=(",", ":"))])
        raw = json.loads(text)
        base = build_setups[path]
        if not isinstance(raw, dict) or raw.get("name") != module or raw.get("package") != base.get("package") or \
                raw.get("isModule", False) != header.get("isModule", False):
            raise BenchmarkError(f"edited header lost original module identity: {path}")
        raw_path = output / f"{module}.raw-setup.json"
        raw_path.write_text(text + ("" if text.endswith("\n") else "\n"))
        setup = json.loads(json.dumps(raw))
        setup["options"] = base.get("options", {})
        if setup["options"].get("compiler.postponeCompile", False):
            raise BenchmarkError("compiler.postponeCompile=true requires a separate leanir compiler")
        setup_path = output / f"{module}.setup.json"
        setup_path.write_text(json.dumps(setup, indent=2) + "\n")
        setups[path] = setup
        records[path] = {
            "source": str(source_files[path]), "source_sha256": sha256(source_files[path].read_bytes()),
            "header": header, "header_file": str(header_path), "header_sha256": sha256(header_path.read_bytes()),
            "raw_setup_file": str(raw_path), "raw_setup_sha256": sha256(raw_path.read_bytes()),
            "setup_file": str(setup_path), "setup_sha256": sha256(setup_path.read_bytes()),
            "compiler_options_source": "original Lake build setup; setup-file server options are excluded",
            "dynlibs": setup.get("dynlibs", []), "plugins": setup.get("plugins", []),
        }
    return setups, records


def setup_artifact_paths(setup, project):
    names = [path for parts in setup.get("importArts", {}).values() for part in parts for path in part]
    names.extend(setup.get("dynlibs", []))
    names.extend(item["path"] if isinstance(item, dict) else item for item in setup.get("plugins", []))
    return [path.resolve() if path.is_absolute() else (project / path).resolve() for path in map(Path, names)]


def setup_record_inputs(records, project, include_imports=False):
    inputs = []
    for record in records.values():
        inputs.extend(Path(record[key]) for key in ["header_file", "raw_setup_file", "setup_file"])
        if include_imports:
            inputs.extend(setup_artifact_paths(json.loads(Path(record["setup_file"]).read_bytes()), project))
        else:
            for entry in record["dynlibs"] + record["plugins"]:
                path = Path(entry["path"] if isinstance(entry, dict) else entry)
                inputs.append(path if path.is_absolute() else project / path)
    return inputs


def normalize_run_paths(value, output):
    prefix = str(output.resolve())
    if isinstance(value, dict):
        return {normalize_run_paths(key, output): normalize_run_paths(item, output) for key, item in value.items()}
    if isinstance(value, list):
        return [normalize_run_paths(item, output) for item in value]
    if isinstance(value, str):
        def normalize(piece):
            path = str(Path(piece).resolve()) if Path(piece).is_absolute() else piece
            if path == prefix or path.startswith(prefix + os.sep):
                return "$RUN" + path[len(prefix):]
            return piece
        return os.pathsep.join(normalize(piece) for piece in value.split(os.pathsep))
    return value


def resolved_runtime_provenance(report, project, output, fingerprints=None):
    variants = {}
    for variant, records in report["source_header_setups"].items():
        variants[variant] = {}
        for path, record in records.items():
            setup = source_setup(json.loads(Path(record["setup_file"]).read_bytes()), {})
            artifacts = setup_artifact_paths(setup, project)
            hashes = fingerprint_inputs(artifacts) if fingerprints is None else {
                str(artifact): fingerprints[str(artifact)] for artifact in artifacts
            }
            native = []
            for kind in ["dynlibs", "plugins"]:
                for entry in setup.get(kind, []):
                    name = entry["path"] if isinstance(entry, dict) else entry
                    absolute = Path(name)
                    absolute = absolute.resolve() if absolute.is_absolute() else (project / absolute).resolve()
                    native.append({"kind": kind, "entry": entry, "sha256": hashes[str(absolute)]})
            variants[variant][path] = {"header": record["header"], "setup": setup,
                                       "artifact_sha256": hashes, "native_libraries": native}
    return normalize_run_paths({
        "schema_version": 1, "variants": variants,
        "lean_environment": report["provenance"].get("lean_environment"),
        "lean_version": report["provenance"].get("lean_version"),
        "lake_version": report["provenance"].get("lake_version"),
        "compiler_executables": report["provenance"].get("compiler_executables"),
        "python_version": report["provenance"].get("python_version"),
    }, output)


def validate_resolved_calibration(calibration, current):
    if not isinstance(calibration.get("resolved_runtime"), dict) or calibration["resolved_runtime"] != current:
        raise BenchmarkError("calibration pilot resolved runtime differs from current headers, build options, import artifacts or native libraries")


def lean_environment_expression():
    return "{key:value for key,value in os.environ.items() if key == 'PATH' or key.startswith(('LEAN_', 'DYLD_', 'LD_'))}"


def lean_environment_probe():
    return "import json, os; print(json.dumps(" + lean_environment_expression() + "))"


def setup_environment(args, report, paths):
    project, output = args.project, args.output
    setup_dir = output / "setup"

    def setup_command(label, command):
        result = run_process(command, project, setup_dir / label, args.timeout)
        report["setup"].append({"label": label, **result})
        require_success(result)
        return (Path(result["log_dir"]) / "stdout.log").read_text().strip()

    if args.rebuild_tactic:
        report["tactic_artifact_invalidation"] = invalidate_tactic_artifacts(project)
        setup_command("tactic-rebuild", [args.lake, "--no-cache", "build", "NormArith"])
    elif not args.skip_setup:
        setup_command("tactic-build", [args.lake, "build", "NormArith"])
    else:
        setup_command("tactic-up-to-date", [args.lake, "--no-build", "build", "NormArith"])
    environment = json.loads(setup_command("environment", [args.lake, "env", sys.executable, "-c", lean_environment_probe()]))
    env = dict(os.environ, **environment)
    prefix = setup_command("lean-prefix", [args.lake, "env", "lean", "--print-prefix"])
    lean = str(Path(prefix) / "bin/lean")
    executables = [Path(lean), Path(prefix) / "bin/lake", Path(sys.executable).resolve()]
    launcher = shutil.which(args.lake)
    if launcher:
        executables.append(Path(launcher).resolve())
    report["provenance"]["compiler_executables"] = fingerprint_inputs(executables)
    report["provenance"]["lean_version"] = setup_command("lean-version", [lean, "--version"])
    report["provenance"]["lake_version"] = setup_command("lake-version", [args.lake, "--version"])
    report["provenance"]["lean_environment"] = environment
    build_setups = {}
    for start in range(0, len(paths), 128):
        batch = paths[start:start + 128]
        modules = [path[:-5].replace("/", ".") for path in batch]
        text = setup_command(f"build-setups-{start:06d}",
                             [args.lake, "-q", "-J", "query", *[f"@mathlib/+{module}:setup" for module in modules]])
        for path, setup in zip(batch, parse_build_setups(text, modules)):
            build_setups[path] = setup
    setups, values = {}, {}
    report["source_header_setups"] = {}
    for variant in ["original", "replacement"]:
        values[variant], records = edited_source_setups(
            {path: output / "sources" / variant / path for path in paths},
            mathlib=args.mathlib, lean=lean, lake=args.lake, command=setup_command,
            output=setup_dir / variant, label=variant, build_setups=build_setups,
        )
        setups[variant] = {path: Path(record["setup_file"]) for path, record in records.items()}
        report["source_header_setups"][variant] = records
    dependencies = {path: {"importArts": {**values["original"][path].get("importArts", {}),
                                          **values["replacement"][path].get("importArts", {})}}
                    for path in paths}
    report["compilation_order"] = dependency_order(dependencies)
    return lean, env, setups


def compile_pass(args, report, prepared, lean, env, setups, phase, pair, variant):
    trial = args.output / "runs" / phase / f"{pair:03d}" / variant
    artifacts = trial / "artifacts"
    if artifacts.exists():
        raise BenchmarkError(f"refusing to reuse compilation outputs: {artifacts}")
    artifacts.mkdir(parents=True)
    source_root = args.output / "sources" / variant
    compiled = {}
    for source in prepared:
        path = source["path"]
        stem = artifacts / path[:-5]
        stem.parent.mkdir(parents=True, exist_ok=True)
        outputs = [stem.with_suffix(suffix) for suffix in [".olean", ".ilean", ".c"]]
        setup = source_setup(json.loads(setups[variant][path].read_text()), compiled)
        setup_path = trial / "setups" / (path[:-5] + ".setup.json")
        setup_path.parent.mkdir(parents=True, exist_ok=True)
        setup_path.write_text(json.dumps(setup, indent=2) + "\n")
        if setup.get("isModule"):
            outputs.extend(Path(str(stem) + suffix) for suffix in [".olean.server", ".olean.private", ".ir", ".ir.sig"])
        command = [lean, str(source_root / path), "-R", str(source_root), "--setup", str(setup_path), "-o", str(outputs[0]), "-i", str(outputs[1]), "-c", str(outputs[2]), "--json"]
        if args.threads is not None:
            command.extend(["-j", str(args.threads)])
        result = run_process(command, args.project, trial / "logs" / path[:-5], args.timeout, env=env)
        row = {"phase": phase, "pair": pair, "variant": variant, "path": path,
               "compilation_status": "failed", **result}
        try:
            row["artifact_sha256"] = validate_compilation(result, outputs)
            row["compilation_status"] = "verified"
        finally:
            report["measurements"].append(row)
            with (args.output / "measurements.jsonl").open("a") as stream:
                stream.write(json.dumps(row) + "\n")
        module = path[:-5].replace("/", ".")
        compiled[module] = [[str(outputs[0])]]
        if setup.get("isModule"):
            compiled[module] = [[str(outputs[0]), str(outputs[3]), str(outputs[4])], [str(outputs[6]), str(outputs[5])]]
        print(f"{phase} {pair + 1}: {variant} {path}: {result['seconds']:.3f}s", flush=True)


CALIBRATION_MATCH_KEYS = (
    "mathlib_revision", "manifest_sha256", "proposed_patch_sha256",
    "project_lean_sources", "project_lake_manifest_sha256", "project_lakefile_sha256",
    "toolchain", "threads", "warmups", "platform", "machine", "cpu", "cpu_count",
    "measurement_protocol_sha256", "python_version",
)


def project_lean_sources(project):
    return sorted(set(project.glob("NormArith*.lean"))
                  | set(project.glob("NormArith/**/*.lean"))
                  | set(project.glob("NormArithTest/**/*.lean")))


def implementation_line_costs(project):
    census = project / "NormArith/Census.lean"
    tactic = [project / "NormArith.lean", *sorted(project.glob("NormArith/**/*.lean"))]
    return {
        "tactic_implementation_code_lines": sum(code_line_count(path.read_text()) for path in tactic if path != census),
        "census_implementation_code_lines": code_line_count(census.read_text()) if census.exists() else 0,
    }


def measurement_protocol_sha256():
    functions = [run_process, require_success, validate_compilation, source_setup,
                 dependency_order, invalidate_tactic_artifacts, parse_build_setups, edited_source_setups,
                 setup_artifact_paths, setup_record_inputs, normalize_run_paths, resolved_runtime_provenance,
                 lean_environment_expression, lean_environment_probe, setup_environment, compile_pass,
                 fingerprint_inputs, verify_frozen_inputs, verify_analysis_plan]
    return sha256("\n".join(inspect.getsource(function) for function in functions))


def fingerprint_inputs(paths):
    return {str(path.resolve()): sha256(path.read_bytes()) for path in sorted(set(paths))}


def verify_frozen_inputs(fingerprints):
    for name, expected in fingerprints.items():
        path = Path(name)
        if not path.is_file():
            raise BenchmarkError(f"frozen input missing: {path}")
        if sha256(path.read_bytes()) != expected:
            raise BenchmarkError(f"frozen input changed: {path}")


def validate_calibration(path, provenance, current_paths):
    artifact = json.loads(path.read_bytes())
    if not isinstance(artifact, dict) or artifact.get("schema_version") != 1:
        raise BenchmarkError("expected calibration schema_version 1")
    try:
        date = datetime.strptime(artifact.get("date", ""), "%Y-%m-%d").date()
    except (TypeError, ValueError) as error:
        raise BenchmarkError("calibration needs a date in YYYY-MM-DD format") from error
    if str(date) != artifact["date"] or date > datetime.now(timezone.utc).date():
        raise BenchmarkError("calibration date must be an existing date in YYYY-MM-DD format")
    if not isinstance(artifact.get("rationale"), str) or not artifact["rationale"].strip():
        raise BenchmarkError("calibration needs a block-length rationale based on pilot diagnostics")
    block_pairs = artifact.get("block_pairs")
    if not isinstance(block_pairs, int) or block_pairs < 2 or block_pairs % 2:
        raise BenchmarkError("calibration block_pairs must be positive and even")
    references = {}
    for key in ["pilot_report", "pilot_measurements"]:
        reference = artifact.get(key, {})
        if not isinstance(reference, dict) or not isinstance(reference.get("path"), str) or not reference["path"]:
            raise BenchmarkError(f"calibration needs {key} path and SHA256")
        referenced = (path.parent / reference["path"]).resolve()
        data = referenced.read_bytes()
        if sha256(data) != reference.get("sha256"):
            raise BenchmarkError(f"calibration {key} hash mismatch: {referenced}")
        references[key] = {"path": str(referenced), "sha256": sha256(data)}
    pilot = json.loads(Path(references["pilot_report"]["path"]).read_bytes())
    if not isinstance(pilot, dict) or pilot.get("status") != "complete" or pilot.get("selection_status") != "frozen":
        raise BenchmarkError("calibration pilot must be complete with frozen candidate selection")
    previous = pilot.get("provenance", {})
    if not isinstance(previous, dict):
        raise BenchmarkError("calibration pilot has invalid provenance")
    for key in CALIBRATION_MATCH_KEYS:
        if key not in provenance or key not in previous or previous[key] != provenance[key]:
            raise BenchmarkError(f"calibration pilot does not match current workload: {key}")
    measurements = [json.loads(line) for line in Path(references["pilot_measurements"]["path"]).read_text().splitlines() if line.strip()]
    if measurements != pilot.get("measurements"):
        raise BenchmarkError("calibration pilot report and raw measurements disagree")
    summary = pilot.get("summary", {})
    if not isinstance(summary, dict) or not isinstance(summary.get("files"), list):
        raise BenchmarkError("calibration pilot has invalid affected-file summary")
    paths = [row["path"] for row in summary["files"]]
    if paths != current_paths:
        raise BenchmarkError("calibration pilot affected files do not match current workload")
    repetitions = previous.get("repetitions")
    if not isinstance(repetitions, int) or repetitions < 1:
        raise BenchmarkError("calibration pilot has invalid repetition count")
    paired_blocks(measurements, paths, repetitions, block_pairs)
    if not isinstance(pilot.get("resolved_runtime"), dict):
        raise BenchmarkError("calibration pilot has no resolved runtime provenance")
    return {"path": str(path.resolve()), "sha256": sha256(path.read_bytes()),
            "resolved_runtime": pilot["resolved_runtime"],
            "date": artifact["date"], "block_pairs": block_pairs,
            "rationale": artifact["rationale"], **references}


def freeze_analysis_plan(args, report, prepared, calibration):
    provenance = report["provenance"]
    paths = [source["path"] for source in prepared]
    inputs = [Path(__file__), args.manifest, args.project / "lean-toolchain",
              args.project / "lake-manifest.json", args.project / "lakefile.toml",
              args.output / "manifest.json", args.output / "mathlib.patch",
              *project_lean_sources(args.project)]
    inputs.extend(args.mathlib / item["path"] for item in report["manifest"]["files"])
    inputs.extend(args.output / "sources" / variant / path
                  for path in paths for variant in ["original", "replacement"])
    if calibration:
        inputs.extend(Path(calibration[key]["path"]) for key in ["pilot_report", "pilot_measurements"])
        inputs.append(Path(calibration["path"]))
    fingerprints = fingerprint_inputs(inputs)
    expected = {args.manifest: provenance["manifest_sha256"],
                args.output / "manifest.json": provenance["manifest_sha256"],
                args.output / "mathlib.patch": provenance["proposed_patch_sha256"],
                Path(__file__): provenance["harness_sha256"],
                args.project / "lean-toolchain": provenance["project_toolchain_sha256"],
                args.project / "lake-manifest.json": provenance["project_lake_manifest_sha256"],
                args.project / "lakefile.toml": provenance["project_lakefile_sha256"]}
    expected.update({args.project / path: digest for path, digest in provenance["project_lean_sources"].items()})
    expected.update({args.mathlib / item["path"]: item["source_sha256"] for item in report["manifest"]["files"]})
    expected.update({args.output / "sources" / variant / source["path"]: sha256(source[variant])
                     for source in prepared for variant in ["original", "replacement"]})
    if calibration:
        expected[Path(calibration["path"])] = calibration["sha256"]
        expected.update({Path(calibration[key]["path"]): calibration[key]["sha256"]
                         for key in ["pilot_report", "pilot_measurements"]})
    fingerprints.update({str(path.resolve()): digest for path, digest in expected.items()})
    verify_frozen_inputs(fingerprints)
    plan = {
        "schema_version": 1, "frozen_at_utc": datetime.now(timezone.utc).isoformat(),
        "mode": "confirmatory" if args.confirmatory else "exploratory",
        "affected_files": paths, "selection_status": report["selection_status"],
        "measured_pairs": args.repetitions, "warmup_pairs": args.warmups,
        "pair_order": "even: original then replacement; odd: replacement then original",
        "compilation_order": "common topological order over both actual variant import graphs, stable manifest traversal",
        "setup_resolution": "Lean-parsed source headers; Lake edited-module imports and native libraries; original Lake build options",
        "all_affected_files_and_pairs_retained": True,
        "primary_statistic": "ratio_of_mean_pass_totals" if args.confirmatory else "ratio_of_median_pass_totals",
        "descriptive_statistic": "ratio_of_median_pass_totals",
        "interval": {"method": "paired_nonoverlapping_equal_block_BCa", "confidence_level": 0.95,
                     "block_pairs": args.block_pairs, "resamples": args.bootstrap_resamples,
                     "seed": args.bootstrap_seed, "bias_ties": "half_weight",
                     "quantile": "linear_interpolation_at_p_times_n_minus_one",
                     "acceleration": "delete_one_whole_block_jackknife",
                     "success": "valid calibrated interval with lower endpoint strictly greater than one"}
                    if args.confirmatory else None,
        "calibration": calibration,
        "coverage_condition": "Independent representative blocks are assumed; pilot calibration does not prove independence."
                              if args.confirmatory else None,
        "input_sha256": fingerprints,
        "provenance": dict(provenance),
    }
    plan_path = args.output / "analysis-plan.json"
    plan_path.write_text(json.dumps(plan, indent=2, ensure_ascii=False) + "\n")
    report["analysis_plan"] = {"path": str(plan_path), "sha256": sha256(plan_path.read_bytes()),
                               "mode": plan["mode"]}
    return {**plan["input_sha256"], **fingerprint_inputs([plan_path])}


def verify_analysis_plan(args, report, fingerprints):
    verify_frozen_inputs(fingerprints)
    actual = {str(path.relative_to(args.project)): sha256(path.read_bytes())
              for path in project_lean_sources(args.project)}
    if actual != report["provenance"]["project_lean_sources"]:
        raise BenchmarkError("project Lean source inventory changed after the analysis plan was frozen")
    if capture(["git", "rev-parse", "HEAD"], args.mathlib) != report["provenance"]["mathlib_revision"]:
        raise BenchmarkError("mathlib revision changed after the analysis plan was frozen")
    if capture(["git", "status", "--porcelain", "--untracked-files=no"], args.mathlib):
        raise BenchmarkError("mathlib tracked sources changed after the analysis plan was frozen")

def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("manifest", type=Path)
    parser.add_argument("--project", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--mathlib", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--repetitions", type=int, help="measured pair count (default: 10 exploratory; 40 confirmatory)")
    parser.add_argument("--warmups", type=int, default=1)
    parser.add_argument("--threads", type=int)
    parser.add_argument("--timeout", type=float, default=1800)
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--skip-setup", action="store_true", help="skip the tactic build; module setup/import dependencies are still resolved")
    parser.add_argument("--rebuild-tactic", action="store_true", help="invalidate only this project's NormArith generated artifacts and time a cache-disabled rebuild")
    parser.add_argument("--prepare-only", action="store_true", help="validate hashes and write proposed sources/patch without compiling")
    parser.add_argument("--confirmatory", action="store_true", help="require frozen selection, pilot calibration and a predeclared paired block BCa analysis")
    parser.add_argument("--calibration", type=Path, help="JSON pilot references, hashes, date, block_pairs and rationale")
    parser.add_argument("--block-pairs", type=int, help="even pairs per bootstrap block; must match calibration")
    parser.add_argument("--bootstrap-resamples", type=int, default=10000)
    parser.add_argument("--bootstrap-seed", type=int, default=20261020)
    args = parser.parse_args(argv)
    if args.confirmatory and args.calibration is None:
        parser.error("--calibration is required for --confirmatory")
    if not args.confirmatory and (args.calibration is not None or args.block_pairs is not None):
        parser.error("--calibration and --block-pairs require --confirmatory")
    args.repetitions = args.repetitions if args.repetitions is not None else (40 if args.confirmatory else 10)
    if args.bootstrap_resamples < 10000:
        parser.error("--bootstrap-resamples must be at least 10000")
    if args.block_pairs is not None and (args.block_pairs < 2 or args.block_pairs % 2):
        parser.error("--block-pairs must be positive and even")
    if args.skip_setup and args.rebuild_tactic:
        parser.error("--skip-setup and --rebuild-tactic are mutually exclusive")
    if args.repetitions < 1 or args.warmups < 1 or args.timeout <= 0 or (args.threads is not None and args.threads < 1):
        parser.error("repetitions, warmups, timeout and threads must be positive")
    args.project = args.project.resolve()
    args.mathlib = (args.mathlib or args.project / ".lake/packages/mathlib").resolve()
    args.output = args.output.resolve()
    if args.output.exists() and any(args.output.iterdir()):
        parser.error("output directory must be empty")
    args.output.mkdir(parents=True, exist_ok=True)
    (args.output / "launch.json").write_text(json.dumps({
        "schema_version": 1, "pid": os.getpid(), "started_at_utc": datetime.now(timezone.utc).isoformat(),
        "argv": [sys.executable, str(Path(__file__).resolve()), *(sys.argv[1:] if argv is None else argv)],
        "cwd": str(Path.cwd()), "interrupt_signal": "SIGINT",
    }, indent=2) + "\n")
    report = {"schema_version": 1, "status": "running", "setup": [], "measurements": [], "provenance": {},
              "inference": {"mode": "confirmatory" if args.confirmatory else "exploratory",
                            "success_criterion_met": False, "reason": "The run is not complete."}}
    try:
        manifest_bytes = args.manifest.read_bytes()
        manifest = json.loads(manifest_bytes)
        report["manifest"] = manifest
        report["selection_status"] = manifest.get("selection_status", "unspecified")
        provenance = report["provenance"]
        provenance.update({
            "created_at_utc": datetime.now(timezone.utc).isoformat(),
            "manifest_sha256": sha256(manifest_bytes),
            "mathlib_revision": capture(["git", "rev-parse", "HEAD"], args.mathlib),
            "project_revision": capture(["git", "rev-parse", "HEAD"], args.project),
            "toolchain": (args.project / "lean-toolchain").read_text().strip(),
            "project_toolchain_sha256": sha256((args.project / "lean-toolchain").read_bytes()),
            "platform": platform.platform(),
            "machine": platform.machine(),
            "cpu": platform.processor(),
            "cpu_count": os.cpu_count(),
            "threads": args.threads if args.threads is not None else "Lean default",
            "repetitions": args.repetitions,
            "warmups": args.warmups,
            "python_version": platform.python_version(),
            "harness_sha256": sha256(Path(__file__).read_bytes()),
            "measurement_protocol_sha256": measurement_protocol_sha256(),
            "project_lean_sources": {str(path.relative_to(args.project)): sha256(path.read_bytes()) for path in project_lean_sources(args.project)},
            "project_lake_manifest_sha256": sha256((args.project / "lake-manifest.json").read_bytes()),
            "project_lakefile_sha256": sha256((args.project / "lakefile.toml").read_bytes()),
        })
        if provenance["mathlib_revision"] != manifest.get("mathlib_revision"):
            raise BenchmarkError("mathlib checkout does not match manifest revision")
        if capture(["git", "status", "--porcelain", "--untracked-files=no"], args.mathlib):
            raise BenchmarkError("mathlib tracked sources must be unmodified; proposed edits use copied sources")
        prepared, report["accounting"] = prepare_sources(manifest, args.mathlib)
        if not prepared:
            raise BenchmarkError("manifest contains no proposed replacements")
        (args.output / "manifest.json").write_bytes(manifest_bytes)
        patches = []
        for source in prepared:
            for variant in ["original", "replacement"]:
                destination = args.output / "sources" / variant / source["path"]
                destination.parent.mkdir(parents=True, exist_ok=True)
                destination.write_text(source[variant])
            patches.extend(difflib.unified_diff(source["original"].splitlines(keepends=True), source["replacement"].splitlines(keepends=True), fromfile="a/" + source["path"], tofile="b/" + source["path"]))
        (args.output / "mathlib.patch").write_text("".join(patches))
        provenance["proposed_patch_sha256"] = sha256("".join(patches))
        provenance.update(implementation_line_costs(args.project))
        calibration = None
        if args.confirmatory:
            if report["selection_status"] != "frozen":
                raise BenchmarkError("confirmatory measurement requires frozen candidate selection")
            calibration = validate_calibration(args.calibration.resolve(), provenance, [source["path"] for source in prepared])
            if args.block_pairs is not None and args.block_pairs != calibration["block_pairs"]:
                raise BenchmarkError("--block-pairs does not match frozen pilot calibration")
            args.block_pairs = calibration["block_pairs"]
            if args.repetitions % args.block_pairs or args.repetitions // args.block_pairs < 3:
                raise BenchmarkError("confirmatory pairs must form at least three complete equal-size blocks")
        fingerprints = freeze_analysis_plan(args, report, prepared, calibration)
        report["inference"] = {"mode": "exploratory", "success_criterion_met": False,
                               "reason": "No calibrated confirmatory analysis was requested."}
        if args.confirmatory:
            report["inference"] = {"mode": "confirmatory", "success_criterion_met": False,
                                   "reason": "The predeclared measurement and input checks are not complete."}
        verify_analysis_plan(args, report, fingerprints)
        if args.prepare_only:
            report["status"] = "prepared"
        else:
            if (args.project / ".lake/packages/mathlib").resolve() != args.mathlib:
                raise BenchmarkError("--mathlib must be the project's resolved .lake/packages/mathlib dependency")
            paths = [source["path"] for source in prepared]
            lean, env, setups = setup_environment(args, report, paths)
            prepared_by_path = {source["path"]: source for source in prepared}
            prepared = [prepared_by_path[path] for path in report["compilation_order"]]
            setup_inputs = [path for variant in setups.values() for path in variant.values()]
            setup_inputs.extend(path for records in report["source_header_setups"].values()
                                for path in setup_record_inputs(records, args.project, include_imports=True))
            setup_inputs.extend(Path(path) for path in provenance["compiler_executables"])
            fingerprints.update(fingerprint_inputs(setup_inputs))
            report["resolved_setup_sha256"] = {str(path): fingerprints[str(path.resolve())] for path in setup_inputs}
            report["resolved_runtime"] = resolved_runtime_provenance(report, args.project, args.output, fingerprints)
            if args.confirmatory:
                validate_resolved_calibration(calibration, report["resolved_runtime"])
                report["resolved_calibration_match"] = True
            verify_analysis_plan(args, report, fingerprints)
            for phase, repetitions in [("warmup", args.warmups), ("measured", args.repetitions)]:
                for pair in range(repetitions):
                    order = ["original", "replacement"] if pair % 2 == 0 else ["replacement", "original"]
                    for variant in order:
                        verify_analysis_plan(args, report, fingerprints)
                        compile_pass(args, report, prepared, lean, env, setups, phase, pair, variant)
                        verify_analysis_plan(args, report, fingerprints)
            report["summary"] = summarize(report["measurements"], paths, args.repetitions)
            verify_analysis_plan(args, report, fingerprints)
            persisted = [json.loads(line) for line in (args.output / "measurements.jsonl").read_text().splitlines() if line.strip()]
            if persisted != report["measurements"]:
                raise BenchmarkError("persisted raw measurements differ from recorded compiler results")
            if args.confirmatory:
                report["inference"] = {
                    "mode": "confirmatory", "calibration_validated": True, "inputs_unchanged": True,
                    "calibration_sha256": calibration["sha256"],
                    "coverage_condition": "Conditional on independent representative calibrated blocks; calibration is not proof of independence.",
                    **confirmatory_statistics(report["measurements"], paths, args.repetitions,
                                              args.block_pairs, args.bootstrap_resamples, args.bootstrap_seed),
                }
            verify_analysis_plan(args, report, fingerprints)
            report["status"] = "complete"
        write_report(args.output, report)
        print(args.output / "report.md")
        return 0
    except KeyboardInterrupt:
        report.update(status="interrupted", error="Interrupted; completed measurements and raw compiler logs are retained.")
        report["inference"]["success_criterion_met"] = False
        write_report(args.output, report)
        print("benchmark interrupted; compiler process group reaped", file=sys.stderr)
        return 130
    except (BenchmarkError, OSError, ValueError, KeyError, TypeError) as error:
        report.update(status="failed", error=str(error))
        if "inference" in report:
            report["inference"]["success_criterion_met"] = False
        write_report(args.output, report)
        print(f"benchmark failed: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
