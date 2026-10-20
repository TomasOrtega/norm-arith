#!/usr/bin/env python3
"""Compile original and proposed mathlib files against one pinned environment."""

import argparse
from collections import Counter
from datetime import datetime, timezone
import difflib
import hashlib
import json
import os
from pathlib import Path
import platform
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


def summarize(measurements, paths, repetitions):
    measured = [row for row in measurements if row["phase"] == "measured"]
    expected = {(pair, variant, path) for pair in range(repetitions) for variant in ["original", "replacement"] for path in paths}
    actual = [(row["pair"], row["variant"], row["path"]) for row in measured]
    if len(set(actual)) != len(actual) or set(actual) != expected:
        raise BenchmarkError("incomplete or duplicated paired measurements")

    def distribution(values):
        return {"median_seconds": statistics.median(values), "min_seconds": min(values), "max_seconds": max(values), "seconds": values}

    def comparison(original, replacement):
        return {"original": distribution(original), "replacement": distribution(replacement), "speedup": statistics.median(original) / statistics.median(replacement)}

    per_file = []
    for path in paths:
        values = {variant: [next(row["seconds"] for row in measured if row["path"] == path and row["variant"] == variant and row["pair"] == pair) for pair in range(repetitions)] for variant in ["original", "replacement"]}
        per_file.append({"path": path, **comparison(values["original"], values["replacement"])})
    totals = {variant: [sum(row["seconds"] for row in measured if row["variant"] == variant and row["pair"] == pair) for pair in range(repetitions)] for variant in ["original", "replacement"]}
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
    if report["status"] == "complete":
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
                lines.extend([f"The separate NormArith rebuild after invalidating its own generated artifacts took **{row['seconds']:.3f} s** with dependency artifacts retained and artifact-cache retrieval disabled.", ""])
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
    return invalidated


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
    setups = {}
    setup_values = {}
    for path in paths:
        module = path[:-5].replace("/", ".")
        text = setup_command(f"module-{module}", [args.lake, "-q", "-J", "query", f"@mathlib/+{module}:setup"])
        try:
            setup = json.loads(text)
        except json.JSONDecodeError as error:
            raise BenchmarkError(f"invalid Lake module setup JSON for {path}") from error
        if isinstance(setup, list) and len(setup) == 1:
            setup = setup[0]
        if not isinstance(setup, dict) or setup.get("name") != module:
            raise BenchmarkError(f"unexpected Lake module setup for {path}")
        if setup.get("options", {}).get("compiler.postponeCompile", False):
            raise BenchmarkError("compiler.postponeCompile=true requires a separate leanir benchmark")
        setup_path = setup_dir / f"{module}.setup.json"
        setup_path.write_text(json.dumps(setup, indent=2) + "\n")
        setups[path] = setup_path
        setup_values[path] = setup
    added_imports = {module for item in report["manifest"]["files"] for module in item.get("imports", []) if item["path"] in paths}
    added_dependencies = {}
    for module in sorted(added_imports):
        text = setup_command(f"added-import-{module}", [args.lake, "-q", "-J", "query", f"+{module}:setup"])
        imported = json.loads(text)
        if not isinstance(imported, dict):
            raise BenchmarkError(f"unexpected Lake module setup for added import {module}")
        added_dependencies[module] = set(imported.get("importArts", {})) | {module}
    for path, setup in setup_values.items():
        imports = next(item.get("imports", []) for item in report["manifest"]["files"] if item["path"] == path)
        for module in imports:
            for dependency in added_dependencies[module]:
                setup["importArts"].setdefault(dependency, [])
    order = dependency_order(setup_values)
    report["compilation_order"] = order
    keys = ["PATH", "LEAN_PATH", "LEAN_SYSROOT", "LEAN_SRC_PATH", "DYLD_LIBRARY_PATH", "LD_LIBRARY_PATH"]
    script = f"import json, os; print(json.dumps({{key: os.environ[key] for key in {keys!r} if key in os.environ}}))"
    environment = json.loads(setup_command("environment", [args.lake, "env", sys.executable, "-c", script]))
    env = dict(os.environ, **environment)
    prefix = setup_command("lean-prefix", [args.lake, "env", "lean", "--print-prefix"])
    lean = str(Path(prefix) / "bin/lean")
    report["provenance"]["lean_version"] = setup_command("lean-version", [lean, "--version"])
    report["provenance"]["lake_version"] = setup_command("lake-version", [args.lake, "--version"])
    report["provenance"]["lean_environment"] = environment
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
        setup = source_setup(json.loads(setups[path].read_text()), compiled)
        setup_path = trial / "setups" / (path[:-5] + ".setup.json")
        setup_path.parent.mkdir(parents=True, exist_ok=True)
        setup_path.write_text(json.dumps(setup, indent=2) + "\n")
        if setup.get("isModule"):
            outputs.extend(Path(str(stem) + suffix) for suffix in [".olean.server", ".olean.private", ".ir", ".ir.sig"])
        command = [lean, str(source_root / path), "-R", str(source_root), "--setup", str(setup_path), "-o", str(outputs[0]), "-i", str(outputs[1]), "-c", str(outputs[2]), "--json"]
        if args.threads is not None:
            command.extend(["-j", str(args.threads)])
        result = run_process(command, args.project, trial / "logs" / path[:-5], args.timeout, env=env)
        row = {"phase": phase, "pair": pair, "variant": variant, "path": path, **result}
        report["measurements"].append(row)
        with (args.output / "measurements.jsonl").open("a") as stream:
            stream.write(json.dumps(row) + "\n")
        validate_compilation(result, outputs)
        module = path[:-5].replace("/", ".")
        compiled[module] = [[str(outputs[0])]]
        if setup.get("isModule"):
            compiled[module] = [[str(outputs[0]), str(outputs[3]), str(outputs[4])], [str(outputs[6]), str(outputs[5])]]
        print(f"{phase} {pair + 1}: {variant} {path}: {result['seconds']:.3f}s", flush=True)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("manifest", type=Path)
    parser.add_argument("--project", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--mathlib", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--repetitions", type=int, default=10)
    parser.add_argument("--warmups", type=int, default=1)
    parser.add_argument("--threads", type=int)
    parser.add_argument("--timeout", type=float, default=1800)
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--skip-setup", action="store_true", help="skip the tactic build; module setup/import dependencies are still resolved")
    parser.add_argument("--rebuild-tactic", action="store_true", help="invalidate only this project's NormArith generated artifacts and time a cache-disabled rebuild")
    parser.add_argument("--prepare-only", action="store_true", help="validate hashes and write proposed sources/patch without compiling")
    args = parser.parse_args(argv)
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
    report = {"schema_version": 1, "status": "running", "setup": [], "measurements": [], "provenance": {}}
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
            "platform": platform.platform(),
            "machine": platform.machine(),
            "cpu": platform.processor(),
            "cpu_count": os.cpu_count(),
            "threads": args.threads if args.threads is not None else "Lean default",
            "repetitions": args.repetitions,
            "warmups": args.warmups,
            "python_version": platform.python_version(),
            "harness_sha256": sha256(Path(__file__).read_bytes()),
            "project_lean_sources": {str(path.relative_to(args.project)): sha256(path.read_bytes()) for path in sorted(set(args.project.glob("NormArith*.lean")) | set(args.project.glob("NormArith/**/*.lean")) | set(args.project.glob("NormArithTest/**/*.lean")))},
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
        provenance["tactic_implementation_code_lines"] = sum(code_line_count(path.read_text()) for path in [args.project / "NormArith.lean", *sorted(args.project.glob("NormArith/**/*.lean"))])
        if args.prepare_only:
            report["status"] = "prepared"
        else:
            if (args.project / ".lake/packages/mathlib").resolve() != args.mathlib:
                raise BenchmarkError("--mathlib must be the project's resolved .lake/packages/mathlib dependency")
            paths = [source["path"] for source in prepared]
            lean, env, setups = setup_environment(args, report, paths)
            prepared_by_path = {source["path"]: source for source in prepared}
            prepared = [prepared_by_path[path] for path in report["compilation_order"]]
            for phase, repetitions in [("warmup", args.warmups), ("measured", args.repetitions)]:
                for pair in range(repetitions):
                    order = ["original", "replacement"] if pair % 2 == 0 else ["replacement", "original"]
                    for variant in order:
                        compile_pass(args, report, prepared, lean, env, setups, phase, pair, variant)
            report["summary"] = summarize(report["measurements"], paths, args.repetitions)
            for path, expected_hash in provenance["project_lean_sources"].items():
                if sha256((args.project / path).read_bytes()) != expected_hash:
                    raise BenchmarkError(f"project source changed during measurements: {path}")
            if sha256((args.project / "lakefile.toml").read_bytes()) != provenance["project_lakefile_sha256"]:
                raise BenchmarkError("project Lake options changed during measurements")
            report["status"] = "complete"
        write_report(args.output, report)
        print(args.output / "report.md")
        return 0
    except (BenchmarkError, OSError, ValueError, KeyError) as error:
        report.update(status="failed", error=str(error))
        write_report(args.output, report)
        print(f"benchmark failed: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
