#!/usr/bin/env python3
"""Run the bounded semantic census over a pinned, tracked Mathlib universe."""

import argparse
from collections import Counter
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
from datetime import datetime, timezone
import gzip
import hashlib
import fcntl
import json
import os
from pathlib import Path
import platform
import signal
import subprocess
import sys
import time


class CensusError(Exception):
    pass


def digest(data):
    return hashlib.sha256(data.encode() if isinstance(data, str) else data).hexdigest()


def canonical_json(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"))


def bounded_results(items, worker, workers, stop_requested):
    items = iter(items)
    with ThreadPoolExecutor(max_workers=workers) as executor:
        pending = {}
        exhausted = False
        while pending or not exhausted:
            while len(pending) < workers and not exhausted and not stop_requested():
                try:
                    item = next(items)
                except StopIteration:
                    exhausted = True
                    break
                pending[executor.submit(worker, item)] = item
            if not pending:
                break
            finished, _ = wait(pending, return_when=FIRST_COMPLETED)
            for future in finished:
                yield pending.pop(future), future


def write_json(path, value):
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")
    temporary.replace(path)


def tracked_files(mathlib):
    result = subprocess.run(["git", "-C", str(mathlib), "ls-files", "-z", "--", "Mathlib"],
                            capture_output=True, check=True)
    return sorted(path.decode() for path in result.stdout.split(b"\0")
                  if path.startswith(b"Mathlib/") and path.endswith(b".lean"))


def freeze_manifest(path, manifest, resume):
    if path.exists():
        old = json.loads(path.read_text())
        if not resume:
            raise CensusError(f"run already exists; use --resume: {path.parent}")
        for field in ("protocol_hash", "files"):
            if old.get(field) != manifest.get(field):
                raise CensusError(f"resume refused: changed {field}")
        return old
    write_json(path, manifest)
    return manifest


def verify_evidence(output, result):
    evidence = result.get("evidence_sha256")
    if not evidence:
        raise CensusError("completed result has no raw-evidence hashes")
    for name, expected in evidence.items():
        path = (output / name).resolve()
        if not path.is_relative_to(output.resolve()) or not path.is_file() or digest(path.read_bytes()) != expected:
            raise CensusError(f"completed result evidence changed or missing: {name}")


def verify_implementation(project, manifest, binary):
    for name, expected in {**manifest["implementation_sha256"], **manifest.get("environment_sha256", {})}.items():
        path = project / name
        if not path.is_file() or digest(path.read_bytes()) != expected:
            raise CensusError(f"frozen implementation changed: {name}")
    if not binary.is_file() or digest(binary.read_bytes()) != manifest["extractor_binary_sha256"]:
        raise CensusError("frozen extractor binary changed")


def read_cached_setup(directory, module):
    metadata = json.loads((directory / f"{module}.metadata.json").read_text())
    with gzip.open(directory / f"{module}.json.gz", "rb") as handle:
        data = handle.read()
    if digest(data) != metadata.get("sha256"):
        raise CensusError(f"cached setup hash mismatch: {module}")
    return data, metadata


def validate_events(events, returncode, parse_error=None, timed_out=False):
    observations = [event for event in events if event.get("type") == "observation"
                    and event.get("phase") == "original"]
    original = {event["key"]: event for event in events
                if event.get("type") == "observation" and event.get("phase") == "original"
                and event.get("replacement_eligible")}
    attempts = [event for event in events if event.get("type") == "attempt"]
    statuses = Counter(event.get("status", "missing_status") for event in attempts)
    fragment_statuses = {}
    for event in attempts:
        fragment = original.get(event.get("key"), {}).get("fragment", "unknown")
        fragment_statuses.setdefault(fragment, Counter())[event.get("status", "missing_status")] += 1
    endings = [event for event in events if event.get("type") == "file_end"]
    original_phases = [event for event in events if event.get("type") == "phase_end"
                       and event.get("phase") == "original"]
    error = None
    if timed_out:
        error = "file_timeout"
    elif returncode != 0:
        error = "process_failed"
    elif parse_error:
        error = "invalid_jsonl"
    elif len(endings) != 1 or len(original_phases) != 1:
        error = "incomplete_ledger"
    elif original_phases[0].get("errors"):
        error = "original_elaboration_failed"
    elif endings[0].get("status") != "complete":
        error = endings[0].get("status", "incomplete_ledger")
    elif Counter(event.get("key") for event in attempts) != Counter(original.keys()):
        error = "invalid_attempt_ledger"
    elif any(event.get("status") == "success" and event.get("kernel_checked") is not True
             for event in attempts):
        error = "unchecked_success"
    return {
        "complete": error is None,
        "status": error or "complete",
        "eligible_observations": len(original),
        "attempt_status_counts": dict(sorted(statuses.items())),
        "original_observation_fragment_counts": dict(Counter(event.get("fragment", "unknown") for event in observations)),
        "original_eligible_fragment_counts": dict(Counter(event.get("fragment", "unknown") for event in original.values())),
        "attempt_status_counts_by_original_fragment": {fragment: dict(counts)
                                                       for fragment, counts in fragment_statuses.items()},
        "successful_proposals": 0 if error else statuses["success"],
        "counts": endings[0].get("counts", {}) if endings else {},
    }


def source_proposal(path, source, attempt):
    start, end = attempt["start_byte"], attempt["end_byte"]
    if not isinstance(start, int) or not isinstance(end, int) or not 0 <= start < end <= len(source):
        raise CensusError(f"invalid UTF-8 source span: {path}")
    try:
        source[:start].decode("utf-8")
        original = source[start:end].decode("utf-8")
        source[end:].decode("utf-8")
    except UnicodeDecodeError as error:
        raise CensusError(f"span splits a UTF-8 character: {path}") from error
    return {**attempt, "path": path, "source_sha256": digest(source),
            "original_sha256": digest(source[start:end]), "original": original,
            "evidence_stage": "isolated_kernel_checked_proposal"}


def run_process(command, cwd, environment, timeout, stdout_path, stderr_path):
    started = time.perf_counter()
    with stdout_path.open("wb") as stdout, stderr_path.open("wb") as stderr:
        process = subprocess.Popen(command, cwd=cwd, env=environment,
                                   stdout=stdout, stderr=stderr, start_new_session=True)
        timed_out, terminated = False, None
        while True:
            pid, status, usage = os.wait4(process.pid, os.WNOHANG)
            if pid:
                returncode = os.waitstatus_to_exitcode(status)
                process.returncode = returncode
                break
            elapsed = time.perf_counter() - started
            if elapsed >= timeout and not timed_out:
                timed_out, terminated = True, time.perf_counter()
                os.killpg(process.pid, signal.SIGTERM)
            elif terminated is not None and time.perf_counter() - terminated > 3:
                os.killpg(process.pid, signal.SIGKILL)
                terminated = None
            time.sleep(0.02)
    return {"command": [str(part) for part in command], "returncode": returncode,
            "timed_out": timed_out, "elapsed_seconds": time.perf_counter() - started,
            "peak_rss_bytes": int(usage.ru_maxrss * (1 if sys.platform == "darwin" else 1024)),
            "user_seconds": usage.ru_utime, "system_seconds": usage.ru_stime}


def parse_setup_batch(text, modules):
    try:
        setups = [json.loads(line) for line in text.splitlines() if line.strip()]
    except json.JSONDecodeError as error:
        raise CensusError("invalid batched Lake setup JSONL") from error
    if len(setups) != len(modules) or any(not isinstance(setup, dict) or setup.get("name") != module
                                         for module, setup in zip(modules, setups)):
        raise CensusError("batched Lake setup module order/count mismatch")
    return setups


def prepare_setups(selected, config, project, output, environment):
    directory = output / "setups"
    directory.mkdir(exist_ok=True)
    remaining = [path for path in selected if not (directory / (path[:-5].replace("/", ".") + ".json.gz")).exists()]
    for start in range(0, len(remaining), config["setup_batch_size"]):
        if (output / "STOP_REQUESTED").exists():
            break
        paths = remaining[start:start + config["setup_batch_size"]]
        modules = [path[:-5].replace("/", ".") for path in paths]
        base_key = digest(canonical_json(modules))[:16]
        batch_key, generation = base_key, 1
        while (directory / f"batch-{batch_key}.metadata.json").exists():
            generation += 1
            batch_key = f"{base_key}-{generation}"
        stdout_path, stderr_path = directory / f"batch-{batch_key}.jsonl", directory / f"batch-{batch_key}.stderr.log"
        command = ["lake", "--no-build", "-q", "-J", "query", *[f"@mathlib/+{module}:setup" for module in modules]]
        process = run_process(command, project, environment, config["setup_timeout_seconds"], stdout_path, stderr_path)
        evidence = {**process, "modules": modules}
        try:
            if process["returncode"] != 0 or process["timed_out"]:
                raise CensusError("batched Lake setup failed; individual fallback required")
            setups = parse_setup_batch(stdout_path.read_text(), modules)
            for module, setup in zip(modules, setups):
                data = canonical_json(setup).encode()
                with gzip.open(directory / f"{module}.json.gz", "wb") as handle:
                    handle.write(data)
                write_json(directory / f"{module}.metadata.json",
                           {"kind": "batched_lake_query", "batch": f"setups/batch-{batch_key}.metadata.json",
                            "sha256": digest(data)})
            evidence["status"] = "complete"
        except (CensusError, OSError, ValueError) as error:
            evidence.update(status="individual_fallback", error=str(error))
            with stdout_path.open("rb") as source, gzip.open(str(stdout_path) + ".gz", "wb") as target:
                while chunk := source.read(1024 * 1024):
                    target.write(chunk)
        write_json(directory / f"batch-{batch_key}.metadata.json", evidence)
        stdout_path.unlink(missing_ok=True)
        print(f"setup batch {start + 1}–{start + len(paths)}/{len(remaining)}: {evidence['status']}", flush=True)


def parse_events(path):
    events = []
    if not path.exists():
        return events, None
    for number, line in enumerate(path.read_text().splitlines(), 1):
        try:
            events.append(json.loads(line))
        except json.JSONDecodeError:
            return events, f"invalid JSONL at line {number}"
    return events, None


def retry_eligible(result):
    return (not result.get("complete") and result.get("resource_tier") == 1
            and result.get("status") in {"file_timeout", "process_failed"})


def run_file(specification, config, project, mathlib, output, environment, import_closure, tier=1):
    relative = specification["path"]
    module = relative[:-5].replace("/", ".")
    directory = output / "files" / module
    directory.mkdir(parents=True, exist_ok=True)
    result_path = directory / "result.json"
    if result_path.exists():
        old = json.loads(result_path.read_text())
        verify_evidence(output, old)
        if old.get("complete"):
            return old
        if old.get("resource_tier", 1) >= tier:
            return old
    number = 1
    while (directory / f"attempt-{number:02d}").exists():
        number += 1
    attempt_directory = directory / f"attempt-{number:02d}"
    attempt_directory.mkdir()
    setup_path = attempt_directory / "setup.json"
    cached_setup = output / "setups" / f"{module}.json.gz"
    if cached_setup.exists():
        data, setup_process = read_cached_setup(cached_setup.parent, module)
        setup_path.write_bytes(data)
        setup_process.update(returncode=0, timed_out=False)
    else:
        setup_command = ["lake", "--no-build", "-q", "-J", "query", f"@mathlib/+{module}:setup"]
        setup_process = run_process(setup_command, project, environment, config["setup_timeout_seconds"],
                                    setup_path, attempt_directory / "setup.stderr.log")
    result = {"path": relative, "module": module, "source_sha256": specification["sha256"],
              "resource_tier": tier, "limits": {"file_timeout_seconds": config["file_timeout_seconds"],
                                                 "memory_mb": config["memory_mb"]},
              "attempt": number, "directory": str(attempt_directory.relative_to(output)),
              "setup": setup_process, "complete": False, "successful_proposals": 0,
              "eligible_observations": 0, "attempt_status_counts": {}, "counts": {}}
    try:
        if setup_process["returncode"] != 0 or setup_process["timed_out"]:
            raise CensusError("setup_failed")
        setup_data = json.loads(setup_path.read_text())
        if setup_data.get("name") != module:
            raise CensusError("setup_module_mismatch")
        source = (mathlib / relative).read_bytes()
        if digest(source) != specification["sha256"]:
            raise CensusError("source_changed_after_freeze")
        request = {
            "source": str(mathlib / relative), "setup": str(setup_path),
            "output": str(attempt_directory / "events.jsonl"), "relativePath": relative,
            "goalHeartbeats": config["goal_heartbeats"], "goalTimeoutMs": config["goal_timeout_ms"],
            "memoryMb": config["memory_mb"], "maxAttemptsPerFile": config["max_attempts_per_file"],
            "attempts": not config["extract_only"], "importCycle": module in import_closure,
            "requireLineSaving": not config["attempt_single_line"],
        }
        write_json(attempt_directory / "request.json", request)
        command = [str(project / ".lake/build/bin/norm_arith_census"),
                   str(attempt_directory / "request.json")]
        process = run_process(command, project, environment, config["file_timeout_seconds"],
                              attempt_directory / "stdout.log", attempt_directory / "stderr.log")
        result["extraction"] = process
        events, parse_error = parse_events(attempt_directory / "events.jsonl")
        result.update(validate_events(events, process["returncode"], parse_error, process["timed_out"]))
        if parse_error:
            result["ledger_parse_error"] = parse_error
        if digest((mathlib / relative).read_bytes()) != specification["sha256"]:
            result.update(complete=False, status="source_changed_after_freeze", successful_proposals=0)
        proposals = []
        if result["complete"]:
            proposals = [source_proposal(relative, source, event) for event in events
                         if event.get("type") == "attempt" and event.get("status") == "success"]
        with (attempt_directory / "proposals.jsonl").open("w") as handle:
            for proposal in proposals:
                handle.write(canonical_json(proposal) + "\n")
        result["proposal_file"] = str((attempt_directory / "proposals.jsonl").relative_to(output))
    except (CensusError, OSError, ValueError) as error:
        result.update(complete=False, status=str(error), successful_proposals=0)
    finally:
        if setup_path.exists():
            result["setup_sha256"] = digest(setup_path.read_bytes())
            if not cached_setup.exists():
                with setup_path.open("rb") as source_handle, gzip.open(str(setup_path) + ".gz", "wb") as target:
                    while chunk := source_handle.read(1024 * 1024):
                        target.write(chunk)
            setup_path.unlink()
        result["evidence_sha256"] = {
            str(path.relative_to(output)): digest(path.read_bytes())
            for path in sorted(attempt_directory.iterdir()) if path.is_file() and path.name != "result.json"
        }
        if cached_setup.exists():
            result["evidence_sha256"][str(cached_setup.relative_to(output))] = digest(cached_setup.read_bytes())
            metadata_path = cached_setup.with_name(f"{module}.metadata.json")
            result["evidence_sha256"][str(metadata_path.relative_to(output))] = digest(metadata_path.read_bytes())
            if "batch" in setup_process:
                batch_path = output / setup_process["batch"]
                result["evidence_sha256"][str(batch_path.relative_to(output))] = digest(batch_path.read_bytes())
        write_json(attempt_directory / "result.json", result)
        write_json(result_path, result)
    return result


def summarize(manifest, results, output):
    statuses = Counter(result["status"] for result in results)
    attempts = Counter()
    counts = Counter()
    observation_fragments, eligible_fragments, fragment_statuses = Counter(), Counter(), {}
    for result in results:
        attempts.update(result.get("attempt_status_counts", {}))
        counts.update(result.get("counts", {}))
        observation_fragments.update(result.get("original_observation_fragment_counts", {}))
        eligible_fragments.update(result.get("original_eligible_fragment_counts", {}))
        for fragment, values in result.get("attempt_status_counts_by_original_fragment", {}).items():
            fragment_statuses.setdefault(fragment, Counter()).update(values)
    complete = sum(result["complete"] for result in results)
    selected = len(manifest["selected_files"])
    integrity_valid = (output / "integrity.json").exists() and json.loads((output / "integrity.json").read_text()).get("status") == "valid"
    summary = {
        "schema_version": 1, "protocol_hash": manifest["protocol_hash"],
        "universe_files": len(manifest["files"]), "selected_files": selected,
        "processed_files": len(results), "completed_files": complete,
        "failed_files": len(results) - complete, "unprocessed_files": selected - len(results),
        "scope": manifest["scope"],
        "full_universe_processed": manifest["scope"] == "full" and len(results) == selected,
        "full_universe_completed": manifest["scope"] == "full" and complete == selected and integrity_valid,
        "file_status_counts": dict(sorted(statuses.items())),
        "attempt_status_counts": dict(sorted(attempts.items())), "counts": dict(counts),
        "original_observation_fragment_counts": dict(observation_fragments),
        "original_eligible_fragment_counts": dict(eligible_fragments),
        "attempt_status_counts_by_original_fragment": {fragment: dict(values)
                                                       for fragment, values in fragment_statuses.items()},
        "resource_tier_counts": dict(Counter(str(result.get("resource_tier", "unknown")) for result in results)),
        "successful_proposals": sum(result.get("successful_proposals", 0) for result in results),
        "eligible_observations": sum(result.get("eligible_observations", 0) for result in results),
        "evidence_stage": "isolated_kernel_checked_proposals_not_compiled_patches",
        "frozen_inputs_verified": integrity_valid,
    }
    write_json(output / "summary.json", summary)
    return summary


def parser():
    result = argparse.ArgumentParser(description=__doc__)
    result.add_argument("--project", type=Path, default=Path(__file__).resolve().parents[1])
    result.add_argument("--mathlib", type=Path)
    result.add_argument("--output", type=Path, required=True)
    result.add_argument("--workers", type=int, default=4)
    result.add_argument("--file", action="append", default=[], help="Tracked relative path; labels run calibration")
    result.add_argument("--limit", type=int, help="First N sorted files; labels run calibration")
    result.add_argument("--resume", action="store_true")
    result.add_argument("--extract-only", action="store_true")
    result.add_argument("--attempt-single-line", action="store_true", help="Calibration override; default logs these as unable to save a code line")
    result.add_argument("--file-timeout", type=float, default=600)
    result.add_argument("--setup-timeout", type=float, default=120)
    result.add_argument("--setup-batch-size", type=int, default=32)
    result.add_argument("--memory-mb", type=int, default=4096)
    result.add_argument("--retry-file-timeout", type=float, default=1800)
    result.add_argument("--retry-memory-mb", type=int, default=8192)
    result.add_argument("--goal-heartbeats", type=int, default=200000)
    result.add_argument("--goal-timeout-ms", type=int, default=2000)
    result.add_argument("--max-attempts-per-file", type=int, default=10000)
    return result


def run(args):
    project = args.project.resolve()
    mathlib = (args.mathlib or project / ".lake/packages/mathlib").resolve()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    stop_marker = output / "STOP_REQUESTED"
    if stop_marker.exists():
        raise CensusError("remove STOP_REQUESTED explicitly before starting or resuming")
    if min(args.workers, args.memory_mb, args.goal_heartbeats, args.goal_timeout_ms,
           args.max_attempts_per_file, args.file_timeout, args.setup_timeout, args.setup_batch_size,
           args.retry_file_timeout, args.retry_memory_mb) <= 0:
        raise CensusError("resource bounds must be positive")
    if not (project / ".lake/build/bin/norm_arith_census").is_file():
        raise CensusError("build the extractor first: lake build norm_arith_census")
    paths = tracked_files(mathlib)
    if not paths:
        raise CensusError("no tracked Mathlib/**/*.lean files")
    unknown = sorted(set(args.file) - set(paths))
    if unknown:
        raise CensusError(f"not in tracked universe: {unknown}")
    selected = sorted(set(args.file)) if args.file else paths
    if args.limit is not None:
        if args.limit <= 0:
            raise CensusError("--limit must be positive")
        selected = selected[:args.limit]
    config = {
        "file_timeout_seconds": args.file_timeout, "setup_timeout_seconds": args.setup_timeout,
        "memory_mb": args.memory_mb, "goal_heartbeats": args.goal_heartbeats,
        "goal_timeout_ms": args.goal_timeout_ms, "max_attempts_per_file": args.max_attempts_per_file,
        "extract_only": args.extract_only, "workers": args.workers, "lean_threads_per_worker": 1,
        "attempt_single_line": args.attempt_single_line,
        "setup_batch_size": args.setup_batch_size,
        "retry": {"file_timeout_seconds": args.retry_file_timeout, "memory_mb": args.retry_memory_mb,
                  "workers": 1, "maximum_resource_tier": 2,
                  "eligible_file_statuses": ["file_timeout", "process_failed"],
                  "goal_limits_unchanged": True},
        "preprocessing": "norm_arith built-in distance normalization; no additional preparation",
        "matching": "original and augmented exact source span plus canonical closed context/goal",
        "graceful_stop_marker": "STOP_REQUESTED; drain active files and preserve incomplete coverage",
    }
    source_files = [project / "NormArith.lean", *sorted((project / "NormArith").rglob("*.lean")),
                    Path(__file__).resolve()]
    hashes = {str(path.relative_to(project)): digest(path.read_bytes()) for path in source_files}
    revision = subprocess.check_output(["git", "-C", str(mathlib), "rev-parse", "HEAD"], text=True).strip()
    files = [{"path": path, "sha256": digest((mathlib / path).read_bytes())} for path in paths]
    if subprocess.check_output(["git", "-C", str(mathlib), "status", "--porcelain", "--untracked-files=no"], text=True):
        raise CensusError("mathlib tracked checkout must be clean")
    environment_hashes = {name: digest((project / name).read_bytes()) for name in
                          ("lean-toolchain", "lakefile.toml", "lake-manifest.json")}
    protocol = {"config": config, "implementation_sha256": hashes, "mathlib_revision": revision,
                "environment_sha256": environment_hashes,
                "selected_files": selected, "extractor_binary_sha256":
                digest((project / ".lake/build/bin/norm_arith_census").read_bytes())}
    manifest = {"schema_version": 1, "created_at": datetime.now(timezone.utc).isoformat(),
                **protocol, "protocol_hash": digest(canonical_json(protocol)), "files": files,
                "scope": "calibration" if args.file or args.limit else "full",
                "project": str(project), "mathlib": str(mathlib), "platform": platform.platform(),
                "lean_version": subprocess.check_output(["lake", "env", "lean", "--version"],
                                                        cwd=project, text=True).strip()}
    manifest = freeze_manifest(output / "manifest.json", manifest, args.resume)
    verify_implementation(project, manifest, project / ".lake/build/bin/norm_arith_census")
    for name, expected in {**hashes, **environment_hashes}.items():
        path = output / "frozen-implementation" / name
        path.parent.mkdir(parents=True, exist_ok=True)
        if path.exists():
            if digest(path.read_bytes()) != expected:
                raise CensusError(f"frozen implementation snapshot changed: {name}")
        else:
            data = (project / name).read_bytes()
            if digest(data) != expected:
                raise CensusError(f"implementation changed while snapshotting: {name}")
            path.write_bytes(data)
    write_json(output / "integrity.json", {"status": "pending", "protocol_hash": manifest["protocol_hash"]})
    startup_number = 1
    while (output / f"startup-{startup_number:02d}.json").exists():
        startup_number += 1
    freshness = run_process(["lake", "--no-build", "--no-cache", "--rehash", "-q", "build", "norm_arith_census"],
                            project, os.environ.copy(), args.setup_timeout,
                            output / f"startup-{startup_number:02d}.stdout.log",
                            output / f"startup-{startup_number:02d}.stderr.log")
    write_json(output / f"startup-{startup_number:02d}.json", freshness)
    if freshness["returncode"] != 0 or freshness["timed_out"]:
        write_json(output / "integrity.json", {"status": "invalid", "error": "extractor_build_not_fresh"})
        raise CensusError("extractor build is not fresh; run lake build norm_arith_census before the census")
    verify_implementation(project, manifest, project / ".lake/build/bin/norm_arith_census")
    env_output = subprocess.check_output(["lake", "env", "python3", "-c",
                                          "import json,os;print(json.dumps(dict(os.environ)))"], cwd=project)
    environment = json.loads(env_output)
    environment["LEAN_NUM_THREADS"] = "1"
    setup = json.loads((project / ".lake/build/ir/NormArith.setup.json").read_text())
    import_closure = set(setup["importArts"])
    prepare_setups(selected, config, project, output, environment)
    results = []
    specifications = {item["path"]: item for item in files}
    def work(path):
        return run_file(specifications[path], config, project, mathlib, output, environment, import_closure)

    for path, future in bounded_results(selected, work, args.workers, stop_marker.exists):
        try:
            result = future.result()
        except Exception as error:
            result = {"path": path, "complete": False, "status": "orchestrator_exception",
                      "error": str(error), "successful_proposals": 0}
            directory = output / "files" / path[:-5].replace("/", ".")
            directory.mkdir(parents=True, exist_ok=True)
            write_json(directory / "orchestrator_error.json", result)
            write_json(directory / "result.json", result)
        results.append(result)
        summary = summarize(manifest, results, output)
        print(f"[{len(results)}/{len(selected)}] {path}: {result['status']} "
              f"({result.get('successful_proposals', 0)} proposals)", flush=True)
    summarize(manifest, results, output)
    retry_config = {**config, **config["retry"]}
    for index, result in enumerate(results):
        if stop_marker.exists():
            break
        if retry_eligible(result):
            print(f"retry tier2: {result['path']}", flush=True)
            results[index] = run_file(specifications[result["path"]], retry_config, project, mathlib,
                                      output, environment, import_closure, tier=2)
            summary = summarize(manifest, results, output)
    if stop_marker.exists():
        number = 1
        while (output / f"interruption-{number:02d}.json").exists():
            number += 1
        interruption = {"status": "interrupted", "reason": "STOP_REQUESTED",
                        "created_at": datetime.now(timezone.utc).isoformat(),
                        "protocol_hash": manifest["protocol_hash"], "processed_files": len(results),
                        "unprocessed_files": len(selected) - len(results)}
        write_json(output / f"interruption-{number:02d}.json", interruption)
        write_json(output / "integrity.json", interruption)
        summarize(manifest, results, output)
        return 130
    try:
        verify_implementation(project, manifest, project / ".lake/build/bin/norm_arith_census")
        if any(digest((mathlib / item["path"]).read_bytes()) != item["sha256"] for item in files):
            raise CensusError("frozen Mathlib sources changed during census")
    except CensusError as error:
        write_json(output / "integrity.json", {"status": "invalid", "error": str(error),
                                                "protocol_hash": manifest["protocol_hash"]})
        summary = summarize(manifest, results, output)
        raise
    write_json(output / "integrity.json", {"status": "valid", "protocol_hash": manifest["protocol_hash"]})
    summary = summarize(manifest, results, output)
    return 0 if summary["failed_files"] == 0 else 1


def main(argv=None):
    args = parser().parse_args(argv)
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    with (output / ".run.lock").open("a") as lock:
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as error:
            raise CensusError(f"another census process owns this output directory: {output}") from error
        return run(args)


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (CensusError, OSError, subprocess.CalledProcessError) as error:
        print(f"census: {error}", file=sys.stderr)
        raise SystemExit(2)
