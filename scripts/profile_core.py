#!/usr/bin/env python3
"""Measure reference search, compact LP, and checked proof replay in fresh processes."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import platform
import re
import signal
import statistics
import subprocess
import tempfile
import time
from datetime import datetime, timezone
from pathlib import Path

from benchmark_snippets import ROOT, command_output, snippet_parts

VARIANTS = ("reference", "lp", "replay")
PROFILE = re.compile(r"search_ns=(\d+) reconstruction_ns=(\d+) proof_nodes=(\d+)")


def message_text(output: str) -> str:
    messages = []
    for line in output.splitlines():
        try:
            message = json.loads(line)
        except json.JSONDecodeError:
            messages.append(line)
        else:
            messages.append(message.get("data", line) if isinstance(message, dict) else line)
    return "\n".join(messages)


def read_replay(output: str) -> tuple[str, dict]:
    text = message_text(output)
    match = re.search(r'norm_arith_replay\s*("(?:[^"\\]|\\.)*")', text)
    if not match:
        raise ValueError("Lean did not emit a complete replay certificate")
    payload = json.loads(match.group(1))
    graph = json.loads(payload)
    if not isinstance(graph, list) or len(graph) != 3 or graph[0] != 1:
        raise ValueError("unsupported replay graph")
    if not isinstance(graph[2], list):
        raise ValueError("invalid replay node list")
    return "norm_arith_replay " + match.group(1), {
        "certificate_bytes": len(payload.encode()), "graph_nodes": len(graph[2]),
        "certificate_sha256": hashlib.sha256(payload.encode()).hexdigest(),
    }


def replace_proof(source: str, tactic: str) -> str:
    _, proof = snippet_parts(source)
    return source.replace(proof, "\n  " + tactic + "\n")


def profile_metrics(stdout: str, stderr: str, system: str) -> dict:
    text = message_text(stdout + "\n" + stderr)
    phases = [tuple(map(int, match)) for match in PROFILE.findall(text)]
    rss = None
    if system == "Darwin":
        match = re.search(r"(\d+)\s+maximum resident set size", stderr)
        if match:
            rss = int(match.group(1))
    elif system == "Linux":
        match = re.search(r"NORM_ARITH_MAX_RSS_KB=(\d+)", stderr)
        if match:
            rss = int(match.group(1)) * 1024
    return {
        "lp_attempts_measured": len(phases),
        "search_ns": sum(row[0] for row in phases) if phases else None,
        "reconstruction_ns": sum(row[1] for row in phases) if phases else None,
        "proof_nodes_without_sharing": sum(row[2] for row in phases) if phases else None,
        "peak_rss_bytes": rss,
    }


def compile_sample(lake: str, source: Path, output: Path, timeout: float) -> dict:
    output.mkdir(parents=True)
    olean = output / "proof.olean"
    command = [lake, "env", "lean", "--json", "-DwarningAsError=true",
               "-o", str(olean), str(source)]
    system = platform.system()
    if Path("/usr/bin/time").is_file():
        if system == "Darwin":
            command = ["/usr/bin/time", "-l", *command]
        elif system == "Linux":
            command = ["/usr/bin/time", "-f", "NORM_ARITH_MAX_RSS_KB=%M", *command]
    started = time.perf_counter()
    with subprocess.Popen(command, cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                          text=True, start_new_session=True) as process:
        timed_out = False
        try:
            stdout, stderr = process.communicate(timeout=timeout)
        except subprocess.TimeoutExpired:
            timed_out = True
            os.killpg(process.pid, signal.SIGKILL)
            stdout, stderr = process.communicate()
    return {
        "seconds": time.perf_counter() - started,
        "success": process.returncode == 0 and not timed_out,
        "returncode": process.returncode, "timed_out": timed_out,
        "stdout": stdout, "stderr": stderr,
        "olean_bytes": olean.stat().st_size if olean.exists() else None,
        **profile_metrics(stdout, stderr, system),
    }


def summarize(samples: list[dict], cases: list[str]) -> dict:
    measured = [sample for sample in samples if sample["phase"] == "measure"]
    expected = {(case, variant) for case in cases for variant in VARIANTS}
    present = {(sample["case"], sample["variant"]) for sample in measured}
    all_success = bool(measured) and expected == present and all(s["success"] for s in samples)
    results = []
    for case in cases:
        entry = {"case": case, "variants": {}}
        for variant in VARIANTS:
            selected = [s for s in measured if s["case"] == case and s["variant"] == variant]
            ok = bool(selected) and all(s["success"] for s in selected)
            fields = ("seconds", "search_ns", "reconstruction_ns", "peak_rss_bytes",
                      "proof_nodes_without_sharing", "olean_bytes")
            entry["variants"][variant] = {
                "all_succeeded": ok,
                **{f"median_{key}": statistics.median([s[key] for s in selected])
                   if ok and all(s.get(key) is not None for s in selected) else None
                   for key in fields},
            }
        results.append(entry)
    return {"all_succeeded": all_success, "cases": results}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--cases", nargs="+", default=["RationalChain4", "CoupledErrors"])
    parser.add_argument("--pairs", type=int, default=3)
    parser.add_argument("--warmups", type=int, default=1)
    parser.add_argument("--timeout", type=float, default=120)
    parser.add_argument("--no-build", action="store_true", help="use an already verified build")
    parser.add_argument("--output", type=Path, default=Path("artifacts/core-profile/results.json"))
    args = parser.parse_args()
    if args.pairs < 1 or args.warmups < 0 or args.timeout <= 0:
        parser.error("pairs and timeout must be positive; warmups must be nonnegative")
    output = args.output if args.output.is_absolute() else ROOT / args.output
    inputs = output.parent / "inputs"
    inputs.mkdir(parents=True, exist_ok=True)
    if not args.no_build:
        build = subprocess.run([args.lake, "build", "NormArith"], cwd=ROOT, text=True, capture_output=True)
        if build.returncode:
            print(build.stdout + build.stderr)
            return build.returncode
    implementation = sorted((ROOT / "NormArith").glob("*.lean"))
    hashes_before = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                     for p in implementation}
    head_before = command_output(["git", "rev-parse", "HEAD"], ROOT)
    samples, captures, sources = [], {}, {}
    with tempfile.TemporaryDirectory(prefix="norm-arith-profile-") as temporary:
        scratch = Path(temporary)
        for case in args.cases:
            original = ROOT / "Benchmarks" / "BackendLP" / f"{case}.lean"
            source = original.read_text()
            _, proof = snippet_parts(source)
            reference = source.replace("set_option norm_arith.forceLP true", "set_option norm_arith.useLP false")
            lp = source.replace("set_option norm_arith.forceLP true", "set_option norm_arith.forceLP true\nset_option trace.norm_arith.profile true")
            capture = lp.replace(proof, proof.replace("norm_arith ", "norm_arith? "))
            capture = capture.replace("set_option maxHeartbeats", "set_option norm_arith.replayText true\nset_option maxHeartbeats")
            capture_file = inputs / f"{case}-capture.lean"
            capture_file.write_text(capture)
            capture_result = compile_sample(args.lake, capture_file, scratch / case / "capture", args.timeout)
            captures[case] = capture_result
            try:
                if not capture_result["success"]:
                    raise ValueError("replay capture compilation failed")
                replay_tactic, metadata = read_replay(capture_result["stdout"])
                captures[case].update(metadata)
            except ValueError as error:
                captures[case]["capture_error"] = str(error)
                replay_tactic = 'fail "replay capture failed"'
            replay = replace_proof(reference, replay_tactic)
            for variant, content in zip(VARIANTS, (reference, lp, replay)):
                path = inputs / f"{case}-{variant}.lean"
                path.write_text(content)
                sources[(case, variant)] = path
        for phase, count in (("warmup", args.warmups), ("measure", args.pairs)):
            for pair in range(count):
                for index, case in enumerate(args.cases):
                    offset = (pair + index) % len(VARIANTS)
                    order = VARIANTS[offset:] + VARIANTS[:offset]
                    for position, variant in enumerate(order):
                        result = compile_sample(args.lake, sources[case, variant],
                                                scratch / phase / str(pair) / case / variant, args.timeout)
                        samples.append({"phase": phase, "pair": pair, "case": case,
                                        "variant": variant, "order": position, **result})
                        print(f"{phase} {pair + 1}/{count} {case} {variant}: "
                              f"{'ok' if result['success'] else 'FAILED'} ({result['seconds']:.3f}s)", flush=True)
    summary = summarize(samples, args.cases)
    hashes_after = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                    for p in implementation}
    if hashes_after != hashes_before:
        summary["all_succeeded"] = False
    report = {
        "schema_version": 1, "created_at": datetime.now(timezone.utc).isoformat(),
        "scope": "Whole compilation in fresh processes. LP traces separate oracle search from proof reconstruction. LP totals include trace and proof-size calculation. Replay includes decoding and kernel checking; it is not isolated kernel time. Peak memory comes from /usr/bin/time and includes imports and process overhead. Failed and timed-out samples remain in this report.",
        "config": {"pairs": args.pairs, "warmups": args.warmups, "cases": args.cases,
                   "timeout_seconds": args.timeout, "build_skipped": args.no_build},
        "platform": platform.platform(), "git_head": head_before,
        "lean": command_output([args.lake, "env", "lean", "--version"], ROOT),
        "source_hashes": hashes_before,
        "source_hashes_after": hashes_after,
        "sources_changed_during_run": hashes_after != hashes_before,
        "captures": captures, "summary": summary, "samples": samples,
    }
    output.write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n")
    print(f"Wrote {output}")
    return 0 if summary["all_succeeded"] and all(c["success"] and "capture_error" not in c for c in captures.values()) else 1


if __name__ == "__main__":
    raise SystemExit(main())
