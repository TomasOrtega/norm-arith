#!/usr/bin/env python3
"""Compile paired, standalone Lean snippets and report measured costs.

This is a small extracted-snippet workload, not a mathlib census. Each invocation
of Lean gets a new output directory. Imports are warmed before recorded pairs;
both compilation order and all measured samples are retained in the report.
"""

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
import sys
import tempfile
import time
from datetime import datetime, timezone
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
VARIANTS = ("Baseline", "Tactic")
MARKERS = ("BENCHMARK-STATEMENT", "BENCHMARK-PROOF", "BENCHMARK-END")


def strip_comments(source: str) -> str:
    """Remove Lean comments, retaining newlines, nested blocks, and strings."""
    out: list[str] = []
    i, depth = 0, 0
    mode = "code"
    while i < len(source):
        ch = source[i]
        pair = source[i : i + 2]
        if mode == "line":
            out.append("\n" if ch == "\n" else " ")
            if ch == "\n":
                mode = "code"
            i += 1
        elif mode == "block":
            if pair == "/-":
                depth += 1
                out.extend("  ")
                i += 2
            elif pair == "-/":
                depth -= 1
                out.extend("  ")
                i += 2
                if depth == 0:
                    mode = "code"
            else:
                out.append("\n" if ch == "\n" else " ")
                i += 1
        elif mode == "string":
            out.append(ch)
            i += 1
            if ch == "\\" and i < len(source):
                out.append(source[i])
                i += 1
            elif ch == '"':
                mode = "code"
        elif pair in ("--", "/-"):
            mode = "line" if pair == "--" else "block"
            depth = 1 if mode == "block" else 0
            out.extend("  ")
            i += 2
        else:
            out.append(ch)
            if ch == '"':
                mode = "string"
            i += 1
    if mode in ("block", "string"):
        raise ValueError(f"unterminated Lean {mode}")
    return "".join(out)


def code_lines(source: str) -> int:
    return sum(bool(line.strip()) for line in strip_comments(source).splitlines())


def snippet_parts(source: str) -> tuple[str, str]:
    matches = [
        list(re.finditer(r"(?m)^\s*-- " + marker + r"\s*$", source))
        for marker in MARKERS
    ]
    if any(len(items) != 1 for items in matches):
        raise ValueError("each snippet must contain each BENCHMARK marker exactly once")
    start, proof, end = (items[0] for items in matches)
    if not start.end() < proof.start() < end.start():
        raise ValueError("benchmark markers are out of order")
    return source[start.end() : proof.start()], source[proof.end() : end.start()]


def inspect_pair(root: Path, case: dict) -> dict:
    metrics: dict = {}
    statements = []
    contexts = []
    for variant in VARIANTS:
        relative = Path(case.get(variant.lower(), f"Benchmarks/{variant}/{case['id']}.lean"))
        source = (root / relative).read_text()
        statement, proof = snippet_parts(source)
        statements.append(" ".join(strip_comments(statement).split()))
        header = source.split("-- BENCHMARK-STATEMENT")[0]
        contexts.append(" ".join(
            line.strip() for line in strip_comments(header).splitlines()
            if not re.match(r"\s*(?:(?:public|meta)\s+)*import\s", line)
            and not re.match(r"\s*set_option norm_arith\.(?:forceLP|useLP) (?:true|false)\s*$", line)
        ))
        tokens = strip_comments(source)
        if re.search(r"\b(?:sorry|admit|axiom)\b", tokens):
            raise ValueError(f"{relative}: unproved declarations are forbidden")
        for name in case.get("forbidden_identifiers", []):
            if re.search(r"(?<![\w'])" + re.escape(name) + r"(?![\w'])", strip_comments(proof)):
                raise ValueError(f"{relative}: proof invokes its source theorem {name}")
        metrics[variant] = {
            "file": relative.as_posix(),
            "sha256": hashlib.sha256(source.encode()).hexdigest(),
            "code_lines": code_lines(source),
            "proof_lines": code_lines(proof),
        }
    if statements[0] != statements[1]:
        raise ValueError(f"{case['id']}: baseline and tactic statements differ")
    if contexts[0].split() != contexts[1].split():
        raise ValueError(f"{case['id']}: baseline and tactic declaration contexts differ")
    metrics["net_code_lines_saved"] = metrics["Baseline"]["code_lines"] - metrics["Tactic"]["code_lines"]
    metrics["proof_lines_saved"] = metrics["Baseline"]["proof_lines"] - metrics["Tactic"]["proof_lines"]
    return metrics


def variant_order(pair: int, case_index: int = 0) -> tuple[str, str]:
    return VARIANTS if (pair + case_index) % 2 == 0 else VARIANTS[::-1]


def compile_one(lake: str, root: Path, source: Path, output: Path, timeout: float) -> dict:
    output.mkdir(parents=True, exist_ok=False)
    olean, ilean = output / "snippet.olean", output / "snippet.ilean"
    command = [lake, "env", "lean", "-DwarningAsError=true", "-o", str(olean), "-i", str(ilean), str(source)]
    started = time.perf_counter()
    with subprocess.Popen(command, cwd=root, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                          text=True, start_new_session=(os.name == "posix")) as proc:
        timed_out = False
        try:
            stdout, stderr = proc.communicate(timeout=timeout)
        except subprocess.TimeoutExpired:
            timed_out = True
            if os.name == "posix":
                os.killpg(proc.pid, signal.SIGKILL)
            else:
                proc.kill()
            stdout, stderr = proc.communicate()
        record = {
            "seconds": time.perf_counter() - started,
            "returncode": proc.returncode,
            "stdout": stdout,
            "stderr": stderr,
            "timed_out": timed_out,
        }
    record["output_created"] = olean.is_file() and ilean.is_file()
    record["success"] = record["returncode"] == 0 and record["output_created"]
    return record


def summarize(cases: list[dict], records: list[dict], metrics: dict, pairs: int) -> dict:
    measured = [row for row in records if row["phase"] == "measure"]
    per_case = []
    complete = all(row["success"] for row in records)
    for case in cases:
        entry = {"id": case["id"], "kind": case["kind"], **metrics[case["id"]]}
        times = {}
        for variant in VARIANTS:
            rows = [r for r in measured if r["id"] == case["id"] and r["variant"] == variant]
            if len(rows) != pairs or not all(r["success"] for r in rows):
                complete = False
                times[variant] = None
            else:
                times[variant] = statistics.median(r["seconds"] for r in rows)
        entry["median_seconds"] = times
        entry["median_ratio_baseline_over_tactic"] = (
            times["Baseline"] / times["Tactic"] if all(times.values()) else None
        )
        per_case.append(entry)
    totals = {v: [] for v in VARIANTS}
    if complete:
        for pair in range(pairs):
            for variant in VARIANTS:
                totals[variant].append(sum(
                    r["seconds"] for r in measured
                    if r["pair"] == pair and r["variant"] == variant
                ))
    medians = {v: statistics.median(totals[v]) if totals[v] else None for v in VARIANTS}
    return {
        "all_compilations_succeeded": complete,
        "case_count": len(cases),
        "baseline_code_lines": sum(m["Baseline"]["code_lines"] for m in metrics.values()),
        "tactic_code_lines": sum(m["Tactic"]["code_lines"] for m in metrics.values()),
        "baseline_proof_lines": sum(m["Baseline"]["proof_lines"] for m in metrics.values()),
        "tactic_proof_lines": sum(m["Tactic"]["proof_lines"] for m in metrics.values()),
        "net_code_lines_saved": sum(m["net_code_lines_saved"] for m in metrics.values()),
        "proof_lines_saved": sum(m["proof_lines_saved"] for m in metrics.values()),
        "paired_total_seconds": totals,
        "median_total_seconds": medians,
        "ratio_of_median_totals": medians["Baseline"] / medians["Tactic"] if all(medians.values()) else None,
        "cases": per_case,
    }


def markdown_report(report: dict) -> str:
    result = report["summary"]
    lines = [
        "# Standalone snippet benchmark", "",
        f"Measured at {report['created_at']}. {result['case_count']} paired snippets, "
        f"{report['config']['warmups']} warmup pass(es), {report['config']['pairs']} recorded pairs.", "",
        f"**Workload:** {report['workload']}.", "",
        report["description"], "",
        f"Case definitions: [{report['manifest_link']}]({report['manifest_link']}). "
        "This is not a census, a whole-file compilation study, or a claim about all PDE proofs.", "",
    ]
    if report["show_source_savings"]:
        lines += [
            "## Source size", "",
            "| Metric | Baseline | Tactic | Saved |", "| --- | ---: | ---: | ---: |",
            f"| Proof-body code lines | {result['baseline_proof_lines']} | {result['tactic_proof_lines']} | {result['proof_lines_saved']} |",
            f"| Whole-snippet code lines | {result['baseline_code_lines']} | {result['tactic_code_lines']} | {result['net_code_lines_saved']} |", "",
            "Counts exclude blank and comment-only lines. Proof bodies are delimited in every file. "
            "Whole-snippet counts include imports, statements, and all preparation. "
            "Imports and local preparation are counted in each file.", "",
        ]
    else:
        lines += ["The two variants run the same proof with different solver settings. "
                  "Their line counts are not included in the mathlib proof-savings total.", ""]
    lines += ["## Compilation", ""]
    if result["all_compilations_succeeded"]:
        medians = result["median_total_seconds"]
        lines.append(
            f"Median total time per corpus pass: **{medians['Baseline']:.3f} s baseline**, "
            f"**{medians['Tactic']:.3f} s tactic**. Their ratio is "
            f"**{result['ratio_of_median_totals']:.3f}×** (baseline/tactic; above one favors the tactic)."
        )
    else:
        lines.append("**At least one compilation failed or timed out. No aggregate runtime ratio is reported.**")
    lines += [
        "", "Each sample launches `lake env lean -DwarningAsError=true` with fresh `.olean` and `.ilean` outputs. "
        "Recorded pairs alternate compilation order. Dependencies are already built and imports are warmed. "
        "Times include process startup, imports, tactic execution, checking, and output writing. "
        "They exclude the separately recorded dependency-build/setup step. Background machine load is uncontrolled. "
        "These descriptive medians do not establish statistical significance.", "",
        "| Snippet | Kind | Proof lines (old → new) | Net code saved | Baseline median (s) | Tactic median (s) | Ratio |",
        "| --- | --- | ---: | ---: | ---: | ---: | ---: |",
    ]
    for case in result["cases"]:
        times = case["median_seconds"]
        old = f"{times['Baseline']:.3f}" if times["Baseline"] is not None else "failed"
        new = f"{times['Tactic']:.3f}" if times["Tactic"] is not None else "failed"
        ratio = case["median_ratio_baseline_over_tactic"]
        ratio_text = f"{ratio:.3f}×" if ratio is not None else "—"
        lines.append(
            f"| [{case['id']}]({case['tactic_link']}) | {case['kind']} | "
            f"{case['Baseline']['proof_lines']} → {case['Tactic']['proof_lines']} | "
            f"{case['net_code_lines_saved']} | {old} | {new} | {ratio_text} |"
        )
    lines += ["", f"Raw samples, failures, source hashes, versions, and timing order are retained in "
              f"[{report['result_filename']}]({report['result_filename']}).", ""]
    return "\n".join(lines)


def command_output(args: list[str], root: Path) -> str:
    proc = subprocess.run(args, cwd=root, capture_output=True, text=True, timeout=60)
    return proc.stdout.strip() if proc.returncode == 0 else proc.stderr.strip()


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake", default="lake", help="Lake executable; inherits the current environment")
    parser.add_argument("--manifest", type=Path, default=Path("Benchmarks/manifest.json"))
    parser.add_argument("--pairs", type=int, default=5)
    parser.add_argument("--warmups", type=int, default=1)
    parser.add_argument("--timeout", type=float, default=120)
    parser.add_argument("--only", nargs="+", help="case identifiers")
    parser.add_argument("--check", action="store_true", help="compile both versions once, without writing timing reports")
    parser.add_argument("--no-build", action="store_true", help="skip the initial lake build NormArith (for an already verified build)")
    parser.add_argument("--output", type=Path, help="JSON report; defaults next to the manifest, with a matching .md report")
    args = parser.parse_args(argv)
    if args.pairs < 1 or args.warmups < 0 or args.timeout <= 0:
        parser.error("pairs and timeout must be positive; warmups must be nonnegative")
    manifest_path = args.manifest if args.manifest.is_absolute() else ROOT / args.manifest
    manifest = json.loads(manifest_path.read_text())
    cases = manifest["cases"]
    if args.only:
        unknown = set(args.only) - {case["id"] for case in cases}
        if unknown:
            parser.error(f"unknown case identifiers: {', '.join(sorted(unknown))}")
        cases = [case for case in cases if case["id"] in args.only]
    if not cases:
        parser.error("no cases selected")
    metrics = {case["id"]: inspect_pair(ROOT, case) for case in cases}
    setup = {"skipped": args.no_build}
    if not args.no_build:
        started = time.perf_counter()
        build = subprocess.run([args.lake, "build", "NormArith"], cwd=ROOT, capture_output=True, text=True)
        setup.update(seconds=time.perf_counter() - started, returncode=build.returncode,
                     stdout=build.stdout[-6000:], stderr=build.stderr[-6000:])
        if build.returncode:
            print(build.stdout + build.stderr, file=sys.stderr)
            return 1
        print(f"Dependency setup: {setup['seconds']:.3f}s (excluded from measurements)", flush=True)
    pairs, warmups = (1, 0) if args.check else (args.pairs, args.warmups)
    records: list[dict] = []
    with tempfile.TemporaryDirectory(prefix="norm-arith-snippets-") as scratch:
        for phase, count in (("warmup", warmups), ("measure", pairs)):
            for pair in range(count):
                for index, case in enumerate(cases):
                    for order, variant in enumerate(variant_order(pair, index)):
                        source = Path(metrics[case["id"]][variant]["file"])
                        output = Path(scratch) / phase / str(pair) / case["id"] / variant
                        sample = compile_one(args.lake, ROOT, source, output, args.timeout)
                        sample.update(phase=phase, pair=pair, id=case["id"], variant=variant, order=order)
                        records.append(sample)
                        status = "ok" if sample["success"] else "FAILED"
                        print(f"{phase} {pair + 1}/{count} {case['id']} {variant}: {status} ({sample['seconds']:.3f}s)", flush=True)
                        if not sample["success"]:
                            print(sample["stdout"] + sample["stderr"], file=sys.stderr, flush=True)
        summary = summarize(cases, records, metrics, pairs)
    if args.check:
        print(f"Checked {len(cases)} paired snippets; all succeeded: {summary['all_compilations_succeeded']}")
        return 0 if summary["all_compilations_succeeded"] else 1
    output = args.output
    if output is None:
        name = "results.json" if manifest_path.stem == "manifest" else f"{manifest_path.stem}-results.json"
        output = manifest_path.parent / name
    elif not output.is_absolute():
        output = ROOT / output
    for case in summary["cases"]:
        case["tactic_link"] = os.path.relpath(ROOT / case["Tactic"]["file"], output.parent)
    sources = sorted((ROOT / "NormArith").rglob("*.lean")) + [ROOT / "NormArith.lean"]
    report = {
        "schema_version": 1,
        "created_at": datetime.now(timezone.utc).isoformat(),
        "workload": manifest.get("workload", "selected standalone mathlib-derived snippets"),
        "description": manifest.get("description", ""),
        "show_source_savings": manifest.get("show_source_savings", True),
        "manifest_link": os.path.relpath(manifest_path, output.parent),
        "result_filename": output.name,
        "setup": setup,
        "config": {"pairs": pairs, "warmups": warmups, "timeout_seconds": args.timeout, "lake": args.lake},
        "environment": {
            "platform": platform.platform(), "python": sys.version,
            "cpu_count": os.cpu_count(),
            "lean": command_output([args.lake, "env", "lean", "--version"], ROOT),
            "git_head": command_output(["git", "rev-parse", "HEAD"], ROOT),
            "git_status": command_output(["git", "status", "--porcelain"], ROOT),
            "lean_toolchain": (ROOT / "lean-toolchain").read_text().strip(),
        },
        "manifest_sha256": hashlib.sha256(manifest_path.read_bytes()).hexdigest(),
        "mathlib_commit": manifest.get("mathlib_commit"),
        "implementation_sha256": {p.relative_to(ROOT).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest() for p in sources},
        "summary": summary,
        "samples": records,
    }
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n")
    output.with_suffix(".md").write_text(markdown_report(report))
    print(f"Wrote {output.relative_to(ROOT) if output.is_relative_to(ROOT) else output}")
    return 0 if summary["all_compilations_succeeded"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
