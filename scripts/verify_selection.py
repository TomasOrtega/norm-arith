#!/usr/bin/env python3
"""Compile a complete selected census patch before freezing it for measurement."""

import argparse
from datetime import datetime, timezone
import difflib
import gzip
import json
import os
from pathlib import Path
import re
import sys

from benchmark import (
    BenchmarkError, capture, dependency_order, fingerprint_inputs, prepare_sources,
    project_lean_sources, require_success, run_process, safe_source_path, sha256,
    edited_source_setups, setup_record_inputs, lean_environment_expression,
    source_setup, validate_compilation, verify_frozen_inputs,
)
from census import CensusError, parse_setup_batch, verify_evidence
from select_census import SelectionError, candidate_from_proposal, render_replacement


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n")


def contained_path(root, relative):
    path = (root / relative).resolve()
    if not path.is_relative_to(root.resolve()):
        raise BenchmarkError(f"census evidence escapes its directory: {relative}")
    return path


def has_norm_arith_token(source):
    code, i = [], 0
    while i < len(source):
        if source.startswith("--", i):
            end = source.find("\n", i)
            i = len(source) if end < 0 else end
            code.append(" ")
        elif source.startswith("/-", i):
            depth, i = 1, i + 2
            while i < len(source) and depth:
                if source.startswith("/-", i):
                    depth, i = depth + 1, i + 2
                elif source.startswith("-/", i):
                    depth, i = depth - 1, i + 2
                else:
                    i += 1
            code.append(" ")
        elif raw := re.match(r'r(#+)?"', source[i:]):
            closing = '"' + (raw[1] or "")
            end = source.find(closing, i + len(raw[0]))
            i = len(source) if end < 0 else end + len(closing)
            code.append(" ")
        elif source[i] in {'"', '«'}:
            closing, escaped = ('"' if source[i] == '"' else '»'), False
            i += 1
            while i < len(source):
                char, i = source[i], i + 1
                if escaped:
                    escaped = False
                elif char == "\\" and closing == '"':
                    escaped = True
                elif char == closing:
                    break
            code.append(" ")
        elif source[i] == "'" and (char := re.match(r"'(?:\\.|[^\\'\n])'", source[i:])):
            i += len(char[0])
            code.append(" ")
        else:
            code.append(source[i])
            i += 1
    return re.search(r"(?<![\w'.])norm_arith(?![\w'])", "".join(code)) is not None


def validate_proof_spans(manifest, mathlib, *, allow_preparation=False):
    specifications = {item["path"]: item for item in manifest["files"]}
    for item in specifications.values():
        if item.get("helpers") or item.get("imports", []) not in ([], ["NormArith"]):
            raise BenchmarkError("source verification accepts the fixed census rule without helper declarations")
    for candidate in manifest["candidates"]:
        if candidate["status"] != "replace":
            continue
        path = candidate["path"]
        source = (mathlib / safe_source_path(path)).read_bytes()
        if sha256(source) != specifications[path]["source_sha256"]:
            raise BenchmarkError(f"source hash mismatch: {path}")
        lines = source.splitlines(keepends=True)
        first, last = candidate["start_line"], candidate["end_line"]
        if not isinstance(first, int) or not isinstance(last, int) or not 1 <= first <= last <= len(lines):
            raise BenchmarkError(f"invalid proof line span: {candidate['id']}")
        left = sum(len(line) for line in lines[:first - 1])
        right = sum(len(line) for line in lines[:last])
        start, end = candidate.get("source_start_byte"), candidate.get("source_end_byte")
        if not isinstance(start, int) or not isinstance(end, int) or not left <= start < end <= right:
            raise BenchmarkError(f"invalid recorded proof byte span: {candidate['id']}")
        body_start, body_end = candidate.get("body_start_byte"), candidate.get("body_end_byte")
        if not isinstance(body_start, int) or not isinstance(body_end, int) or not (
                0 <= body_start <= start < end <= body_end <= len(source)):
            raise BenchmarkError(f"selected edit is outside the declaration proof body: {candidate['id']}")
        if allow_preparation:
            if candidate.get("manual_review") is not True:
                raise BenchmarkError(f"prepared proof requires manual_review=true: {candidate['id']}")
            proof = candidate.get("proof_replacement")
            if not isinstance(proof, str) or not proof.strip():
                raise BenchmarkError(f"prepared proof requires an explicit proof_replacement string: {candidate['id']}")
            if not has_norm_arith_token(proof):
                raise BenchmarkError(f"prepared proof requires a norm_arith token outside comments and literals: {candidate['id']}")
            if any(len(line) > 100 for line in candidate["replacement"].splitlines()):
                raise BenchmarkError(f"prepared replacement exceeds 100 Unicode characters on a line: {candidate['id']}")
            expected = [(source[left:start] + proof.encode() + source[end:right]).decode()]
        else:
            expected = []
            for token in ["norm_arith", "by norm_arith"]:
                try:
                    expected.append(render_replacement(source[left:start], token, source[end:right]))
                except SelectionError:
                    continue
        if candidate["replacement"] not in expected:
            raise BenchmarkError(f"replacement changes source outside the recorded proof span: {candidate['id']}")


def validate_body_censuses(censuses, manifest, mathlib):
    selected = [item for item in manifest["candidates"] if item["status"] == "replace"]
    specifications = {item["path"]: item for item in manifest["files"]}
    fingerprints, records, matched = {}, [], set()
    for census in dict.fromkeys(path.resolve() for path in censuses):
        manifest_path = census / "manifest.json"
        manifest_bytes = manifest_path.read_bytes()
        evidence_manifest = json.loads(manifest_bytes)
        if evidence_manifest.get("mathlib_revision") != manifest["mathlib_revision"]:
            raise BenchmarkError(f"body census uses a different mathlib revision: {census}")
        merge_fingerprints(fingerprints, {str(manifest_path): sha256(manifest_bytes)})
        inventory = {item["path"]: item["sha256"] for item in evidence_manifest["files"]}
        for path in dict.fromkeys(item["path"] for item in selected if item["id"] not in matched):
            if path not in inventory:
                continue
            source = (mathlib / safe_source_path(path)).read_bytes()
            expected_source = specifications[path]["source_sha256"]
            if inventory[path] != expected_source or sha256(source) != expected_source:
                raise BenchmarkError(f"body census source hash mismatch: {path}")
            module = path[:-5].replace("/", ".")
            result_path = census / "files" / module / "result.json"
            if not result_path.exists():
                continue
            result_bytes = result_path.read_bytes()
            result = json.loads(result_bytes)
            if not result.get("complete") or result.get("status") != "complete":
                continue
            if (result.get("path"), result.get("module"), result.get("source_sha256")) != (path, module, expected_source):
                raise BenchmarkError(f"completed body census file metadata differs from its source: {path}")
            verify_evidence(census, result)
            events = contained_path(census, result["directory"]) / "events.jsonl"
            relative_events = str(events.relative_to(census))
            if relative_events not in result["evidence_sha256"]:
                raise BenchmarkError(f"body census original observation ledger has no evidence hash: {path}")
            observations = [json.loads(line) for line in events.read_text().splitlines() if line.strip()]
            observations = [row for row in observations if row.get("type") == "observation" and row.get("phase") == "original"]
            merge_fingerprints(fingerprints, {str(result_path): sha256(result_bytes)})
            merge_fingerprints(fingerprints, {str(contained_path(census, name)): digest
                                             for name, digest in result["evidence_sha256"].items()})
            for candidate in selected:
                if candidate["path"] != path or candidate["id"] in matched:
                    continue
                parent = candidate.get("parent_declaration", candidate.get("declaration"))
                if not isinstance(parent, str) or not parent or (
                        candidate.get("declaration") is not None and candidate["declaration"] != parent):
                    raise BenchmarkError(f"reviewed candidate has an inconsistent parent declaration: {candidate['id']}")
                matches = [row for row in observations if (
                    row.get("parent_declaration"), row.get("body_start_byte"), row.get("body_end_byte")) == (
                        parent, candidate.get("body_start_byte"), candidate.get("body_end_byte")) and (
                            not candidate.get("observation_key") or row.get("key") == candidate["observation_key"])]
                if not matches:
                    continue
                observation = matches[0]
                matched.add(candidate["id"])
                records.append({
                    "candidate_id": candidate["id"], "path": path, "parent_declaration": parent,
                    "body_start_byte": candidate["body_start_byte"], "body_end_byte": candidate["body_end_byte"],
                    "source_sha256": expected_source, "census": str(census),
                    "census_protocol_hash": evidence_manifest.get("protocol_hash"),
                    "original_observation_key": observation["key"], "events_path": str(events),
                    "events_sha256": result["evidence_sha256"][relative_events],
                    "result_sha256": sha256(result_bytes), "manifest_sha256": sha256(manifest_bytes),
                    "role": "original_source_body_evidence_only_not_a_checked_replacement_proposal",
                })
    missing = [item["id"] for item in selected if item["id"] not in matched]
    if missing:
        raise BenchmarkError(f"no completed original observation body evidence for selected edits: {', '.join(missing)}")
    verify_frozen_inputs(fingerprints)
    return fingerprints, records


def load_census_setups(census, manifest, paths):
    specifications = {item["path"]: item for item in manifest["files"]}
    setups, fingerprints = {}, fingerprint_inputs([census / "manifest.json"])
    for path in paths:
        module = path[:-5].replace("/", ".")
        result_path = census / "files" / module / "result.json"
        result_bytes = result_path.read_bytes()
        result = json.loads(result_bytes)
        fingerprints[str(result_path.resolve())] = sha256(result_bytes)
        if not result.get("complete") or result.get("path") != path or result.get("module") != module:
            raise BenchmarkError(f"census has no complete latest result for {path}")
        if result.get("source_sha256") != specifications[path]["source_sha256"]:
            raise BenchmarkError(f"census source hash mismatch: {path}")
        if result.get("evidence_sha256"):
            verify_evidence(census, result)
            fingerprints.update({str(contained_path(census, name)): digest
                                 for name, digest in result["evidence_sha256"].items()})
        cached = census / "setups" / f"{module}.json.gz"
        if not cached.exists():
            cached = contained_path(census, result["directory"]) / "setup.json.gz"
        if cached.exists():
            raw = cached.read_bytes()
            data = gzip.decompress(raw)
        else:
            cached = contained_path(census, result["directory"]) / "setup.json"
            raw = data = cached.read_bytes()
        if sha256(data) != result.get("setup_sha256"):
            raise BenchmarkError(f"census setup hash mismatch: {path}")
        setup = json.loads(data)
        if not isinstance(setup, dict) or setup.get("name") != module:
            raise BenchmarkError(f"census setup module mismatch: {path}")
        setups[path] = setup
        merge_fingerprints(fingerprints, {str(cached.resolve()): sha256(raw)})
    verify_frozen_inputs(fingerprints)
    return setups, fingerprints


def validate_census_candidates(census, manifest, mathlib):
    fingerprints = {}
    for path in dict.fromkeys(item["path"] for item in manifest["candidates"] if item["status"] == "replace"):
        result_path = census / "files" / path[:-5].replace("/", ".") / "result.json"
        result_bytes = result_path.read_bytes()
        result = json.loads(result_bytes)
        proposal_path = contained_path(census, result["proposal_file"])
        proposal_bytes = proposal_path.read_bytes()
        proposals = [json.loads(line) for line in proposal_bytes.decode().splitlines() if line.strip()]
        source = (mathlib / path).read_bytes()
        for item in manifest["candidates"]:
            if item["path"] != path or item["status"] != "replace":
                continue
            matches = [proposal for proposal in proposals if proposal.get("key") == item["observation_key"]]
            if len(matches) != 1:
                raise BenchmarkError(f"selected candidate has no unique census proof: {item['id']}")
            expected = candidate_from_proposal(matches[0], source)
            fields = ["id", "path", "start_line", "end_line", "original_sha256", "replacement",
                      "source_start_byte", "source_end_byte", "body_start_byte", "body_end_byte", "observation_key"]
            if any(expected[field] != item[field] for field in fields):
                raise BenchmarkError(f"selected candidate differs from its checked census proposal: {item['id']}")
        fingerprints.update({str(result_path.resolve()): sha256(result_bytes),
                             str(proposal_path.resolve()): sha256(proposal_bytes)})
    return fingerprints


def merge_fingerprints(fingerprints, incoming):
    for name, digest in incoming.items():
        if name in fingerprints and fingerprints[name] != digest:
            raise BenchmarkError(f"input changed while loading source verification evidence: {name}")
        fingerprints[name] = digest


def long_line_diagnostics(result):
    diagnostics = []
    for name in ["stdout.log", "stderr.log"]:
        for line in (Path(result["log_dir"]) / name).read_text().splitlines():
            try:
                message = json.loads(line)
            except json.JSONDecodeError:
                continue
            if isinstance(message, dict) and message.get("kind") == "linter.style.longLine":
                diagnostics.append(dict(message, log_stream=name))
    return diagnostics


def compile_selected(prepared, setups, candidates, *, project, output, lean, environment, threads, timeout):
    originals = {source["path"]: sha256(source["original"]) for source in prepared}
    if len(originals) != len(prepared) or set(originals) != set(setups):
        raise BenchmarkError("selected sources and module setups do not match exactly")
    artifacts = output / "artifacts"
    if artifacts.exists():
        raise BenchmarkError(f"refusing to reuse verification outputs: {artifacts}")
    artifacts.mkdir()
    order = dependency_order(setups)
    affected = {path[:-5].replace("/", "."): path for path in order}
    selected_ids = {path: sorted(item["id"] for item in candidates
                                 if item["status"] == "replace" and item["path"] == path) for path in order}
    compiled, failed, rows, excluded = {}, set(), [], {}
    for path in order:
        setup = setups[path]
        source = output / "sources" / path
        row = {"path": path, "candidate_ids": selected_ids[path],
               "original_source_sha256": originals[path],
               "replacement_source_sha256": sha256(source.read_bytes())}
        blocked = sorted(affected[module] for module in setup.get("importArts", {}) if module in failed)
        if blocked:
            row.update(status="blocked_dependency", blocked_by=blocked,
                       reason="an affected dependency failed source verification")
            failed.add(setup["name"])
            rows.append(row)
            continue
        if setup.get("options", {}).get("compiler.postponeCompile", False):
            raise BenchmarkError(f"compiler.postponeCompile requires a separate leanir verifier: {path}")
        stem = artifacts / path[:-5]
        stem.parent.mkdir(parents=True, exist_ok=True)
        outputs = [Path(str(stem) + suffix) for suffix in [".olean", ".ilean", ".c"]]
        if setup.get("isModule"):
            outputs.extend(Path(str(stem) + suffix) for suffix in [".olean.server", ".olean.private", ".ir", ".ir.sig"])
        resolved = source_setup(setup, compiled)
        setup_path = output / "resolved-setups" / (path[:-5] + ".setup.json")
        setup_path.parent.mkdir(parents=True, exist_ok=True)
        write_json(setup_path, resolved)
        command = [lean, str(source), "-R", str(output / "sources"), "--setup", str(setup_path),
                   "-o", str(outputs[0]), "-i", str(outputs[1]), "-c", str(outputs[2]), "--json", "-j", str(threads)]
        result = run_process(command, project, output / "logs" / path[:-5], timeout, env=environment)
        row.update(process=result, setup_sha256=sha256(setup_path.read_bytes()),
                   style_diagnostics=long_line_diagnostics(result))
        try:
            validate_compilation(result, outputs)
            if row["style_diagnostics"]:
                raise BenchmarkError(f"selected source has linter.style.longLine diagnostics; logs: {result['log_dir']}")
            compiled[setup["name"]] = [[str(outputs[0])]]
            if setup.get("isModule"):
                compiled[setup["name"]] = [[str(outputs[0]), str(outputs[3]), str(outputs[4])],
                                            [str(outputs[6]), str(outputs[5])]]
            row.update(status="verified", artifact_sha256=fingerprint_inputs(outputs))
        except BenchmarkError as error:
            row.update(status="failed", reason=str(error))
            failed.add(setup["name"])
            reason = (f"combined_source_compile_failure: {path}; source_sha256={originals[path]}; "
                      f"replacement_sha256={row['replacement_source_sha256']}; "
                      f"selected ids rejected as one file-level set: {','.join(selected_ids[path])}; {error}")
            excluded.update({identifier: reason for identifier in selected_ids[path]})
        rows.append(row)
        print(f"{path}: {row['status']}", flush=True)
    return rows, excluded


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__, epilog=(
        "Failed files reject their selected edits as a set. Feed exclusions.json to "
        "select_census.py --exclude, then verify the reselected patch in a new output directory. "
        "Only complete success writes manifest.json; it remains a source-verified trial."))
    parser.add_argument("manifest", type=Path)
    parser.add_argument("--project", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--mathlib", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--census", type=Path, help="reuse hash-checked setups and checked proposal records from this census")
    parser.add_argument("--allow-preparation", action="store_true", help="accept explicitly reviewed proof replacements with counted preparation")
    parser.add_argument("--body-census", type=Path, action="append", default=[], help="source-bound original body observations for reviewed replacements; repeatable")
    parser.add_argument("--threads", type=int, default=1)
    parser.add_argument("--timeout", type=float, default=600)
    parser.add_argument("--setup-batch-size", type=int, default=256)
    parser.add_argument("--lake", default="lake")
    args = parser.parse_args(argv)
    if args.threads < 1 or args.timeout <= 0 or args.setup_batch_size < 1:
        parser.error("threads, timeout and setup-batch-size must be positive")
    if args.census and (args.allow_preparation or args.body_census):
        parser.error("--census checked-proposal mode cannot use preparation or body-census flags")
    if args.allow_preparation != bool(args.body_census):
        parser.error("--allow-preparation and at least one --body-census must be used together")
    args.project, args.output = args.project.resolve(), args.output.resolve()
    args.mathlib = (args.mathlib or args.project / ".lake/packages/mathlib").resolve()
    args.census = args.census.resolve() if args.census else None
    if args.output.exists() and any(args.output.iterdir()):
        parser.error("output directory must be empty")
    args.output.mkdir(parents=True, exist_ok=True)
    report = {"schema_version": 1, "status": "running", "created_at_utc": datetime.now(timezone.utc).isoformat(),
              "selection_basis": "proof correctness and deterministic net lines only; durations never select candidates",
              "setup": [], "files": []}
    try:
        data = args.manifest.read_bytes()
        manifest = json.loads(data)
        revision = capture(["git", "rev-parse", "HEAD"], args.mathlib)
        if revision != manifest["mathlib_revision"]:
            raise BenchmarkError("mathlib checkout does not match selection revision")
        if capture(["git", "status", "--porcelain", "--untracked-files=no"], args.mathlib):
            raise BenchmarkError("mathlib tracked sources must be unmodified")
        if (args.project / ".lake/packages/mathlib").resolve() != args.mathlib:
            raise BenchmarkError("mathlib must be the project's resolved dependency")
        prepared, report["accounting"] = prepare_sources(manifest, args.mathlib)
        if not prepared:
            raise BenchmarkError("selection contains no replacement files")
        validate_proof_spans(manifest, args.mathlib, allow_preparation=args.allow_preparation)
        report.update(mathlib_revision=revision, input_manifest_sha256=sha256(data))
        (args.output / "input-manifest.json").write_bytes(data)
        patch = []
        for source in prepared:
            destination = args.output / "sources" / source["path"]
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_text(source["replacement"])
            patch.extend(difflib.unified_diff(source["original"].splitlines(keepends=True),
                                             source["replacement"].splitlines(keepends=True),
                                             fromfile="a/" + source["path"], tofile="b/" + source["path"]))
        (args.output / "mathlib.patch").write_text("".join(patch))
        report["patch_sha256"] = sha256("".join(patch))
        paths = [source["path"] for source in prepared]
        inputs = [args.manifest, args.output / "input-manifest.json", args.output / "mathlib.patch",
                  *[args.mathlib / item["path"] for item in manifest["files"]],
                  *[args.output / "sources" / path for path in paths], *project_lean_sources(args.project),
                  args.project / "lean-toolchain", args.project / "lakefile.toml", args.project / "lake-manifest.json",
                  Path(__file__), Path(__file__).with_name("benchmark.py"), Path(__file__).with_name("census.py"),
                  Path(__file__).with_name("select_census.py")]
        fingerprints = fingerprint_inputs(inputs)
        if args.allow_preparation:
            body_inputs, report["body_census_evidence"] = validate_body_censuses(args.body_census, manifest, args.mathlib)
            merge_fingerprints(fingerprints, body_inputs)
            report["proof_span_policy"] = "manually_reviewed_exact_proof_replacement_with_source_bound_original_body_evidence"
        else:
            report["proof_span_policy"] = "fixed_bare_norm_arith_checked_source_span"
        expected = {str(args.manifest.resolve()): sha256(data),
                    str(args.output / "input-manifest.json"): sha256(data),
                    str(args.output / "mathlib.patch"): report["patch_sha256"]}
        expected.update({str(args.mathlib / item["path"]): item["source_sha256"] for item in manifest["files"]})
        expected.update({str(args.output / "sources" / item["path"]): sha256(item["replacement"]) for item in prepared})
        merge_fingerprints(fingerprints, expected)
        report["project_lean_sources"] = {str(path.relative_to(args.project)): sha256(path.read_bytes())
                                          for path in project_lean_sources(args.project)}

        def check_inputs():
            verify_frozen_inputs(fingerprints)
            actual = {str(path.relative_to(args.project)): sha256(path.read_bytes())
                      for path in project_lean_sources(args.project)}
            if actual != report["project_lean_sources"]:
                raise BenchmarkError("project source inventory changed during source verification")

        def setup_command(label, command):
            result = run_process(command, args.project, args.output / "setup" / label, args.timeout)
            report["setup"].append({"label": label, **result})
            require_success(result)
            return (Path(result["log_dir"]) / "stdout.log").read_text()

        setups = {}
        if args.census:
            census_manifest_bytes = (args.census / "manifest.json").read_bytes()
            census_manifest = json.loads(census_manifest_bytes)
            if manifest.get("census_protocol_hash") != census_manifest.get("protocol_hash"):
                raise BenchmarkError("selection and census protocol hashes differ")
            if census_manifest.get("mathlib_revision") != revision:
                raise BenchmarkError("selection and census source revisions differ")
            if Path(census_manifest.get("project", "")).resolve() != args.project or Path(
                    census_manifest.get("mathlib", "")).resolve() != args.mathlib:
                raise BenchmarkError("census setups belong to different project or mathlib paths")
            merge_fingerprints(fingerprints, {str(args.census / "manifest.json"): sha256(census_manifest_bytes)})
            setups, evidence = load_census_setups(args.census, manifest, paths)
            merge_fingerprints(fingerprints, evidence)
            merge_fingerprints(fingerprints, validate_census_candidates(args.census, manifest, args.mathlib))
        check_inputs()
        setup_command("tactic-up-to-date", [args.lake, "--no-build", "build", "NormArith"])
        script = ("import json,os,subprocess; print(json.dumps({"
                  f"'environment':{lean_environment_expression()},"
                  "'prefix':subprocess.check_output(['lean','--print-prefix'],text=True).strip(),"
                  "'version':subprocess.check_output(['lean','--version'],text=True).strip()}))")
        details = json.loads(setup_command("lean-environment", [args.lake, "env", sys.executable, "-c", script]))
        environment = dict(os.environ, **details["environment"])
        environment["LEAN_NUM_THREADS"] = str(args.threads)
        lean = str(Path(details["prefix"]) / "bin/lean")
        report.update(lean_version=details["version"], threads=args.threads)
        if args.census and census_manifest.get("lean_version") != details["version"]:
            raise BenchmarkError("census setups use a different Lean toolchain version")
        missing = [path for path in paths if path not in setups]
        queries = [(path, "@mathlib/+" + path[:-5].replace("/", ".")) for path in missing]
        for start in range(0, len(queries), args.setup_batch_size):
            batch = queries[start:start + args.setup_batch_size]
            modules = [query.split("+")[-1] for _, query in batch]
            text = setup_command(f"module-batch-{start:06d}",
                                 [args.lake, "--no-build", "-q", "-J", "query", *[query + ":setup" for _, query in batch]])
            for (path, _), setup in zip(batch, parse_setup_batch(text, modules)):
                setups[path] = setup
        patched, records = edited_source_setups(
            {path: args.output / "sources" / path for path in paths}, mathlib=args.mathlib,
            lean=lean, lake=args.lake, command=setup_command,
            output=args.output / "edited-setups", label="replacement", build_setups=setups,
        )
        report["source_header_setups"] = {"replacement": records}
        merge_fingerprints(fingerprints, fingerprint_inputs(setup_record_inputs(records, args.project, include_imports=True)))
        setup_dir = args.output / "input-setups"
        setup_dir.mkdir()
        for path, setup in setups.items():
            destination = setup_dir / (path[:-5].replace("/", ".") + ".json")
            write_json(destination, setup)
            fingerprints.update(fingerprint_inputs([destination]))
        setups = patched
        report["input_sha256"] = fingerprints
        write_json(args.output / "verification.json", report)
        check_inputs()
        report["files"], exclusions = compile_selected(
            prepared, setups, manifest["candidates"], project=args.project, output=args.output,
            lean=lean, environment=environment, threads=args.threads, timeout=args.timeout,
        )
        specifications = {item["path"]: item for item in manifest["files"]}
        for row in report["files"]:
            row["original_source_sha256"] = specifications[row["path"]]["source_sha256"]
        write_json(args.output / "exclusions.json", exclusions)
        check_inputs()
        if capture(["git", "rev-parse", "HEAD"], args.mathlib) != revision or capture(
                ["git", "status", "--porcelain", "--untracked-files=no"], args.mathlib):
            raise BenchmarkError("mathlib checkout changed during source verification")
        if not all(row["status"] == "verified" for row in report["files"]):
            report.update(status="failed", error="combined source patch failed; reselect with exclusions.json and verify again")
        else:
            final = dict(manifest, selection_status="source-verified-trial", source_verification={
                "path": str(args.output / "verification.json"), "input_manifest_sha256": sha256(data),
                "patch_sha256": report["patch_sha256"],
            })
            write_json(args.output / "manifest.json", final)
            report.update(status="complete", final_manifest_sha256=sha256((args.output / "manifest.json").read_bytes()),
                          evidence_stage="combined_source_patch_kernel_checked_with_fresh_outputs")
        write_json(args.output / "verification.json", report)
        print(args.output / "verification.json")
        return 0 if report["status"] == "complete" else 1
    except (BenchmarkError, CensusError, SelectionError, OSError, ValueError, KeyError, TypeError) as error:
        report.update(status="failed", error=str(error))
        write_json(args.output / "verification.json", report)
        print(f"source verification failed: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
