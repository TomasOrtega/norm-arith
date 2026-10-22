#!/usr/bin/env python3
"""Generate paper tables and verbatim snippets from recorded source artifacts."""

import argparse
import hashlib
import json
import math
import re
from pathlib import Path

from evidence import implementation_sha, load_evidence
from plots import generate_plots

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
GENERATED = HERE / "generated"
NAMES = ("hidden", "reverse", "mathlib", "boundary")
EXPANSION_NAMES = (*NAMES, "quantified", "metric")
IMPLEMENTATION_EXCERPTS = (
    {"id": "certificate", "relative_source": "NormArith/Certificate.lean",
     "first_line": 63, "last_line": 75, "first_anchor": "variable [NormedSpace ℝ E]",
     "last_anchor": "  bound_add (bound_smul c hx) (bound_smul d hy)"},
    {"id": "search", "relative_source": "NormArith/Search.lean",
     "first_line": 179, "last_line": 210,
     "first_anchor": "def referenceDecompositions (sources : Array (Array Rat)) (target : Array Rat)",
     "last_anchor": "  return result"},
    {"id": "tactic", "relative_source": "NormArith/Tactic.lean",
     "first_line": 480, "last_line": 512,
     "first_anchor": "private def addConstraint (sources : Array Source) (target : Expr)",
     "last_anchor": "  withMainContext <| Term.elabTermAndSynthesize name none"},
)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def tex(value):
    replacements = {
        "\\": r"\textbackslash{}", "&": r"\&", "%": r"\%", "$": r"\$",
        "#": r"\#", "_": r"\_", "{": r"\{", "}": r"\}",
        "~": r"\textasciitilde{}", "^": r"\textasciicircum{}",
    }
    return "".join(replacements.get(char, char) for char in str(value))


def write(name, content):
    (GENERATED / name).write_text(content.rstrip() + "\n")


def implementation_data(evidence, expected_aggregate, *, excerpt_specs=None):
    root = evidence.get("project_source_root")
    if root is None:
        raise ValueError("validated project source root is required for the implementation appendix")
    root = Path(root).resolve()
    hashes = ((evidence.get("patch") or {}).get("verification") or {}).get("project_lean_sources", {})
    pending, sources = [root / "NormArith.lean"], {}
    while pending:
        path = pending.pop()
        if path in sources:
            continue
        name = str(path.relative_to(root))
        if name not in hashes:
            raise ValueError("implementation source lacks a final verification fingerprint: " + name)
        if not path.is_file() or path.is_symlink() or not path.resolve().is_relative_to(root):
            raise ValueError("missing validated implementation source: " + name)
        data = path.read_bytes()
        if hashlib.sha256(data).hexdigest() != hashes[name]:
            raise ValueError("measured implementation source hash differs: " + name)
        sources[path] = data
        imports = re.findall(r"(?m)^\s*(?:(?:public|meta)\s+)*import\s+(NormArith(?:\.[\w']+)*)\s*$", data.decode())
        pending.extend(root / (module.replace(".", "/") + ".lean") for module in imports)
    aggregate = hashlib.sha256()
    for path, data in sorted(sources.items()):
        aggregate.update(str(path.relative_to(root)).encode() + b"\0" + data)
    if aggregate.hexdigest() != expected_aggregate:
        raise ValueError("measured implementation aggregate hash differs from checked examples")
    relative_sources = {path.relative_to(root).as_posix(): data for path, data in sources.items()}
    if excerpt_specs is None:
        known_modules = {"NormArith.lean", "NormArith/Certificate.lean", "NormArith/Search.lean",
                         "NormArith/Metric.lean", "NormArith/Tactic.lean"}
        if relative_sources.keys() == known_modules:
            excerpt_specs = IMPLEMENTATION_EXCERPTS
        elif relative_sources.keys() == {"NormArith.lean"}:
            excerpt_specs = ()
        else:
            raise ValueError("implementation import closure needs an explicit excerpt plan")
    excerpts, ids = [], set()
    for specification in excerpt_specs:
        identifier, relative = specification["id"], specification["relative_source"]
        if not re.fullmatch(r"[a-z][a-z0-9-]*", identifier) or identifier in ids:
            raise ValueError("invalid or duplicate implementation excerpt id")
        ids.add(identifier)
        if relative not in relative_sources:
            raise ValueError("implementation excerpt is not a validated runtime source: " + relative)
        lines = relative_sources[relative].splitlines(keepends=True)
        first, last = specification["first_line"], specification["last_line"]
        if type(first) is not int or type(last) is not int or not 1 <= first <= last <= len(lines):
            raise ValueError("invalid implementation excerpt range: " + identifier)
        if (lines[first - 1].decode().rstrip("\r\n") != specification["first_anchor"] or
                lines[last - 1].decode().rstrip("\r\n") != specification["last_anchor"]):
            raise ValueError("implementation excerpt boundary anchor differs: " + identifier)
        excerpt = b"".join(lines[first - 1:last])
        excerpts.append({**specification, "module": relative[:-5].replace("/", "."),
                         "generated_path": "implementation/" + relative,
                         "wrapper": "implementation-" + identifier + ".tex",
                         "source_sha256": hashes[relative],
                         "excerpt_sha256": hashlib.sha256(excerpt).hexdigest(),
                         "bytes": len(excerpt), "lines": last - first + 1})
    modules = []
    for path, data in sorted(sources.items()):
        relative = path.relative_to(root).as_posix()
        generated = "implementation/" + relative
        destination = GENERATED / generated
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes(data)
        modules.append({"module": relative[:-5].replace("/", "."), "relative_source": relative,
                        "generated_path": generated,
                        "sha256": hashlib.sha256(data).hexdigest(), "bytes": len(data),
                        "lines": len(data.splitlines())})
    for alias in ("certificate", "search", "metric", "tactic", "entry"):
        (GENERATED / ("implementation-" + alias + ".tex")).unlink(missing_ok=True)
    for excerpt in excerpts:
        first, last = excerpt["first_line"], excerpt["last_line"]
        write(excerpt["wrapper"], rf"\VerbatimInput[firstline={first},lastline={last},firstnumber={first}]" +
              "{generated/" + excerpt["generated_path"] + "}")
    manifest = {"schema_version": 1, "entrypoint": "NormArith.lean",
                "source_role": "measured_runtime_import_closure",
                "implementation_sha256": aggregate.hexdigest(), "modules": modules, "excerpts": excerpts}
    write("implementation.json", json.dumps(manifest, indent=2))
    return manifest


def marked_blocks(source):
    blocks = {}
    current = None
    lines = source.splitlines(keepends=True)
    for number, line in enumerate(lines, 1):
        match = re.fullmatch(r"\s*-- paper:begin ([a-z-]+)\s*\n?", line)
        if match:
            if current is not None:
                raise ValueError("nested paper snippet markers")
            current = (match[1], number + 1, [])
            continue
        match = re.fullmatch(r"\s*-- paper:end ([a-z-]+)\s*\n?", line)
        if match:
            if current is None or current[0] != match[1]:
                raise ValueError("unmatched paper snippet end")
            name, first, contents = current
            if name in blocks:
                raise ValueError(f"duplicate paper snippet {name}")
            blocks[name] = {"text": "".join(contents), "start_line": first, "end_line": number - 1}
            current = None
            continue
        if current is not None:
            current[2].append(line)
    if current is not None:
        raise ValueError("unclosed paper snippet marker")
    return blocks


def example_data(draft, inputs=None, required_names=NAMES):
    source = inputs["examples_source"] if inputs else ROOT / "NormArithTest/Paper.lean"
    check_path = inputs["examples_check"] if inputs else HERE / "output/lean-check.json"
    program_hash = inputs["implementation_sha256"] if inputs else implementation_sha()
    blocks = marked_blocks(source.read_text()) if source.exists() else {}
    check = json.loads(check_path.read_text()) if check_path.exists() else {}
    checked = (source.exists() and check.get("source_sha256") == sha(source)
               and check.get("implementation_sha256") == program_hash and check.get("returncode") == 0)
    if not draft and (not checked or any(name not in blocks for name in required_names)):
        raise ValueError("all required marked examples need a successful current Lean check; run paper/build.py")
    manifest = {"source": "NormArithTest/Paper.lean", "source_sha256": sha(source) if source.exists() else None,
                "implementation_sha256": program_hash,
                "checked": checked, "snippets": {}}
    for name in required_names:
        block = blocks.get(name)
        if block is None:
            write(name + ".tex", r"\begin{quote}\small\textbf{Draft status:} " +
                  tex(name) + r" example has not yet been imported from its checked source.\end{quote}")
            manifest["snippets"][name] = {"status": "missing"}
        else:
            write(name + ".lean", block["text"])
            write(name + ".tex", r"\VerbatimInput{generated/" + name + ".lean}")
            manifest["snippets"][name] = {
                "status": "checked" if checked else "source-present-unchecked",
                "start_line": block["start_line"], "end_line": block["end_line"],
                "sha256": hashlib.sha256(block["text"].encode()).hexdigest(),
            }
    write("examples.json", json.dumps(manifest, indent=2))
    message = ("The build compiled the source module before it imported all marked blocks."
               if checked and all(name in blocks for name in required_names) else
               "Draft status: the marked example source check is incomplete. No missing block is a verified Lean example.")
    if inputs and checked:
        message = "The release records a successful source compilation for all marked blocks. This build checked their saved hashes."
    write("example-status.tex", tex(message))
    return manifest


def community_request_data(evidence):
    root = evidence.get("project_source_root")
    if root is None:
        raise ValueError("validated project source root is required for the community request")
    root = Path(root).resolve()
    relative = "NormArithTest/Tactic.lean"
    path = root / relative
    hashes = ((evidence.get("patch") or {}).get("verification") or {}).get("project_lean_sources", {})
    if relative not in hashes:
        raise ValueError("community request source lacks a final verification fingerprint")
    if not path.is_file() or path.is_symlink() or not path.resolve().is_relative_to(root):
        raise ValueError("missing validated community request source")
    data = path.read_bytes()
    if hashlib.sha256(data).hexdigest() != hashes[relative]:
        raise ValueError("community request source hash differs")
    expected = (
        "-- The 2020 motivating example: 2a + b = 3a + (b - a).",
        "example (a b : E) : ‖(2 : ℝ) • a + b‖ ≤ 3 * ‖a‖ + ‖b - a‖ := by",
        "  norm_arith [le_refl ‖a‖, le_refl ‖b - a‖]",
    )
    lines = data.splitlines(keepends=True)
    text = [line.decode().rstrip("\r\n") for line in lines]
    starts = [index for index, line in enumerate(text) if line == expected[0]]
    if len(starts) != 1 or tuple(text[starts[0]:starts[0] + len(expected)]) != expected:
        raise ValueError("community request source anchor or body differs")
    start = starts[0]
    snippet = b"".join(lines[start:start + len(expected)])
    (GENERATED / "community-request.lean").write_bytes(snippet)
    write("community-request.tex", r"\VerbatimInput{generated/community-request.lean}")
    return {"source": relative, "source_sha256": hashes[relative],
            "start_line": start + 1, "end_line": start + len(expected),
            "sha256": hashlib.sha256(snippet).hexdigest(),
            "generated_path": "community-request.lean", "wrapper": "community-request.tex"}


def source_example_data(inputs=None):
    path = inputs["pilot_manifest"] if inputs else ROOT / "benchmarks/results/manifest.json"
    manifest = json.loads(path.read_text())
    candidate = next(c for c in manifest["candidates"] if c["id"] == "fderiv-telescope")
    source_path = inputs["pilot_source"] if inputs else ROOT / ".lake/packages/mathlib" / candidate["path"]
    if source_path.exists():
        original = "".join(source_path.read_text().splitlines(keepends=True)[candidate["start_line"] - 1:candidate["end_line"]])
        if hashlib.sha256(original.encode()).hexdigest() != candidate["original_sha256"]:
            raise ValueError("pinned original mathlib source block has drifted")
    else:
        raise ValueError("the pinned mathlib checkout is needed to extract the original source block")
    write("mathlib-original.lean", original)
    write("mathlib-replacement.lean", candidate["replacement"])
    return {"manifest": str(path), "manifest_sha256": sha(path), "candidate_id": candidate["id"],
            "source": str(source_path), "source_sha256": sha(source_path),
            "original_sha256": candidate["original_sha256"],
            "replacement_sha256": hashlib.sha256(candidate["replacement"].encode()).hexdigest()}


def table(name, caption, headings, rows, *, long=False):
    if not rows:
        write(name, "")
        return
    if long:
        columns = r"p{0.63\linewidth}rrr"
        start = r"\begin{longtable}{" + columns + "}\n" + r"\caption{" + caption + r"}\\\toprule" + "\n"
        start = "{\\small\n" + start
        end = r"\bottomrule\end{longtable}}"
    else:
        start = r"\begin{table}[!htbp]\centering\small" + "\n" + r"\caption{" + caption + "}\n" + r"\begin{tabular}{lr}\toprule" + "\n"
        end = r"\bottomrule\end{tabular}\end{table}"
    header = " & ".join(headings) + r"\\\midrule" + "\n"
    if long:
        header += r"\endfirsthead" + "\n" + " & ".join(headings) + r"\\\midrule\endhead" + "\n"
    write(name, start + header +
          "\n".join(" & ".join(row) + r"\\" for row in rows) + "\n" + end)


def final_tables(evidence):
    census, selection, patch, timing = (evidence[key] for key in ["census", "selection", "patch", "timing"])
    for name in ["census-table.tex", "census-outcomes.tex", "census-fragments.tex", "selector-outcomes.tex",
                 "line-costs.tex", "timing-table.tex", "timing-setup.tex",
                 "targeted-outcomes.tex", "targeted-fragments.tex"]:
        write(name, "")
    if census is not None:
        summary = census["summary"]
        rows = [("Tracked files processed", str(summary["processed_files"])),
                ("Files with complete extraction", str(summary["completed_files"])),
                ("Files with incomplete outcomes", str(summary["failed_files"])),
                ("Known eligible observations", str(summary["eligible_observations"])),
                ("Isolated checked proposals", str(summary["successful_proposals"]))]
        targeted = evidence.get("targeted")
        if targeted is not None:
            followup = targeted["summary"]
            rows.extend([("Targeted follow-up files processed", str(followup["processed_files"])),
                         ("Follow-up complete / incomplete files", f"{followup['completed_files']} / {followup['failed_files']}"),
                         ("Follow-up isolated checked proposals", str(followup["successful_proposals"]))])
        if patch is not None:
            account = patch["accounting"]
            rows.extend([(r"Compiled proof spans / affected files", f"{account['proposed_replacements']} / {len(patch['affected_files'])}"),
                         ("Original / replacement proof lines", f"{account['original_proof_lines']} / {account['replacement_proof_lines']}"),
                         ("Added helper / import lines", f"{account['added_helper_lines']} / {account['added_import_lines']}"),
                         ("Net lines saved after helpers and imports", str(account["net_lines_saved_including_imports"]))])
        if timing is not None:
            rows.append(("Ratio of mean compilation times", f"{timing['estimate']:.4f}"))
            interval = timing["interval"]
            rows.append((r"Paired 95\% interval", f"[{interval['lower']:.4f}, {interval['upper']:.4f}]" if interval["status"] == "valid" else "Undefined"))
        caption = ("Historical full census, targeted follow-up, and composed verified patch. The datasets are separate."
                   if targeted is not None else "Census protocol and verified local patch. The denominator includes all file outcomes.")
        table("census-table.tex", caption + " Proof counts include preparation, helpers, and imports.", ["Measure", "Value"], rows)
        status_rows = [(tex(key), str(value)) for key, value in sorted(summary["file_status_counts"].items())]
        status_rows.extend((tex("attempt: " + key), str(value)) for key, value in sorted(summary["attempt_status_counts"].items()))
        status_rows.append(("Unknown due to incomplete files", str(census["unknown_due_incomplete_file"])))
        status_rows.extend((tex("final file record: " + key), str(value)) for key, value in sorted(summary["counts"].items()))
        table("census-outcomes.tex", "Final file outcomes and outcomes for known eligible observations. The counters use final file records and exclude files without those records. Known observations without outcomes are not tactic failures.", ["Recorded outcome", "Count"], status_rows)
        fragments = []
        for kind, key in [("observed", "original_observation_fragment_counts"), ("eligible", "original_eligible_fragment_counts")]:
            fragments.extend((tex(kind + ": " + name), str(value)) for name, value in sorted(summary[key].items()))
        for fragment, outcomes in sorted(summary["attempt_status_counts_by_original_fragment"].items()):
            fragments.extend((tex(fragment + ": " + name), str(value)) for name, value in sorted(outcomes.items()))
        table("census-fragments.tex", "Observed fragments and their recorded outcomes. These counts are not combined patch savings.", ["Fragment and outcome", "Count"], fragments)
        if targeted is not None:
            followup = targeted["summary"]
            outcomes = [(tex("file: " + key), str(value)) for key, value in sorted(followup["file_status_counts"].items())]
            outcomes.extend((tex("attempt: " + key), str(value)) for key, value in sorted(followup["attempt_status_counts"].items()))
            outcomes.append(("Unknown due to incomplete files", str(targeted["unknown_due_incomplete_file"])))
            table("targeted-outcomes.tex", "Targeted follow-up outcomes. This subset does not give a new full-universe census.",
                  ["Recorded outcome", "Count"], outcomes)
            fragments = [(tex(name), str(value)) for name, value in sorted(followup["original_eligible_fragment_counts"].items())]
            table("targeted-fragments.tex", "Known eligible follow-up observations by original goal fragment. Isolated proposals and composed patch savings are separate.",
                  ["Fragment", "Count"], fragments)
    if selection is not None:
        outcomes = {}
        for name, value in selection["summary"]["outcome_counts"].items():
            label = "Combined source compile failure" if name.startswith("combined_source_compile_failure:") else name
            label = label if len(label) <= 70 else "Other exclusions; see selection ledger"
            outcomes[label] = outcomes.get(label, 0) + value
        table("selector-outcomes.tex", "Deterministic selection outcomes before source verification. The selection ledger records the causes. The verified combined patch gives the proof savings.", ["Selection outcome", "Count"],
              [(tex(key), str(value)) for key, value in sorted(outcomes.items())])
    if patch is not None:
        costs = patch["implementation_costs"]
        table("line-costs.tex", "Implementation code has a separate cost from the proposed mathlib proof savings. These totals do not show a reduction in total repository size.", ["Component", "Code lines"],
              [("Tactic implementation", str(costs["tactic_implementation_code_lines"])),
               ("Census infrastructure", str(costs["census_implementation_code_lines"]))])
    if timing is not None:
        rows = [(r"\nolinkurl{" + row["path"] + "}", f"{row['original_mean_seconds']:.3f}",
                 f"{row['replacement_mean_seconds']:.3f}", f"{row['ratio']:.4f}") for row in timing["files"]]
        rows.append(("Total", f"{timing['original_mean_seconds']:.3f}", f"{timing['replacement_mean_seconds']:.3f}", f"{timing['estimate']:.4f}"))
        table("timing-table.tex", "Confirmatory means in seconds for each affected file. The ratio is original time divided by replacement time. The analysis includes slower files.",
              ["Affected file", "Original", "Patch", "Ratio"], rows, long=True)
        setup = timing["report"].get("setup", [])
        rebuild = [row for row in setup if row["label"] == "tactic-rebuild"]
        table("timing-setup.tex", "Recorded setup costs outside measured compilation times. These costs do not include a full build without dependency artifacts.", ["Setup measurement", "Seconds"],
              [("Recorded setup processes", f"{sum(row['seconds'] for row in setup):.3f}" if setup else "Not measured"),
               ("Separate tactic rebuild", f"{rebuild[0]['seconds']:.3f}" if len(rebuild) == 1 else "Not measured"),
               ("Build without dependency/native artifacts", "Not measured")])


def study_data(config, evidence):
    census, patch = evidence["census"], evidence["patch"]
    facts = {name: r"\textnormal{pending}" for name in [
        "CensusFiles", "CensusComplete", "CensusFailed", "CensusEligible", "CensusProposals",
        "CensusUnknown", "PatchReplacements", "PatchFiles", "PatchBefore", "PatchAfter",
        "PatchProofSaved", "PatchNetSaved", "PatchImports", "CaseID", "CaseBefore", "CaseAfter",
        "FollowupFiles", "FollowupComplete", "FollowupFailed", "FollowupProposals",
        "StudyRatio", "StudyLower", "StudyUpper", "StudyOriginal", "StudyReplacement"]}
    if census is not None:
        summary = census["summary"]
        facts.update(CensusFiles=summary["universe_files"], CensusComplete=summary["completed_files"],
                     CensusFailed=summary["failed_files"], CensusEligible=summary["eligible_observations"],
                     CensusProposals=summary["successful_proposals"], CensusUnknown=census["unknown_due_incomplete_file"])
    if evidence.get("targeted") is not None:
        summary = evidence["targeted"]["summary"]
        facts.update(FollowupFiles=summary["processed_files"], FollowupComplete=summary["completed_files"],
                     FollowupFailed=summary["failed_files"], FollowupProposals=summary["successful_proposals"])
    if patch is not None:
        account = patch["accounting"]
        facts.update(PatchReplacements=account["proposed_replacements"], PatchFiles=len(patch["affected_files"]),
                     PatchBefore=account["original_proof_lines"], PatchAfter=account["replacement_proof_lines"],
                     PatchProofSaved=account["net_proof_lines_saved"], PatchNetSaved=account["net_lines_saved_including_imports"],
                     PatchImports=account["added_import_lines"])
    if evidence["timing"] is not None:
        timing = evidence["timing"]
        interval = timing["interval"]
        facts.update(StudyRatio=f"{timing['estimate']:.4f}",
                     StudyLower=f"{interval['lower']:.4f}" if interval["status"] == "valid" else r"\textnormal{undefined}",
                     StudyUpper=f"{interval['upper']:.4f}" if interval["status"] == "valid" else r"\textnormal{undefined}",
                     StudyOriginal=f"{timing['original_mean_seconds']:.3f}", StudyReplacement=f"{timing['replacement_mean_seconds']:.3f}")
    facts["CaseID"] = tex(config.get("example_candidate_id") or "pending")
    write("study-facts.tex", "\n".join("\\newcommand{\\" + key + "}{" + str(value) + "}" for key, value in facts.items()))
    identifier = config.get("example_candidate_id")
    if identifier is None:
        write("census-example-original.lean", "-- No verified final example selected.")
        write("census-example-replacement.lean", "-- No verified final example selected.")
        write("census-example.json", json.dumps({"status": "awaiting-selected-verified-example"}, indent=2))
        write("census-example-provenance.tex", "A selected, verified final example is not available.")
        return
    if patch is None:
        raise ValueError("a final library example needs a validated combined source patch")
    candidates = [row for row in patch["manifest"]["candidates"] if row["id"] == identifier and row["status"] == "replace"]
    if len(candidates) != 1:
        raise ValueError("the final library example is not a unique selected replacement")
    candidate = candidates[0]
    counted = next(row for row in patch["accounting"]["candidates"] if row["id"] == identifier)
    facts.update(CaseBefore=counted["original_proof_lines"], CaseAfter=counted["replacement_proof_lines"])
    write("study-facts.tex", "\n".join("\\newcommand{\\" + key + "}{" + str(value) + "}" for key, value in facts.items()))
    source = next(row for row in evidence["selection"]["prepared"] if row["path"] == candidate["path"])
    original = "".join(source["original"].splitlines(keepends=True)[candidate["start_line"] - 1:candidate["end_line"]])
    if hashlib.sha256(original.encode()).hexdigest() != candidate["original_sha256"]:
        raise ValueError("final library example source span changed")
    checked = next(row for row in patch["verification"]["files"] if row["path"] == candidate["path"])
    if checked["status"] != "verified" or identifier not in checked["candidate_ids"]:
        raise ValueError("final library example has no combined source verification")
    replacement = candidate["replacement"]
    write("census-example-original.lean", original)
    write("census-example-replacement.lean", replacement)
    write("census-example-provenance.tex",
          "The selected entry is " + r"\texttt{" + tex(identifier) + "}. " +
          "Its source is " + r"\sourcepath{" + candidate["path"] + "}, " +
          f"lines {candidate['start_line']}--{candidate['end_line']}. " +
          "Its declaration is " + r"\sourcepath{" + candidate.get("declaration", "unknown") + "}. " +
          "The final combined source check includes this entry.")
    write("census-example.json", json.dumps({
        "status": "selected_combined_source_verified", "candidate_id": identifier,
        "path": candidate["path"], "declaration": candidate.get("declaration"),
        "fragment": candidate.get("fragment"), "source_lines": [candidate["start_line"], candidate["end_line"]],
        "mathlib_revision": patch["manifest"]["mathlib_revision"],
        "census_protocol_hash": patch["manifest"].get("census_protocol_hash"),
        "targeted_protocol_hash": evidence["targeted"]["manifest"]["protocol_hash"] if evidence.get("targeted") is not None else None,
        "combined_patch_sha256": patch["patch_sha256"], "original_sha256": candidate["original_sha256"],
        "replacement_sha256": hashlib.sha256(replacement.encode()).hexdigest(),
        "original_file_sha256": checked["original_source_sha256"],
        "replacement_file_sha256": checked["replacement_source_sha256"],
        "compiler_artifact_sha256": checked["artifact_sha256"],
    }, indent=2))


def future_status(config=None, evidence=None):
    config = config if config is not None else json.loads((HERE / "status.json").read_text())
    evidence = evidence if evidence is not None else load_evidence(config, ROOT)
    final_tables(evidence)
    study_data(config, evidence)
    write("implementation-status.tex", r"\paragraph{Artifact status.} " + tex(config["description"]))
    census, patch, timing = (evidence[key] for key in ["census", "patch", "timing"])
    if census is None:
        write("census-status.tex", r"\textbf{Current status:} this artifact does not contain a complete semantic census.")
        write("census-detail.tex", "This build has no complete semantic-census summary.")
    else:
        summary = census["summary"]
        message = f"The census processed all {summary['universe_files']} tracked files. "
        message += f"Extraction completed in {summary['completed_files']} files. {summary['failed_files']} files had incomplete outcomes. "
        message += f"It recorded {summary['eligible_observations']} known eligible observations and {summary['successful_proposals']} isolated checked proposals."
        if patch is not None:
            account = patch["accounting"]
            message += f"\n\nThe verified local patch replaces {account['proposed_replacements']} proof spans in {len(patch['affected_files'])} files. "
            message += f"Proof code decreases by {account['net_proof_lines_saved']} lines after preparation and helpers, or {account['net_lines_saved_including_imports']} after imports."
        else:
            message += "\n\nThese proposals do not establish compiled source savings."
        if timing is not None:
            message += "\n\nThe predeclared speed criterion is " + ("met." if timing["success_criterion_met"] else "not met.")
        targeted = evidence.get("targeted")
        if targeted is not None:
            followup = targeted["summary"]
            prefix = f"The historical full census processed {summary['universe_files']} files, with {summary['failed_files']} incomplete outcomes. "
            prefix += f"The targeted follow-up processed {followup['processed_files']} files. {followup['failed_files']} are incomplete. "
            prefix += "It does not show new coverage of the full universe."
            if patch is not None:
                prefix += f" The composed patch replaces {account['proposed_replacements']} spans in {len(patch['affected_files'])} files. "
                prefix += f"It removes {account['net_lines_saved_including_imports']} code lines after all preparation and imports."
            write("census-status.tex", tex(prefix))
        else:
            write("census-status.tex", tex(message) + "\n" + r"\input{generated/census-table.tex}")
        detail = f"The census has {census['unknown_due_incomplete_file']} known eligible observations without a recorded outcome because a file did not complete. "
        detail += "Failed files can also have goals that extraction did not record. "
        detail += "Counters from final file records do not count all known observations."
        if targeted is not None:
            detail += f" The follow-up has {targeted['unknown_due_incomplete_file']} known eligible observations without terminal outcomes."
        tables = ([r"\input{generated/census-table.tex}"] if targeted is not None else [])
        tables += [r"\input{generated/census-outcomes.tex}", r"\input{generated/census-fragments.tex}",
                   r"\input{generated/targeted-outcomes.tex}", r"\input{generated/targeted-fragments.tex}",
                   r"\input{generated/selector-outcomes.tex}", r"\input{generated/line-costs.tex}"]
        write("census-detail.tex", tex(detail) + "\n" + "\n".join(tables))
    if timing is None:
        write("confirmatory-status.tex", "This build has no confirmatory timing report. The paper-phase speedup is unproved.")
        write("timing-main.tex", "The confirmatory timing result is not available. Compilation speed is unproved.")
    else:
        interval = timing["interval"]
        message = f"The confirmatory run uses {timing['block_count']} blocks of {timing['block_pairs']} paired passes. "
        message += f"It uses {timing['bootstrap_resamples']} bootstrap samples with seed {timing['bootstrap_seed']}. "
        message += f"The ratio of mean full-pass times is {timing['estimate']:.4f}."
        if interval["status"] == "valid":
            message += f" The conditional paired 95% interval is [{interval['lower']:.4f}, {interval['upper']:.4f}]."
        else:
            message += " The paired 95% interval is undefined. " + interval["reason"] + "."
        message += "\n\nThe predeclared speed criterion is " + ("met." if timing["success_criterion_met"] else "not met.")
        message += " The analysis includes all affected files and measured passes."
        if evidence.get("targeted") is not None:
            count = timing["report"]["provenance"]["repetitions"]
            rows = [row for row in timing["report"]["measurements"] if row["phase"] == "measured"]
            changes = []
            for variant in ["original", "replacement"]:
                first = sum(row["seconds"] for row in rows if row["variant"] == variant and row["pair"] < count // 2)
                last = sum(row["seconds"] for row in rows if row["variant"] == variant and row["pair"] >= count // 2)
                changes.append(100 * (last / first - 1))
            message += f"\n\nSecond-half mean times changed by {changes[0]:+.2f}% for original and {changes[1]:+.2f}% for replacement relative to the first half. "
            message += "The interval remains conditional on independent, representative timing blocks."
        main_message = f"Mean original and replacement full-pass times were {timing['original_mean_seconds']:.3f} and {timing['replacement_mean_seconds']:.3f} seconds. "
        main_message += f"The ratio of mean full-pass times is {timing['estimate']:.4f}. "
        if interval["status"] == "valid":
            main_message += f"The conditional paired 95% interval is [{interval['lower']:.4f}, {interval['upper']:.4f}]. "
        else:
            main_message += "The paired 95% interval is undefined. "
        main_message += "The predeclared speed criterion is " + ("met." if timing["success_criterion_met"] else "not met.")
        slower = [row for row in timing["files"] if row["ratio"] < 1]
        slower_text = f"Compilation was slower for {len(slower)} files. The appendix reports every file." if slower else ""
        write("timing-main.tex", tex(main_message) + " " + slower_text)
        write("confirmatory-status.tex", tex(message) + "\n" + r"\input{generated/timing-table.tex}" + "\n" + r"\input{generated/timing-setup.tex}")
    compact = {"stages": evidence["stages"], "inputs": evidence["inputs"],
               "validation_context": evidence["validation_context"],
               "bundle_sha256": evidence.get("bundle_sha256"),
               "census": {"summary": census["summary"], "unknown_due_incomplete_file": census["unknown_due_incomplete_file"]} if census is not None else None,
               "targeted": {key: evidence["targeted"][key] for key in ["summary", "unknown_due_incomplete_file"]} if evidence.get("targeted") is not None else None,
               "patch": {key: patch[key] for key in ["accounting", "affected_files", "patch_sha256", "implementation_costs"]} if patch is not None else None,
               "timing": {key: value for key, value in timing.items() if key != "report"} if timing is not None else None}
    write("final-evidence.json", json.dumps(compact, indent=2))
    return {"configuration": config, "validated_evidence": compact}


def blinded_calibration_data(metadata, values, plan, timing):
    review, decision = values["calibration_review"], values["calibration_decision"]
    calibration = plan["calibration"]
    keys = {"schema_version", "scope", "measured_pairs", "affected_files", "pair_series_autocorrelations",
            "AB_minus_BA", "half_run_drift", "candidate_blocks", "limits", "input_sha256"}
    if (set(review) != keys or review["schema_version"] != 1 or review["measured_pairs"] != 24 or
            review["affected_files"] != len(plan["affected_files"]) or
            set(review["candidate_blocks"]) != {"4", "8"}):
        raise ValueError("invalid speed-level-blinded calibration review")
    references = review["input_sha256"]
    b = calibration["block_pairs"]
    if (b not in [4, 8] or metadata["calibration_decision"]["sha256"] != calibration["sha256"] or
            decision.get("speed_level_blinded") is not True or decision.get("block_pairs") != b or
            decision.get("predeclared_confirmatory_pairs") != plan["measured_pairs"] or
            plan["measured_pairs"] != 10 * b or timing["block_count"] != 10 or timing["block_pairs"] != b or
            decision.get("review_inputs") != {metadata["calibration_review"]["source"]: metadata["calibration_review"]["sha256"]}):
        raise ValueError("blinded calibration decision differs from the frozen design")
    for key in ["pilot_report", "pilot_measurements"]:
        if (references.get(key) != calibration[key]["sha256"] or
                decision.get(key, {}).get("sha256") != calibration[key]["sha256"]):
            raise ValueError("blinded calibration pilot lineage differs")
    for key, source in [("diagnostic_source", "diagnostics_source"), ("review_source", "calibration_review_source")]:
        if references.get(key) != metadata.get(source, {}).get("sha256") or references.get(key) is None:
            raise ValueError("blinded calibration source fingerprint differs")
    if decision.get("review_source_sha256") != references["review_source"]:
        raise ValueError("blinded calibration decision used a different review source")
    for length, block in review["candidate_blocks"].items():
        n = int(length)
        if (block.get("pilot_blocks") != 24 // n or block.get("confirmatory_pairs") != 10 * n or
                block.get("confirmatory_blocks") != 10):
            raise ValueError("blinded calibration block counts differ")

    def number(value, *, percent=False):
        if value is None:
            return "Undefined"
        if type(value) not in [int, float] or not math.isfinite(value):
            raise ValueError("invalid blinded calibration diagnostic")
        return f"{value * (100 if percent else 1):.3f}"

    acf, drift, order = (review[key] for key in ["pair_series_autocorrelations", "half_run_drift", "AB_minus_BA"])
    block = review["candidate_blocks"][str(b)]
    rows = [("Measured pilot pairs", "24")]
    for lag in [1, 2]:
        rows.append((f"Duration correlation at lag {lag} (original / patch)",
                     " / ".join(number(acf[key][str(lag)]) for key in ["original_seconds", "replacement_seconds"])))
    for length in [4, 8]:
        correlations = review["candidate_blocks"][str(length)]["lag_autocorrelations"]
        rows.append((f"{length}-pair duration correlation at lag one", " / ".join(number(correlations[key]["1"])
                     for key in ["original_mean_seconds_per_pair", "replacement_mean_seconds_per_pair"])))
    rows += [(r"Half-run duration change (\%)", " / ".join(number(drift[key], percent=True)
              for key in ["original_relative_mean_change", "replacement_relative_mean_change"])),
             ("Change in mean log ratio", number(drift["change_in_mean_log_paired_ratio"])),
             (r"AB minus BA relative duration (\%)", " / ".join(number(order[key], percent=True)
              for key in ["original_relative_duration_difference", "replacement_relative_duration_difference"])),
             ("AB minus BA mean log ratio", number(order["mean_log_paired_ratio_difference"])),
             (f"{b}-pair log-ratio correlations at lags 1--3", " / ".join(number(block["lag_autocorrelations"]
              ["log_ratio_of_block_totals"][str(lag)]) for lag in [1, 2, 3])),
             ("Pilot / confirmatory blocks", f"{block['pilot_blocks']} / {timing['block_count']}")]
    write("calibration-status.tex", "The block-length review used a separate 24-pair pilot. "
          "It excluded absolute times, average speed levels, confidence intervals, and significance. "
          f"It selected {b} pairs for each block before the confirmatory run. "
          f"There were {block['pilot_blocks']} pilot blocks at this block length. "
          "These diagnostics do not prove block independence.\n" + r"\input{generated/calibration-table.tex}")
    table("calibration-table.tex", "Blinded pilot diagnostics for the frozen block-length decision. The review used serial, drift, and order metrics. These diagnostics do not prove independence.", ["Diagnostic", "Value"], rows)


def metadata_data(config, evidence, inputs=None):
    metadata = {}
    values = {}
    for key, spec in (config.get("paper_metadata") or evidence.get("paper_metadata", {})).items():
        path = inputs["metadata_" + key] if inputs else ROOT / spec["path"]
        if sha(path) != spec["sha256"]:
            raise ValueError("paper metadata changed: " + key)
        metadata[key] = {"source": spec["path"], "sha256": spec["sha256"]}
        if path.suffix == ".json":
            values[key] = json.loads(path.read_text())
    write("calibration-status.tex", "")
    write("calibration-table.tex", "")
    if "calibration_review" not in values:
        return metadata
    if evidence["timing"] is None:
        raise ValueError("calibration review needs validated final timing")
    plan_path = inputs["final_analysis_plan"] if inputs else ROOT / config["confirmatory_analysis_plan"]
    plan = json.loads(plan_path.read_text())
    calibration = plan["calibration"]
    if config.get("study_mode") == "composed_expansion" or "candidate_blocks" in values["calibration_review"]:
        blinded_calibration_data(metadata, values, plan, evidence["timing"])
        return metadata
    review, diagnostic, decision = (values[key] for key in ["calibration_review", "pilot_diagnostics", "calibration_decision"])
    if (review["diagnostics_sha256"] != metadata["pilot_diagnostics"]["sha256"] or
            diagnostic["input_sha256"]["report"]["sha256"] != calibration["pilot_report"]["sha256"] or
            diagnostic["input_sha256"]["measurements"]["sha256"] != calibration["pilot_measurements"]["sha256"] or
            decision["speed_level_blinded"] is not True or decision["block_pairs"] != calibration["block_pairs"]):
        raise ValueError("calibration review lineage differs from the frozen experiment")
    for key in ["calibration_review", "pilot_diagnostics"]:
        if decision["review_inputs"][metadata[key]["source"]] != metadata[key]["sha256"]:
            raise ValueError("calibration decision used different review inputs")
    expected_blocks = {key: {field: row[field] for field in ["pilot_blocks", "confirmatory_blocks_at_40_pairs", "lag_autocorrelations"]}
                       for key, row in diagnostic["compatible_block_diagnostics"].items()}
    if (review["pair_series_autocorrelations"] != diagnostic["lag_autocorrelations"] or
            review["AB_minus_BA"] != diagnostic["AB_minus_BA"] or review["blocks"] != expected_blocks or
            any(value != diagnostic["half_run_drift"][key] for key, value in review["half_run_drift"].items())):
        raise ValueError("blinded review differs from the recorded diagnostics")
    b = calibration["block_pairs"]
    block = review["blocks"][str(b)]
    count = diagnostic["repetitions"]
    write("calibration-status.tex", f"The block-length review used a separate {count}-pair pilot. "
          "It excluded absolute times, average speed levels, confidence intervals, and significance. "
          f"It selected {b} pairs for each block before the confirmatory run. "
          f"There were {block['pilot_blocks']} pilot blocks at this block length. "
          "These diagnostics do not prove block independence.\n" + r"\input{generated/calibration-table.tex}")
    def pair(mapping, keys):
        return " / ".join(f"{mapping[key]:.3f}" for key in keys)
    acf = review["pair_series_autocorrelations"]
    rows = [("Measured pilot pairs", str(count)),
            ("Duration lag-one correlation (original / patch)", f"{acf['original_seconds']['1']:.3f} / {acf['replacement_seconds']['1']:.3f}"),
            ("Duration lag-two correlation (original / patch)", f"{acf['original_seconds']['2']:.3f} / {acf['replacement_seconds']['2']:.3f}")]
    for length in [2, b]:
        correlations = review["blocks"][str(length)]["lag_autocorrelations"]
        rows.append((f"{length}-pair duration correlation at lag one", f"{correlations['original_mean_seconds_per_pair']['1']:.3f} / {correlations['replacement_mean_seconds_per_pair']['1']:.3f}"))
    drift = review["half_run_drift"]
    rows += [(r"Half-run duration change (\%)", f"{100*drift['original_relative_mean_change']:.3f} / {100*drift['replacement_relative_mean_change']:.3f}"),
             ("Change in mean log ratio", tex(f"{drift['change_in_mean_log_paired_ratio']:.2e}")),
             ("AB minus BA mean log ratio", tex(f"{review['AB_minus_BA']['mean_log_paired_ratio']:.2e}")),
             (f"{b}-pair log-ratio correlations at lags 1--3", pair(block["lag_autocorrelations"]["log_ratio_of_block_totals"], ["1", "2", "3"])),
             ("Pilot / confirmatory blocks", f"{block['pilot_blocks']} / {evidence['timing']['block_count']}")]
    table("calibration-table.tex", "Pilot diagnostics for the frozen block-length decision. The review used serial, drift, and order metrics. These diagnostics do not prove independence.", ["Diagnostic", "Value"], rows)
    return metadata


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--draft", action="store_true", help="allow missing or unchecked example snippets, with visible status labels")
    args = parser.parse_args()
    GENERATED.mkdir(exist_ok=True)
    config = json.loads((HERE / "status.json").read_text())
    evidence = load_evidence(config, ROOT)
    inputs = evidence.get("paper_inputs")
    names = EXPANSION_NAMES if evidence.get("targeted") is not None else NAMES
    examples = example_data(args.draft, inputs, names)
    implementation = implementation_data(evidence, examples["implementation_sha256"])
    provenance = {"schema_version": 2, "source_example": source_example_data(inputs), "examples": examples,
                  "implementation": implementation, "status": future_status(config, evidence),
                  "metadata": metadata_data(config, evidence, inputs)}
    if evidence.get("targeted") is not None:
        provenance["community_request"] = community_request_data(evidence)
    provenance["plots"] = generate_plots(evidence, GENERATED)
    write("provenance.json", json.dumps(provenance, indent=2))


if __name__ == "__main__":
    main()
