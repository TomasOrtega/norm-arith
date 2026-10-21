#!/usr/bin/env python3
"""Archive the finished study and roundtrip its portable analysis transport."""

import argparse
from datetime import datetime, timezone
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import types

import archive_targeted


ROOT = Path(__file__).resolve().parents[2]
ARCHIVE = archive_targeted.archive
sha = ARCHIVE.file_hash


def save(path, value):
    with path.open("x") as stream:
        json.dump(value, stream, indent=2, sort_keys=True)
        stream.write("\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("study", type=Path)
    parser.add_argument("--local", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    study, local, output = args.study.resolve(), args.local.resolve(), args.output.resolve()
    assert not local.exists() and not output.exists()
    local.mkdir(parents=True)
    output.mkdir(parents=True)
    compact = local / "compact"
    compact.mkdir()
    copied = {}

    def copy(source, relative):
        source = Path(source)
        destination = compact / relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        expected = sha(source)
        shutil.copyfile(source, destination)
        assert sha(destination) == expected
        copied[str(relative)] = {"sha256": expected, "bytes": destination.stat().st_size}

    for source in study.iterdir():
        if source.is_file():
            copy(source, source.name)
    for source in (study / "frozen").iterdir():
        copy(source, Path("frozen") / source.name)
    for label in ["pilot", "confirmation"]:
        run = study / label
        for source in run.iterdir():
            if source.is_file():
                copy(source, Path(label) / source.name)
        for source in sorted((run / "sources").rglob("*.lean")):
            copy(source, Path(label) / source.relative_to(run))
    report = json.loads((study / "confirmation/report.json").read_bytes())
    for name, expected in report["provenance"]["project_lean_sources"].items():
        assert sha(ROOT / name) == expected
        copy(ROOT / name, Path("frozen-project") / name)
    for name in ["lean-toolchain", "lakefile.toml", "lake-manifest.json", "scripts/benchmark.py"]:
        copy(ROOT / name, Path("frozen-project") / name)
    for name in ["machine-profile-before-study.json", "machine-profile-after-study.json", "quiet-start.json",
                 "implementation-costs-v4.json", "expanded-study-protocol.md"]:
        copy(ROOT / "artifacts/expansion" / name, Path("metadata") / name)
    for source in [Path(__file__), ROOT / "artifacts/expansion/audit_study_bytes.py",
                   ROOT / "artifacts/expansion/verify_expanded_statistics.py",
                   ROOT / "artifacts/expansion/calibration_review.py", ROOT / "artifacts/pilot_serial_diagnostics.py",
                   ROOT / "paper/evidence_transport.py"]:
        copy(source, Path("audit-tools") / source.name)
    save(compact / "bundle.json", {"schema_version": 1, "kind": "expanded_compilation_study_compact",
                                  "inventory": copied})
    transport_source = compact / "audit-tools/evidence_transport.py"
    transport = types.ModuleType("study_transport")
    exec(compile(transport_source.read_bytes(), str(transport_source), "exec"), transport.__dict__)
    print("Packing checked compact transport", flush=True)
    packed = transport.pack_bundle(compact, output / "transport")
    transport_path = output / "transport/transport.json"
    restored = Path(tempfile.mkdtemp(prefix="norm-arith-study-roundtrip-", dir="/private/tmp")) / "restored"
    transport.unpack_bundle(transport_path, restored, expected_receipt_sha256=sha(transport_path),
                            expected_bundle_sha256=packed["bundle_sha256"])
    portable_result = restored.parent / "roundtrip-statistics.json"
    command = """import os,runpy,sys
blocked,checker,report,result=sys.argv[1:]
def guard(event,args):
 if event=='open' and isinstance(args[0],(str,bytes)):
  path=os.path.abspath(os.fsdecode(args[0]))
  if path==blocked or path.startswith(blocked+os.sep):raise RuntimeError('original project access denied: '+path)
sys.addaudithook(guard)
sys.argv=[checker,report,'--output',result]
runpy.run_path(checker,run_name='__main__')
"""
    result = subprocess.run([sys.executable, "-c", command, str(ROOT),
                             str(restored / "audit-tools/verify_expanded_statistics.py"),
                             str(restored / "confirmation/report.json"), str(portable_result)],
                            cwd=restored, capture_output=True, text=True)
    assert result.returncode == 0, result.stderr
    assert portable_result.read_bytes() == (study / "independent-statistics.json").read_bytes()
    shutil.copyfile(portable_result, local / "roundtrip-statistics.json")
    roundtrip = {"schema_version": 1, "status": "restored_analysis_matches_exactly",
                 "created_at_utc": datetime.now(timezone.utc).isoformat(),
                 "original_project_open_access_forbidden_by_python_audit_hook": True,
                 "restored_tree": str(restored), "python": sys.version,
                 "transport_receipt_sha256": sha(transport_path), "bundle_sha256": packed["bundle_sha256"],
                 "recomputed_statistics_sha256": sha(portable_result),
                 "all_payload_files_checked_against_inventory": True}
    save(output / "roundtrip-integrity.json", roundtrip)
    copy_receipts = ["independent-statistics.json", "calibration.json", "pilot-calibration-review.json",
                     "calibration-superseded-relative-review-path.json", "calibration-decision-receipt.json",
                     "calibration-decision-receipt-v2.json", "calibration-root-check.json"]
    for name in copy_receipts:
        shutil.copyfile(study / name, output / name)
    byte_audit = json.loads((study / "timed-output-byte-audit.json").read_bytes())
    shutil.copyfile(study / "timed-output-byte-audit.json", output / "timed-output-byte-audit.json")
    print("Compact roundtrip passed; indexing and compressing all raw study files", flush=True)
    names = ARCHIVE.regular_files(study)
    signatures = {name: ARCHIVE.signature(study / name) for name in names}
    inventory = {}
    known = byte_audit["output_inventory"]
    for name in names:
        inventory[name] = known.get(name) or {"sha256": sha(study / name), "bytes": (study / name).stat().st_size}
    ARCHIVE.make_tar(local / "raw-study.tar.gz", study, names, "run", inventory)
    index = archive_targeted.verify_tar(local / "raw-study.tar.gz", inventory)
    ARCHIVE.verify_unchanged(study, {"inventory": inventory, "signatures": signatures})
    save(output / "raw-study-index.json", {"schema_version": 1, "files": index})
    receipt = {"schema_version": 1, "status": "validated_expanded_study_archive",
               "created_at_utc": datetime.now(timezone.utc).isoformat(), "source": str(study),
               "helper_sha256": sha(Path(__file__)),
               "compact_transport": {"receipt": "transport/transport.json", "sha256": sha(transport_path), **packed},
               "portable_statistics_roundtrip": roundtrip,
               "raw_archive": {"local_path": str(local / "raw-study.tar.gz"),
                               "sha256": sha(local / "raw-study.tar.gz"),
                               "bytes": (local / "raw-study.tar.gz").stat().st_size,
                               "files": len(index), "uncompressed_file_bytes": sum(v["bytes"] for v in inventory.values()),
                               "index_sha256": sha(output / "raw-study-index.json"),
                               "all_members_reopened_and_rehashed": True,
                               "original_files_unchanged_during_archive": True},
               "timed_output_byte_audit_sha256": sha(output / "timed-output-byte-audit.json"),
               "independent_statistics_sha256": sha(output / "independent-statistics.json")}
    save(output / "archive.json", receipt)
    save(output / "inventory.json", {name: {"sha256": sha(output / name), "bytes": (output / name).stat().st_size}
                                     for name in ARCHIVE.regular_files(output)})
    print(json.dumps({k: v for k, v in receipt.items() if k != "compact_transport"}, indent=2))


if __name__ == "__main__":
    main()
