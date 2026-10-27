#!/usr/bin/env python3
"""Compile README examples in a separate project using a Git package dependency.

The temporary consumer is removed afterwards. Dependency checkouts and builds
are retained in this repository's .lake/packages cache, including norm-arith's
separate Git checkout. The requested revision must be available from GitHub.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import shlex
import subprocess
import tempfile
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
REMOTE = "https://github.com/TomasOrtega/norm-arith.git"


def run(command: list[str], cwd: Path) -> None:
    print(f"+ {shlex.join(command)}", flush=True)
    subprocess.run(command, cwd=cwd, check=True)


def readme_examples() -> tuple[str, int]:
    """Move the README blocks' imports before their otherwise unchanged code."""
    blocks = re.findall(r"^```lean\s*\n(.*?)^```\s*$",
                        (ROOT / "README.md").read_text(encoding="utf-8"),
                        flags=re.MULTILINE | re.DOTALL)
    imports, bodies = [], []
    for block in blocks:
        lines = block.splitlines()
        imports.extend(line for line in lines if line.startswith("import "))
        bodies.append("\n".join(line for line in lines
                                if not line.startswith("import ")).strip())
    count = sum(len(re.findall(r"^example\b", body, re.MULTILINE)) for body in bodies)
    if count == 0 or not {"import NormArith", "import NormArith.Analysis"} <= set(imports):
        raise ValueError("README must contain examples importing both package entry points")
    source = "module\n\n" + "\n".join(dict.fromkeys(imports)) + "\n\n"
    return source + "\n\n".join(bodies) + "\n", count


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake", default="lake", help="Lake executable (default: lake on PATH)")
    parser.add_argument("--revision", help="Git revision to fetch (default: current Git HEAD)")
    args = parser.parse_args()
    revision = args.revision or subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
    # Keep an elan proxy's filename; resolving its symlink changes its behavior.
    lake = os.path.abspath(os.path.expanduser(args.lake)) if os.path.dirname(args.lake) else args.lake
    source, count = readme_examples()
    packages = ROOT / ".lake" / "packages"
    packages.mkdir(parents=True, exist_ok=True)
    print(f"Checking {count} README examples against {REMOTE} at {revision}", flush=True)
    with tempfile.TemporaryDirectory(prefix="norm-arith-consumer-") as temporary:
        consumer = Path(temporary)
        (consumer / "lean-toolchain").write_text(
            (ROOT / "lean-toolchain").read_text(encoding="utf-8"), encoding="utf-8")
        (consumer / "Consumer.lean").write_text(source, encoding="utf-8")
        (consumer / "lakefile.toml").write_text(
            'name = "norm-arith-consumer-smoke"\nversion = "0.1.0"\n'
            'defaultTargets = ["Consumer"]\n'
            f'packagesDir = {json.dumps(str(packages))}\n\n'
            '[[require]]\nname = "norm-arith"\n'
            f'git = {json.dumps(REMOTE)}\nrev = {json.dumps(revision)}\n\n'
            '[[lean_lib]]\nname = "Consumer"\n', encoding="utf-8")
        run([lake, "update"], consumer)
        manifest = json.loads((consumer / "lake-manifest.json").read_text(encoding="utf-8"))
        # Lake serializes a hyphenated Lean name with identifier quotation.
        matches = [p for p in manifest["packages"]
                   if p.get("name") in {"norm-arith", "«norm-arith»"}
                   and p.get("type") == "git" and p.get("url") == REMOTE]
        if len(matches) != 1:
            raise RuntimeError("consumer did not resolve norm-arith as the requested Git package")
        package = matches[0]
        if re.fullmatch(r"[0-9a-f]{40}", revision) and package["rev"] != revision:
            raise RuntimeError("consumer resolved a different Git commit")
        print(f"Resolved norm-arith commit: {package['rev']}", flush=True)
        run([lake, "build", "--wfail", "Consumer"], consumer)
    print(f"Passed: {count} README examples compile as a downstream Git consumer.", flush=True)


if __name__ == "__main__":
    main()
