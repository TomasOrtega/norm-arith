#!/usr/bin/env python3
"""Record a deterministic lexical search for additive norm proof blocks."""

import argparse
import json
import subprocess
from pathlib import Path


QUERIES = [
    ("three-term-triangle", "Mathlib", "norm_add₃_le"),
    ("repeated-triangle", "Mathlib", r"norm_sub_le.*norm_sub_le|norm_add_le.*norm_add_le"),
    ("explicit-additive-identity", "Mathlib/Analysis", r"congr.*abel|abel.*norm|norm.*abel"),
]


def discover(root):
    revision = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=root, text=True
    ).strip()
    results = []
    for name, scope, pattern in QUERIES:
        command = ["rg", "--json", "--glob", "*.lean", pattern, scope]
        process = subprocess.run(command, cwd=root, text=True, capture_output=True)
        if process.returncode not in (0, 1):
            raise RuntimeError(process.stderr)
        matches = []
        for event in map(json.loads, process.stdout.splitlines()):
            if event["type"] == "match":
                data = event["data"]
                matches.append(
                    {
                        "path": data["path"]["text"],
                        "line": data["line_number"],
                        "text": data["lines"]["text"].rstrip("\n"),
                    }
                )
        matches.sort(key=lambda item: (item["path"], item["line"]))
        results.append({"id": name, "command": command, "matches": matches})
    return {
        "schema_version": 1,
        "mathlib_revision": revision,
        "lean_files_in_mathlib": sum(1 for _ in (root / "Mathlib").rglob("*.lean")),
        "queries": results,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mathlib", type=Path, default=Path(".lake/packages/mathlib"))
    parser.add_argument("--output", type=Path, default=Path("benchmarks/discovery.json"))
    args = parser.parse_args()
    args.output.write_text(json.dumps(discover(args.mathlib), ensure_ascii=False, indent=2) + "\n")


if __name__ == "__main__":
    main()
