import contextlib
import gzip
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from types import SimpleNamespace

import benchmark

from benchmark import BenchmarkError, sha256
from census import CensusError
from select_census import candidate_from_proposal
import verify_selection


class ProofSpanTests(unittest.TestCase):
    def test_wrapped_replacement_preserves_the_recorded_proof_and_body(self):
        with tempfile.TemporaryDirectory() as tmp:
            mathlib = Path(tmp)
            (mathlib / "Mathlib").mkdir()
            prefix = b"example " + b"x" * 70 + b" : True := "
            proof = b"by\n  change True\n  change True\n  trivial"
            source = b"import Mathlib.Init\n" + prefix + proof + b"\n"
            (mathlib / "Mathlib/Example.lean").write_bytes(source)
            start = source.index(proof)
            proposal = {"path": "Mathlib/Example.lean", "key": "wrapped", "status": "success",
                        "kernel_checked": True, "replacement_eligible": True,
                        "source_sha256": sha256(source), "original_sha256": sha256(proof),
                        "start_byte": start, "end_byte": start + len(proof), "replacement": "by norm_arith",
                        "body_start_byte": start, "body_end_byte": start + len(proof)}
            candidate = dict(candidate_from_proposal(proposal, source), status="replace",
                             replacement=(prefix + b"by\n  norm_arith\n").decode())
            manifest = {"files": [{"path": proposal["path"], "source_sha256": sha256(source),
                                   "imports": ["NormArith"], "helpers": []}], "candidates": [candidate]}
            verify_selection.validate_proof_spans(manifest, mathlib)
            candidate["replacement"] = candidate["replacement"].replace("True", "False")
            with self.assertRaisesRegex(BenchmarkError, "outside the recorded proof span"):
                verify_selection.validate_proof_spans(manifest, mathlib)
            candidate["replacement"] = (prefix + b"by\n  norm_arith\n").decode()
            candidate["body_end_byte"] = start
            with self.assertRaisesRegex(BenchmarkError, "declaration proof body"):
                verify_selection.validate_proof_spans(manifest, mathlib)

    def test_only_the_recorded_proof_bytes_may_change(self):
        with tempfile.TemporaryDirectory() as tmp:
            mathlib = Path(tmp)
            (mathlib / "Mathlib").mkdir()
            source = b"import Mathlib.Init\nexample : True := by\n  trivial\n  done\n"
            (mathlib / "Mathlib/Example.lean").write_bytes(source)
            proof = b"by\n  trivial\n  done"
            start = source.index(proof)
            proposal = {"path": "Mathlib/Example.lean", "key": "proof", "status": "success",
                        "kernel_checked": True, "replacement_eligible": True,
                        "source_sha256": sha256(source), "original_sha256": sha256(proof),
                        "start_byte": start, "end_byte": start + len(proof), "replacement": "by norm_arith",
                        "body_start_byte": start, "body_end_byte": start + len(proof)}
            candidate = dict(candidate_from_proposal(proposal, source), status="replace")
            manifest = {"files": [{"path": proposal["path"], "source_sha256": sha256(source),
                                   "imports": ["NormArith"], "helpers": []}], "candidates": [candidate]}
            verify_selection.validate_proof_spans(manifest, mathlib)
            candidate["body_start_byte"] = start + len(proof)
            with self.assertRaisesRegex(BenchmarkError, "declaration proof body"):
                verify_selection.validate_proof_spans(manifest, mathlib)
            candidate["body_start_byte"] = start
            candidate["replacement"] = candidate["replacement"].replace("True", "False")
            with self.assertRaisesRegex(BenchmarkError, "outside the recorded proof span"):
                verify_selection.validate_proof_spans(manifest, mathlib)

    def test_stale_census_setup_is_rejected_before_compilation(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "manifest.json").write_text("{}")
            module = "Mathlib.Example"
            setup = {"name": module, "importArts": {}}
            (root / "setups").mkdir()
            path = root / "setups" / f"{module}.json.gz"
            with gzip.open(path, "wb") as stream:
                stream.write(json.dumps(setup).encode())
            directory = root / "files" / module
            directory.mkdir(parents=True)
            (directory / "result.json").write_text(json.dumps({
                "complete": True, "path": "Mathlib/Example.lean", "module": module,
                "source_sha256": "a" * 64, "setup_sha256": sha256(json.dumps(setup)),
                "directory": f"files/{module}/attempt-01",
            }))
            manifest = {"files": [{"path": "Mathlib/Example.lean", "source_sha256": "a" * 64}]}
            setups, fingerprints = verify_selection.load_census_setups(root, manifest, ["Mathlib/Example.lean"])
            self.assertEqual(setups, {"Mathlib/Example.lean": setup})
            verify_selection.verify_frozen_inputs(fingerprints)
            with gzip.open(path, "wb") as stream:
                stream.write(json.dumps(dict(setup, options={"autoImplicit": True})).encode())
            with self.assertRaisesRegex(BenchmarkError, "setup hash mismatch"):
                verify_selection.load_census_setups(root, manifest, ["Mathlib/Example.lean"])

    def test_body_range_must_match_the_checked_census_proposal_exactly(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            mathlib, census = root / "mathlib", root / "census"
            (mathlib / "Mathlib").mkdir(parents=True)
            source = b"example : True := by trivial\n"
            (mathlib / "Mathlib/Example.lean").write_bytes(source)
            start = source.index(b"by trivial")
            proposal = {"path": "Mathlib/Example.lean", "key": "proof", "status": "success",
                        "kernel_checked": True, "replacement_eligible": True,
                        "source_sha256": sha256(source), "original_sha256": sha256(b"by trivial"),
                        "start_byte": start, "end_byte": len(source) - 1, "replacement": "by norm_arith",
                        "body_start_byte": start, "body_end_byte": len(source) - 1}
            candidate = dict(candidate_from_proposal(proposal, source), status="replace")
            directory = census / "files/Mathlib.Example"
            directory.mkdir(parents=True)
            proposals = directory / "proposals.jsonl"
            proposals.write_text(json.dumps(proposal) + "\n")
            (directory / "result.json").write_text(json.dumps({"proposal_file": str(proposals.relative_to(census))}))
            manifest = {"candidates": [candidate]}
            verify_selection.validate_census_candidates(census, manifest, mathlib)
            candidate["body_start_byte"] = 0
            with self.assertRaisesRegex(BenchmarkError, "differs from its checked census proposal"):
                verify_selection.validate_census_candidates(census, manifest, mathlib)


class PreparedProofTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.mathlib = self.root / "mathlib"
        (self.mathlib / "Mathlib").mkdir(parents=True)
        self.source = b"import Mathlib.Init\nexample : True := by\n  change True\n  trivial\n"
        (self.mathlib / "Mathlib/Example.lean").write_bytes(self.source)
        start, end = self.source.index(b"by\n"), len(self.source) - 1
        self.candidate = {
            "id": "reviewed", "path": "Mathlib/Example.lean", "status": "replace",
            "start_line": 2, "end_line": 4,
            "source_start_byte": start, "source_end_byte": end,
            "body_start_byte": start, "body_end_byte": end,
            "declaration": "Example.proof", "parent_declaration": "Example.proof",
            "observation_key": "original-proof", "manual_review": True,
            "proof_replacement": "by\n  have h : True := by trivial\n  norm_arith",
        }
        self.update_replacement()
        self.manifest = {"mathlib_revision": "pinned-revision", "files": [{
            "path": "Mathlib/Example.lean", "source_sha256": sha256(self.source),
            "imports": ["NormArith"], "helpers": [],
        }], "candidates": [self.candidate]}
        self.census = self.root / "census"
        self.events = self.census / "files/Mathlib.Example/attempt-01/events.jsonl"
        self.events.parent.mkdir(parents=True)
        self.observation = {
            "type": "observation", "phase": "original", "key": "original-proof",
            "parent_declaration": "Example.proof", "body_start_byte": start, "body_end_byte": end,
            "start_byte": start, "end_byte": end,
        }
        (self.census / "manifest.json").write_text(json.dumps({
            "mathlib_revision": "pinned-revision", "protocol_hash": "old-protocol",
            "implementation_sha256": {"NormArith.lean": "intentionally-old-implementation"},
            "files": [{"path": "Mathlib/Example.lean", "sha256": sha256(self.source)}],
        }))
        self.write_events()

    def update_replacement(self):
        c = self.candidate
        left = self.source.rfind(b"\n", 0, c["source_start_byte"]) + 1
        c["replacement"] = (self.source[left:c["source_start_byte"]]
                            + c["proof_replacement"].encode()
                            + self.source[c["source_end_byte"]:]).decode()

    def write_events(self):
        self.events.write_text(json.dumps(self.observation) + "\n")
        (self.events.parent.parent / "result.json").write_text(json.dumps({
            "complete": True, "status": "complete", "path": "Mathlib/Example.lean",
            "module": "Mathlib.Example", "source_sha256": sha256(self.source),
            "directory": str(self.events.parent.relative_to(self.census)),
            "evidence_sha256": {str(self.events.relative_to(self.census)): sha256(self.events.read_bytes())},
        }))

    def validate_body(self):
        return verify_selection.validate_body_censuses([self.census], self.manifest, self.mathlib)

    def test_prepared_proof_requires_explicit_review_and_exact_reconstruction(self):
        with self.assertRaisesRegex(BenchmarkError, "outside the recorded proof span"):
            verify_selection.validate_proof_spans(self.manifest, self.mathlib)
        verify_selection.validate_proof_spans(self.manifest, self.mathlib, allow_preparation=True)
        self.candidate["manual_review"] = False
        with self.assertRaisesRegex(BenchmarkError, "manual_review"):
            verify_selection.validate_proof_spans(self.manifest, self.mathlib, allow_preparation=True)
        self.candidate["manual_review"] = True
        proof = self.candidate.pop("proof_replacement")
        with self.assertRaisesRegex(BenchmarkError, "proof_replacement"):
            verify_selection.validate_proof_spans(self.manifest, self.mathlib, allow_preparation=True)
        self.candidate["proof_replacement"] = proof
        self.candidate["replacement"] = self.candidate["replacement"].replace(": True :=", ": False :=")
        with self.assertRaisesRegex(BenchmarkError, "outside the recorded proof span"):
            verify_selection.validate_proof_spans(self.manifest, self.mathlib, allow_preparation=True)

    def test_comment_string_and_identifier_mentions_do_not_count_as_a_tactic(self):
        for text in ["by trivial -- norm_arith", "by /- outer /- norm_arith -/ -/ trivial",
                     'by have s := "norm_arith"; trivial', "by exact norm_arith_aux", "by exact norm_arith'"]:
            with self.subTest(text=text):
                self.candidate["proof_replacement"] = text
                self.update_replacement()
                with self.assertRaisesRegex(BenchmarkError, "norm_arith token"):
                    verify_selection.validate_proof_spans(self.manifest, self.mathlib, allow_preparation=True)

    def test_unicode_line_limit_counts_characters_and_all_preparation(self):
        self.candidate["proof_replacement"] = "by\n--" + "λ" * 98 + "\n  norm_arith"
        self.update_replacement()
        verify_selection.validate_proof_spans(self.manifest, self.mathlib, allow_preparation=True)
        self.candidate["proof_replacement"] = self.candidate["proof_replacement"].replace("λ" * 98, "λ" * 99)
        self.update_replacement()
        with self.assertRaisesRegex(BenchmarkError, "100"):
            verify_selection.validate_proof_spans(self.manifest, self.mathlib, allow_preparation=True)

    def test_old_implementation_body_evidence_is_source_bound_and_frozen(self):
        self.observation["start_byte"] = self.observation["end_byte"] - 7
        self.write_events()
        fingerprints, records = self.validate_body()
        self.assertEqual(records[0]["candidate_id"], "reviewed")
        self.assertEqual(records[0]["original_observation_key"], "original-proof")
        self.assertEqual(fingerprints[str(self.events.resolve())], sha256(self.events.read_bytes()))
        self.events.write_text(self.events.read_text() + "\n")
        with self.assertRaisesRegex(BenchmarkError, "frozen input changed"):
            verify_selection.verify_frozen_inputs(fingerprints)
        with self.assertRaisesRegex(CensusError, "evidence changed"):
            self.validate_body()

    def test_forged_declaration_body_or_augmented_only_observation_is_rejected(self):
        for field, value in [("parent_declaration", "Other.proof"), ("body_start_byte", 0), ("phase", "augmented")]:
            with self.subTest(field=field):
                original = dict(self.observation)
                self.observation[field] = value
                self.write_events()
                with self.assertRaisesRegex(BenchmarkError, "original.*body"):
                    self.validate_body()
                self.observation = original
        self.write_events()
        self.candidate["parent_declaration"] = "Other.proof"
        with self.assertRaisesRegex(BenchmarkError, "declaration"):
            self.validate_body()

    def test_missing_proof_span_and_wrong_source_revision_are_rejected(self):
        del self.candidate["source_start_byte"]
        with self.assertRaises((BenchmarkError, KeyError)):
            verify_selection.validate_proof_spans(self.manifest, self.mathlib, allow_preparation=True)
        self.manifest["mathlib_revision"] = "another-revision"
        with self.assertRaisesRegex(BenchmarkError, "revision"):
            self.validate_body()

    def test_incomplete_or_unhashed_file_is_not_body_evidence(self):
        path = self.events.parent.parent / "result.json"
        result = json.loads(path.read_text())
        for change in [{"complete": False}, {"evidence_sha256": {}}]:
            with self.subTest(change=change):
                path.write_text(json.dumps(dict(result, **change)))
                with self.assertRaisesRegex((BenchmarkError, CensusError), "complete|hash|evidence"):
                    self.validate_body()

    def test_actual_source_hash_and_every_selected_body_are_required(self):
        (self.mathlib / "Mathlib/Example.lean").write_bytes(self.source + b" ")
        with self.assertRaisesRegex(BenchmarkError, "source hash mismatch"):
            self.validate_body()
        (self.mathlib / "Mathlib/Example.lean").write_bytes(self.source)
        self.manifest["candidates"].append(dict(self.candidate, id="another-edit", observation_key="absent"))
        with self.assertRaisesRegex(BenchmarkError, "another-edit"):
            self.validate_body()

    def test_manual_flags_cannot_bypass_checked_proposal_mode(self):
        cases = [["--allow-preparation"], ["--body-census", str(self.census)],
                 ["--census", str(self.census), "--allow-preparation", "--body-census", str(self.census)]]
        for flags in cases:
            with self.subTest(flags=flags), contextlib.redirect_stderr(io.StringIO()):
                with self.assertRaises(SystemExit) as error:
                    verify_selection.main(["unused.json", "--output", str(self.root / "unused"), *flags])
                self.assertEqual(error.exception.code, 2)


class CompilationTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.output = self.root / "output"
        self.output.mkdir()
        self.sources = self.output / "sources" / "Mathlib"
        self.sources.mkdir(parents=True)
        self.compiler = self.root / "lean-fixture"
        self.compiler.write_text(f"#!{sys.executable}\n" + '''import json, pathlib, sys
args = sys.argv[1:]
source = pathlib.Path(args[0]).read_text()
setup = json.loads(pathlib.Path(args[args.index('--setup') + 1]).read_text())
if setup['name'] == 'Mathlib.B':
    dependency = pathlib.Path(setup['importArts']['Mathlib.A'][0][0])
    if not dependency.is_file() or 'fresh A' not in dependency.read_text():
        print(json.dumps({'severity': 'error', 'data': 'stale dependency'}))
for flag in ['-o', '-i', '-c']:
    pathlib.Path(args[args.index(flag) + 1]).write_text(source)
if 'FAIL' in source:
    print(json.dumps({'severity': 'error', 'data': 'invalid proof'}))
if 'LONG_LINE_WARNING' in source:
    print(json.dumps({'severity': 'warning', 'kind': 'linter.style.longLine',
                      'data': 'This line exceeds the 100 character limit, please shorten it!',
                      'pos': {'line': 1, 'column': 100}, 'endPos': {'line': 1, 'column': 110}}))
''')
        self.compiler.chmod(0o755)
        self.setups = {
            "Mathlib/B.lean": {"name": "Mathlib.B", "importArts": {"Mathlib.A": [["cached/A.olean"]]}},
            "Mathlib/A.lean": {"name": "Mathlib.A", "importArts": {}},
        }
        self.prepared = [{"path": path, "original": "original " + path} for path in self.setups]
        (self.sources / "A.lean").write_text("fresh A")
        (self.sources / "B.lean").write_text("fresh B")
        self.candidates = [{"id": "a", "path": "Mathlib/A.lean", "status": "replace"},
                           {"id": "b", "path": "Mathlib/B.lean", "status": "replace"}]

    def compile(self):
        with contextlib.redirect_stdout(io.StringIO()):
            return verify_selection.compile_selected(
                self.prepared, self.setups, self.candidates, project=self.root,
                output=self.output, lean=str(self.compiler), environment=dict(os.environ),
                threads=1, timeout=5,
            )

    def test_fresh_affected_dependency_compiles_once_before_its_importer(self):
        rows, excluded = self.compile()
        self.assertEqual([(row["path"], row["status"]) for row in rows],
                         [("Mathlib/A.lean", "verified"), ("Mathlib/B.lean", "verified")])
        self.assertEqual(excluded, {})
        setup = json.loads((self.output / "resolved-setups/Mathlib/B.setup.json").read_text())
        self.assertEqual(setup["importArts"]["Mathlib.A"],
                         [[str(self.output / "artifacts/Mathlib/A.olean")]])
        with self.assertRaisesRegex(BenchmarkError, "reuse"):
            self.compile()

    def test_zero_exit_error_rejects_file_and_blocks_affected_dependents(self):
        (self.sources / "A.lean").write_text("fresh A FAIL")
        rows, excluded = self.compile()
        self.assertEqual([row["status"] for row in rows], ["failed", "blocked_dependency"])
        self.assertEqual(list(excluded), ["a"])
        self.assertEqual(rows[0]["candidate_ids"], ["a"])
        self.assertEqual(rows[0]["replacement_source_sha256"], sha256("fresh A FAIL"))
        self.assertIn("error diagnostic", rows[0]["reason"])
        self.assertIn("source_sha256=" + sha256("original Mathlib/A.lean"), excluded["a"])
        self.assertFalse((self.output / "artifacts/Mathlib/B.olean").exists())

    def test_long_line_warning_rejects_fresh_outputs_and_blocks_dependents(self):
        (self.sources / "A.lean").write_text("fresh A LONG_LINE_WARNING")
        rows, excluded = self.compile()
        self.assertEqual([row["status"] for row in rows], ["failed", "blocked_dependency"])
        self.assertEqual(rows[0]["process"]["returncode"], 0)
        self.assertTrue((self.output / "artifacts/Mathlib/A.olean").is_file())
        self.assertEqual(rows[0]["style_diagnostics"][0]["kind"], "linter.style.longLine")
        self.assertEqual(rows[0]["style_diagnostics"][0]["pos"], {"line": 1, "column": 100})
        self.assertIn("linter.style.longLine", rows[0]["reason"])
        self.assertIn("linter.style.longLine", excluded["a"])
        self.assertFalse((self.output / "artifacts/Mathlib/B.olean").exists())


class VerificationRunTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.project = self.root / "project"
        self.project.mkdir()
        self.mathlib = self.project / ".lake/packages/mathlib"
        (self.mathlib / "Mathlib").mkdir(parents=True)
        source = b"import Mathlib.Init\nexample : True := by\n  change True\n  trivial\n"
        (self.mathlib / "Mathlib/Example.lean").write_bytes(source)
        (self.project / ".gitignore").write_text(".lake/\n")
        for directory in [self.mathlib, self.project]:
            subprocess.run(["git", "init", "-q", str(directory)], check=True)
            subprocess.run(["git", "-C", str(directory), "add", "."], check=True)
            subprocess.run(["git", "-C", str(directory), "-c", "user.name=Test", "-c",
                            "user.email=test@example.org", "commit", "-qm", "fixture", "--allow-empty"], check=True)
        revision = subprocess.check_output(["git", "-C", str(self.mathlib), "rev-parse", "HEAD"], text=True).strip()
        for name, value in {"lean-toolchain": "lean:fixture\n", "lake-manifest.json": "{}\n",
                            "lakefile.toml": 'name = "fixture"\n', "NormArith.lean": "-- fixture\n"}.items():
            (self.project / name).write_text(value)
        proof = b"by\n  change True\n  trivial"
        start = source.index(proof)
        proposal = {"path": "Mathlib/Example.lean", "key": "proof", "status": "success",
                    "kernel_checked": True, "replacement_eligible": True,
                    "source_sha256": sha256(source), "original_sha256": sha256(proof),
                    "start_byte": start, "end_byte": start + len(proof), "replacement": "by norm_arith",
                        "body_start_byte": start, "body_end_byte": start + len(proof)}
        candidate = dict(candidate_from_proposal(proposal, source), status="replace")
        self.manifest = self.root / "manifest.json"
        self.manifest.write_text(json.dumps({
            "schema_version": 1, "mathlib_revision": revision, "selection_status": "integration-trial",
            "files": [{"path": proposal["path"], "source_sha256": sha256(source), "imports": ["NormArith"]}],
            "candidates": [candidate],
        }))
        prefix = self.root / "toolchain"
        (prefix / "bin").mkdir(parents=True)
        lean = prefix / "bin/lean"
        lean.write_text(f"#!{sys.executable}\n" + r'''import json, pathlib, sys
prefix = pathlib.Path(__file__).resolve().parent.parent
args = sys.argv[1:]
if args == ['--print-prefix']:
    print(prefix)
elif args == ['--version']:
    print('Lean fixture')
elif args and args[0] == '--deps-json':
    results = []
    for name in args[1:]:
        imports = [{'module': line.split()[1], 'isExported': True, 'isMeta': False, 'importAll': False}
                   for line in pathlib.Path(name).read_text().splitlines() if line.startswith('import ')]
        results.append({'errors': [], 'result': {'isModule': False, 'imports': imports}})
    print(json.dumps({'imports': results}))
else:
    for flag in ['-o', '-i', '-c']:
        pathlib.Path(args[args.index(flag) + 1]).write_text('fresh artifact')
    if (prefix / 'fail').exists():
        print(json.dumps({'severity': 'error', 'data': 'proof rejected'}))
    if (prefix / 'long-line-warning').exists():
        print(json.dumps({'severity': 'warning', 'kind': 'linter.style.longLine',
                          'data': 'This line exceeds the 100 character limit, please shorten it!'}))
''')
        lean.chmod(0o755)
        self.lake = prefix / "bin/lake-fixture"
        self.lake.write_text(f"#!{sys.executable}\n" + r'''import json, os, pathlib, subprocess, sys
args = sys.argv[1:]
mutation = pathlib.Path(__file__).parent.parent / 'mutate'
if mutation.exists():
    target = pathlib.Path(mutation.read_text())
    target.write_bytes(target.read_bytes() + b' ')
if args[0] == 'env':
    env = dict(os.environ, PATH=str(pathlib.Path(__file__).parent) + os.pathsep + os.environ['PATH'])
    raise SystemExit(subprocess.run(args[1:], env=env).returncode)
if args[0] == 'setup-file':
    path = pathlib.Path(args[1])
    module = '.'.join(path.with_suffix('').parts[path.parts.index('Mathlib'):])
    header = json.loads(args[2])
    print(json.dumps({'name': module, 'importArts': {}, 'isModule': header['isModule'],
                      'options': {'autoImplicit': True},
                      'dynlibs': ([str(pathlib.Path(__file__).parent.parent / 'fixture.dylib')]
                                  if any(i['module'] == 'NormArith' for i in header['imports']) else [])}))
if 'query' in args:
    for query in args[args.index('query') + 1:]:
        module = query.split('+')[1].split(':')[0]
        print(json.dumps({'name': module, 'importArts': {}, 'options': {'autoImplicit': False}}))
''')
        self.lake.chmod(0o755)
        (prefix / "bin/lake").write_bytes(self.lake.read_bytes())
        (prefix / "bin/lake").chmod(0o755)
        (prefix / "fixture.dylib").write_text("native fixture")
        self.prefix = prefix

    def run_verification(self, name, *extra):
        output = self.root / name
        with contextlib.redirect_stdout(io.StringIO()):
            code = verify_selection.main([str(self.manifest), "--project", str(self.project),
                                          "--lake", str(self.lake), "--output", str(output), *extra])
        return code, output, json.loads((output / "verification.json").read_bytes())

    def prepared_body_census(self):
        manifest = json.loads(self.manifest.read_text())
        candidate = manifest["candidates"][0]
        candidate.update(manual_review=True, declaration="Example.proof", parent_declaration="Example.proof",
                         proof_replacement="by\n  change True\n  norm_arith",
                         replacement="example : True := by\n  change True\n  norm_arith\n")
        self.manifest.write_text(json.dumps(manifest))
        census = self.root / "body-census"
        directory = census / "files/Mathlib.Example/attempt-01"
        directory.mkdir(parents=True)
        events = directory / "events.jsonl"
        events.write_text(json.dumps({
            "type": "observation", "phase": "original", "key": candidate["observation_key"],
            "parent_declaration": "Example.proof", "body_start_byte": candidate["body_start_byte"],
            "body_end_byte": candidate["body_end_byte"], "start_byte": candidate["source_start_byte"],
            "end_byte": candidate["source_end_byte"],
        }) + "\n")
        (census / "manifest.json").write_text(json.dumps({
            "mathlib_revision": manifest["mathlib_revision"], "protocol_hash": "source-body-only",
            "files": [{"path": "Mathlib/Example.lean", "sha256": manifest["files"][0]["source_sha256"]}],
        }))
        (directory.parent / "result.json").write_text(json.dumps({
            "complete": True, "status": "complete", "path": "Mathlib/Example.lean", "module": "Mathlib.Example",
            "source_sha256": manifest["files"][0]["source_sha256"], "directory": str(directory.relative_to(census)),
            "evidence_sha256": {str(events.relative_to(census)): sha256(events.read_bytes())},
        }))
        return census, events

    def test_prepared_full_verification_charges_preparation_and_freezes_body_evidence(self):
        census, events = self.prepared_body_census()
        code, output, report = self.run_verification("prepared", "--allow-preparation", "--body-census", str(census))
        self.assertEqual(code, 0)
        self.assertEqual(report["accounting"]["replacement_proof_lines"], 3)
        self.assertEqual(report["accounting"]["added_import_lines"], 1)
        self.assertEqual(report["input_sha256"][str(events.resolve())], sha256(events.read_bytes()))
        self.assertEqual(report["body_census_evidence"][0]["census_protocol_hash"], "source-body-only")
        self.assertTrue((output / "manifest.json").exists())

    def test_body_evidence_drift_during_setup_cannot_emit_verified_manifest(self):
        census, events = self.prepared_body_census()
        (self.prefix / "mutate").write_text(str(events))
        with contextlib.redirect_stderr(io.StringIO()):
            code, output, report = self.run_verification("body-drift", "--allow-preparation", "--body-census", str(census))
        self.assertEqual(code, 1)
        self.assertIn("frozen input changed", report["error"])
        self.assertFalse((output / "manifest.json").exists())

    def test_benchmark_keeps_original_and_replacement_native_setups_separate(self):
        output = self.root / "benchmark"
        manifest = json.loads(self.manifest.read_bytes())
        prepared, _ = benchmark.prepare_sources(manifest, self.mathlib)
        for source in prepared:
            for variant in ["original", "replacement"]:
                path = output / "sources" / variant / source["path"]
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(source[variant])
        args = SimpleNamespace(project=self.project, mathlib=self.mathlib, output=output,
                               lake=str(self.lake), timeout=5, rebuild_tactic=False, skip_setup=True, threads=1)
        report = {"setup": [], "provenance": {}, "manifest": manifest, "measurements": []}
        path = prepared[0]["path"]
        with contextlib.redirect_stdout(io.StringIO()):
            lean, environment, setups = benchmark.setup_environment(args, report, [path])
            benchmark.compile_pass(args, report, prepared, lean, environment, setups, "measured", 0, "original")
            benchmark.compile_pass(args, report, prepared, lean, environment, setups, "measured", 0, "replacement")
        original = json.loads(setups["original"][path].read_bytes())
        replacement = json.loads(setups["replacement"][path].read_bytes())
        self.assertEqual(original["dynlibs"], [])
        self.assertEqual(replacement["dynlibs"], [str(self.prefix / "fixture.dylib")])
        self.assertEqual(original["options"], {"autoImplicit": False})
        self.assertEqual(replacement["options"], original["options"])
        self.assertEqual([row["variant"] for row in report["measurements"]], ["original", "replacement"])

    def test_complete_combined_patch_produces_a_verified_trial_manifest(self):
        code, output, report = self.run_verification("success")
        self.assertEqual(code, 0)
        self.assertEqual(report["status"], "complete")
        final = json.loads((output / "manifest.json").read_bytes())
        self.assertEqual(final["selection_status"], "source-verified-trial")
        self.assertEqual(report["final_manifest_sha256"], sha256((output / "manifest.json").read_bytes()))
        self.assertEqual(json.loads((output / "exclusions.json").read_bytes()), {})
        self.assertTrue(report["files"][0]["artifact_sha256"])
        metadata = report["source_header_setups"]["replacement"]["Mathlib/Example.lean"]
        setup = json.loads(Path(metadata["setup_file"]).read_bytes())
        raw = json.loads(Path(metadata["raw_setup_file"]).read_bytes())
        self.assertEqual(setup["options"], {"autoImplicit": False})
        self.assertEqual(raw["options"], {"autoImplicit": True})
        self.assertEqual(setup["dynlibs"], [str(self.prefix / "fixture.dylib")])

    def test_inputs_changing_during_setup_invalidate_the_run(self):
        (self.prefix / "mutate").write_text(str(self.manifest))
        error = io.StringIO()
        with contextlib.redirect_stderr(error):
            code, output, report = self.run_verification("changed")
        self.assertEqual(code, 1)
        self.assertEqual(report["status"], "failed")
        self.assertIn("frozen input changed", report["error"])
        self.assertFalse((output / "manifest.json").exists())
        self.assertEqual(report["files"], [])

    def test_imported_artifacts_are_frozen_and_later_byte_drift_is_detected(self):
        imported = [self.prefix / "dependency.olean", self.prefix / "dependency.ir.sig"]
        for path in imported:
            path.write_text("imported fixture")
        script = self.lake.read_text()
        script = script.replace("module, 'importArts': {}, 'isModule'",
                                "module, 'importArts': {'Mathlib.FixtureDep': [[str(pathlib.Path(__file__).parent.parent / 'dependency.olean')], [str(pathlib.Path(__file__).parent.parent / 'dependency.ir.sig')]]}, 'isModule'")
        self.lake.write_text(script)
        code, _, report = self.run_verification("imports")
        self.assertEqual(code, 0)
        for path in imported:
            self.assertEqual(report["input_sha256"].get(str(path.resolve())), sha256(path.read_bytes()))
        imported[1].write_text("changed imported fixture")
        with self.assertRaisesRegex(BenchmarkError, "frozen input changed"):
            verify_selection.verify_frozen_inputs(report["input_sha256"])

    def test_failed_source_patch_cannot_emit_a_verified_subset(self):
        (self.prefix / "fail").touch()
        code, output, report = self.run_verification("failure")
        self.assertEqual(code, 1)
        self.assertEqual(report["status"], "failed")
        self.assertFalse((output / "manifest.json").exists())
        rejected = json.loads((output / "exclusions.json").read_bytes())
        selected = json.loads(self.manifest.read_bytes())["candidates"][0]["id"]
        self.assertEqual(list(rejected), [selected])
        self.assertEqual(report["files"][0]["status"], "failed")

    def test_long_line_warning_cannot_emit_a_verified_manifest(self):
        (self.prefix / "long-line-warning").touch()
        code, output, report = self.run_verification("style-failure")
        self.assertEqual(code, 1)
        self.assertEqual(report["status"], "failed")
        self.assertFalse((output / "manifest.json").exists())
        self.assertEqual(report["files"][0]["process"]["returncode"], 0)
        self.assertEqual(report["files"][0]["style_diagnostics"][0]["kind"], "linter.style.longLine")
        selected = json.loads(self.manifest.read_bytes())["candidates"][0]["id"]
        self.assertIn("linter.style.longLine", json.loads((output / "exclusions.json").read_bytes())[selected])


if __name__ == "__main__":
    unittest.main()
