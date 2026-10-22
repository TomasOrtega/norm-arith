"""Retain complete-file successes and preserve every measure-theory trial."""

import hashlib
import json
from pathlib import Path
import shutil
import sys

ROOT = Path(__file__).resolve().parents[4]
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / 'scripts'))
from benchmark import prepare_sources


def digest(data):
    return hashlib.sha256(data).hexdigest()


manifest = json.loads((HERE / 'manifest.json').read_text())
prepared, _ = prepare_sources(manifest, ROOT / '.lake/packages/mathlib')
current = {row['path']: digest(row['replacement'].encode()) for row in prepared}
verified, reports = {}, []
for number in [1, 2, 3]:
    trial = ROOT / f'.lake/followup-measure-{number:02d}'
    archive = HERE / 'trials' / trial.name
    for path in [trial / 'report.json', trial / 'input-manifest.json',
                 *sorted((trial / 'logs').rglob('*.log'))]:
        target = archive / path.relative_to(trial)
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(path, target)
    report = json.loads((trial / 'report.json').read_text())
    reports.append(dict(path=str((archive / 'report.json').relative_to(ROOT)),
                        sha256=digest((trial / 'report.json').read_bytes())))
    for row in report['files']:
        if row['status'] != 'verified' or current.get(row['path']) != row['replacement_source_sha256']:
            continue
        for artifact, expected in row['artifact_sha256'].items():
            data = Path(artifact).read_bytes()
            assert data and digest(data) == expected, artifact
        log_dir = Path(row['process']['log_dir'])
        assert not (log_dir / 'stderr.log').read_text().strip(), row['path']
        for line in (log_dir / 'stdout.log').read_text().splitlines():
            assert json.loads(line).get('severity') not in {'warning', 'error'}, row['path']
        verified[row['path']] = row

confirmed = dict(manifest)
confirmed['selection_status'] = 'followup-complete-file-checked-exploration'
confirmed['files'] = [row for row in manifest['files'] if row['path'] in verified]
confirmed['candidates'] = [row for row in manifest['candidates'] if row['path'] in verified]
confirmed['trial_evidence'] = dict(reports=reports,
    scope='Fresh copied complete-file compilation; final union needs combined verification.')
_, accounting = prepare_sources(confirmed, ROOT / '.lake/packages/mathlib')
for name, value in [('confirmed.json', confirmed), ('confirmed-accounting.json', accounting)]:
    (HERE / name).write_text(json.dumps(value, ensure_ascii=False, indent=2) + '\n')
print(json.dumps({key: accounting[key] for key in ['proposed_replacements',
    'original_proof_lines', 'replacement_proof_lines', 'added_import_lines',
    'net_lines_saved_including_imports']}))
