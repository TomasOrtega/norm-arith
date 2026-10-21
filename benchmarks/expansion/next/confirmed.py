"""Extract exact current proposals whose complete copied files compiled."""
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT/'scripts'))
from benchmark import prepare_sources

HERE = Path(__file__).resolve().parent
manifest = json.loads((HERE/'manifest.json').read_text())
prepared, _ = prepare_sources(manifest, ROOT/'.lake/packages/mathlib')
current = {row['path']: row for row in prepared}
verified, evidence = {}, []
for number in [5]:
    report_path = ROOT/f'.lake/expansion-next-{number:02d}/report.json'
    report = json.loads(report_path.read_text())
    evidence.append(dict(path=str(report_path.relative_to(ROOT)),
                        sha256=hashlib.sha256(report_path.read_bytes()).hexdigest()))
    for row in report['files']:
        if row['status'] != 'verified' or row['path'] not in current:
            continue
        actual = hashlib.sha256(current[row['path']]['replacement'].encode()).hexdigest()
        if actual != row['replacement_source_sha256']:
            continue
        for artifact, digest in row['artifact_sha256'].items():
            data = Path(artifact).read_bytes()
            if not data or hashlib.sha256(data).hexdigest() != digest:
                raise ValueError(f'compiler artifact changed: {artifact}')
        verified[row['path']] = row
for row in verified.values():
    log = Path(row['process']['log_dir'])/'stdout.log'
    for line in log.read_text().splitlines():
        diagnostic = json.loads(line)
        if diagnostic.get('severity') in {'warning', 'error'}:
            raise ValueError(f'compiler diagnostic remains: {row["path"]}: {diagnostic["data"]}')
confirmed = dict(manifest)
confirmed['selection_status'] = 'next-full-file-checked-exploration'
confirmed['files'] = [row for row in manifest['files'] if row['path'] in verified]
confirmed['candidates'] = [row for row in manifest['candidates']
                           if row['status'] == 'replace' and row['path'] in verified]
confirmed['trial_evidence'] = dict(reports=evidence,
    scope='Fresh copied complete-file compilation, including style checks; final union needs combined verification.')
_, accounting = prepare_sources(confirmed, ROOT/'.lake/packages/mathlib')
(HERE/'confirmed.json').write_text(json.dumps(confirmed, ensure_ascii=False, indent=2)+'\n')
(HERE/'confirmed-accounting.json').write_text(json.dumps(accounting, ensure_ascii=False, indent=2)+'\n')
print(json.dumps({k: accounting[k] for k in ['proposed_replacements','original_proof_lines',
    'replacement_proof_lines','added_import_lines','net_lines_saved_including_imports']}))
