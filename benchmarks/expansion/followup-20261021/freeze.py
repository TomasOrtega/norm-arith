"""Archive the checked follow-up without changing the published study."""

from collections import defaultdict
import difflib
import gzip
import hashlib
import io
import json
from pathlib import Path
import shutil
import sys
import tarfile

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
RAW = ROOT / '.lake/followup-combined-02'
OUT = HERE / 'verified'
sys.path.insert(0, str(ROOT / 'scripts'))
from benchmark import code_line_count, prepare_sources


def digest(data):
    return hashlib.sha256(data).hexdigest()


def write_json(path, value):
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + '\n')


report = json.loads((RAW / 'verification.json').read_text())
assert report['status'] == 'complete'
assert all(row['status'] == 'verified' for row in report['files'])
audit = json.loads((HERE / 'independent-audit.json').read_text())
assert audit['status'] == 'passed'
artifacts = {}
for row in report['files']:
    assert not row['style_diagnostics'], row['path']
    log_dir = Path(row['process']['log_dir'])
    assert not (log_dir / 'stderr.log').read_text().strip(), row['path']
    for line in (log_dir / 'stdout.log').read_text().splitlines():
        assert json.loads(line).get('severity') not in {'warning', 'error'}, row['path']
    for name, expected in row['artifact_sha256'].items():
        path = Path(name)
        data = path.read_bytes()
        assert data and digest(data) == expected, name
        artifacts[str(path.relative_to(RAW))] = dict(sha256=expected, bytes=len(data))
for name, expected in report['input_sha256'].items():
    assert digest(Path(name).read_bytes()) == expected, name

baseline = json.loads((ROOT / 'benchmarks/expansion/verified-05/manifest.json').read_text())
manifest = json.loads((RAW / 'manifest.json').read_text())
assert digest((RAW / 'manifest.json').read_bytes()) == report['final_manifest_sha256']
old = {row['id']: row for row in baseline['candidates'] if row['status'] == 'replace'}
selected = {row['id']: row for row in manifest['candidates'] if row['status'] == 'replace'}
for key, row in old.items():
    assert all(selected[key][field] == row[field] for field in [
        'path', 'start_line', 'end_line', 'replacement', 'original_sha256',
        'source_start_byte', 'source_end_byte']), key
extra = [row for key, row in selected.items() if key not in old]
old_paths = {row['path'] for row in old.values()}
new_paths = {row['path'] for row in extra}
assert not old_paths & new_paths
additional = dict(manifest, candidates=extra,
    files=[row for row in manifest['files'] if row['path'] in new_paths],
    selection_status='source-verified-as-part-of-combined-followup')
additional['combined_source_verification'] = additional.pop('source_verification')
prepared, accounting = prepare_sources(additional, ROOT / '.lake/packages/mathlib')
patch = ''.join(line for row in prepared for line in difflib.unified_diff(
    row['original'].splitlines(keepends=True), row['replacement'].splitlines(keepends=True),
    fromfile='a/' + row['path'], tofile='b/' + row['path']))
by_path = defaultdict(list)
for row in extra:
    by_path[row['path']].append(row)
files = []
for row in prepared:
    assert digest(row['replacement'].encode()) == next(
        item['replacement_source_sha256'] for item in report['files'] if item['path'] == row['path'])
    before = code_line_count(row['original'])
    after = code_line_count(row['replacement'])
    files.append(dict(path=row['path'], replacements=len(by_path[row['path']]),
                      original_file_code_lines=before, replacement_file_code_lines=after,
                      net_lines_saved=before - after,
                      declarations=sorted({item['declaration'] for item in by_path[row['path']]})))
assert sum(row['net_lines_saved'] for row in files) == accounting['net_lines_saved_including_imports']

OUT.mkdir(exist_ok=False)
for name in ['manifest.json', 'input-manifest.json', 'mathlib.patch']:
    shutil.copyfile(RAW / name, OUT / name)
write_json(OUT / 'additional-manifest.json', additional)
(OUT / 'additional.patch').write_text(patch)
write_json(OUT / 'artifact-index.json', artifacts)
(OUT / 'verification.json.gz').write_bytes(gzip.compress((RAW / 'verification.json').read_bytes(), mtime=0))
archive_index = {}
with (OUT / 'raw-verification.tar.gz').open('wb') as destination:
    with gzip.GzipFile(fileobj=destination, mode='wb', mtime=0, filename='') as compressed:
        with tarfile.open(fileobj=compressed, mode='w') as archive:
            for path in sorted(RAW.rglob('*')):
                relative = path.relative_to(RAW)
                if not path.is_file() or relative.parts[0] == 'artifacts':
                    continue
                data = path.read_bytes()
                archive_index[str(relative)] = dict(sha256=digest(data), bytes=len(data))
                info = tarfile.TarInfo(str(relative))
                info.size, info.mode, info.mtime = len(data), 0o644, 0
                archive.addfile(info, io.BytesIO(data))
with tarfile.open(OUT / 'raw-verification.tar.gz', 'r:gz') as archive:
    assert set(archive.getnames()) == set(archive_index)
    for member in archive.getmembers():
        data = archive.extractfile(member).read()
        assert digest(data) == archive_index[member.name]['sha256'], member.name
        assert len(data) == archive_index[member.name]['bytes'], member.name
assert gzip.decompress((OUT / 'verification.json.gz').read_bytes()) == (RAW / 'verification.json').read_bytes()
write_json(OUT / 'raw-verification-index.json', archive_index)
old_receipt = json.loads((ROOT / 'benchmarks/expansion/verified-05/verification-receipt.json').read_text())
counts = ['proposed_replacements', 'original_proof_lines', 'replacement_proof_lines',
          'added_import_lines', 'added_helper_lines', 'net_lines_saved_including_imports']
for key in counts:
    assert old_receipt['accounting'][key] + accounting[key] == report['accounting'][key], key
summary = dict(status='complete', mathlib_revision=manifest['mathlib_revision'],
    lean_version=report['lean_version'],
    baseline={**{key: old_receipt['accounting'][key] for key in counts}, 'files': len(old_paths)},
    additional={**{key: accounting[key] for key in counts}, 'files': len(new_paths)},
    combined={**{key: report['accounting'][key] for key in counts}, 'files': len(report['files'])},
    baseline_edits_retained_exactly=len(old), fresh_artifacts=len(artifacts),
    timing_status='untimed; the published speedup applies only to the earlier 46-file workload',
    files=sorted(files, key=lambda row: (-row['net_lines_saved'], row['path'])),
    verification_receipt_sha256=digest((RAW / 'verification.json').read_bytes()),
    combined_patch_sha256=digest((OUT / 'mathlib.patch').read_bytes()),
    additional_patch_sha256=digest((OUT / 'additional.patch').read_bytes()),
    independent_audit_sha256=digest((HERE / 'independent-audit.json').read_bytes()),
    no_build_wrapper_sha256=digest((HERE / 'lake-no-build').read_bytes()))
write_json(OUT / 'summary.json', summary)
write_json(OUT / 'inventory.json', {path.name: dict(sha256=digest(path.read_bytes()), bytes=path.stat().st_size)
    for path in sorted(OUT.iterdir()) if path.is_file()})
print(json.dumps({key: summary[key] for key in ['status', 'additional', 'combined', 'fresh_artifacts']}))
