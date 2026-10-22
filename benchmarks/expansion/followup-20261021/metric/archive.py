"""Retain source, diagnostics, and independently recounted follow-up evidence."""
import difflib
import hashlib
import json
from pathlib import Path
import runpy
import shutil

ROOT = Path(__file__).resolve().parents[4]
HERE = Path(__file__).resolve().parent
sha = lambda data: hashlib.sha256(data).hexdigest()
lexer = runpy.run_path(str(ROOT/'artifacts/independent-line-count.py'))
lexer['lexical_checks']()
code_lines = lexer['code_lines']
manifest = json.loads((HERE/'confirmed.json').read_bytes())
output = HERE/'trial-evidence'
output.mkdir()
reports, artifact_rows, matches = [], [], {}
for number in (1, 2, 3):
    origin = ROOT/f'.lake/followup-metric-{number:02d}'
    target = output/f'trial-{number:02d}'
    target.mkdir()
    for filename in ('report.json', 'input-manifest.json'):
        shutil.copy2(origin/filename, target/filename)
    for directory in ('logs', 'sources', 'edited-setups', 'resolved-setups', 'setup'):
        shutil.copytree(origin/directory, target/directory)
    shutil.copy2(ROOT/f'.lake/followup-metric-{number:02d}.log', target/'driver.log')
    report = json.loads((origin/'report.json').read_bytes())
    reports.append({'trial': number, 'report_sha256': sha((origin/'report.json').read_bytes()),
                    'outcomes': {row['path']: row['status'] for row in report['files']}})
    for row in report['files']:
        artifacts = []
        for path, expected in row.get('artifact_sha256', {}).items():
            data = Path(path).read_bytes()
            assert data and sha(data) == expected, path
            artifacts.append({'path': path, 'sha256': expected, 'bytes': len(data)})
        artifact_rows.append({'trial': number, 'path': row['path'], 'status': row['status'],
                              'artifacts': artifacts})
        if row['status'] == 'verified':
            matches[row['replacement_source_sha256']] = (origin, row)
files, spans, patch, observations = [], [], [], {}
for specification in manifest['files']:
    path = specification['path']
    before = (ROOT/'.lake/packages/mathlib'/path).read_bytes()
    assert sha(before) == specification['source_sha256']
    assert specification['helpers'] == [] and specification['imports'] == ['NormArith']
    candidates = sorted((c for c in manifest['candidates'] if c['path'] == path),
                        key=lambda c: c['start_line'])
    original_lines = before.decode().splitlines(keepends=True)
    expected = original_lines[:]
    previous = 0
    for candidate in candidates:
        start, end = candidate['start_line'], candidate['end_line']
        assert start > previous
        previous = end
        original_span = ''.join(original_lines[start-1:end])
        assert sha(original_span.encode()) == candidate['original_sha256']
        left, right = candidate['source_start_byte'], candidate['source_end_byte']
        line_left = sum(len(s.encode()) for s in original_lines[:start-1])
        line_right = line_left + len(original_span.encode())
        reconstructed = (before[line_left:left] + candidate['proof_replacement'].encode() +
                         before[right:line_right]).decode()
        assert reconstructed == candidate['replacement']
        assert candidate['body_start_byte'] <= left < right <= candidate['body_end_byte']
        assert max(map(len, candidate['replacement'].splitlines())) <= 100
        origin = ROOT/candidate['origin_event_path']
        found = None
        for line in origin.read_text().splitlines(keepends=True):
            event = json.loads(line)
            if event.get('key') == candidate['observation_key'] and event.get('phase') == 'original':
                assert event['parent_declaration'] == candidate['parent_declaration']
                assert (event['body_start_byte'], event['body_end_byte']) == (
                    candidate['body_start_byte'], candidate['body_end_byte'])
                found = line
                break
        assert found is not None
        observations[(candidate['origin_event_path'], candidate['observation_key'])] = found
        spans.append({'id': candidate['id'], 'path': path, 'start_line': start, 'end_line': end,
                      'original_code_lines': sum(code_lines(original_span)),
                      'replacement_code_lines': sum(code_lines(candidate['replacement']))})
    for candidate in reversed(candidates):
        expected[candidate['start_line']-1:candidate['end_line']] = candidate['replacement'].splitlines(keepends=True)
    matching = []
    for digest, (origin, row) in matches.items():
        if row['path'] != path:
            continue
        after = (origin/'sources'/path).read_bytes()
        assert sha(after) == digest
        patched_lines = after.decode().splitlines(keepends=True)
        assert patched_lines.count('import NormArith\n') == 1
        patched_lines.remove('import NormArith\n')
        if patched_lines == expected:
            matching.append((origin, row, after))
    assert len(matching) == 1, (path, len(matching))
    origin, row, after = matching[0]
    for channel in ('stdout.log', 'stderr.log'):
        data = (Path(row['process']['log_dir'])/channel).read_text()
        for line in data.splitlines():
            try:
                diagnostic = json.loads(line)
            except json.JSONDecodeError:
                assert 'warning:' not in line and 'error:' not in line
            else:
                assert diagnostic.get('severity') not in {'warning', 'error'}
    for label, data in (('original', before), ('patched', after)):
        destination = HERE/'sources'/label/path
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes(data)
    patch.extend(difflib.unified_diff(before.decode().splitlines(keepends=True),
        after.decode().splitlines(keepends=True), fromfile='a/'+path, tofile='b/'+path))
    files.append({'path': path, 'original_sha256': sha(before), 'patched_sha256': sha(after),
                  'verified_trial': str(origin.relative_to(ROOT)),
                  'before_code_lines': sum(code_lines(before.decode())),
                  'after_code_lines': sum(code_lines(after.decode())), 'added_import_lines': 1,
                  'fresh_artifact_count': len(row['artifact_sha256'])})
(HERE/'mathlib.patch').write_text(''.join(patch))
(HERE/'original-body-observations.jsonl').write_text(''.join(observations.values()))
old, new = sum(s['original_code_lines'] for s in spans), sum(s['replacement_code_lines'] for s in spans)
net = sum(row['before_code_lines']-row['after_code_lines'] for row in files)
assert (len(spans), len(files), old, new, net) == (9, 4, 30, 16, 10)
assert net == old-new-len(files)
receipt = {'schema_version': 1, 'status': 'verified_exploratory_source_patch',
    'scope': 'Bounded manual follow-up; complete copied-file compilation; no timing claim; union requires fresh combined verification.',
    'manifest_sha256': sha((HERE/'confirmed.json').read_bytes()),
    'patch_sha256': sha((HERE/'mathlib.patch').read_bytes()),
    'independent_lexer_sha256': sha((ROOT/'artifacts/independent-line-count.py').read_bytes()),
    'replacements': len(spans), 'affected_files': len(files), 'original_proof_code_lines': old,
    'replacement_proof_code_lines': new, 'added_import_code_lines': len(files),
    'added_helper_code_lines': 0, 'net_code_lines_saved': net,
    'files': files, 'proof_spans': spans, 'trials': reports, 'compiler_outputs_rehashed': artifact_rows,
    'retained_files': {str(path.relative_to(HERE)): {'sha256': sha(path.read_bytes()), 'bytes': path.stat().st_size}
        for path in sorted(output.rglob('*')) if path.is_file()}}
(HERE/'receipt.json').write_text(json.dumps(receipt, ensure_ascii=False, indent=2)+'\n')
print(json.dumps({key: receipt[key] for key in ('status','manifest_sha256','patch_sha256','replacements',
    'affected_files','original_proof_code_lines','replacement_proof_code_lines','net_code_lines_saved')}))
