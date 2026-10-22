"""Independently audit the follow-up source spans and their selected union."""
from collections import defaultdict
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import runpy

ROOT = Path(__file__).resolve().parents[4]
BASE = ROOT/'benchmarks/expansion/followup-20261021'
sha = lambda data: hashlib.sha256(data).hexdigest()
load = lambda path: json.loads(path.read_bytes())
lexer = runpy.run_path(str(ROOT/'artifacts/independent-line-count.py'))
lexer['lexical_checks']()
code_lines = lexer['code_lines']
read_hashes = {}

def fingerprint(path):
    digest = sha(path.read_bytes())
    read_hashes[str(path.relative_to(ROOT))] = digest
    return digest

def signature(candidate):
    return (candidate['path'], candidate['start_line'], candidate['end_line'],
            candidate['original_sha256'], candidate['replacement'])

def inspect(path):
    manifest = load(path)
    fingerprint(path)
    assert manifest['mathlib_revision'] == '2f3c7c8a8949b04a32f9303f59163acffb766996'
    selected = [c for c in manifest['candidates'] if c['status'] == 'replace']
    assert len({c['id'] for c in selected}) == len(selected)
    assert len({signature(c) for c in selected}) == len(selected)
    grouped = defaultdict(list)
    for candidate in selected:
        grouped[candidate['path']].append(candidate)
    sources, file_rows, span_rows = {}, [], []
    specifications = {f['path']: f for f in manifest['files']}
    assert len(specifications) == len(manifest['files'])
    for name, candidates in sorted(grouped.items()):
        specification = specifications[name]
        assert specification.get('helpers', []) == []
        assert specification['imports'] == ['NormArith']
        data = (ROOT/'.lake/packages/mathlib'/name).read_bytes()
        assert sha(data) == specification['source_sha256']
        lines = data.decode().splitlines(keepends=True)
        offsets, cursor = [], 0
        for line in lines:
            offsets.append(cursor)
            cursor += len(line.encode())
        offsets.append(cursor)
        previous = 0
        for candidate in sorted(candidates, key=lambda c: c['start_line']):
            start, end = candidate['start_line'], candidate['end_line']
            assert previous < start <= end <= len(lines), candidate['id']
            previous = end
            original = ''.join(lines[start-1:end])
            assert sha(original.encode()) == candidate['original_sha256']
            replacement = candidate['replacement']
            assert replacement.endswith('\n')
            assert max(map(len, replacement.splitlines())) <= 100, candidate['id']
            left, right = candidate['source_start_byte'], candidate['source_end_byte']
            assert offsets[start-1] <= left < right <= offsets[end]
            reconstructed = data[offsets[start-1]:left] + candidate['proof_replacement'].encode() + data[right:offsets[end]]
            assert reconstructed.decode() == replacement, candidate['id']
            assert candidate['body_start_byte'] <= left < right <= candidate['body_end_byte']
            assert re.search(r'\bnorm_arith\b', candidate['proof_replacement'])
            before, after = sum(code_lines(original)), sum(code_lines(replacement))
            if 'original_proof_lines' in candidate:
                assert before == candidate['original_proof_lines']
            if 'replacement_proof_lines' in candidate:
                assert after == candidate['replacement_proof_lines']
            span_rows.append({'id': candidate['id'], 'path': name, 'start_line': start, 'end_line': end,
                              'original_code_lines': before, 'replacement_code_lines': after})
        patched = lines[:]
        for candidate in sorted(candidates, key=lambda c: c['start_line'], reverse=True):
            patched[candidate['start_line']-1:candidate['end_line']] = candidate['replacement'].splitlines(keepends=True)
        first = next(i for i, line in enumerate(patched) if re.match(r'(?:(?:public|meta) )*import\b', line))
        assert 'import NormArith\n' not in patched
        patched.insert(first, 'import NormArith\n')
        after = ''.join(patched).encode()
        own_spans = [row for row in span_rows if row['path'] == name]
        before_count, after_count = sum(code_lines(data.decode())), sum(code_lines(after.decode()))
        net = before_count-after_count
        assert net == sum(row['original_code_lines']-row['replacement_code_lines'] for row in own_spans)-1
        assert net > 0, name
        sources[name] = after
        file_rows.append({'path': name, 'original_sha256': sha(data), 'patched_sha256': sha(after),
                          'original_proof_lines': sum(row['original_code_lines'] for row in own_spans),
                          'replacement_proof_lines': sum(row['replacement_code_lines'] for row in own_spans),
                          'added_import_lines': 1, 'net_lines_saved': net})
    totals = {'replacements': len(selected), 'affected_files': len(grouped),
              'original_proof_code_lines': sum(s['original_code_lines'] for s in span_rows),
              'replacement_proof_code_lines': sum(s['replacement_code_lines'] for s in span_rows),
              'added_import_code_lines': len(grouped), 'added_helper_code_lines': 0,
              'net_code_lines_saved': sum(f['net_lines_saved'] for f in file_rows)}
    return manifest, selected, sources, {'manifest': str(path.relative_to(ROOT)),
        'manifest_sha256': sha(path.read_bytes()), 'totals': totals, 'files': file_rows, 'proof_spans': span_rows}

runs = [ROOT/'.lake/census-full-v3', ROOT/'.lake/expansion-discovery-v4']
body_rows, event_cache = [], {}

def validate_body(candidate):
    module = candidate['path'][:-5].replace('/', '.')
    if candidate.get('origin_event_path'):
        paths = [ROOT/candidate['origin_event_path']]
    else:
        paths = [path for run in runs for path in sorted((run/'files'/module).glob('attempt-*/events.jsonl'))]
    expected = (candidate.get('parent_declaration', candidate['declaration']),
                candidate['body_start_byte'], candidate['body_end_byte'])
    matches = []
    for path in paths:
        if path not in event_cache:
            result_path = path.parent.parent/'result.json'
            result = load(result_path)
            census = path.parents[3]
            relative = str(path.relative_to(census))
            assert result['complete'] and result['source_sha256'] == sha((ROOT/'.lake/packages/mathlib'/candidate['path']).read_bytes())
            assert result['evidence_sha256'][relative] == fingerprint(path)
            fingerprint(result_path)
            fingerprint(census/'manifest.json')
            event_cache[path] = {e['key']: e for e in map(json.loads,path.read_text().splitlines())
                                 if e.get('type') == 'observation' and e.get('phase') == 'original'}
        event = event_cache[path].get(candidate['observation_key'])
        if event is not None and (event.get('parent_declaration'),event.get('body_start_byte'),event.get('body_end_byte')) == expected:
            matches.append((path,event))
    assert matches, candidate['id']
    path, event = matches[-1]
    body_rows.append({'candidate_id': candidate['id'], 'path': candidate['path'],
                      'parent_declaration': expected[0], 'body_start_byte': expected[1], 'body_end_byte': expected[2],
                      'original_observation_key': candidate['observation_key'],
                      'events': str(path.relative_to(ROOT)), 'events_sha256': sha(path.read_bytes()),
                      'claim': 'Original declaration body evidence only; replacement soundness requires whole-file compilation.'})

batches, all_new, batch_sources = [], [], {}
for name in ('measure','metric','calculus','analysis'):
    path = BASE/name/'confirmed.json'
    manifest, selected, sources, receipt = inspect(path)
    for candidate in selected:
        validate_body(candidate)
    all_new.extend(selected)
    assert not set(batch_sources)&set(sources), name
    batch_sources.update(sources)
    batches.append(receipt)

baseline_path = ROOT/'benchmarks/expansion/verified-05/manifest.json'
baseline, old, old_sources, baseline_receipt = inspect(baseline_path)
selection_path = BASE/'selection/manifest.json'
selection, chosen, chosen_sources, selection_receipt = inspect(selection_path)
old_signatures, new_signatures, chosen_signatures = map(lambda rows: {signature(c) for c in rows}, (old,all_new,chosen))
assert not old_signatures & new_signatures
assert len(new_signatures) == len(all_new)
assert old_signatures | new_signatures == chosen_signatures
assert not set(old_sources) & set(batch_sources)
assert {**old_sources, **batch_sources} == chosen_sources
assert all(any(all(other.get(k) == value for k,value in candidate.items()) for other in chosen) for candidate in old)
for reference in selection['input_manifests']:
    actual = Path(reference['source'])
    assert fingerprint(actual) == reference['sha256']
    snapshot = selection_path.parent/reference['snapshot']
    assert snapshot.read_bytes() == actual.read_bytes()
    fingerprint(snapshot)
assert selection_receipt['totals'] == {'replacements':117,'affected_files':63,
    'original_proof_code_lines':705,'replacement_proof_code_lines':286,
    'added_import_code_lines':63,'added_helper_code_lines':0,'net_code_lines_saved':356}
assert sum(b['totals']['net_code_lines_saved'] for b in batches) == 46

report_paths = []
for name in ('measure','metric','calculus'):
    m = load(BASE/name/'confirmed.json')
    evidence = m['trial_evidence']
    entries = evidence['reports'] if isinstance(evidence,dict) else evidence
    for entry in entries:
        path = ROOT/entry.get('report',entry.get('path'))
        digest = entry.get('sha256',entry.get('report_sha256'))
        assert fingerprint(path) == digest
        report_paths.append(path)
analysis_report = BASE/'analysis/trials/final-01/report.json'
assert fingerprint(analysis_report) == load(BASE/'analysis/verification-receipt.json')['report_sha256']
report_paths.append(analysis_report)
verified = {}
for report_path in dict.fromkeys(report_paths):
    for row in load(report_path)['files']:
        if row['status'] != 'verified' or row['path'] not in batch_sources:
            continue
        expected = batch_sources[row['path']]
        if row['replacement_source_sha256'] != sha(expected):
            continue
        assert row['process']['returncode'] == 0 and not row['process']['timed_out']
        artifacts = []
        for path, digest in row['artifact_sha256'].items():
            data = Path(path).read_bytes()
            assert data and sha(data) == digest
            artifacts.append({'path': path,'sha256': digest,'bytes': len(data)})
        assert len(artifacts) == 7
        logdir = Path(row['process']['log_dir'])
        for channel in ('stdout.log','stderr.log'):
            for line in (logdir/channel).read_text().splitlines():
                try:
                    diagnostic = json.loads(line)
                except json.JSONDecodeError:
                    assert 'error:' not in line and 'warning:' not in line
                else:
                    assert diagnostic.get('severity') not in {'error','warning'}
        artifact_path = Path(artifacts[0]['path'])
        source_root = Path(str(artifact_path).split('/artifacts/')[0])/'sources'
        assert (source_root/row['path']).read_bytes() == expected
        verified[row['path']] = {'path': row['path'], 'report':str(report_path.relative_to(ROOT)),
             'report_sha256':sha(report_path.read_bytes()), 'original_source_sha256':row['original_source_sha256'],
             'replacement_source_sha256':sha(expected),'artifacts':artifacts}
assert set(verified) == set(batch_sources), (set(batch_sources)-set(verified))

result = {'schema_version':1,'status':'passed', 'created_at_utc':datetime.now(timezone.utc).isoformat(),
    'scope':'Independent literal source/count/body-provenance and selection audit; exploratory batch compiles rechecked. Final combined fresh-source verification is separate. No new timing claim.',
    'method':'Stdlib source rendering and independent comment/string-aware lexer; no benchmark.py or select_expansion.py imports.',
    'checker_source':str(Path(__file__).resolve().relative_to(ROOT)), 'checker_source_sha256':sha(Path(__file__).read_bytes()),
    'lexer_source_sha256':sha((ROOT/'artifacts/independent-line-count.py').read_bytes()),
    'batches':batches,'baseline':baseline_receipt,'selected_union':selection_receipt,
    'baseline_retention':{'retained_byte_identical_replacements':len(old),'dropped':0,'new_replacements':len(all_new),
                          'new_files':len(batch_sources),'new_net_code_lines_saved':46,
                          'duplicate_or_overlapping_active_spans':0,'added_helpers':0,
                          'changes_outside_original_body_ranges_except_imports':0},
    'original_body_matches':body_rows,'checked_batch_compilations':list(verified.values()),'input_sha256':read_hashes}
output = BASE/'independent-audit.json'
with output.open('x') as stream:
    stream.write(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'status':result['status'],'selected':selection_receipt['totals'],
                  'new':result['baseline_retention'],'audit_sha256':sha(output.read_bytes())}))
