"""Source-bound candidates for a further measure-theory proof review."""

import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
HERE = Path(__file__).resolve().parent
MATHLIB = ROOT / '.lake/packages/mathlib'
CENSUS = ROOT / '.lake/census-full-v3'
rows = []


def digest(data):
    return hashlib.sha256(data).hexdigest()


def add(identifier, path, start, end, replacement):
    source = (MATHLIB / path).read_bytes()
    lines = source.splitlines(keepends=True)
    left, right = sum(map(len, lines[:start - 1])), sum(map(len, lines[:end]))
    original = source[left:right]
    prefix = original[:len(original) - len(original.lstrip())]
    suffix = original[len(original.rstrip()):]
    first, stop = left + len(prefix), right - len(suffix)
    assert replacement.startswith(prefix.decode()) and replacement.endswith(suffix.decode())
    assert all(len(line) <= 100 for line in replacement.splitlines())
    proof = replacement[len(prefix):-len(suffix)] if suffix else replacement[len(prefix):]
    module = path[:-5].replace('/', '.')
    result = json.loads((CENSUS / 'files' / module / 'result.json').read_text())
    assert result['complete']
    events = CENSUS / result['directory'] / 'events.jsonl'
    enclosing = []
    with events.open() as stream:
        for line in stream:
            event = json.loads(line)
            if (event.get('type') == 'observation' and event.get('phase') == 'original'
                    and event.get('body_start_byte') is not None
                    and event.get('body_end_byte') is not None
                    and event['body_start_byte'] <= first < stop <= event['body_end_byte']):
                enclosing.append(event)
    provenance = min(enclosing, key=lambda event: event['body_end_byte'] - event['body_start_byte'])
    rows.append(dict(
        id=identifier, path=path, status='replace', reason='reviewed_followup',
        declaration=provenance['parent_declaration'],
        parent_declaration=provenance['parent_declaration'],
        start_line=start, end_line=end, original_sha256=digest(original),
        replacement=replacement, proof_replacement=proof,
        source_start_byte=first, source_end_byte=stop,
        observation_key=provenance['key'], origin_event_path=str(events.relative_to(ROOT)),
        origin_syntax_kind=provenance.get('syntax_kind'),
        body_start_byte=provenance['body_start_byte'], body_end_byte=provenance['body_end_byte'],
        proof_kind='reviewed_tactic_sequence_or_calc_fragment', manual_review=True))


add('followup-density-center', 'Mathlib/MeasureTheory/Covering/DensityTheorem.lean', 104, 106,
    "    norm_arith [mem_closedBall'.1 (H (mem_closedBall_self rpos.le))]\n")
add('followup-density-triangle', 'Mathlib/MeasureTheory/Covering/DensityTheorem.lean', 127, 128,
    '    norm_arith\n')
add('followup-smooth-pointwise', 'Mathlib/Analysis/Normed/Lp/SmoothApprox.lean', 73, 75,
    '  exact fun x => by norm_arith [hg₂ x]\n')
add('followup-besicovitch-self', 'Mathlib/MeasureTheory/Covering/Besicovitch.lean', 179, 181,
    '  · rcases top_le_iff.1 H with rfl\n    norm_arith [a.rpos (last N)]\n')
add('followup-resolvent-separation', 'Mathlib/MeasureTheory/Measure/ResolventTransform.lean', 157, 166,
    "    have hx' := infDist_le_dist_of_mem (x := a) (s := algebraMap 𝕜 A '' μ.support)\n"
    "      (y := algebraMap 𝕜 A x) ⟨x, hx, rfl⟩\n"
    "    change dist w a < infDist a (algebraMap 𝕜 A '' μ.support) / 2 at hw\n"
    "    norm_arith [hx', hw]\n")

previous = json.loads((ROOT / 'benchmarks/expansion/verified-05/manifest.json').read_text())
for path, start in [('Mathlib/MeasureTheory/Covering/DensityTheorem.lean', 90),
                    ('Mathlib/MeasureTheory/Covering/Besicovitch.lean', 167)]:
    old = next(row for row in previous['candidates'] if row['path'] == path and row['start_line'] == start)
    rows.append(dict(old, status='replace'))

manifest = dict(schema_version=1, mathlib_revision=previous['mathlib_revision'],
                selection_status='followup-exploratory-proposals',
                files=[dict(path=path, source_sha256=digest((MATHLIB / path).read_bytes()),
                            imports=['NormArith'], helpers=[])
                       for path in sorted({row['path'] for row in rows})], candidates=rows)
(HERE / 'manifest.json').write_text(json.dumps(manifest, ensure_ascii=False, indent=2) + '\n')
print(f'{len(rows)} candidates in {len(manifest["files"])} files')
