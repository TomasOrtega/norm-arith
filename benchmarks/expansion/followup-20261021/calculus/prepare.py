"""Build source-bound follow-up candidates without changing Mathlib."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
OUT = Path(__file__).resolve().parent
MATHLIB = ROOT / '.lake/packages/mathlib'
rows = []
observations = {}

def sha(data):
    return hashlib.sha256(data).hexdigest()

def add(identifier, path, start, end, replacement, reason):
    source = (MATHLIB / path).read_bytes()
    lines = source.splitlines(keepends=True)
    first, stop = sum(map(len, lines[:start - 1])), sum(map(len, lines[:end]))
    original = source[first:stop]
    prefix = original[:len(original) - len(original.lstrip())]
    suffix = original[len(original.rstrip()):]
    token_start, token_end = first + len(prefix), stop - len(suffix)
    assert replacement.startswith(prefix.decode()) and replacement.endswith(suffix.decode())
    assert all(len(line) <= 100 for line in replacement.splitlines())
    internal = replacement[len(prefix):-len(suffix)] if suffix else replacement[len(prefix):]
    module = path[:-5].replace('/', '.')
    result = json.loads((ROOT / '.lake/census-full-v3/files' / module / 'result.json').read_text())
    events = ROOT / '.lake/census-full-v3' / result['directory'] / 'events.jsonl'
    if path not in observations:
        observations[path] = [event for line in events.open() if
            (event := json.loads(line)).get('type') == 'observation'
            and event.get('phase') == 'original' and event.get('body_start_byte') is not None
            and event.get('body_end_byte') is not None]
    enclosing = [e for e in observations[path]
        if e['body_start_byte'] <= token_start <= token_end <= e['body_end_byte']]
    provenance = min(enclosing, key=lambda e: e['body_end_byte'] - e['body_start_byte'])
    rows.append(dict(id='followup-calculus-' + identifier, path=path, status='replace', reason=reason,
        declaration=provenance['parent_declaration'], parent_declaration=provenance['parent_declaration'],
        start_line=start, end_line=end, original_sha256=sha(original), replacement=replacement,
        proof_replacement=internal, source_start_byte=token_start, source_end_byte=token_end,
        observation_key=provenance['key'], origin_event_path=str(events.relative_to(ROOT)),
        origin_syntax_kind=provenance['syntax_kind'], body_start_byte=provenance['body_start_byte'],
        body_end_byte=provenance['body_end_byte'],
        proof_kind='reviewed_tactic_sequence_or_calc_fragment', manual_review=True))

add('finite-witness', 'Mathlib/Analysis/Normed/Module/FiniteDimension.lean', 435, 439,
"""  refine ⟨x, xR, fun y hy => ?_⟩
  norm_arith [hx y (Submodule.subset_span hy)]
""", 'Instantiate the existing Riesz bound directly and reverse the difference norm.')
add('finite-symmetry', 'Mathlib/Analysis/Normed/Module/FiniteDimension.lean', 450, 451,
"""    norm_arith [show 1 ≤ ‖x - y‖ from hxy]
""", 'Reverse the difference norm in the symmetric relation.')
add('contdiff-inside', 'Mathlib/Analysis/Calculus/ContDiff/Convolution.lean', 191, 192,
"""      norm_arith [hC (mem_image_of_mem _ H)]
""", 'Use the continuous image closed-ball estimate directly.')
add('contdiff-outside', 'Mathlib/Analysis/Calculus/ContDiff/Convolution.lean', 193, 195,
"""    · norm_arith [g'_zero _ _ hps hx]
""", 'Use the vanishing derivative outside the support and the positive scalar bound.')
add('uniform-ball', 'Mathlib/Analysis/Calculus/UniformLimitsDeriv.lean', 142, 143,
"""      norm_arith
""", 'Use membership in the ball of minimum radius.')
add('uniform-mvt', 'Mathlib/Analysis/Calculus/UniformLimitsDeriv.lean', 212, 216,
"""    refine lt_of_le_of_lt mvt ?_
    exact (mul_lt_mul_of_pos_left (by norm_arith [hy]) hqpos).trans hq
""", 'Charge the positive scalar multiplication step before the final norm comparison.')
add('convolution-local', 'Mathlib/Analysis/Convolution.lean', 855, 856,
"""    norm_arith [hgδ hpi (show dist x' x₀ < δ by norm_arith), hgi]
""", 'Combine the two local distances and check the domain by the triangle inequality.')
add('convolution-limit', 'Mathlib/Analysis/Convolution.lean', 858, 859,
"""  norm_arith
""", 'Combine the convolution error bound and the local target distance.')
add('picard-ball', 'Mathlib/Analysis/ODE/PicardLindelof.lean', 234, 245,
"""  rw [mem_closedBall, dist_eq_norm]
  have ht : L * |t.1 - t₀.1| ≤ L * max (tmax - t₀) (t₀ - tmin) := by
    gcongr
    exact abs_sub_le_max_sub t.2.1 t.2.2 _
  have hd := α.lipschitzWith.dist_le_mul t t₀
  simp only [Subtype.dist_eq, dist_eq_norm] at hd
  norm_arith [hd.trans (ht.trans h), α.mem_closedBall₀]
""", 'Retain the nonlinear time bound, then combine the Lipschitz and initial-point bounds.')
add('picard-local', 'Mathlib/Analysis/ODE/PicardLindelof.lean', 686, 698,
"""    have hxs : x ∈ s := has (closedBall_subset_ball (half_lt_self ha) hx)
    have hd := hl.norm_sub_le hxs (mem_of_mem_nhds hs)
    have hmul : K * ‖x - x₀‖ ≤ K * a := by
      gcongr
      norm_arith
    norm_arith [hd.trans hmul, hL]
""", 'Retain domain membership and scalar monotonicity before closing the norm triangle bound.')

add('schwartz-antilipschitz', 'Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean', 976, 978,
"""  ‖x‖ ≤ K * ‖g x - g 0‖ := by norm_arith [h'g.le_mul_dist x 0]
""", 'Normalize the existing antilipschitz distance bound in the norm calculation.')
add('schwartz-max', 'Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean', 979, 984,
"""  _ ≤ K * (‖g x‖ + max 1 ‖g 0‖) := by
    gcongr
    norm_arith
""", 'Retain scalar monotonicity and combine the norm triangle with the maximum bound.')
census = json.loads((ROOT / '.lake/expansion-discovery-selection-v4/manifest.json').read_text())
checked = dict(next(c for c in census['candidates'] if c['id'] == 'census-61a56545ce568b55b7fa'))
path = checked['path']
source = (MATHLIB / path).read_bytes()
lines = source.splitlines(keepends=True)
first = sum(map(len, lines[:checked['start_line'] - 1]))
stop = sum(map(len, lines[:checked['end_line']]))
prefix = source[first:checked['source_start_byte']].decode()
suffix = source[checked['source_end_byte']:stop].decode()
proof = checked['replacement'][len(prefix):-len(suffix)]
event = next(e for e in observations[path]
    if e['body_start_byte'] == checked['body_start_byte']
    and e['body_end_byte'] == checked['body_end_byte'])
result = json.loads((ROOT / '.lake/census-full-v3/files' / path[:-5].replace('/', '.') /
                     'result.json').read_text())
checked.update(id='followup-calculus-schwartz-norm', status='replace',
    reason='Reuse the isolated census success after other edits amortize its import.',
    proof_replacement=proof, parent_declaration=event['parent_declaration'],
    observation_key=event['key'], origin_syntax_kind=event['syntax_kind'],
    origin_event_path=str(Path('.lake/census-full-v3') / result['directory'] / 'events.jsonl'),
    proof_kind='reviewed_checked_census', manual_review=True)
rows.append(checked)
paths = sorted({row['path'] for row in rows})
manifest = dict(schema_version=1, mathlib_revision='2f3c7c8a8949b04a32f9303f59163acffb766996',
    selection_status='followup-calculus-exploratory-trial', candidates=rows,
    files=[dict(path=p, source_sha256=sha((MATHLIB / p).read_bytes()),
                imports=['NormArith'], helpers=[]) for p in paths])
(OUT / 'manifest.json').write_text(json.dumps(manifest, ensure_ascii=False, indent=2) + '\n')
print(OUT / 'manifest.json')
