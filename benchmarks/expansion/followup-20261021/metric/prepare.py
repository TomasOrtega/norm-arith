"""Prepare additional metric proof replacements against pinned source."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
MATHLIB = ROOT / '.lake/packages/mathlib'
OUT = Path(__file__).resolve().parent

def sha(data):
    return hashlib.sha256(data).hexdigest()

rows = []

def add(identifier, path, start, end, replacement, reason):
    source = (MATHLIB / path).read_bytes()
    lines = source.splitlines(keepends=True)
    first, stop = sum(map(len, lines[:start - 1])), sum(map(len, lines[:end]))
    original = source[first:stop]
    prefix = original[:len(original) - len(original.lstrip())]
    suffix = original[len(original.rstrip()):]
    token_start, token_end = first + len(prefix), stop - len(suffix)
    if not replacement.startswith(prefix.decode()) or not replacement.endswith(suffix.decode()):
        raise ValueError(f'replacement must preserve outer whitespace: {identifier}')
    internal = replacement[len(prefix):-len(suffix)] if suffix else replacement[len(prefix):]
    module = path[:-5].replace('/', '.')
    result = json.loads((ROOT / '.lake/census-full-v3/files' / module / 'result.json').read_text())
    events = ROOT / '.lake/census-full-v3' / result['directory'] / 'events.jsonl'
    enclosing = []
    for line in events.open():
        event = json.loads(line)
        if event.get('type') == 'observation' and event.get('phase') == 'original':
            if (event.get('body_start_byte') is not None and event.get('body_end_byte') is not None
                    and event['body_start_byte'] <= token_start <= token_end <= event['body_end_byte']):
                enclosing.append(event)
    enclosing.sort(key=lambda e: e['body_end_byte'] - e['body_start_byte'])
    provenance = enclosing[0] if enclosing else {}
    rows.append(dict(id=identifier, path=path, status='replace', reason=reason,
                     declaration=provenance.get('parent_declaration'),
                     parent_declaration=provenance.get('parent_declaration'),
                     start_line=start, end_line=end, original_sha256=sha(source[first:stop]),
                     replacement=replacement, proof_replacement=internal, source_start_byte=token_start, source_end_byte=token_end,
                     observation_key=provenance.get('key'),
                     origin_event_path=str(events.relative_to(ROOT)),
                     origin_syntax_kind=provenance.get('syntax_kind'),
                     body_start_byte=provenance.get('body_start_byte'),
                     body_end_byte=provenance.get('body_end_byte'),
                     proof_kind='reviewed_tactic_sequence_or_calc_fragment',
                     manual_review=True))

add('metric-followup-causeq-limit', 'Mathlib/Topology/MetricSpace/CauSeqFilter.lean', 40, 43,
"""      have hn : ‖f.lim - f b‖ < ε := hN b hb
      exact hεs (show dist (f b) f.lim < ε from by norm_arith [hn]))
""", 'Normalize the reversed limit difference through the checked norm arithmetic path.')
add('metric-followup-causeq-cauchy', 'Mathlib/Topology/MetricSpace/CauSeqFilter.lean', 81, 82,
"""    norm_arith
""", 'Use the existing pointwise Cauchy estimate as a distance bound.')
add('metric-followup-sphere-radius-positive', 'Mathlib/Geometry/Euclidean/Sphere/Tangent.lean', 523, 530,
"""      have ha : |s₂.radius - s₁.radius| = s₂.radius - s₁.radius :=
        abs_of_nonneg (by norm_arith [h])
      have hr0 : s₂.radius - s₁.radius ≠ 0 :=
        ne_of_gt (by norm_arith [h, dist_pos.mpr (Ne.symm h0)])
""", 'Combine the center-distance equality with distance nonnegativity and strict positivity.')
add('metric-followup-urysohn-first', 'Mathlib/Topology/UrysohnsLemma.lean', 293, 294,
"""      norm_arith
""", 'Close the first midpoint scalar remainder.')
add('metric-followup-urysohn-second', 'Mathlib/Topology/UrysohnsLemma.lean', 306, 308,
"""      norm_arith [hydl, hydr]
""", 'Combine the two induction bounds after the existing midpoint triangle reductions.')
add('metric-followup-hausdorff-cover', 'Mathlib/Topology/MetricSpace/HausdorffDimension.lean', 567, 569,
"""    norm_arith [hδ ⟨Metric.mem_ball.2 (hzx.trans_lt hnδ), hz⟩,
      mul_le_mul_of_nonneg_right ((le_max_left _ _).trans_lt hn).le (dist_nonneg : 0 ≤ dist z x)]
""", 'Retain explicit monotonicity of the variable coefficient and discharge the distance bound.')
add('metric-followup-hausdorff-lipschitz', 'Mathlib/Topology/MetricSpace/HausdorffDimension.lean', 571, 572,
"""    .of_dist_le_mul fun z ⟨⟨hzt, _⟩, hzb⟩ w ⟨⟨_, hwP⟩, hwb⟩ ↦ hwP z hzt <| by norm_arith
""", 'Use the two ball memberships to bound the distance in the Lipschitz restriction.')
add('metric-followup-sphere-ext-centers', 'Mathlib/Geometry/Euclidean/Sphere/Tangent.lean', 477, 479,
"""  rcases h with ⟨p, h₁, h₂, h⟩
  norm_arith [mem_sphere'.1 h₁, mem_sphere'.1 h₂, dist_add_dist_eq_iff.mpr h]
""", 'Combine the two radius identities with the equality from betweenness.')
add('metric-followup-sphere-int-centers', 'Mathlib/Geometry/Euclidean/Sphere/Tangent.lean', 483, 485,
"""  rcases h with ⟨p, h₁, h₂, h⟩
  norm_arith [mem_sphere'.1 h₁, mem_sphere'.1 h₂, dist_add_dist_eq_iff.mpr h]
""", 'Discharge the internal tangency center-distance equality from the three metric facts.')
files = [dict(path=path, source_sha256=sha((MATHLIB/path).read_bytes()), imports=['NormArith'], helpers=[])
         for path in sorted({row['path'] for row in rows})]
manifest = dict(schema_version=1, mathlib_revision='2f3c7c8a8949b04a32f9303f59163acffb766996',
                selection_status='followup-metric-exploratory', files=files, candidates=rows)
with (OUT/'manifest-v3.json').open('x') as stream:
    json.dump(manifest, stream, ensure_ascii=False, indent=2)
    stream.write('\n')
print(OUT/'manifest-v3.json')
