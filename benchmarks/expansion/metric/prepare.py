"""Maintain metric prototype replacements against the pinned original source."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
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
                     proof_kind='reviewed_metric_proof',
                     manual_review=True))
add('metric-arzela-ascoli', 'Mathlib/Topology/ContinuousMap/Bounded/ArzelaAscoli.lean', 73, 88,
'''  change dist (f x) (g x) ≤ ε₁
  have F_fg : F (f x') = F (g x') := congr($f_eq_g ⟨x', x'tα⟩)
  have hFg := (hF (g x')).2
  rw [← F_fg] at hFg
  dsimp only [ε₂] at hU hF hFg
  metric_arith [(hU x').2.2 _ hx' _ (hU x').1 hf, (hU x').2.2 _ hx' _ (hU x').1 hg,
    (hF (f x')).2, hFg]
''', 'Instantiate the four existing continuity/discretization bounds and combine a five-point generic metric chain.')
add('metric-kuratowski-tail', 'Mathlib/Topology/MetricSpace/Kuratowski.lean', 68, 82,
'''  have hv : |embeddingOfSubset x b n - embeddingOfSubset x a n| ≤
      dist (embeddingOfSubset x b) (embeddingOfSubset x a) := by
    rw [dist_eq_norm]
    exact lp.norm_apply_le_norm ENNReal.top_ne_zero
      (embeddingOfSubset x b - embeddingOfSubset x a) n
  have hbc := (le_abs_self (embeddingOfSubset x b n - embeddingOfSubset x a n)).trans hv
  rw [← C] at hbc
  metric_arith [hn, hbc]
''', 'Retain the coordinate norm estimate and combine it with the generic reverse-distance inequality and density bound.')
add('metric-bounded-closed-ball', 'Mathlib/Topology/MetricSpace/Bounded.lean', 75, 76,
'''    by metric_arith [show dist y x ≤ r from hy, show dist z x ≤ r from hz]⟩
''', 'Replace the bounded closed-ball triangle calc with explicit distance forms of membership facts.')
add('metric-diameter-closed-ball', 'Mathlib/Topology/MetricSpace/Bounded.lean', 525, 528,
'''    by
      metric_arith [show dist a x ≤ r from h ha, show dist b x ≤ r from h hb]
''', 'Replace the diameter estimate after explicitly applying the subset hypothesis at both points.')
add('metric-contracting-tail', 'Mathlib/Topology/MetricSpace/Contracting.lean', 252, 254,
'''  by metric_arith [hf.dist_le_mul x y]
''', 'Use the existing contraction comparison after the unchanged positive-denominator reduction.')
add('metric-pinat-approximation', 'Mathlib/Topology/MetricSpace/PiNat.lean', 735, 740,
'''    have hx' := A x n
    have hy' := A y n
    rw [← B] at hy'
    dsimp only [g, n] at hx' hy' ⊢
    simp only [pow_succ]; ring_nf
    metric_arith [hx', hy']
''', 'Retain coordinate equality and power normalization, then combine the two approximation distances.')
add('metric-pinat-surjection', 'Mathlib/Topology/MetricSpace/PiNat.lean', 749, 753,
'''    have J : ∀ n : ℕ, dist (g ⟨x, I⟩) y ≤ (1 / 2) ^ n + (1 / 2) ^ n := fun n => by
      metric_arith [A ⟨x, I⟩ n, show dist y (u (x n)) ≤ (1 / 2) ^ n from hx n]
''', 'Replace the whole quantified three-point estimate with explicit applications of its two local bounds.')
add('metric-polish-cauchy-tail', 'Mathlib/MeasureTheory/Constructions/Polish/Basic.lean', 767, 772,
'''      have hm' := ((dist_le_diam_of_mem (hs m).1 (hy m) zsm).trans (hs m).2)
      have hn' := ((dist_le_diam_of_mem (hs n).1 zsn (hy n)).trans (hs n).2)
      metric_arith [hm', hn', u_anti.antitone hmn, dist_triangle (y m) z (y n)]
''', 'Instantiate the two diameter estimates and the decreasing scalar bound before the generic metric triangle.')


add('metric-bcf-limit-bounded', 'Mathlib/Topology/ContinuousMap/Bounded/Basic.lean', 322, 325,
'''      metric_arith [hC x y, fF_bdd x 0, fF_bdd y 0]
''', 'Combine the existing bound and the two uniform approximation comparisons in a generic four-point metric chain.')
add('metric-zero-at-infinity-closed', 'Mathlib/Topology/ContinuousMap/ZeroAtInfty.lean', 436, 439,
'''    metric_arith [show dist (g x) (f x) ≤ dist g.toBCF f from dist_coe_le_dist x,
      show dist g.toBCF f < ε / 2 from mem_ball.1 hg, hx]
''', 'Combine evaluation distance and eventual smallness without the original three-step triangle calc.')

add('metric-polish-open-image', 'Mathlib/MeasureTheory/Constructions/Polish/Basic.lean', 796, 799,
'''      change dist a z < δ
      have hb := (dist_le_diam_of_mem (hs n).1 ha (hy n)).trans (hs n).2
      metric_arith [hb, hn, dist_triangle a (y n) z]
''', 'Instantiate the diameter comparison, then combine it with the convergent sequence distance bound.')
add('metric-polish-complete-copy-triangle', 'Mathlib/Topology/MetricSpace/Polish.lean', 193, 198,
'''  · simp only [dist_eq, ← Real.dist_eq]
    metric_arith
''', 'Unfold only the new distance before using the already existing ambient and real metric instances.')

files = []
for path in sorted({row['path'] for row in rows}):
    files.append(dict(path=path, source_sha256=sha((MATHLIB/path).read_bytes()),
                      imports=['MetricPrototype'], helpers=[]))
manifest = dict(schema_version=1, mathlib_revision='2f3c7c8a8949b04a32f9303f59163acffb766996',
                selection_status='exploratory-metric-proposals', files=files, candidates=rows,
                scope='Scratch generic pseudometric extension; not a production norm_arith result.')
(OUT/'manifest.json').write_text(json.dumps(manifest, ensure_ascii=False, indent=2)+'\n')
print(OUT/'manifest.json')
