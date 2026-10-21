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
                     proof_kind='reviewed_tactic_sequence_or_calc_fragment',
                     manual_review=True))
add('next-right-deriv-error', 'Mathlib/Analysis/Calculus/FDeriv/Measurable.lean', 491, 507,
"""  have hbound (w : ℝ) (hw : w ∈ Icc x (x + r)) :
      ‖f w - f x - (w - x) • derivWithin f (Ici x) x‖ ≤ ε * r / 2 := by
    apply (hm ⟨hw.1, hw.2.trans_lt (by linarith [hr.2])⟩).trans
    rw [Real.norm_of_nonneg (by linarith [hw.1])]
    nlinarith [hw.2]
  simp only [sub_smul] at hbound ⊢
  norm_arith [hbound y hy, hbound z hz]
""", 'Retain a pointwise scalar estimate before combining the two derivative error norms.')
add('next-besicovitch-separation', 'Mathlib/MeasureTheory/Covering/BesicovitchVectorSpace.lean', 315, 339,
"""  have δnonneg : 0 ≤ δ := by linarith only [hτ, hδ1]
  have D : 0 ≤ 1 - δ / 4 := by linarith only [hδ2]
  have τpos : 0 < τ := zero_lt_one.trans_le hτ
  have I : (1 - δ / 4) * τ ≤ 1 := by
    nlinarith only [mul_nonneg D (sub_nonneg.2 hδ1), sq_nonneg δ]
  have K : 1 - δ / 4 ≤ τ⁻¹ := by rw [inv_eq_one_div, le_div_iff₀ τpos]; exact I
  have hτ' : ∀ k, τ⁻¹ ≤ a.r k := by
    intro k
    rw [inv_eq_one_div, div_le_iff₀ τpos, ← lastr, mul_comm]
    exact a.hlast' k hτ
  rcases a.h inej with (H | H) <;> norm_arith [hτ' i, hτ' j, H.1]
""", 'Preserve the nonlinear reciprocal bound as scalar preparation, then combine either separation case.')
add('next-haar-normalized-inside', 'Mathlib/MeasureTheory/Constructions/HaarToSphere.lean', 179, 183,
"""  have hscaled : ‖(1 - ε / 4) • x‖ = 1 - ε / 4 := by simp [norm_smul, habs, hx]
  have hy₁ : ‖y‖ < 1 := by norm_arith [hy, hscaled]
""", 'Prepare the scaled unit vector norm, then use the local distance bound.')
add('next-haar-normalized-distance', 'Mathlib/MeasureTheory/Constructions/HaarToSphere.lean', 189, 198,
"""  have hscaled : dist ((1 - ε / 4) • x) x = ε / 4 := by
    simp [sub_smul, norm_smul, hx, abs_of_pos hε]
  have huy : dist u y ≤ dist x y := by
    have H : u - y = (1 - ‖y‖) • u := by simp [u, hy₀, sub_smul]
    simpa [dist_eq_norm_sub, H, norm_smul, abs_of_nonneg, hy₁.le, hu₁, hx]
      using dist_triangle x y 0
  norm_arith [hy, hscaled, huy]
""", 'Keep the radial normalization estimate and combine the resulting metric bounds.')
add('next-besicovitch-radial-error', 'Mathlib/MeasureTheory/Covering/BesicovitchVectorSpace.lean', 383, 394,
"""  have hrad : ‖d - a.c j‖ ≤ a.r j - 1 := by
    have hnonneg : 0 ≤ 1 - 2 / ‖a.c j‖ := by
      simpa [div_le_iff₀ (zero_le_two.trans_lt hj)] using hj.le
    rw [← one_smul ℝ (a.c j), hd, ← sub_smul, norm_smul, norm_sub_rev,
      Real.norm_eq_abs, abs_of_nonneg hnonneg, sub_mul]
    field_simp
    linarith only [hcrj]
  norm_arith [A, hrad]
""", 'Retain the normalized radial error estimate and close the reverse triangle calculation.')
add('next-multilinear-insert-tail', 'Mathlib/Analysis/Normed/Module/Multilinear/Basic.lean', 231, 241,
"""      rw [Finset.sum_insert his, mul_add]
      norm_arith [Hrec, I]
""", 'Normalize the inserted sum, then combine the two existing induction estimates.')
add('next-polish-cauchy-estimate', 'Mathlib/MeasureTheory/Constructions/Polish/Basic.lean', 767, 772,
"""      have hm' := ((dist_le_diam_of_mem (hs m).1 (hy m) zsm).trans (hs m).2)
      have hn' := ((dist_le_diam_of_mem (hs n).1 zsn (hy n)).trans (hs n).2)
      norm_arith [hm', hn', u_anti.antitone hmn]
""", 'Instantiate both diameter estimates and combine them with the decreasing scalar sequence.')
add('next-polish-open-image', 'Mathlib/MeasureTheory/Constructions/Polish/Basic.lean', 796, 799,
"""      change dist a z < δ
      have hb := (dist_le_diam_of_mem (hs n).1 ha (hy n)).trans (hs n).2
      norm_arith [hb, hn]
""", 'Expose the ball comparison and combine a diameter bound with the limiting point distance.')
add('next-lattice-inf-distance', 'Mathlib/Analysis/Normed/Order/Lattice.lean', 98, 108,
"""  have h1 : ‖a ⊓ b - c ⊓ b‖ ≤ ‖a - c‖ :=
    solid (abs_inf_sub_inf_le_abs _ _ _)
  have h2 : ‖c ⊓ b - c ⊓ d‖ ≤ ‖b - d‖ := by
    simpa only [inf_comm c] using solid (abs_inf_sub_inf_le_abs b d c)
  norm_arith [h1, h2]
""", 'Use the two lattice contraction bounds and combine them by a norm triangle estimate.')
add('next-lattice-sup-distance', 'Mathlib/Analysis/Normed/Order/Lattice.lean', 111, 121,
"""  have h1 : ‖a ⊔ b - c ⊔ b‖ ≤ ‖a - c‖ :=
    solid (abs_sup_sub_sup_le_abs _ _ _)
  have h2 : ‖c ⊔ b - c ⊔ d‖ ≤ ‖b - d‖ := by
    simpa only [sup_comm c] using solid (abs_sup_sub_sup_le_abs b d c)
  norm_arith [h1, h2]
""", 'Use the two lattice contraction bounds and combine them by a norm triangle estimate.')
add('next-fderiv-shell-bound', 'Mathlib/Analysis/Calculus/FDeriv/Measurable.lean', 180, 194,
"""  have hnear : x + y ∈ closedBall x (r / 2) := by
    simpa only [mem_closedBall, dist_eq_norm, add_sub_cancel_left] using ylt.le
  have hcenter : x ∈ closedBall x (r / 2) := mem_closedBall_self (half_pos hr).le
  have hL1 := le_of_mem_A h₁ hcenter hnear
  have hL2 := le_of_mem_A h₂ hcenter hnear
  have hs : ε * r + ε * r ≤ 4 * ‖c‖ * ε * ‖y‖ := by
    nlinarith [mul_nonneg hε.le (sub_nonneg.2 ley)]
  simp only [add_sub_cancel_left] at hL1 hL2
  simp only [FunLike.coe_sub, Pi.sub_apply]
  norm_arith [hL1, hL2, hs]
""", 'Apply both local derivative estimates at the same two points and preserve the shell scalar bound explicitly.')
files = []
for path in sorted({row['path'] for row in rows}):
    files.append(dict(path=path, source_sha256=sha((MATHLIB/path).read_bytes()),
                      imports=['NormArith'], helpers=[]))
manifest = dict(schema_version=1, mathlib_revision='2f3c7c8a8949b04a32f9303f59163acffb766996',
                selection_status='next-exploratory-proposals', files=files, candidates=rows)
(OUT/'manifest.json').write_text(json.dumps(manifest, ensure_ascii=False, indent=2)+'\n')
print(OUT/'manifest.json')
