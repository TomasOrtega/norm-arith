"""Maintain exploratory replacements against the pinned original source."""
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
            if event.get('body_start_byte', token_start + 1) <= token_start and event.get('body_end_byte', -1) >= token_end:
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

add('manual-analytic-partial-sums', 'Mathlib/Analysis/Analytic/Basic.lean', 654, 671,
'''  simp only [FormalMultilinearSeries.partialSum] at hz ⊢
  simp only [← sum_range_add_sum_Ico _ hkn]
  norm_arith [hz.le, I z h'z, I y yr']
''', 'Replace the complete final estimate after finite-sum normalization; instantiate quantified tail estimates explicitly.')
add('manual-fderiv-param', 'Mathlib/Analysis/Calculus/FDeriv/Measurable.lean', 835, 852,
'''  have hz' : ‖f a' z - f a z‖ ≤ ε := by
    simpa only [Function.uncurry, dist_eq_norm] using
      (hu (a', z) ha'x'.1 (mem_closedBall.2 dzx)).le
  have hy' : ‖f a' y - f a y‖ ≤ ε := by
    simpa only [Function.uncurry, dist_eq_norm] using
      (hu (a', y) ha'x'.1 (mem_closedBall.2 dyx)).le
  norm_arith [hz', hy', hb y (mem_closedBall.2 dyx) z (mem_closedBall.2 dzx)]
''', 'Instantiate the two uniform distance estimates and the old derivative bound, then discharge the whole strict telescoping estimate.')
add('manual-fderiv-map', 'Mathlib/Analysis/Calculus/FDeriv/Measurable.lean', 164, 170,
'''    ‖f z - f y - (fderiv 𝕜 f x) (z - y)‖ ≤ δ * ‖z - x‖ + δ * ‖y - x‖ := by
      have hz' := hR z (ball_subset_ball hr.2.le hz)
      have hy' := hR y (ball_subset_ball hr.2.le hy)
      simp only [map_sub] at hz' hy' ⊢
      norm_arith [hz', hy']
''', 'Normalize continuous-linear-map subtraction and instantiate local estimates before norm arithmetic.')
add('manual-right-deriv-symbolic', 'Mathlib/Analysis/Calculus/FDeriv/Measurable.lean', 492, 502,
'''    ‖f z - f y - (z - y) • derivWithin f (Ici x) x‖
        ≤ ε / 2 * ‖z - x‖ + ε / 2 * ‖y - x‖ := by
      have hz' := hm ⟨hz.1, hz.2.trans_lt (by linarith [hr.2])⟩
      have hy' := hm ⟨hy.1, hy.2.trans_lt (by linarith [hr.2])⟩
      simp only [sub_smul] at hz' hy' ⊢
      norm_arith [hz', hy']
''', 'Distribute variable real scalar subtraction explicitly, keeping the existing later scalar bounds.')

add('manual-strong-law-sums', 'Mathlib/Probability/StrongLaw.lean', 760, 780,
'''  simp only [Pi.sub_apply] at hn
  have hsum : ‖(n : ℝ)⁻¹ • ∑ i ∈ range n, (X i ω - Y k i ω)‖ ≤ δ := by
    grw [norm_smul, norm_inv, RCLike.norm_natCast, norm_sum_le, ← div_eq_inv_mul, hn.le]
  simp only [sum_sub_distrib, smul_sub] at hsum
  norm_arith
''', 'Prepare only the norm of the average difference; replace the whole final three-part strict estimate.')
add('manual-banach-preimage', 'Mathlib/Analysis/Normed/Operator/Banach.lean', 127, 134,
'''    have I : ‖f x - d • y‖ ≤ 2 * δ := by
      rw [dist_eq_norm] at h₁ h₂
      simp only [x, f.map_sub]
      norm_arith [h₁.le, h₂.le]
''', 'Normalize the linear map and use both local distance approximation bounds.')
add('manual-uniform-lower', 'Mathlib/Analysis/Convex/Uniform.lean', 79, 89,
'''  have hxy' : ε / 3 ≤ ‖x' - y'‖ := by
    have hx'' := (h₂ _ hx hx'.le).trans <| min_le_of_right_le <| min_le_left _ _
    have hy'' := (h₂ _ hy hy'.le).trans <| min_le_of_right_le <| min_le_left _ _
    norm_arith [hx'', hy'', hxy]
''', 'Instantiate the two normalization errors and discharge the complete reverse-triangle estimate.')
add('manual-uniform-upper', 'Mathlib/Analysis/Convex/Uniform.lean', 90, 100,
'''  have hδδ : δ' ≤ δ / 3 := min_le_of_right_le <| min_le_right _ _
  norm_arith [h (h₁ _ hx') (h₁ _ hy') hxy', h₂ _ hx hx'.le, h₂ _ hy hy'.le]
''', 'Replace the complete upper estimate, including the final scalar arithmetic.')

add('manual-asymptotic-smul', 'Mathlib/Analysis/Asymptotics/AsymptoticEquivalent.lean', 256, 263,
'''  have hmul : ‖(φ x - 1) • u x‖ ≤ c / 2 * ‖v x‖ := by
    simpa only [norm_smul] using key
  simp only [Pi.sub_apply, sub_smul, one_smul] at hmul huvx ⊢
  norm_arith [hmul, huvx]
''', 'Prepare the variable-scalar norm bound and distribute scalar subtraction before the additive estimate.')
add('manual-jacobian-cover', 'Mathlib/MeasureTheory/Function/Jacobian.lean', 164, 176,
'''    have hsmall : ‖f y - f x - (f' x) (y - x)‖ ≤ ε * ‖y - x‖ := by
      apply hδ
      rw [inter_comm]
      exact inter_subset_inter_right _ (ball_subset_ball hn.le) hy
    have hop := ContinuousLinearMap.le_opNorm (f' x - f' z) (y - x)
    calc
      _ ≤ ε * ‖y - x‖ + ‖f' x - f' z‖ * ‖y - x‖ := by
        simp only [FunLike.coe_sub, Pi.sub_apply] at hop
        norm_arith [hsmall, hop]
      _ ≤ r (f' z) * ‖y - x‖ := by rw [← add_mul, add_comm]; gcongr
''', 'Instantiate differentiability and operator-norm facts; replace the additive identity and triangle step.')
add('manual-jacobian-dense', 'Mathlib/MeasureTheory/Function/Jacobian.lean', 531, 543,
'''  have ha : ‖(f' x - A) a‖ ≤ (δ + ε) * (‖z‖ + ε) := by
    rw [mul_assoc] at I
    exact (mul_le_mul_iff_right₀ rpos).1 I
  have hop : ‖(f' x - A) (z - a)‖ ≤ ‖f' x - A‖ * ε := by
    apply (ContinuousLinearMap.le_opNorm _ _).trans
    gcongr
    exact mem_closedBall_iff_norm'.1 az
  simp only [FunLike.coe_sub, map_sub, Pi.sub_apply] at ha hop ⊢
  norm_arith [ha, hop]
''', 'Prepare two existing analytic bounds and replace the linear-map decomposition plus norm arithmetic.')
add('manual-lprojection-product', 'Mathlib/Analysis/Normed/Module/MStructure.lean', 144, 150,
'''  · have hp := h₁.Lnorm (Q • x)
    have hq := h₂.Lnorm x
    simp only [sub_smul, one_smul, mul_smul] at hp hq ⊢
    norm_arith
''', 'Use both projection norm equalities after symbolic action preprocessing, replacing the complete triangle argument.')

add('manual-akra-positive-lower', 'Mathlib/Computability/AkraBazzi/GrowsPolynomially.lean', 407, 413,
'''      have hx_scaled := mul_le_mul_of_nonneg_left hx_ub hc₁_mem.le
      have hf_bound := (hf₁ u ⟨hu_lb, hu_ub⟩).1
      norm_arith
''', 'Scale the existing endpoint bound once; combine the local polynomial-growth instance with the real norm bridge.')
add('manual-akra-positive-upper', 'Mathlib/Computability/AkraBazzi/GrowsPolynomially.lean', 415, 420,
'''      have hx_scaled := mul_le_mul_of_nonneg_left hx_lb hc₂_mem.le
      have hf_bound := (hf₁ u ⟨hu_lb, hu_ub⟩).2
      norm_arith
''', 'Scale the existing endpoint bound once and discharge the remaining scalar-norm estimate.')
add('manual-akra-negative-lower', 'Mathlib/Computability/AkraBazzi/GrowsPolynomially.lean', 456, 466,
'''      have hx_scaled := mul_le_mul_of_nonneg_left hx_ub hc₁_mem.le
      have hf_bound := (hf₁ u ⟨hu_lb, hu_ub⟩).1
      norm_arith
''', 'Replace the longer nonpositive branch with an explicit scaled endpoint inequality and checked scalar norm arithmetic.')
add('manual-akra-negative-upper', 'Mathlib/Computability/AkraBazzi/GrowsPolynomially.lean', 468, 476,
'''      have hx_scaled := mul_le_mul_of_nonneg_left hx_lb hc₂_mem.le
      have hf_bound := (hf₁ u ⟨hu_lb, hu_ub⟩).2
      norm_arith
''', 'Replace the nonpositive upper branch after explicit positive scaling of the endpoint inequality.')

add('manual-unitization-lipschitz', 'Mathlib/Analysis/Normed/Algebra/Unitization.lean', 161, 168,
'''    have hs := norm_algebraMap' (𝕜' := A →L[𝕜] A) x.fst
    have hm := (isometry_mul 𝕜 A).norm_map_of_map_zero (map_zero _) x.snd
    norm_arith [hs, hm]
''', 'Provide the two norm-preservation identities; the tactic handles the reverse triangle and max comparison.')
add('manual-unitization-antilipschitz', 'Mathlib/Analysis/Normed/Algebra/Unitization.lean', 178, 183,
'''    have hs := norm_algebraMap' (𝕜' := A →L[𝕜] A) x.fst
    have hm := (isometry_mul 𝕜 A).norm_map_of_map_zero (map_zero _) x.snd
    norm_arith [hs, hm]
''', 'Provide norm-preservation identities and discharge the triangle plus maximum estimate.')
add('manual-finite-measure-additive', 'Mathlib/MeasureTheory/Integral/FinMeasAdditive.lean', 240, 246,
'''  norm_arith [
    (hT.2 s hs hμs).trans
      (mul_le_mul_of_nonneg_right (le_max_left C C') (measureReal_nonneg)),
    (hT'.2 s hs hνs).trans
      (mul_le_mul_of_nonneg_right (le_max_right C C') (measureReal_nonneg))]
''', 'Instantiate the two finite-additive norm bounds and explicitly enlarge their variable scalar coefficients.')

add('manual-banach-preimage-limit', 'Mathlib/Analysis/Normed/Operator/Banach.lean', 198, 206,
'''  have x_ineq : ‖x‖ ≤ (2 * C + 1) * ‖y‖ := by
    have hn := (norm_tsum_le_tsum_norm sNu).trans
      (sNu.tsum_le_tsum ule <| Summable.mul_right _ summable_geometric_two)
    have heq : (∑' n : ℕ, (1 / 2 : ℝ) ^ n * (C * ‖y‖)) =
        (∑' n : ℕ, (1 / 2 : ℝ) ^ n) * (C * ‖y‖) := tsum_mul_right
    rw [heq, tsum_geometric_two] at hn
    norm_arith [hn]
''', 'Prepare the infinite-sum estimate and use the checked scalar norm nonnegativity for the final relaxed bound.')
add('manual-controlled-initial', 'Mathlib/Analysis/Normed/Group/ControlledClosure.lean', 85, 93,
'''    have hnorm₀ : ‖u 0‖ ≤ C * b 0 + C * ‖h‖ := by
      have hv0 : ‖v 0‖ ≤ b 0 + ‖h‖ := by norm_arith [hv₀.le, le_refl ‖h‖]
      have hs := mul_le_mul_of_nonneg_left hv0 hC.le
      norm_arith [hnorm_u 0, hs]
''', 'Derive the initial vector bound, apply the positive scalar once, and combine the existing preimage bound.')
add('manual-controlled-partial-sum', 'Mathlib/Analysis/Normed/Group/ControlledClosure.lean', 100, 109,
'''    have hrest := Finset.sum_le_sum (s := range n) (fun k _ =>
      (hnorm_u (k + 1)).trans (mul_le_mul_of_nonneg_left (hv _ k.succ_pos).le hC.le))
    have hsum := norm_sum_le (range (n + 1)) u
    conv at hsum => rhs; rw [sum_range_succ']
    have heq := sum_range_succ' (fun k ↦ C * b k) n
    dsimp only [s]
    norm_arith [hsum, hrest, hnorm₀, this, heq]
''', 'Charge finite-sum preparation, then combine the finite tail estimate with the geometric scalar bound.')
add('manual-littleo-partial-sum', 'Mathlib/Analysis/Asymptotics/SpecificAsymptotics.lean', 152, 166,
'''  have htail : ‖∑ i ∈ Ico N n, f i‖ ≤ ∑ i ∈ range n, ε / 2 * g i := by
    apply (norm_sum_le_of_le _ (fun i hi => hN _ (mem_Ico.1 hi).1)).trans
    gcongr
    · exact fun i _ _ ↦ mul_nonneg (half_pos εpos).le (hg i)
    · rw [range_eq_Ico]
      exact Ico_subset_Ico zero_le le_rfl
  rw [← mul_sum, ← B n] at htail
  have hn' : ‖∑ i ∈ range N, f i‖ ≤ ε / 2 * ‖∑ i ∈ range n, g i‖ := hn
  rw [← sum_range_add_sum_Ico f Nn]
  norm_arith [htail, hn']
''', 'Prepare the finite tail bound and normalize the split sum, replacing the complete final asymptotic estimate.')
add('manual-dominated-uniform-bound', 'Mathlib/MeasureTheory/Integral/DominatedConvergence.lean', 595, 605,
'''      · have hbase : ‖f q x‖ ≤ M :=
          hM (mem_image_of_mem (fun p : X × ℝ ↦ ‖f.uncurry p‖)
            (show (q, x) ∈ {q} ×ˢ Icc a b from ⟨rfl, h'δ hx⟩))
        norm_arith [hbase, hv p hp x (h'δ hx)]
''', 'Instantiate the compact-image bound with a direct product-membership witness and combine the uniform error estimate.')

add('manual-local-exp-lipschitz', 'Mathlib/Analysis/SpecialFunctions/Exp.lean', 51, 64,
'''  have hbound := exp_bound_sq x (y - x) (hyx.le.trans hr_le)
  have hsq := mul_le_mul hyx.le (le_refl ‖y - x‖) (norm_nonneg _) hr_nonneg
  have hpow := mul_le_mul_of_nonneg_left hsq (norm_nonneg (exp x))
  rw [show x + (y - x) = y by abel] at hbound
  norm_arith [hbound, (norm_smul (y - x) (exp x)).le, hpow]
''', 'Use the existing exponential remainder estimate at the actual increment, prepare its scalar error bound, and combine both norm terms.')
add('manual-log-inverse-denominator', 'Mathlib/Analysis/SpecialFunctions/Complex/LogBounds.lean', 122, 130,
'''  have ht_norm : ‖t * z‖ ≤ ‖z‖ := by
    rw [norm_mul, Complex.norm_of_nonneg ht.1]
    nlinarith [norm_nonneg z]
  norm_arith [ht_norm, norm_one (α := ℂ)]
''', 'Prepare the variable real scalar norm bound and replace the complete reverse-triangle denominator estimate.')
add('manual-log-half', 'Mathlib/Analysis/SpecialFunctions/Complex/LogBounds.lean', 213, 226,
'''  have hlog := norm_log_one_add_le (lt_of_le_of_lt hz one_half_lt_one)
  have hinv : (1 - ‖z‖)⁻¹ ≤ 2 := by
    rw [inv_eq_one_div, div_le_iff₀] <;> linarith
  have hsq : ‖z‖ ^ 2 ≤ ‖z‖ / 2 := by nlinarith [norm_nonneg z]
  have hb : ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 ≤ ‖z‖ / 2 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hinv) (sq_nonneg ‖z‖)]
  norm_arith [hlog, hb]
''', 'Keep the required nonlinear scalar bounds explicit and combine them with the existing logarithm norm estimate.')

for row in rows:
    if row['id'] == 'manual-right-deriv-symbolic':
        row['status'] = 'failed'
        row['reason'] += ' Initial complete-file attempt failed: opaque upper-bound extension found no certificate after sub_smul; retained for diagnosis.'
    if row['id'] == 'manual-uniform-lower':
        row['status'] = 'failed'
        row['reason'] += ' Trials04–06 failed to find a certificate, including the explicit lower norm hypothesis. Retain the baseline proof.'
    if row['id'] in {'manual-unitization-lipschitz', 'manual-unitization-antilipschitz'}:
        row['status'] = 'failed'
        row['reason'] += ' Trial06 failed: opaque upper-bound extension found no certificate; no unsupportedness claim.'

files = []
for path in sorted({r['path'] for r in rows}):
    files.append(dict(path=path, source_sha256=sha((MATHLIB/path).read_bytes()), imports=['NormArith'], helpers=[]))
manifest = dict(schema_version=1, mathlib_revision='2f3c7c8a8949b04a32f9303f59163acffb766996',
                selection_status='exploratory-manual-proposals', files=files, candidates=rows)
(OUT / 'manifest.json').write_text(json.dumps(manifest, ensure_ascii=False, indent=2)+'\n')
print(OUT / 'manifest.json')
