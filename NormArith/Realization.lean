module

public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.Normed.Module.Seminorm.Norm

/-!
# Finite norm observations

The support constraints are equivalent to a realization in a finite real space
with the sup norm. This module proves the semantic result. The tactic and its
certificate checker do not need this module or Hahn–Banach.

Coefficients are rational. No independence assumption is made on the vectors.
The observation type can be empty, and observed norms can be zero.
-/

public section

namespace NormArith.Realization

open scoped BigOperators

variable {ι κ η σ : Type*} [Fintype ι] [Fintype κ]

@[expose] def combination {E : Type*} [AddCommGroup E] [Module ℝ E]
    (a : κ → ℚ) (x : κ → E) : E :=
  ∑ k, (a k : ℝ) • x k

@[expose] def pairing (a : κ → ℚ) (f : κ → ℝ) : ℝ :=
  ∑ k, (a k : ℝ) * f k

/-- Each row has an anchor and bounds every observed vector. -/
structure Supports (a : ι → κ → ℚ) (r : ι → ℝ) (f : ι → κ → ℝ) : Prop where
  nonneg : ∀ j, 0 ≤ r j
  anchor : ∀ j, pairing (a j) (f j) = r j
  bound : ∀ i j, |pairing (a j) (f i)| ≤ r j

/-- Each support row must also vanish on every supplied vector relation. -/
def Annihilates (e : η → κ → ℚ) (f : ι → κ → ℝ) : Prop :=
  ∀ i h, pairing (e h) (f i) = 0

omit [Fintype ι] in
theorem supports_of_vectors {E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] (a : ι → κ → ℚ) (x : κ → E) :
    ∃ f, Supports a (fun j => ‖combination (a j) x‖) f := by
  classical
  choose φ hφ hnorm using fun j => exists_dual_vector'' ℝ (combination (a j) x)
  refine ⟨fun i k => φ i (x k), ?_⟩
  refine ⟨fun j => norm_nonneg _, ?_, ?_⟩
  · intro j
    simpa [pairing, combination, map_sum, map_smul] using hnorm j
  · intro i j
    have h := (φ i).le_opNorm (combination (a j) x)
    have h' := mul_le_mul_of_nonneg_right (hφ i) (norm_nonneg (combination (a j) x))
    simpa [pairing, combination, map_sum, map_smul, Real.norm_eq_abs] using h.trans h'

omit [Fintype ι] in
theorem supports_of_vectors_with_relations {E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] (a : ι → κ → ℚ) (x : κ → E) (e : η → κ → ℚ)
    (he : ∀ h, combination (e h) x = 0) :
    ∃ f, Supports a (fun j => ‖combination (a j) x‖) f ∧ Annihilates e f := by
  classical
  choose φ hφ hnorm using fun j => exists_dual_vector'' ℝ (combination (a j) x)
  refine ⟨fun i k => φ i (x k), ⟨fun j => norm_nonneg _, ?_, ?_⟩, ?_⟩
  · intro j
    simpa [pairing, combination, map_sum, map_smul] using hnorm j
  · intro i j
    have h := (φ i).le_opNorm (combination (a j) x)
    have h' := mul_le_mul_of_nonneg_right (hφ i) (norm_nonneg (combination (a j) x))
    simpa [pairing, combination, map_sum, map_smul, Real.norm_eq_abs] using h.trans h'
  · intro i h
    have hz := congrArg (φ i) (he h)
    simpa [pairing, combination, map_sum, map_smul] using hz

omit [Fintype ι] in
theorem supports_of_seminorm_with_relations {E : Type*} [AddCommGroup E]
    [Module ℝ E] (p : Seminorm ℝ E) (a : ι → κ → ℚ) (x : κ → E)
    (e : η → κ → ℚ) (he : ∀ h, combination (e h) x = 0) :
    ∃ f, Supports a (fun j => p (combination (a j) x)) f ∧ Annihilates e f := by
  let := p.toAddGroupSeminorm.toSeminormedAddCommGroup
  let : NormedSpace ℝ E := ⟨fun c v => (map_smul_eq_mul p c v).le⟩
  exact supports_of_vectors_with_relations a x e he

/-- The columns of the support matrix are the realizing vectors. -/
def columns (f : ι → κ → ℝ) : κ → ι → ℝ := fun k i => f i k

omit [Fintype ι] in
theorem combination_columns (a : κ → ℚ) (f : ι → κ → ℝ) (i : ι) :
    combination a (columns f) i = pairing a (f i) := by
  simp [combination, columns, pairing, Finset.sum_apply]

theorem norm_combination_columns {a : ι → κ → ℚ} {r : ι → ℝ}
    {f : ι → κ → ℝ} (h : Supports a r f) (j : ι) :
    ‖combination (a j) (columns f)‖ = r j := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (h.nonneg j)).2
    intro i
    simpa [combination_columns, Real.norm_eq_abs] using h.bound i j
  · have hn := norm_le_pi_norm (combination (a j) (columns f)) j
    simpa [combination_columns, h.anchor j, Real.norm_eq_abs,
      abs_of_nonneg (h.nonneg j)] using hn

omit [Fintype ι] in
theorem combination_columns_relation {e : η → κ → ℚ} {f : ι → κ → ℝ}
    (h : Annihilates e f) (j : η) : combination (e j) (columns f) = 0 := by
  funext i
  exact (combination_columns (e j) f i).trans (h i j)

/-- Feasible finite constraints have a concrete sup-norm realization. -/
theorem feasible_iff_realizable (a : ι → κ → ℚ) (r : ι → ℝ) :
    (∃ f, Supports a r f) ↔
      ∃ x : κ → ι → ℝ, ∀ j, ‖combination (a j) x‖ = r j := by
  constructor
  · rintro ⟨f, h⟩
    exact ⟨columns f, norm_combination_columns h⟩
  · rintro ⟨x, hx⟩
    obtain ⟨f, hf⟩ := supports_of_vectors a x
    exact ⟨f, by simpa only [hx] using hf⟩

theorem feasible_iff_realizable_with_relations
    (a : ι → κ → ℚ) (r : ι → ℝ) (e : η → κ → ℚ) :
    (∃ f, Supports a r f ∧ Annihilates e f) ↔
      ∃ x : κ → ι → ℝ,
        (∀ j, ‖combination (a j) x‖ = r j) ∧
        (∀ h, combination (e h) x = 0) := by
  constructor
  · rintro ⟨f, hf, he⟩
    exact ⟨columns f, norm_combination_columns hf, combination_columns_relation he⟩
  · rintro ⟨x, hx, he⟩
    obtain ⟨f, hf, hf'⟩ := supports_of_vectors_with_relations a x e he
    exact ⟨f, by simpa only [hx] using hf, hf'⟩

/-- Different families use different coordinate blocks on one common space. -/
noncomputable def blockSeminorm (s : σ) : Seminorm ℝ (σ → ι → ℝ) :=
  (normSeminorm ℝ (ι → ℝ)).comp (LinearMap.proj s)

theorem seminorm_families_realizable
    (a : ι → κ → ℚ) (r : σ → ι → ℝ) (f : σ → ι → κ → ℝ)
    (h : ∀ s, Supports a (r s) (f s)) (e : η → κ → ℚ)
    (he : ∀ s, Annihilates e (f s)) :
    ∃ x : κ → σ → ι → ℝ,
      (∀ s j, blockSeminorm s (combination (a j) x) = r s j) ∧
      (∀ q, combination (e q) x = 0) := by
  refine ⟨fun k s i => f s i k, ?_, ?_⟩
  · intro s j
    change ‖fun i => (combination (a j) (fun k s i => f s i k)) s i‖ = r s j
    have heq : (fun i => (combination (a j) (fun k s i => f s i k)) s i) =
        combination (a j) (columns (f s)) := by
      funext i
      simp [combination, columns, Finset.sum_apply]
    rw [heq]
    exact norm_combination_columns (h s) j
  · intro q
    funext s i
    simpa [combination, pairing, Finset.sum_apply] using he s i q

/-- Every family of real seminorms has the same finite support representation. -/
theorem seminorm_families_feasible_iff
    (a : ι → κ → ℚ) (r : σ → ι → ℝ) (e : η → κ → ℚ) :
    (∃ f : σ → ι → κ → ℝ,
      (∀ s, Supports a (r s) (f s)) ∧ (∀ s, Annihilates e (f s))) ↔
    ∃ x : κ → σ → ι → ℝ,
      (∀ s j, blockSeminorm s (combination (a j) x) = r s j) ∧
      (∀ q, combination (e q) x = 0) := by
  classical
  constructor
  · rintro ⟨f, hf, he⟩
    exact seminorm_families_realizable a r f hf e he
  · rintro ⟨x, hx, he⟩
    choose f hf hf' using fun s =>
      supports_of_seminorm_with_relations (blockSeminorm s) a x e he
    exact ⟨f, fun s => by simpa only [hx] using hf s, hf'⟩

end NormArith.Realization
