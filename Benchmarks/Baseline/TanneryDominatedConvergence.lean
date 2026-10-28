/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
/-
Standalone exact theorem from Mathlib/Analysis/Normed/Group/Tannery.lean.
Pinned source and adaptations: Benchmarks/manifest.json (TanneryDominatedConvergence).
-/
module

import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic

open Filter
open scoped Topology

-- BENCHMARK-STATEMENT
example {α β G : Type*} {𝓕 : Filter α}
    [NormedAddCommGroup G] [CompleteSpace G]
    {f : α → β → G} {g : β → G} {bound : β → ℝ} (h_sum : Summable bound)
    (hab : ∀ k : β, Tendsto (f · k) 𝓕 (𝓝 (g k)))
    (h_bound : ∀ᶠ n in 𝓕, ∀ k, ‖f n k‖ ≤ bound k) :
    Tendsto (∑' k, f · k) 𝓕 (𝓝 (∑' k, g k)) := by
  -- BENCHMARK-PROOF
  -- WLOG β is nonempty
  rcases isEmpty_or_nonempty β
  · simpa only [tsum_empty] using tendsto_const_nhds
  -- WLOG 𝓕 ≠ ⊥
  rcases 𝓕.eq_or_neBot with rfl | _
  · simp only [tendsto_bot]
  -- Auxiliary lemmas
  have h_g_le (k : β) : ‖g k‖ ≤ bound k :=
    le_of_tendsto (tendsto_norm.comp (hab k)) <| h_bound.mono (fun n h => h k)
  have h_sumg : Summable (‖g ·‖) :=
    h_sum.of_norm_bounded (fun k ↦ (norm_norm (g k)).symm ▸ h_g_le k)
  have h_suma : ∀ᶠ n in 𝓕, Summable (‖f n ·‖) := by
    filter_upwards [h_bound] with n h
    exact h_sum.of_norm_bounded <| by simpa only [norm_norm] using h
  -- Now main proof, by an `ε / 3` argument
  rw [Metric.tendsto_nhds]
  intro ε hε
  let ⟨S, hS⟩ := h_sum
  obtain ⟨T, hT⟩ : ∃ (T : Finset β), dist (∑ b ∈ T, bound b) S < ε / 3 := by
    rw [HasSum, Metric.tendsto_nhds] at hS
    exact Eventually.exists <| hS _ (by positivity)
  have h1 : ∑' (k : (Tᶜ : Set β)), bound k < ε / 3 := by
    calc _ ≤ ‖∑' (k : (Tᶜ : Set β)), bound k‖ := Real.le_norm_self _
         _ = ‖S - ∑ b ∈ T, bound b‖ := congrArg _ ?_
         _ < ε / 3 := by rwa [dist_eq_norm, norm_sub_rev] at hT
    simpa only [h_sum.sum_add_tsum_compl, eq_sub_iff_add_eq'] using hS.tsum_eq
  have h2 : Tendsto (∑ k ∈ T, f · k) 𝓕 (𝓝 (T.sum g)) := tendsto_finsetSum _ (fun i _ ↦ hab i)
  rw [Metric.tendsto_nhds] at h2
  filter_upwards [h2 (ε / 3) (by positivity), h_suma, h_bound] with n hn h_suma h_bound
  rw [dist_eq_norm, ← h_suma.of_norm.tsum_sub h_sumg.of_norm,
    ← (h_suma.of_norm.sub h_sumg.of_norm).sum_add_tsum_compl (s := T),
    (by ring : ε = ε / 3 + (ε / 3 + ε / 3))]
  refine (norm_add_le _ _).trans_lt (add_lt_add ?_ ?_)
  · simpa only [dist_eq_norm, Finset.sum_sub_distrib] using hn
  · rw [(h_suma.subtype _).of_norm.tsum_sub (h_sumg.subtype _).of_norm]
    refine (norm_sub_le _ _).trans_lt (add_lt_add ?_ ?_)
    · refine ((norm_tsum_le_tsum_norm (h_suma.subtype _)).trans ?_).trans_lt h1
      exact (h_suma.subtype _).tsum_le_tsum (h_bound ·) (h_sum.subtype _)
    · refine ((norm_tsum_le_tsum_norm <| h_sumg.subtype _).trans ?_).trans_lt h1
      exact (h_sumg.subtype _).tsum_le_tsum (h_g_le ·) (h_sum.subtype _)
  -- BENCHMARK-END
