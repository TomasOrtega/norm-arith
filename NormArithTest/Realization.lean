module

import NormArith.Realization
import NormArith.SeminormCertificate
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

open scoped BigOperators
open NormArith NormArith.Realization

-- The empty family does not need a nonempty coordinate space.
example (a : Fin 0 → Fin 0 → ℚ) (r : Fin 0 → ℝ) :
    ∃ x : Fin 0 → Fin 0 → ℝ, ∀ j, ‖combination (a j) x‖ = r j := by
  apply (feasible_iff_realizable a r).1
  exact ⟨fun i => Fin.elim0 i, ⟨fun i => Fin.elim0 i,
    fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩⟩

example (a : Fin 2 → Fin 2 → ℚ) :
    Supports a (fun _ => 0) (fun _ _ => 0) := by
  constructor <;> intros <;> simp [pairing]

-- Two observations may have the same vector and the same support row.
example {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (x : E) :
    ∃ f, Supports (fun _ : Fin 2 => ![(1 : ℚ), 0]) (fun _ => ‖x‖) f ∧
      Annihilates (fun _ : Fin 1 => ![(1 : ℚ), -1]) f := by
  have he : ∀ q : Fin 1,
      combination (![(1 : ℚ), -1]) (fun _ : Fin 2 => x) = 0 := by
    intro q
    simp [combination, Fin.sum_univ_two]
  simpa [combination, Fin.sum_univ_two] using
    supports_of_vectors_with_relations (fun _ : Fin 2 => ![(1 : ℚ), 0])
      (fun _ : Fin 2 => x) (fun _ : Fin 1 => ![(1 : ℚ), -1]) he

example : Supports (fun _ : Fin 1 => ![(1 : ℚ)]) (fun _ => 2)
    (fun _ => ![(2 : ℝ)]) := by
  constructor <;> intros <;> norm_num [pairing, Fin.sum_univ_one]

-- A changed radius cannot pass the anchor condition.
example : ¬ Supports (fun _ : Fin 1 => ![(1 : ℚ)]) (fun _ => 3)
    (fun _ => ![(2 : ℝ)]) := by
  intro h
  have ha := h.anchor 0
  norm_num [pairing, Fin.sum_univ_one] at ha

example {E : Type*} [AddCommGroup E] [Module ℝ E] (p : Seminorm ℝ E)
    (a : Fin 3 → Fin 2 → ℚ) (x : Fin 2 → E) :
    ∃ f, Supports a (fun j => p (combination (a j) x)) f := by
  obtain ⟨f, hf, _⟩ := supports_of_seminorm_with_relations p a x
    (fun q : Fin 0 => Fin.elim0 q) (fun q => Fin.elim0 q)
  exact ⟨f, hf⟩

example (a : Fin 2 → Fin 3 → ℚ) (r : Fin 2 → Fin 2 → ℝ)
    (f : Fin 2 → Fin 2 → Fin 3 → ℝ) (h : ∀ s, Supports a (r s) (f s))
    (e : Fin 1 → Fin 3 → ℚ) (he : ∀ s, Annihilates e (f s)) :
    ∃ x : Fin 3 → Fin 2 → Fin 2 → ℝ,
      (∀ s j, blockSeminorm s (combination (a j) x) = r s j) ∧
      (∀ q, combination (e q) x = 0) :=
  seminorm_families_realizable a r f h e he

example {E : Type*} [AddCommGroup E] [Module ℝ E] (p : Seminorm ℝ E)
    (x y : E) : p (x - y) ≤ p x + p y := by
  have h := seminorm_block_certificate p ![x, y] (x - y) 1 ![1, 0] ![0, 1]
    (by norm_num) (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_two, sub_eq_add_neg])
  simpa [Fin.sum_univ_two] using h

example {E : Type*} [AddCommGroup E] [Module ℝ E] (p : Seminorm ℝ E)
    (x y : E) : (0 : ℝ) * p x ≤ ∑ _ : Fin 1, (0 + 0 : ℝ) * p y := by
  exact seminorm_block_certificate p (fun _ : Fin 1 => y) x 0
    (fun _ => 0) (fun _ => 0) (by norm_num) (by simp) (by simp) (by simp)

example (a b : ℝ) (h : a < b) : a < b := by
  exact certificate_lt (fun _ : Fin 0 => 0) (fun _ => 0)
    (fun _ : Fin 1 => a - b) (fun _ => 1) a b 0
    (by simp) (by intro; linarith) (by simp) (by linarith) (by norm_num)
    (by simp)

example (a b : ℝ) (h : a ≤ b) : a ≤ b := by
  exact certificate_le (fun _ : Fin 0 => 0) (fun _ => 0)
    (fun _ : Fin 1 => a - b) (fun _ => 1) a b
    (by simp) (by intro; linarith) (by simp) (by simp)
