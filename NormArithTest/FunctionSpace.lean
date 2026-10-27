module

import NormArith.FunctionSpace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

open NormArith MeasureTheory
open scoped ENNReal NNReal

set_option linter.unusedVariables false

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ}

example (hf : MemLp f ∞ μ) : ‖hf.toLp f‖ = lpNorm f ∞ μ := by
  analytic_estimate

example (hf : MemLp f ∞ μ) (hg : MemLp g 2 μ) :
    lpNorm (f * g) 2 μ ≤ lpNorm f ∞ μ * lpNorm g 2 μ :=
  finite_lp_mul hf hg

example (hf2 : MemLp f 2 μ) (hf6 : MemLp f 6 μ) :
    lpNorm f 4 μ ≤ lpNorm f 2 μ ^ (1 / 4 : ℝ) * lpNorm f 6 μ ^ (3 / 4 : ℝ) := by
  lp_interpolate 2 6 4

#guard_msgs (drop info) in
example (hf2 : MemLp f 2 μ) (hf6 : MemLp f 6 μ) :
    lpNorm f 4 μ ≤ lpNorm f 2 μ ^ (1 / 4 : ℝ) * lpNorm f 6 μ ^ (3 / 4 : ℝ) := by
  lp_interpolate? 2 6 4

example (hf2 : MemLp f 2 μ) (hfTop : MemLp f ∞ μ) :
    lpNorm f 4 μ ≤ lpNorm f 2 μ ^ (1 / 2 : ℝ) * lpNorm f ∞ μ ^ (1 / 2 : ℝ) := by
  lp_interpolate 2 ∞ 4

example (hf : MemLp f 2 μ) :
    lpNorm f 2 μ ≤ lpNorm f 2 μ ^ (1 : ℝ) * lpNorm f 6 μ ^ (0 : ℝ) := by
  lp_interpolate 2 6 2

example (hf2 : MemLp f 2 μ) (hf6 : MemLp f 6 μ)
    (hg2 : MemLp g 2 μ) (hg6 : MemLp g 6 μ) :
    lpNorm (f * g) 2 μ ≤
      (lpNorm f 2 μ ^ (1 / 4 : ℝ) * lpNorm f 6 μ ^ (3 / 4 : ℝ)) *
      (lpNorm g 2 μ ^ (1 / 4 : ℝ) * lpNorm g 6 μ ^ (3 / 4 : ℝ)) := by
  analytic_estimate

example (u f b du : α → ℝ) (ν S : ℝ) (hν : 0 < ν) (hS : 0 ≤ S)
    (hu : MemLp u 6 μ) (hf : MemLp f (6 / 5) μ)
    (hb : MemLp b 3 μ) (hdu : MemLp du 2 μ)
    (hs : lpNorm u 6 μ ≤ S * lpNorm du 2 μ)
    (hbsmall : S * lpNorm b 3 μ ≤ ν / 2)
    (he : ν * lpNorm du 2 μ ^ 2 ≤
      |∫ x, f x * u x ∂μ| + |∫ x, (b x * du x) * u x ∂μ|) :
    lpNorm du 2 μ ≤ 2 * S * lpNorm f (6 / 5) μ / ν ∧
    lpNorm u 6 μ ≤ 2 * S ^ 2 * lpNorm f (6 / 5) μ / ν := by
  analytic_estimate

example : lpNorm f ∞ (0 : Measure α) = 0 := by simp

example (u f : EuclideanSpace ℝ (Fin 3) → ℝ)
    (b du : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (ν S : ℝ) (hν : 0 < ν) (hS : 0 ≤ S)
    (hu : MemLp u 6) (hf : MemLp f (6 / 5))
    (hb : MemLp b 3) (hdu : MemLp du 2)
    (hs : lpNorm u 6 volume ≤ S * lpNorm du 2 volume)
    (hbsmall : S * lpNorm b 3 volume ≤ ν / 2)
    (he : ν * lpNorm du 2 volume ^ 2 ≤
      |∫ x, f x * u x| + |∫ x, inner ℝ (b x) (du x) * u x|) :
    lpNorm du 2 volume ≤ 2 * S * lpNorm f (6 / 5) volume / ν ∧
    lpNorm u 6 volume ≤ 2 * S ^ 2 * lpNorm f (6 / 5) volume / ν := by
  exact elliptic_lp_pairing_estimate (innerSL ℝ) (norm_innerSL_le ℝ)
    hν hS hu hf hb hdu hs hbsmall he

example (hf : MemLp f 2 μ) : True := by
  fail_if_success
    have : lpNorm f 4 μ ≤ lpNorm f 2 μ ^ (1 / 4 : ℝ) * lpNorm f 6 μ ^ (3 / 4 : ℝ) := by
      lp_interpolate 2 6 4
  fail_if_success
    have : eLpNorm g 2 μ ≤ ENNReal.ofReal (lpNorm g 2 μ) := by analytic_estimate
  trivial

example (ν : Measure α) (hf2 : MemLp f 2 μ) (hf6 : MemLp f 6 ν) : True := by
  fail_if_success
    have : lpNorm f 4 μ ≤ lpNorm f 2 μ ^ (1 / 4 : ℝ) * lpNorm f 6 μ ^ (3 / 4 : ℝ) := by
      lp_interpolate 2 6 4
  trivial

section Mixed

variable {T E F G : Type*} [MeasurableSpace T]
  [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
  [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace ℝ G]
  (ν : Measure T)

local instance : ENNReal.HolderTriple 3 6 2 := by holder_arith
local instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
local instance : Fact ((1 : ℝ≥0∞) ≤ 3) := ⟨by norm_num⟩
local instance : Fact ((1 : ℝ≥0∞) ≤ 6) := ⟨by norm_num⟩
local instance : Fact ((1 : ℝ≥0∞) ≤ ∞) := ⟨le_top⟩

example (B : E →L[ℝ] F →L[ℝ] G)
    (f : Lp (Lp E 3 μ) ∞ ν) (g : Lp (Lp F 6 μ) 2 ν) :
    ‖(B.holderL μ 3 6 2).holder 2 f g‖ ≤ ‖B‖ * ‖f‖ * ‖g‖ := by
  exact mixed_holder_bound μ ν B f g

end Mixed
