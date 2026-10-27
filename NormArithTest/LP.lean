module

import NormArith.Tactic
public meta import NormArith.LP

/-!
Regression tests for compact LP search and checked reconstruction. The direct
oracle tests ensure the new backend runs even when a cheap frontend path could
prove the corresponding mathematical example. Negative tests cover strictness,
typed blocks, missing real homogeneity, and explicit fact selection.
-/

open NormArith.LP

set_option linter.unusedTactic false

#guard checkCertificate
  #[{ str := .lt, coeffs := [(1, 1)] }, { str := .le, coeffs := [(1, -1)] }] #[1, 1]
#guard !checkCertificate
  #[{ str := .le, coeffs := [(1, 1)] }, { str := .le, coeffs := [(1, -1)] }] #[1, 1]
#guard !checkCertificate
  #[{ str := .lt, coeffs := [(1, 1)] }, { str := .le, coeffs := [(1, -1)] }] #[1, 0]
#guard !checkCertificate #[{ str := .lt, coeffs := [(0, -1)] }] #[1]
#guard !checkCertificate #[{ str := .lt, coeffs := [] }] #[]

#guard match encode #[#[1]] #[#[]] #[] { maxNorms := 0 } with
  | .error _ => true
  | .ok _ => false
#guard match encode #[#[1], #[1, 0]] #[#[0], #[1]] #[] with
  | .error _ => true
  | .ok _ => false
#guard match encode #[#[1]] #[#[1]] #[] with
  | .error _ => true
  | .ok _ => false

-- Directly exercise support encoding, the exact simplex oracle, and extraction.
example : True := by
  run_tac do
    let columns : Array (Array Rat) := #[#[1, 0], #[0, 1], #[1, 1]]
    let result ← propose columns #[#[0, 1, 2], #[0, 1, 2], #[0, 1, 2]]
      #[{ str := .lt, coeffs := #[(1, 1), (2, 1), (3, -1)] }]
    unless result.proposals.any (fun p => p.target == 2) do
      throwError "the triangle refutation must recover its sum-vector certificate"
    for p in result.proposals do
      unless NormArith.Search.isDecomposition columns columns[p.target]! p.coefficients do
        throwError "LP returned an invalid decomposition"
  trivial

-- Denominator clearing must also scale row multipliers during extraction.
example : True := by
  run_tac do
    let columns : Array (Array Rat) := #[#[1], #[3 / 2]]
    let result ← propose columns #[#[0, 1], #[0, 1]]
      #[{ str := .lt, coeffs := #[(1, 3 / 2), (2, -1)] }]
    unless result.proposals.any (fun p => p.target == 1) do
      throwError "the rational scaling refutation must recover its target certificate"
  trivial

-- A feasible problem must never be reported as an inconsistency.
example : True := by
  run_tac do
    let succeeded ← try
      let _ ← propose #[#[1], #[1]] #[#[0], #[1]]
        #[{ str := .lt, coeffs := #[(1, 1), (2, -1)] }]
      pure true
    catch _ => pure false
    if succeeded then
      throwError "separate normed-space blocks were incorrectly identified"
  trivial

section

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

set_option norm_arith.forceLP true

-- No three-source decomposition exists in the free four-vector space. This
-- invocation must use compact LP and cannot fall back to reference enumeration.
example (t w x y z : E) (h : (2 : ℝ) • t = w + x + y + z) :
    2 * ‖t‖ ≤ ‖w‖ + ‖x‖ + ‖y‖ + ‖z‖ := by
  norm_arith [h]

-- These affine left sides bypass the frontend's simple upper-bound path.
example (x y : E) : 2 * ‖x‖ ≤ ‖x + y‖ + ‖x - y‖ := by
  norm_arith

example (x y : E) : ‖x‖ + ‖y‖ ≤ ‖x + y‖ + ‖x - y‖ := by
  norm_arith

example (x y : E) (A B L : ℝ)
    (hL : L ≤ ‖x + y‖) (hB : ‖x - y‖ ≤ B) (_hA : ‖x‖ ≤ A) :
    L - B ≤ 2 * ‖x‖ := by
  norm_arith [hL, hB]

example (x y : E) (A B : ℝ)
    (hA : ‖x + y‖ < A) (hB : ‖x - y‖ ≤ B) : 2 * ‖x‖ < A + B := by
  norm_arith [hA, hB]

example (x y : E) (A B : ℝ)
    (hA : ‖x + y‖ ≤ A) (hB : ‖x - y‖ ≤ B) : 2 * ‖x‖ ≤ A + B := by
  fail_if_success
    have : 2 * ‖x‖ < A + B := by norm_arith [hA, hB]
  norm_arith [hA, hB]

example (x : E) : ‖(3 / 2 : ℝ) • x‖ = 3 * ‖x‖ / 2 := by
  norm_arith

example (x y z : E) (h : (5 : ℝ) • x = (2 : ℝ) • y - (3 : ℝ) • z) :
    5 * ‖x‖ ≤ 2 * ‖y‖ + 3 * ‖z‖ := by
  norm_arith [h]

example {F : Type*} [SeminormedAddCommGroup F] [NormedSpace ℝ F]
    (x y : E) (u v : F) :
    2 * ‖x‖ + 2 * ‖u‖ ≤ ‖x + y‖ + ‖x - y‖ + ‖u + v‖ + ‖u - v‖ := by
  norm_arith

example (x y : E) (A B : ℝ)
    (hA : ‖x + y‖ ≤ A) (hB : ‖x - y‖ ≤ B) : 2 * ‖x‖ ≤ A + B := by
  fail_if_success norm_arith [hA]
  norm_arith [hA, hB]

example (x y : E) : 2 * ‖x‖ ≤ ‖x + y‖ + ‖x - y‖ := by
  fail_if_success
    have : 3 * ‖x‖ ≤ ‖x + y‖ + ‖x - y‖ := by norm_arith
  norm_arith

end

-- The old reference path remains available for comparative benchmarks.
set_option norm_arith.useLP false in
example {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (x y : E) : 2 * ‖x‖ ≤ ‖x + y‖ + ‖x - y‖ := by
  norm_arith

-- Real scalar multiplication alone supplies no norm homogeneity theorem.
example {E : Type*} [SeminormedAddCommGroup E] [Module ℝ E]
    (x : E) (A : ℝ) (h : ‖(2 : ℝ) • x‖ ≤ A) : ‖(2 : ℝ) • x‖ ≤ A := by
  fail_if_success
    have : 2 * ‖x‖ ≤ A := by norm_arith [h]
  exact h
