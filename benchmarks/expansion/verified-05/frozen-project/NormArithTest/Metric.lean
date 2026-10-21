module

import NormArith

section

variable {X : Type*} [PseudoMetricSpace X]

example (a b c : X) : dist a c ≤ dist a b + dist b c := by norm_arith

example (a b c : X) (r s : ℝ) (h : dist a b ≤ r) (h' : dist b c < s) :
    dist a c < r + s := by norm_arith

example (a b c d : X) (r s t : ℝ) (h : dist a b ≤ r) (h' : dist c b ≤ s)
    (h'' : dist c d ≤ t) : dist a d ≤ r + s + t := by norm_arith

example (a b c : X) : dist a b - dist a c ≤ dist b c := by norm_arith

example (a b : X) : dist a b = dist b a := by norm_arith

example (a : X) : dist a a = 0 := by norm_arith

example (a b : X) : 0 ≤ dist a b := by norm_arith

example (a b c : X) (r s : ℝ) (h : dist a b ≤ r) (h' : dist b c < s) :
    dist a c < r + s := by
  fail_if_success norm_arith [h]
  norm_arith [h, h']

example (a b : X) (r s : ℝ) (h : dist a b ≤ r) (hr : r ≤ s) :
    dist a b ≤ s := by norm_arith [h]

example (a b : X) (r : ℝ) (h : dist a b ≤ r) : 0 ≤ r := by norm_arith [h]

example (a b : X) (r x : ℝ) (hm : dist a b ≤ r) (_hn : ‖x‖ ≤ 1) :
    0 ≤ r := by norm_arith [hm]

example (a b : X) (r x : ℝ) (_hm : dist a b ≤ 1) (hn : ‖x‖ ≤ r) :
    0 ≤ r := by norm_arith [hn]

example {Y : Type*} [PseudoMetricSpace Y] (a b c : X) (u v w : Y)
    (r s : ℝ) (h : dist a b + dist b c ≤ r) (h' : dist u v + dist v w ≤ s) :
    dist a c + dist u w ≤ r + s := by norm_arith [h, h']

example (a b c : X) : dist a c ≤ dist a b + dist b c := by
  fail_if_success have : dist a c < dist a b + dist b c := by norm_arith
  norm_arith

end
