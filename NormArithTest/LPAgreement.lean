module

import NormArith.Tactic

/-! Compare compact LP with complete support enumeration on small rational inputs. -/

set_option linter.unusedTactic false
set_option maxHeartbeats 2000000

example : True := by
  run_tac do
    let sources : Array (Array Rat) := #[#[1, 0], #[0, 1], #[1, 1]]
    let values : Array Rat := #[-3 / 2, -1, 0, 1 / 2, 2]
    for a in values do
      for b in values do
        let target := #[a, b]
        let reference := NormArith.Search.referenceDecompositions sources target
        unless reference.status == .complete && !reference.coefficients.isEmpty do
          throwError "small reference search did not finish"
        let costs := reference.coefficients.map fun coefficients =>
          coefficients.foldl (fun cost q => cost + if q < 0 then -q else q) (0 : Rat)
        let bound := costs.foldl min costs[0]!
        let columns := sources.push target
        let groups := Array.replicate 4 #[0, 1, 2, 3]
        let rows : Array NormArith.LP.Row := #[
          { coeffs := #[(1, 1), (0, -1)] },
          { coeffs := #[(2, 1), (0, -1)] },
          { coeffs := #[(3, 1), (0, -1)] }]
        let _ ← NormArith.LP.propose columns groups
          (rows.push { str := .lt, coeffs := #[(0, bound), (4, -1)] })
        let tooStrong ← try
          let _ ← NormArith.LP.propose columns groups
            (rows.push { str := .lt, coeffs := #[(0, bound - 1 / 2), (4, -1)] })
          pure true
        catch _ => pure false
        if tooStrong then throwError "LP disagrees with complete support enumeration"
  trivial
