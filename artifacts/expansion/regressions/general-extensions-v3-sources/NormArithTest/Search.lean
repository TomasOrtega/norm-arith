module

import NormArith.Search
public meta import NormArith.Search

/-! Computational regression tests for the untrusted exact-rational search. -/

open NormArith.Search

-- The reference search is not limited to three-source certificates.
#guard (referenceDecompositions
  #[#[1, 0, 0, 0], #[0, 1, 0, 0], #[0, 0, 1, 0], #[0, 0, 0, 1]]
  #[1, 1, 1, 1]).coefficients == #[#[1, 1, 1, 1]]
#guard (referenceDecompositions
  #[#[1, 0, 0, 0], #[0, 1, 0, 0], #[0, 0, 1, 0], #[0, 0, 0, 1]]
  #[1, 1, 1, 1]).status == .complete

-- Every supplied column is eligible, including those after the first twelve.
#guard (referenceDecompositions ((Array.replicate 12 #[1, 0]).push #[0, 1])
  #[0, 1]).coefficients == #[(Array.replicate 12 0).push 1]
#guard (referenceDecompositions ((Array.replicate 12 #[1, 0]).push #[0, 1])
  #[0, 1]).status == .complete

-- Independent signed supports recover exact averaging certificates.
#guard (referenceDecompositions #[#[1, 1], #[1, -1]] #[1, 0]).coefficients ==
  #[#[1 / 2, 1 / 2]]
#guard (referenceDecompositions #[#[1, 1], #[1, -1]] #[0, 1]).coefficients ==
  #[#[1 / 2, -1 / 2]]

-- Rank bounds support sizes without losing alternative dependent-source bounds.
#guard (referenceDecompositions #[#[1, 0], #[2, 0], #[0, 1]] #[3, 2]).coefficients ==
  #[#[3, 0, 2], #[0, 3 / 2, 2]]
#guard (referenceDecompositions #[#[1, 0], #[2, 0], #[0, 1]] #[3, 2]).rank == 2
#guard (referenceDecompositions #[#[1, 0], #[2, 0], #[0, 1]] #[3, 2]).attempts == 6
#guard (referenceDecompositions #[#[1, 0], #[2, 0], #[0, 1]] #[3, 2]).status == .complete

-- The final row participates in both rank and span checks.
#guard (referenceDecompositions #[#[1, 0, 0], #[0, 0, 1]] #[0, 0, 1]).rank == 2
#guard (referenceDecompositions #[#[1, 0, 0], #[0, 0, 1]] #[0, 0, 1]).coefficients ==
  #[#[0, 1]]
#guard (referenceDecompositions #[#[1, 0, 0], #[0, 1, 0]] #[0, 0, 1]).coefficients == #[]
#guard (referenceDecompositions #[#[1, 0, 0], #[0, 1, 0]] #[0, 0, 1]).status == .complete

-- Exhaustion is distinct from a completed search with no decomposition.
#guard (referenceDecompositions #[#[1, 0], #[0, 1]] #[1, 1]
  { maxSubsets := 2 }).status == .exhausted .subsets
#guard (referenceDecompositions #[#[1, 0], #[0, 1]] #[1, 1]
  { maxSubsets := 2 }).attempts == 2
#guard (referenceDecompositions #[#[1, 0], #[0, 1]] #[1, 1]
  { maxSubsets := 3 }).status == .complete
#guard (referenceDecompositions #[#[1], #[2]] #[1]
  { maxResults := 1 }).status == .exhausted .results
#guard (referenceDecompositions #[#[1], #[2]] #[1]
  { maxResults := 1 }).coefficients == #[#[1, 0]]
#guard (referenceDecompositions #[#[1], #[2]] #[1]
  { maxResults := 2 }).status == .complete

#guard (referenceDecompositions #[] #[]).coefficients == #[#[]]
#guard (referenceDecompositions #[#[1]] #[0] { maxSubsets := 0 }).status == .complete
#guard (referenceDecompositions #[#[1]] #[0] { maxResults := 0 }).status == .exhausted .results
#guard (referenceDecompositions #[#[1]] #[1] { maxSubsets := 0 }).status == .exhausted .subsets
#guard (referenceDecompositions #[#[1, 0], #[1]] #[1, 0]).status == .invalidDimensions

-- An identity that requires combining two available vectors.
#guard decompositions #[#[1, 1], #[1, -1]] #[3, 1] == #[#[2, 1]]

-- Fractions and negative coefficients must be retained exactly.
#guard decompositions #[#[1, 1], #[1, -1]] #[1, 0] == #[#[1 / 2, 1 / 2]]
#guard decompositions #[#[1, 0], #[0, 1]] #[2, -3] == #[#[2, -3]]

-- Pivoting past an initial zero row is necessary for this system.
#guard decompositions #[#[0, 2]] #[0, 3] == #[#[3 / 2]]

-- Dependent source columns can give different useful decompositions.
-- Searching the dependent triple must not return a duplicate of the first pair.
#guard decompositions #[#[1, 0], #[2, 0], #[0, 1]] #[3, 2] ==
  #[#[3, 0, 2], #[0, 3 / 2, 2]]

-- A target outside the rational span must not receive a certificate.
#guard decompositions #[#[1, 0], #[2, 0]] #[0, 1] == #[]

-- Reach the final pair in lexicographic order, rather than only adjacent pairs.
#guard decompositions #[#[1, 0, 0, 0], #[0, 1, 0, 0], #[0, 0, 1, 0], #[0, 0, 0, 1]]
  #[0, 0, 1, 1] { maxSupport := 2 } == #[#[0, 0, 1, 1]]

-- Empty and malformed inputs have explicit behavior.
#guard decompositions #[] #[] == #[#[]]
#guard decompositions #[] #[1] == #[]
#guard decompositions #[#[1, 0]] #[0, 0] == #[#[0]]
#guard decompositions #[#[1, 0], #[1]] #[1, 0] == #[]

-- Limits bound failed attempts as well as successful proposals.
#guard decompositions #[#[1, 0], #[0, 1]] #[2, 3] { maxSupport := 1 } == #[]
#guard decompositions #[#[1, 0], #[0, 1]] #[2, 3] { maxSources := 1 } == #[]
#guard decompositions #[#[1, 0], #[0, 1]] #[2, 3] { maxSubsets := 2 } == #[]
#guard decompositions #[#[1, 0], #[0, 1]] #[2, 3] { maxSubsets := 3 } == #[#[2, 3]]
#guard decompositions #[#[1]] #[1] { maxSubsets := 0 } == #[]
#guard decompositions #[#[1]] #[0] { maxResults := 0 } == #[]
#guard decompositions #[#[1, 0], #[2, 0], #[0, 1]] #[3, 2] { maxResults := 1 } ==
  #[#[3, 0, 2]]

-- The separate checker rejects wrong coefficients and dimension mismatches.
#guard isDecomposition #[#[1, 1], #[1, -1]] #[3, 1] #[2, 1]
#guard !isDecomposition #[#[1, 1], #[1, -1]] #[3, 1] #[1, 2]
#guard !isDecomposition #[#[1]] #[1] #[]
#guard !isDecomposition #[#[1, 0]] #[1] #[1]
