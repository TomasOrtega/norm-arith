module

import NormArith.Search
public meta import NormArith.Search

/-! Computational regression tests for the untrusted exact-rational search. -/

open NormArith.Search

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
