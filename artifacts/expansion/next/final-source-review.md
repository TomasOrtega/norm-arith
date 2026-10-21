# Final tactic and preparation review

No blocking concern found. This was read-only review against the retained
verified-03 tactic, without new compiles or changes to frozen inputs. Combined
selection 08 and its proposed savings still require their verifier and audit.

The tactic delta is consistent with the checked-certificate design:

- `Tactic.lean:480–501` disables error-to-sorry recovery while constructing
  certificates and synthesizes the identity proof immediately with its expected
  equality type. An elaboration failure can reach the existing saved-state
  boundary before a certificate is retained.
- `Tactic.lean:342–355` uses the same `.default` transparency for linear atom
  matching and the `ring1!` discharger. This matches mathlib's
  `LinarithConfig.updateReducibility true` in `Tactic/Linarith/Frontend.lean:183–190`.
  Mathlib implements `ring1!` and `abel!` with `.default` atom transparency.
  The new discharger also disables tactic recovery, so failed algebraic checking
  throws into `tryLinear`'s saved-state restoration. The same configuration is
  used for bounded premise proofs.
- `abel!` changes definitional atom matching, not which local inequalities are
  available. Certificate identities still need checked equality proofs.
- `Set.mem_ofPred_eq` is applied only to `initialFacts` already admitted by
  `selectedFacts`. The checked simplifier equality transports each supplied proof
  to its normalized proposition. It neither reads an excluded local norm bound
  nor adds a new premise. Explicit norm-fact selection and retained norm-free
  scalar comparisons keep their earlier policy.
- Failed upper-bound and finite-constraint candidates retain their existing
  saved-state restoration. The new immediate synthesis and nonrecovering
  discharger place failures inside those boundaries.

The four new examples in `NormArithTest/Expansion.lean:180–209` cover uncurry
aliases, an excluded aliased norm bound, supplied set membership, an excluded
membership bound, and a subset-result proposition. Their negative checks are
meaningful fact-selection regressions. Source review found no new path that
bypasses those restrictions. This review does not certify every possible tactic
output or expand the completeness scope.

All ten preparation candidates preserve the existing proof statements and
assumptions. Exact source hashes, inclusive line spans, body containment, internal
proof replacement reconstruction, and the 100-character line limit were checked
without invoking Lean. Their recorded accounting includes inline proof arguments
and retained goal headers:

| Candidate suffix | Original proof lines | Replacement lines |
| --- | ---: | ---: |
| fderiv-param | 18 | 3 |
| uniform-upper | 11 | 1 |
| controlled-initial | 9 | 3 |
| banach-preimage | 8 | 3 |
| akra-positive-lower | 7 | 2 |
| akra-positive-upper | 6 | 2 |
| akra-negative-lower | 11 | 2 |
| akra-negative-upper | 9 | 2 |
| jacobian-cover | 13 | 6 |
| dominated-uniform-bound | 11 | 2 |

The scalar multiplication bounds remain explicit in ControlledClosure and all
four Akra–Bazzi cases. Banach retains map subtraction normalization. Jacobian
retains its operator-norm bound, membership application, and final product
estimate. FDeriv and dominated-convergence replacements now pass the same bounds
directly through definitional aliases. Uniform relies on the existing min/radius
scalar facts, consistent with the explicit-fact policy. No omitted preparation or
clear unused declaration was found. These ten overlap earlier replacements;
their standalone totals must not be added to the final union's savings.

Reviewed SHA256:

- Current `NormArith/Tactic.lean`: `53c79f56f2c5c66fc2a9af885e37e715f464eeb9557450d19a7274bd88d1de77`
- Retained verified-03 tactic: `27b311a82a893e3857b0d4bdeffbe8bb8b0ae323580f284d171f8d2e1e9d18ba`
- Current `NormArithTest/Expansion.lean`: `fc30e227186e9fc29c39e3e79ea70cc32de73a5590c47645820e3af69b43f7db`
- `prep-confirmed-v1.json`: `7fb90329727ad6180b689ce75e5c6768afdabd4adaacf80bee23339fb611d8b5`
- Its accounting: `5951f435eb1f5fae856062e469e46943c6ac274c669b575baeefbbe991f8f35b`
