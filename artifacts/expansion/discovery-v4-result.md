# Final targeted discovery v4

The fixed follow-up visited the same 885 files as v3. It finished with valid frozen-input integrity: 875 complete outcomes, eight augmented-elaboration failures, and two partial extractions. All 23 process failures from the 4 GiB first tier were retried serially at 8 GiB. The ten incomplete files remain explicit gaps; this is not full Mathlib coverage.

The run retained 158 isolated kernel-checked proposals. Its standalone deterministic selection proposes 61 edits in 30 files and 111 net proof-code lines saved after imports. These are local checked proposals, not a compiled combined patch.

Selection09 keeps all 82 edits from verified-04 and adds five bare tactic replacements in three files: two Weierstrass estimates, the Padic norm-symmetry proof, and two Gromov–Hausdorff distance identities. They save nine proof lines and cost three imports, adding six net lines. The proposed union has 87 edits in 46 files: 582 original proof lines become 226, with 46 imports and no helpers, for 310 net lines saved. Whole-file verification is owned by the root agent and remains a separate requirement.

The archive contains 885 latest file outcomes, 908 attempts, 158 proposal records, and 8,263 raw files. It reopens the compressed archive and checks every member hash. Numeric failures and all raw records are preserved.

Exact input hashes, selected-entry provenance, protocol settings, archive hashes, and the proposed manifest are bound by [the receipt](discovery-v4-result.json). No extra discovery pass or production change was made.
