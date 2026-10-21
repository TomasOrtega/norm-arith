# Final local patch

These are byte-identical copies of the final experiment's frozen records.
[inventory.json](inventory.json) records their original paths and hashes.

- [mathlib.patch](mathlib.patch): 16 replacements and 10 imports, saving 41 net
  code lines. It passes `git apply --check` at the pinned mathlib revision.
- [manifest.json](manifest.json): all 40 proposals, literal replacements,
  selection decisions, source guards, and the final verification binding.
- [selection.jsonl](selection.jsonl): selection outcomes and incomplete files.
- [selection-summary.json](selection-summary.json): the original selector-stage
  accounting. Full combined source compilation follows this stage.
- [verification-receipt.json](verification-receipt.json): final combined source
  verification and freeze hashes.

The mathlib pin is `2f3c7c8a8949b04a32f9303f59163acffb766996`.
The patch is tested in this project's Lake environment, which supplies the
`NormArith` import. The mathlib checkout remains unmodified; these are local
proposed changes, with no upstream merge.

The [final result summary](../FINAL-RESULTS.md) gives the timing result, scope,
and evidence links. The portable paper bundle retains the full source
verification and timing records.
