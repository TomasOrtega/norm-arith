# Quantified-bound proposals

`manifest-v4.json` preserves the original manual source hashes, byte spans and
semantic proof-body provenance. It replaces explicit local bound applications
with the bounded quantified specialization added to `norm_arith`.

The two complete copied files compiled with the interpreter prototype; see
`scratch-corpus-report.json`. The production Lean module build and all 26
expansion regressions then passed. This is development evidence. The final
combined patch must pass fresh complete-file source verification before it is
frozen or timed.

The isolated proposals save 19 proof lines, or 17 lines after their two imports.
Accounting in a larger union must count each file import only once.
