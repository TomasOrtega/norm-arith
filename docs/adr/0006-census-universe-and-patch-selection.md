# Fix the production mathlib universe and select patches by net line reduction

The census covers every tracked Lean source under `Mathlib/` at a pinned
revision, including tactic-style and term-style proofs. Tests, `Archive`, and
external dependencies are outside the main denominator. Record an extraction
outcome for every file.

Select the final patch by correctness and total net line reduction with a
deterministic overlap rule. Compile the combined patch and measure every
resulting affected file, including files that become slower. The entire selected
patch must meet the paper's aggregate speedup requirement; timing results do not
select which files enter that measurement.

Format replacements before counting lines. Fixed proof replacements must fit
100 Unicode characters per line; wrap a long `by norm_arith` as an indented
`by` block and charge its continuation line. Reject proposals that the fixed
format cannot express within that limit. Require positive net savings in each
affected file after charging its import. Source verification also rejects
long-line linter diagnostics. Preserve superseded studies when this check
changes the selected workload, and collect fresh timing evidence for the revision.

Preprocessing and bound discovery use a fixed, documented rule set. One-off
human-invented lemmas are outside the headline census and can appear in separately
identified case studies. Generated preparation remains part of replacement size.
