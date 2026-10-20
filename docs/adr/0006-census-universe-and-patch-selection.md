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

Preprocessing and bound discovery use a fixed, documented rule set. One-off
human-invented lemmas are outside the headline census and can appear in separately
identified case studies. Generated preparation remains part of replacement size.
