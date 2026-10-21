# Historical 41-line paper

This directory preserves the paper for the 16-replacement, ten-file patch that
saved 41 net code lines and measured a 1.105× warm affected-file speedup. These
results describe that frozen implementation and workload.

`paper.tar.gz` contains the original LaTeX, PDF, generated data, language review,
and build records. `receipt.json` lists their hashes. Extract it into a separate
checkout to inspect or rebuild the historical manuscript; the current `paper/`
directory describes the expanded study.

The original portable evidence bundle is stored in two compressed parts under
`evidence-transport/`. Restore it from the repository root with:

```sh
python3 paper/evidence_transport.py unpack \
  artifacts/paper-baseline-41line/evidence-transport/transport.json \
  --output artifacts/paper-evidence \
  --receipt-sha256 15cdd512ce00d02c37c7c32f3c593431888d9b2089bac5a64ce9ab25152cf516 \
  --bundle-sha256 9ea6f5e7381073707b00b007d72cd16d20ce7bc71cdf12d2bf460a3cb45ae7b0
```

The destination must be absent. The restore verifies each compressed part and
all 313 bundle files. `evidence-transport-check.json` records a successful
round trip. This check restores existing evidence; it does not run a new Lean
compilation or timing experiment. Follow the archived paper's README for its
portable PDF rebuild.
