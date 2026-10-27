# Earlier work

The feature branch keeps the current package, tests, standalone benchmark
corpus, and Markdown documentation in a small working tree. Earlier paper assets,
census transports, and full-file benchmark artifacts remain in Git history.

The archive reference is commit
[`177a21dfd81ef0e9be9188f91e8a39bea44fe4e4`](https://github.com/TomasOrtega/norm-arith/tree/177a21dfd81ef0e9be9188f91e8a39bea44fe4e4),
the main-branch revision from which this feature branch was created.

| Material | Stable link |
| --- | --- |
| Earlier README and reported results | [README](https://github.com/TomasOrtega/norm-arith/blob/177a21dfd81ef0e9be9188f91e8a39bea44fe4e4/README.md) |
| Paper sources and build instructions | [paper/](https://github.com/TomasOrtega/norm-arith/tree/177a21dfd81ef0e9be9188f91e8a39bea44fe4e4/paper) |
| Expanded full-file patch and measurements | [benchmarks/expansion/](https://github.com/TomasOrtega/norm-arith/tree/177a21dfd81ef0e9be9188f91e8a39bea44fe4e4/benchmarks/expansion) |
| Historical census and earlier measurements | [benchmarks/](https://github.com/TomasOrtega/norm-arith/tree/177a21dfd81ef0e9be9188f91e8a39bea44fe4e4/benchmarks) |
| Archived evidence and transports | [artifacts/](https://github.com/TomasOrtega/norm-arith/tree/177a21dfd81ef0e9be9188f91e8a39bea44fe4e4/artifacts) |
| Previous architecture decisions | [docs/adr/](https://github.com/TomasOrtega/norm-arith/tree/177a21dfd81ef0e9be9188f91e8a39bea44fe4e4/docs/adr) |

Those results concern earlier implementations and workloads. They are not
measurements of the new LP or analytic frontend. The current
[results page](results.md) uses the standalone paired workload shipped on this
branch and records its own setup and limits.

The prior `NormArithTest/Paper.lean` examples are retained as
[`NormArithTest/Examples.lean`](../NormArithTest/Examples.lean), without paper-build
markers. No upstream mathlib files are changed by this reorganization.
