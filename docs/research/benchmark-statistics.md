# Benchmark statistics: sources and methods wording

Research date: 2026-10-20. This note documents the existing experiment. It does
not change the harness, analysis plan, or calibration. The research used primary
papers, publisher records, and author or university publication pages.

## Correct sampling unit

`scripts/benchmark.py` uses full-pass totals, then equal, adjacent, nonoverlapping
blocks. A pass compiles every affected file for one variant. Write the paired
pass totals as `(O_t, R_t)`, the even block length as `b`, and the number of
blocks as `K = N / b`. The primary estimate is

\[
\widehat S=\frac{\sum_{t=1}^{N} O_t}{\sum_{t=1}^{N} R_t}.
\]

Each bootstrap draw samples `K` block indices with replacement. The same drawn
indices select the original and replacement totals. Each block contains whole
AB/BA pairs and every affected file. The bootstrap does not sample individual
file times or individual pairs independently. Equal block lengths make the ratio
of block-total means equal to the ratio of pass-total means.

The acceleration calculation deletes one whole block at a time. Thus `K`, not
`N` or the number of compiler processes, is the number of resampling units.
The current sentence in `paper/appendix.tex`, “preserves the pairs as sampling
units,” should specify blocks of pairs. These are facts about `paired_blocks`,
`bootstrap_ratios`, and `bca_interval` in the checked-in harness.

## Primary citations and their limits

**Efron (1987), Better Bootstrap Confidence Intervals.** JASA 82(397), 171–185.
Use this for the BCa probability transformation. Equations (3.2) and (4.1) use
strict inequality in the bias-correction probability. Do not attribute the
harness's half-weight treatment of ties to that formula. The article with its
discussion extends to page 200; 171–185 is the publisher's article range. The
publication year is 1987, despite a later online-publication date.
[Publisher DOI](https://doi.org/10.1080/01621459.1987.10478410),
[JSTOR record](https://www.jstor.org/stable/2289144).

**DiCiccio and Efron (1996), Bootstrap Confidence Intervals.** Statistical
Science 11(3), 189–228, with discussion. Section 6, equations (6.6)–(6.7), gives
the jackknife acceleration using influences proportional to the mean of the
leave-one estimates minus each leave-one estimate. This verifies the sign in
our implementation. Applying this formula to blocks treats whole blocks as
the observations; it does not establish that our temporal blocks are independent.
[Publisher DOI](https://doi.org/10.1214/ss/1032280214),
[primary-paper PDF, printed p. 201](https://www.math.wustl.edu/~kuffner/AlastairYoung/LeeYoung1996b.pdf).

**Field and Welsh (2007), Bootstrapping clustered data.** JRSS Series B 69(3),
369–390. This is a suitable primary reference for the model dependence of
clustered-data bootstrap methods. Its variance-consistency results concern
specified one-way-array models. They do not establish the coverage of our BCa
interval for serially dependent compilation times.
[Publisher abstract and metadata](https://rss.onlinelibrary.wiley.com/doi/abs/10.1111/j.1467-9868.2007.00593.x),
[author's institutional publication record](https://researchportalplus.anu.edu.au/en/publications/bootstrapping-clustered-data/).

**Künsch (1989), The Jackknife and the Bootstrap for General Stationary
Observations.** Annals of Statistics 17(3), 1217–1241, is a relevant historical
stationary-data reference. Its identity and page range are confirmed by the
author's publication list. The publisher text was inaccessible during this
review, so this note does not rely on an uninspected theorem or claim that its
procedure equals our fixed nonoverlapping-block BCa implementation.
[Publisher DOI](https://doi.org/10.1214/aos/1176347265),
[author publication list](https://people.math.ethz.ch/~kuensch/papers/).

## Exact implementation conventions

The following specify our implementation, rather than a theorem about timing
data. Let `S*_r` be the bootstrap ratios and `B` the fixed replicate count:

\[
\widehat z_0=\Phi^{-1}\!\left(
 \frac{\#\{S_r^*<\widehat S\}+\tfrac12\#\{S_r^*=\widehat S\}}{B}\right).
\]

Let `S_(-j)` be the estimate after deleting block `j`, and let `J` be their mean.
The common influence-scale factor cancels in

\[
\widehat a=
\frac{\sum_{j=1}^{K}(J-S_{(-j)})^3}
 {6\{\sum_{j=1}^{K}(J-S_{(-j)})^2\}^{3/2}}.
\]

For each `alpha` in `{0.025, 0.975}`, use the BCa adjustment

\[
p_\alpha=\Phi\!\left[
\widehat z_0+
\frac{\widehat z_0+\Phi^{-1}(\alpha)}
 {1-\widehat a\{\widehat z_0+\Phi^{-1}(\alpha)\}}
\right].
\]

The harness sorts the `B` ratios and interpolates linearly at index
`p_alpha * (B - 1)`, using zero-based indexing. It uses the frozen seed and
replicate count, with at least 10,000 draws. Half-ties, this empirical quantile
rule, floating-point equality, and rejection of adjusted probabilities outside
`[1/B, 1-1/B]` are explicit numerical choices. Degenerate distributions,
undefined acceleration, or invalid adjustments give an undefined interval and
cannot pass the speed gate. Success requires a valid interval whose lower
endpoint is strictly greater than one.

## Recommended methods statement

> We use the ratio of mean original and replacement full-pass times. We group
> adjacent paired passes into equal, nonoverlapping blocks of the calibrated
> even length. We resample whole blocks and retain all affected files and both
> variants within each sampled block. The BCa transformation follows Efron
> (1987). Acceleration uses a jackknife that deletes the same whole blocks
> (DiCiccio and Efron, 1996). We give half weight to bias-correction ties and use
> linear interpolation for empirical quantiles. The frozen plan records the
> sample count, block length, seed, replicate count, and decision rule.

> The interval is conditional on treating these blocks as independent and
> representative of the stated timing conditions. Blocking retains dependence
> within blocks; it does not establish independence between blocks or remove
> drift. Pilot diagnostics support the choice of block length but do not prove
> those assumptions. We do not claim a coverage theorem for arbitrary timing
> dependence or second-order accuracy for this experiment.

These are proposed methods statements, not quotations from the cited papers.
The uncertainty concerns repeated runs of this fixed affected-file workload on
the stated machine and environment. The files are not sampled from Mathlib;
the interval does not support generalization to other hardware or revisions.

## BibTeX metadata

```bibtex
@article{efron1987,
  author = {Efron, Bradley},
  title = {Better Bootstrap Confidence Intervals},
  journal = {Journal of the American Statistical Association},
  year = {1987},
  volume = {82},
  number = {397},
  pages = {171--185},
  doi = {10.1080/01621459.1987.10478410},
  url = {https://doi.org/10.1080/01621459.1987.10478410}
}

@article{diciccioefron1996,
  author = {DiCiccio, Thomas J. and Efron, Bradley},
  title = {Bootstrap Confidence Intervals},
  journal = {Statistical Science},
  year = {1996},
  volume = {11},
  number = {3},
  pages = {189--228},
  note = {With discussion},
  doi = {10.1214/ss/1032280214},
  url = {https://doi.org/10.1214/ss/1032280214}
}

@article{fieldwelsh2007,
  author = {Field, C. A. and Welsh, A. H.},
  title = {Bootstrapping Clustered Data},
  journal = {Journal of the Royal Statistical Society: Series B
             (Statistical Methodology)},
  year = {2007},
  volume = {69},
  number = {3},
  pages = {369--390},
  doi = {10.1111/j.1467-9868.2007.00593.x},
  url = {https://doi.org/10.1111/j.1467-9868.2007.00593.x}
}

@article{kunsch1989,
  author = {K{\"u}nsch, Hans R.},
  title = {The Jackknife and the Bootstrap for General Stationary Observations},
  journal = {The Annals of Statistics},
  year = {1989},
  volume = {17},
  number = {3},
  pages = {1217--1241},
  doi = {10.1214/aos/1176347265},
  url = {https://doi.org/10.1214/aos/1176347265}
}
```
