# Core knowledge in statistics and data science: synopses

The series `SYNOPSIS101.md`–`SYNOPSIS108.md` describes the mathematical content
of Sections 101–108 in [CKSD-bib.md](CKSD-bib.md). It is addressed to
mathematicians and is independent of any later library-coverage inventory.
Sections 101–106 form Part XI, Mathematical Statistics, and Sections 107 and
108 the synopsized part of Part XII, Data Science. Section 109 of the
bibliography, on optimization and numerical algorithms, is outside this
series.

The division into sections follows the style of the sibling analysis
project: each section is a body of results of comparable size, and lettered
subdivisions are used only where they separate different bodies of results.
Numbered entries, cited as `<ddd>.<k>`, are stable identifiers. An entry
keeps its number when its wording is revised. A removed number is not
reused. A new entry takes the next free number in its file. The
identifiers in use before the reorganization of 2026-11-01 are mapped to
the current ones in [SYNOPSIS-CONCORDANCE.md](SYNOPSIS-CONCORDANCE.md).

Each synopsis gives the definitions and principal theorems of its section,
followed by a reference guide. The reference guides name the source basis of
the selected material and the local copies that were used. A subdivision
heading does not imply that every topic in its bibliography has a numbered
entry. Selection keeps the working core: statements that recur in several of the
graduate texts and monographs of the section. The formulation recorded is a
standard usable one. Proofs are outside the
scope of these synopses.

Probability tools are not restated when they already have a numbered entry in
the sibling analysis project. Those entries are cited as CKMA SYNOPSIS items.

## Progress

As of 2026-11-01, Sections 101–108 contain 535 numbered entries.

The series was first written on 2026-10-29 as thirteen synopses, Sections
101–113, with 220 entries. A mathematical-statistics expansion and a
data-science review on 2026-10-30 brought them to 333 entries, and a third
expansion on 2026-11-01 to 542. A review then removed six entries that
repeated other material or had not been checked against a source, together
with unchecked claims inside three others.

On 2026-11-01 the thirteen synopses were reorganized into eight sections of
51 to 77 entries, matching the granularity of the analysis project: the
general texts and classical decision theory form Section 101; asymptotic,
semiparametric, and robust theory Section 102; nonparametric and
high-dimensional inference Section 103; Bayesian inference with Monte Carlo
and stochastic sampling dynamics Section 104; linear and multivariate
models with design and causal inference Section 105; dependent data
Section 106; statistical learning and machine learning Section 107; and
the geometry of data, with optimal transport and kernel discrepancies,
Section 108. The lettered subdivisions were reduced from 33 to 13. Entries
were renumbered in reading order within each new section, and all
cross-references were rewritten; no statement was changed by the
reorganization. The bibliography was reorganized in the same way.

A review the same day checked every entry for a precise
definition–theorem formulation: one whose hypotheses, quantifiers, and
terms are explicit enough to be stated formally without guessing.
Unstated regularity conditions were written out or replaced by a clean
special case, hedged or approximate conclusions were replaced by exact
limits, inequalities, or explicitly quantified constants, commentary on
practice was deleted, and several incorrect statements were corrected.
Of the 536 entries, 398 were reworded and one, the Bartlett correction
(102.54), was removed because its hypotheses have no concise precise
form.

The first expansion develops exact sampling and confidence procedures, decision
bounds and simultaneous tests, functional and resampling asymptotics,
rank and shape-restricted methods, semiparametric derivatives, Bayesian
decisions and prediction, regression and covariance models, minimax lower
bounds, censored-data inference, and causal identification. It also corrects
several existing assumptions and conclusions, including the mean domain of
an exponential family, the loss class for local minimaxity, smoothing bias
in normal approximations, and the distinction between detection and
estimation rates.

The data-science review of the same day develops geometric coordinates and means,
persistent summaries, empirical transport and barycenters, kernel
estimation and testing, stochastic sampling and filtering, denoising and
flow identities, probabilistic prediction, graph symmetry, policy values,
and privacy mechanisms. Corrections include kernel-test scaling,
landscape central-limit assumptions, noisy-manifold model restrictions,
averaging of sampling laws, stochastic-approximation stability signs,
score normalization and reversal errors, graphon equivalence, recovery
threshold boundaries, and the conditions for fairness and privacy claims.
Each affected reference guide records the substantive qualifications and
distinguishes local full texts from primary papers consulted online.

The third expansion completes the classical finite-sample theory with
UMVU characterization, completeness of the order statistic, pivots and
Pratt's theorem, the generalized Neyman–Pearson lemma, Neyman structure,
interval hypotheses, least favorable distributions, invariant tests, and
Blyth's method. In asymptotics it adds one-step and $M$-estimator rate
theory, Bahadur representations, $L$-statistics, power envelopes, Pitman
efficiency, and second-order bootstrap accuracy and failure. Further additions
cover optimal rank scores and rank correlation, bandwidth selection and
smoothing splines, log-concave estimation, adaptation and missing
information; empirical Bayes and hierarchical shrinkage, exact simulation
and the convergence of Markov chain samplers; quadratic forms, the $F$ test,
variance components, Wishart structure, covariance tests, factor analysis,
and design optimality; packing and hypercube lower bounds, sparse recovery,
low-rank and covariance estimation, high-dimensional principal components,
surrogate losses and stability; spectral prediction theory, counting-process
martingales, optimal sequential and change-point procedures, random-field
covariances and point-process likelihoods; and stratified and adjusted
experiments, instrumental variables, sensitivity, mediation, probabilities
of causation, time-varying treatments, and causal discovery. In data
science it adds graph-Laplacian limits, Fréchet-mean and Procrustes
theory, the persistence algorithm and topological inference; transport-map
and entropic estimation, Wasserstein linearization, characteristic kernels,
and kernel Stein discrepancies; functional-inequality convergence of
Langevin dynamics, Metropolis-adjusted and kinetic Langevin methods,
stochastic approximation, particle-filter fluctuations, variational
assimilation, and diffusion-model training and convergence; and boosting,
variational inference, network capacity and approximation, implicit bias,
random graphs and graph limits, planning and policy optimization, linear
bandits, and further privacy and distribution-shift results. Corrections
sharpen the extreme-value domain-of-attraction conditions and the Hill
estimator limit (now 106.46 and 106.49) and the sampling
constants for homology inference (now 108.22). Several
data-science entries rest on primary papers that are not local; the
affected reference guides identify them, including papers read online.

Reference guides distinguish passages read for the expansion, other local
copies, and unavailable sources. Both `../lean-CKMA/References/` and
`../lean-CKMA/ReferencesSuppl/` were checked. Van der Vaart's *Asymptotic
Statistics* is local; the supplemental directory contains full texts of
Tsybakov, Ghosal–van der Vaart, and Robert–Casella used here. Lehmann–Casella,
Lehmann–Romano, and Shao's main *Mathematical Statistics* text were not
located; overlapping local graduate texts provide the classical source
basis. Image scans without usable text extraction are identified where
relevant. Definitions are interleaved with the results they support, and
cross-references place shared probability and analytic tools in CKMA.

* 101. Statistical inference: foundations, decision theory, estimation, and testing: [SYNOPSIS101.md](SYNOPSIS101.md), 70 numbered entries.
* 102. Asymptotic, semiparametric, and robust statistics: [SYNOPSIS102.md](SYNOPSIS102.md), 60 numbered entries.
* 103. Nonparametric and high-dimensional inference: [SYNOPSIS103.md](SYNOPSIS103.md), 55 numbered entries.
* 104. Bayesian inference and stochastic computation: [SYNOPSIS104.md](SYNOPSIS104.md), 77 numbered entries.
* 105. Linear models, multivariate analysis, experimental design, and causal inference: [SYNOPSIS105.md](SYNOPSIS105.md), 71 numbered entries.
* 106. Dependent data and stochastic models: [SYNOPSIS106.md](SYNOPSIS106.md), 51 numbered entries.
* 107. Statistical learning and machine learning: [SYNOPSIS107.md](SYNOPSIS107.md), 77 numbered entries.
* 108. Geometry of data: manifolds, topology, optimal transport, and kernels: [SYNOPSIS108.md](SYNOPSIS108.md), 74 numbered entries.

## Lettered subdivisions

The following synopses follow the bibliographical subdivisions that separate
different bodies of results. Each link opens the corresponding part of the
synopsis. Section 101 has no lettered subdivisions in the synopsis; its
bibliography separates the general texts and decision-theoretic monographs
(101A) from handbooks and histories (101B).

- **Section 102:**

  - [102A. First-Order Asymptotics, Statistical Experiments, and Semiparametric and Robust Inference](SYNOPSIS102.md#synopsis-102a)

  - [102B. Higher-Order Asymptotics, Resampling, and Information Geometry](SYNOPSIS102.md#synopsis-102b)

- **Section 103:**

  - [103A. Ranks, Smoothing, Shape Constraints, Minimax Estimation, and Functional Data](SYNOPSIS103.md#synopsis-103a)

  - [103B. High-Dimensional and Large-Scale Inference](SYNOPSIS103.md#synopsis-103b)

- **Section 104:**

  - [104A. Foundations, Parametric Bayesian Theory, and Nonparametric Bayes](SYNOPSIS104.md#synopsis-104a)

  - [104B. Monte Carlo, Langevin Dynamics, and Particle Methods](SYNOPSIS104.md#synopsis-104b)

  - [104C. Score Matching, Diffusion Generative Models, and Schrödinger Bridges](SYNOPSIS104.md#synopsis-104c)

- **Section 105:**

  - [105A. Regression, Multivariate Analysis, and Graphical Models](SYNOPSIS105.md#synopsis-105a)

  - [105B. Experimental Design and Causal Inference](SYNOPSIS105.md#synopsis-105b)

- **Section 106:**

  - [106A. Time Series, Stochastic Processes, and Spatial Data](SYNOPSIS106.md#synopsis-106a)

  - [106B. Survival Analysis, Sequential Analysis, and Extreme Values](SYNOPSIS106.md#synopsis-106b)

- **Section 107:**

  - [107A. Learning Theory, Probabilistic Models, Deep Learning, and Networks](SYNOPSIS107.md#synopsis-107a)

  - [107B. Bandits, Reinforcement Learning, Privacy, Fairness, and Distribution Shift](SYNOPSIS107.md#synopsis-107b)

- **Section 108:**

  - [108A. Manifold Learning, Geometric Statistics, Shape, and Persistent Homology](SYNOPSIS108.md#synopsis-108a)

  - [108B. Optimal Transport and Kernel Discrepancies](SYNOPSIS108.md#synopsis-108b)
