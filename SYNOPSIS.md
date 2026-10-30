# Core knowledge in statistics and data science: synopses

The series `SYNOPSIS101.md`–`SYNOPSIS113.md` describes the mathematical content
of Sections 101–113 in [CKSD-bib.md](CKSD-bib.md). It is addressed to
mathematicians and is independent of any later library-coverage inventory.
Section 114 is outside this series.

Section numbers remain stable. The mathematical material is grouped under the
lettered subdivisions of the bibliography where those subdivisions separate
different bodies of results. Numbered entries, cited as `<ddd>.<k>`, are stable
identifiers. An entry keeps its number when its wording is revised. A removed
number is not reused. A new entry takes the next free number in its file.

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

As of 2026-10-30, Sections 101–113 contain 333 numbered entries.
The initial selective pass of 2026-10-29 had 220. The mathematical-statistics
expansion added 72 entries to Sections 101–109, which now have 228.
The subsequent review of data science, Sections 110–113, adds 41 entries,
bringing those sections to 105. All existing identifiers are preserved;
Section 114 remains outside the series.

The expansion develops exact sampling and confidence procedures, decision
bounds and simultaneous tests, functional and resampling asymptotics,
rank and shape-restricted methods, semiparametric derivatives, Bayesian
decisions and prediction, regression and covariance models, minimax lower
bounds, censored-data inference, and causal identification. It also corrects
several existing assumptions and conclusions, including the mean domain of
an exponential family, the loss class for local minimaxity, smoothing bias
in normal approximations, and the distinction between detection and
estimation rates.

The data-science review develops geometric coordinates and means,
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

* 101. Statistical inference: general texts, references, and history: [SYNOPSIS101.md](SYNOPSIS101.md), 23 numbered entries.
* 102. Classical inference: decision theory, estimation, and testing: [SYNOPSIS102.md](SYNOPSIS102.md), 26 numbered entries.
* 103. Asymptotic statistics: [SYNOPSIS103.md](SYNOPSIS103.md), 32 numbered entries.
* 104. Nonparametric, semiparametric, and robust inference: [SYNOPSIS104.md](SYNOPSIS104.md), 31 numbered entries.
* 105. Bayesian statistics and Monte Carlo methods: [SYNOPSIS105.md](SYNOPSIS105.md), 21 numbered entries.
* 106. Linear models, multivariate analysis, and experimental design: [SYNOPSIS106.md](SYNOPSIS106.md), 28 numbered entries.
* 107. High-dimensional statistics and statistical learning: [SYNOPSIS107.md](SYNOPSIS107.md), 21 numbered entries.
* 108. Dependent data and stochastic models: [SYNOPSIS108.md](SYNOPSIS108.md), 31 numbered entries.
* 109. Causal inference: [SYNOPSIS109.md](SYNOPSIS109.md), 15 numbered entries.
* 110. Geometric and topological data analysis: [SYNOPSIS110.md](SYNOPSIS110.md), 23 numbered entries.
* 111. Optimal transport and kernel discrepancies for comparing datasets: [SYNOPSIS111.md](SYNOPSIS111.md), 18 numbered entries.
* 112. Mean-field limits and stochastic dynamics for data: [SYNOPSIS112.md](SYNOPSIS112.md), 24 numbered entries.
* 113. Machine-learning models, representation, and sequential decisions: [SYNOPSIS113.md](SYNOPSIS113.md), 40 numbered entries.

## Lettered subdivisions

The following synopses follow the bibliographical subdivisions that separate
different bodies of results. Each link opens the corresponding part of the
synopsis.

- **Section 101:**

  - [101A. General Graduate Texts](SYNOPSIS101.md#synopsis-101a)

  - [101B. Large References, Distribution Handbooks, and History](SYNOPSIS101.md#synopsis-101b)

- **Section 103:**

  - [103A. First-Order Asymptotics, Statistical Experiments, and Empirical Processes](SYNOPSIS103.md#synopsis-103a)

  - [103B. Higher-Order Asymptotics, Resampling, and Information Geometry](SYNOPSIS103.md#synopsis-103b)

- **Section 104:**

  - [104A. Ranks, Smoothing, Shape Constraints, and Minimax Estimation](SYNOPSIS104.md#synopsis-104a)

  - [104B. Semiparametric Models and Missing Data](SYNOPSIS104.md#synopsis-104b)

  - [104C. Robust Statistics](SYNOPSIS104.md#synopsis-104c)

  - [104D. Functional Data Analysis](SYNOPSIS104.md#synopsis-104d)

- **Section 105:**

  - [105A. Foundations and Parametric Bayesian Theory](SYNOPSIS105.md#synopsis-105a)

  - [105B. Nonparametric Bayes, Posterior Asymptotics, and Inverse Problems](SYNOPSIS105.md#synopsis-105b)

  - [105C. Monte Carlo and Bayesian Computation](SYNOPSIS105.md#synopsis-105c)

- **Section 106:**

  - [106A. Regression, Generalised Linear Models, and Mixtures](SYNOPSIS106.md#synopsis-106a)

  - [106B. Multivariate Analysis, Invariance, and Graphical Models](SYNOPSIS106.md#synopsis-106b)

  - [106C. Experimental Design](SYNOPSIS106.md#synopsis-106c)

- **Section 107:**

  - [107A. High-Dimensional and Large-Scale Inference](SYNOPSIS107.md#synopsis-107a)

  - [107B. Statistical Learning Theory](SYNOPSIS107.md#synopsis-107b)

- **Section 108:**

  - [108A. Time Series and Inference for Stochastic Processes](SYNOPSIS108.md#synopsis-108a)

  - [108B. Survival Analysis and Counting Processes](SYNOPSIS108.md#synopsis-108b)

  - [108C. Sequential Analysis, Change Detection, and Anytime-Valid Inference](SYNOPSIS108.md#synopsis-108c)

  - [108D. Spatial Data, Point Patterns, and Gaussian Processes](SYNOPSIS108.md#synopsis-108d)

  - [108E. Extreme-Value Statistics](SYNOPSIS108.md#synopsis-108e)

- **Section 110:**

  - [110A. Manifold Learning, Geometric Statistics, and Shape](SYNOPSIS110.md#synopsis-110a)

  - [110B. Persistent Homology and Computational Topology](SYNOPSIS110.md#synopsis-110b)

- **Section 111:**

  - [111A. Optimal Transport, Wasserstein Distances, and Their Statistics](SYNOPSIS111.md#synopsis-111a)

  - [111B. Kernel Mean Embeddings and Integral Probability Metrics](SYNOPSIS111.md#synopsis-111b)

- **Section 112:**

  - [112A. Langevin Dynamics, Sampling, and Gradient Flows](SYNOPSIS112.md#synopsis-112a)

  - [112B. Particle Methods, Data Assimilation, and Training Dynamics](SYNOPSIS112.md#synopsis-112b)

  - [112C. Score Matching, Diffusion Generative Models, and Schrödinger Bridges](SYNOPSIS112.md#synopsis-112c)

- **Section 113:**

  - [113A. General Foundations, Probabilistic Modelling, and Ensembles](SYNOPSIS113.md#synopsis-113a)

  - [113B. Deep Learning: Architectures, Approximation, and Training Theory](SYNOPSIS113.md#synopsis-113b)

  - [113C. Networks and Graph Representation Learning](SYNOPSIS113.md#synopsis-113c)

  - [113D. Bandits and Reinforcement Learning](SYNOPSIS113.md#synopsis-113d)

  - [113E. Privacy, Fairness, and Distribution Shift](SYNOPSIS113.md#synopsis-113e)
