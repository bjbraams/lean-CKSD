# Mathlib coverage of Sections 101–108

This file summarises, section by section, what Mathlib contains of the
mathematical content described in [`SYNOPSIS101.md`](SYNOPSIS101.md)–[`SYNOPSIS108.md`](SYNOPSIS108.md).
It is a digest of the Mathlib parts of the coverage inventories
[`STRUCTURE101.md`](STRUCTURE101.md)–[`STRUCTURE108.md`](STRUCTURE108.md), which give the
declarations, source files, and hypotheses, and classify every numbered synopsis
entry as covered, partly covered, or not covered by the three libraries together.
The companion files [TauCetiCoverage.md](TauCetiCoverage.md) and
[StatlibCoverage.md](StatlibCoverage.md) summarise the TauCeti and Statlib
additions in the same way, and [GAPS.md](GAPS.md) selects and assesses the principal
missing results.

Statistics and data science are thinly covered by Mathlib. Its probability
library supplies much of the infrastructure on which the subject rests, but
`Mathlib.Probability.Decision` already represents measurable parametrized
models and randomized estimators by Markov kernels and supplies their risk
integrals, average risk, Bayes risk, and minimax risk. Dedicated APIs for
sufficiency, tests, confidence sets, and learning rules are absent. Six of the eight
verdicts below are Thin and two are None.

## Source baseline

Mathlib commit
[`6135ffb78e8bcd3fcc8ec02f3f82ea0b0737358b`](https://github.com/leanprover-community/mathlib4/tree/6135ffb78e8bcd3fcc8ec02f3f82ea0b0737358b)
of 2026-11-05, using Lean `v4.36.0-rc2`. The coverage was checked on 2026-11-06 by
inspecting the source of a local checkout; see the
[source conventions](STRUCTURE.md#source-baseline-and-conventions) of the series.
The project, with Statlib, builds against this Mathlib pin.
Statements here are summaries: the full hypotheses of the cited declarations, as
recorded in the STRUCTURE files, govern their use.

The classification of entries follows the uniform rule of
[STRUCTURE.md](STRUCTURE.md): an entry is partly covered when a library
declaration proves one of the claims the entry makes, or a special case of it;
an entry for which the libraries supply only ingredients, from which the
statement would follow by a further argument however short, is not covered.
Such *ingredients only* entries are mentioned below among the supporting
material, not as coverage.

These are direct-coverage verdicts under the CKSD rule. They are not
numerically comparable with CKMA's verdicts without reconciling the rules
and source revisions; see [Comparison with CKMA](STRUCTURE.md#comparison-with-ckma).

Each section below gives a verdict for this library alone, judged against the
content of the corresponding synopsis:

- **Substantial:** a large part of the graduate core of the section is proved.
- **Partial:** a real cluster of the section's own definitions and theorems is
  proved, but the section as a whole is not.
- **Thin:** a few of the section's results, or only neighbouring ingredients.
- **None:** nothing of the section's own content beyond general infrastructure.

## Overview

- [101](#101-statistical-inference-foundations-decision-theory-estimation-and-testing) Statistical inference: foundations, decision theory, estimation, and testing — Thin
- [102](#102-asymptotic-semiparametric-and-robust-statistics) Asymptotic, semiparametric, and robust statistics — Thin
- [103](#103-nonparametric-and-high-dimensional-inference) Nonparametric and high-dimensional inference — None
- [104](#104-bayesian-inference-and-stochastic-computation) Bayesian inference and stochastic computation — Thin
- [105](#105-linear-models-multivariate-analysis-experimental-design-and-causal-inference) Linear models, multivariate analysis, experimental design, and causal inference — None
- [106](#106-dependent-data-and-stochastic-models) Dependent data and stochastic models — Thin
- [107](#107-statistical-learning-and-machine-learning) Statistical learning and machine learning — Thin
- [108](#108-geometry-of-data-manifolds-topology-optimal-transport-and-kernels) Geometry of data: manifolds, topology, optimal transport, and kernels — Thin

Across the 537 numbered entries of Sections 101–108, the three libraries together
cover 5 entries, partly cover 55, and do not cover 477. Mathlib takes part in one
covered entry (101.44, together with TauCeti) and in 16 partly covered entries:
101.4, 101.32, 101.42, 102.43, 104.22, 104.27, 106.38, 107.38 and 108.11 on its
own, 101.17, 101.27, 104.21, 104.25 and 106.20 together with TauCeti, and 101.33
and 104.9 together with Statlib.

## 101. Statistical inference: foundations, decision theory, estimation, and testing

**Thin.** Mathlib's one statistical framework is its decision-theory directory: a model is a kernel from parameters to data, a randomized rule is a Markov kernel, and the average, Bayes and minimax risks are defined for losses in \([0,\infty]\). It proves that the Bayes risk under any probability prior is at most the minimax risk (101.32, partly; equality, minimax rules and least favorable priors are absent), and, with the posterior kernel defined by disintegration on a standard Borel parameter space, that a measurable minimizer of posterior expected loss is a Bayes rule attaining the Bayes risk (101.33, partly, with Statlib's density form of the Bayes risk; the converse is not stated). The basic theory of relative entropy, namely vanishing exactly at equality, the chain rule for composition products, and data processing under maps and kernels, gives 101.44 (covered, with TauCeti's tensorization). In one dimension the tilted measure and the cumulant-generating function give convexity of the natural domain, analyticity, and the tilted mean and variance as first and second derivatives (101.4, 101.42, partly). Mathlib also contributes the normality of the Gaussian sample mean (101.17, partly), and the law of total variance as the prediction identity for constant predictors (101.27, partly). Supporting are total variation through a Hahn set and the passage from argmin rules to Bayes rules, on which the Statlib and TauCeti proof of the covered entry 101.66 rests, conditional Jensen, the easy direction of Blackwell's comparison in integrated form (garbling cannot decrease Bayes or minimax risk; 101.62 has ingredients only), DeGroot's statistical information, Sion's minimax theorem, differentiation under the integral sign to any order, the union bound and Haar measure. Absent are dedicated APIs for sufficiency, ancillarity and completeness, the score, Fisher information and the information inequality, tests, \(p\)-values and confidence sets, the Neyman–Pearson lemma and the optimal-test theory, admissibility and complete classes, equivariance, and the James–Stein phenomenon. [Details in STRUCTURE101.md](STRUCTURE101.md).

## 102. Asymptotic, semiparametric, and robust statistics

**Thin.** Essentially the whole of Section 102 is missing from Mathlib. The only entry reached is 102.43 (partly): the tower property of conditional expectation is its first identity, and the second is proved only in unconditional form, as the law of total variance. Supporting material is the probabilistic and analytic infrastructure of the subject: convergence in distribution for statistics on varying probability spaces, with the continuous-mapping theorem and Slutsky's theorem; the one-dimensional i.i.d. central limit theorem and the Cramér–Wold device, from which the unstated multivariate central limit theorem would follow; multivariate Gaussian laws; log-likelihood ratios and the KL divergence; the \(L^2\) conditional expectation as an orthogonal projection; Taylor expansion of characteristic functions; differentiation under the integral sign to any order; the tilted mean and variance used at a saddlepoint; the Lévy–Prokhorov metric; the decision-theoretic risks; and Riemannian manifolds. The particular case \(n\bar X^2\Rightarrow\sigma^2\chi^2_1\) of 102.27 follows in two steps from these with a TauCeti law but is not stated. Absent are stochastic order symbols and the delta method, maximum likelihood, Z- and M-estimation, contiguity, local asymptotic normality, Le Cam's lemmas, the convolution and local asymptotic minimax theorems, quantile functions, empirical distribution functions, U- and L-statistics and the Hájek projection, Pitman efficiency, tangent spaces and efficient scores, influence functions and breakdown points, Hadamard differentiability, Edgeworth and saddlepoint expansions, the bootstrap, jackknife and empirical likelihood, and the Fisher–Rao metric with Čencov's theorem. [Details in STRUCTURE102.md](STRUCTURE102.md).

## 103. Nonparametric and high-dimensional inference

**None.** Mathlib proves no entry of Section 103, even in part. The supporting material is broad but general: the one-dimensional central limit theorem and Cramér–Wold, Brownian motion characterized by its finite-dimensional laws, almost-everywhere convergence of convolutions with shrinking smooth bumps (the deterministic bias of kernel smoothing), reproducing-kernel Hilbert spaces with Moore's theorem (from which the representer theorem would follow by projection, not stated), nearest-point projection onto closed convex sets (existence of the isotonic projection), Hölder conditions, the minimax and Bayes risks with their data-processing inequalities, the total variation distance and the KL divergence, the Hamming distance with packing and covering numbers, sub-Gaussian tail bounds, the covariance operator of a measure on a Hilbert space, matrix norms, and the spectral theorem with Rayleigh quotients. Absent are empirical distribution functions, the Kolmogorov–Smirnov limit and the Dvoretzky–Kiefer–Wolfowitz inequality, ranks and rank statistics, kernel density and regression estimators, cross-validation, local polynomials and splines, shape-constrained estimators, the Gaussian sequence model and Pinsker's minimax theorem, the two-point, Fano and Assouad lower bounds, the Varshamov–Gilbert bound, the lasso, basis pursuit and restricted isometry, information criteria, false-discovery control, covariance thresholding and graphical-model estimation, random-matrix spectral limits, and functional data analysis. [Details in STRUCTURE103.md](STRUCTURE103.md).

## 104. Bayesian inference and stochastic computation

**Thin.** Mathlib has a measure-theoretic core for Bayesian statistics. The posterior is a Markov kernel characterized, uniquely almost everywhere, by disintegration of the joint law of parameter and data; under domination it is the prior reweighted by a Radon–Nikodym derivative against the marginal, which is Bayes' formula; and for two models encoded on `Bool` the posterior model probabilities are given explicitly (104.9, partly, with Statlib's maximum-posterior rule under 0–1 loss; the Bayes-factor ratio is not stated). Bayes estimators as posterior argmins are described under Section 101. For Monte Carlo it proves the change-of-measure identity of importance sampling (104.21, partly, with TauCeti's sample-mean variance), that a reversible kernel leaves its measure invariant (104.22, partly; the Metropolis–Hastings kernel is not defined), the relative entropy against a tilted reference, which is the evidence identity of 104.25 in tilted-reference form (partly, with TauCeti), and, through the law of total variance, the single-draw form of Rao–Blackwellization (104.27, partly). Supporting are the Kolmogorov extension theorem for projective families on Polish factors, the maximal ergodic inequality, Etemadi's strong law, the i.i.d. central limit theorem and Slutsky's theorem, \(\varphi\)-irreducibility and Ionescu–Tulcea trajectory laws, Lévy's upward theorem (the martingale step of Doob's consistency theorem), covering numbers, KL data processing, Gaussian laws and reproducing-kernel Hilbert spaces. Absent are conjugate updates, Fisher information and the Jeffreys prior, Bernstein–von Mises and the Laplace approximation, the Dirichlet process and posterior contraction, Markov-chain sampler kernels and their convergence theory, stochastic differential equations and every Langevin and diffusion-model entry, stochastic approximation, interacting particle systems and particle filters. [Details in STRUCTURE104.md](STRUCTURE104.md).

## 105. Linear models, multivariate analysis, experimental design, and causal inference

**None.** Mathlib defines no linear model, least-squares estimator, analysis-of-variance decomposition, generalized linear model, design, potential-outcome model or directed graphical model, and proves no entry of Section 105, even in part. Its supporting linear algebra is extensive: orthogonal projection as the nearest-point map with its orthogonality characterization, the trace of a projection equal to its rank (hence \(\mathop{\mathrm{tr}}H=p\) for a hat matrix), the Woodbury identity, Schur-complement determinant, inverse and positivity criteria, and \(\mathop{\mathrm{rank}}(A^{\mathsf T}A)=\mathop{\mathrm{rank}}A\). On the probabilistic side it has the tilted-measure identities \(\mathbb EY=b'(\theta)\), \(\mathop{\mathrm{Var}}Y=b''(\theta)\) for one-parameter natural families, independence of jointly Gaussian variables with zero covariance, conditional independence, the posterior kernel and Bayes estimators, and the scalar limit theorems. Combinatorial ingredients include the graph Laplacian with its kernel dimension equal to the number of components, Hadamard matrices, finite projective planes, Galois fields, shifted Legendre polynomials, directed graphs and kernel composition; Fisher's inequality is available only for \(\lambda=1\), through incidence configurations (105.42 has ingredients only). Finite-population inclusion-probability estimators and the survey-sampling variance and allocation formulas (105.72, 105.73) are also absent; finite moment identities are ingredients only. Absent are Gauss–Markov, the normal sampling theory of least squares and the noncentral laws, Cochran's theorem and exact \(F\) tests, generalized linear model fitting and asymptotics, Hotelling's \(T^2\), Wilks's lambda and covariance tests, Markov properties on graphs, optimal and combinatorial designs, randomization inference, the identification formulas of causal inference, \(d\)-separation and the do-calculus. [Details in STRUCTURE105.md](STRUCTURE105.md).

## 106. Dependent data and stochastic models

**Thin.** Mathlib proves Doob's maximal inequality for nonnegative submartingales, which gives Ville's bound for nonnegative martingales on each finite horizon (106.38, partly; the supermartingale case, the infinite horizon and the e-value consequences are not stated). Its orthogonal projection theorem supplies the abstract minimality among linear predictors in 106.20 (partly, together with TauCeti's Gaussian conditioning), without the explicit kriging coefficients and error formula. Supporting are the Kolmogorov extension theorem, the maximal ergodic inequality for Birkhoff averages, uniqueness of Fourier coefficients on the circle, first-passage stopping times, the i.i.d. one-dimensional central limit theorem, Gram–Schmidt orthogonalization (finite-sample innovations), the variance of a sum as a double sum of covariances, Fourier series and Parseval's identity on the circle, positive semidefiniteness of Gram matrices, von Neumann's mean ergodic theorem, Markov kernels with invariance, reversibility and trajectory laws, the Gaussian-process predicate, the Poisson law with the binomial-to-Poisson limit, the limit \((1+a_n)^n\to e^t\), the exponential and Pareto laws, and Bessel functions of the first kind. No central limit theorem for dependent data is present. Absent are weakly stationary processes, autocovariances and spectral densities, the Wold decomposition, ARMA, Whittle and GARCH theory, Kalman filtering and hidden Markov models, mixing and the block bootstrap, Matérn covariances, point processes, counting processes and their martingales, Kaplan–Meier, Nelson–Aalen and Cox regression, sequential probability ratio tests and Wald's identity, CUSUM and optimal change detection, regular variation and extreme-value limit theory. [Details in STRUCTURE106.md](STRUCTURE106.md).

## 107. Statistical learning and machine learning

**Thin.** The only entry reached is 107.38 (partly): circulant matrices commute with one another and hence with the cyclic shift; the converse, the Fourier diagonalization, permutation-equivariant layers and self-attention are not stated. Mathlib has no learning rule, hypothesis class with risk, policy, Markov decision process or privacy mechanism. Supporting material is varied: shattering, VC dimension of finite set families and the Sauer–Shelah bound; Hoeffding's lemma and inequality and the Azuma–Hoeffding bound; nearest-point projection onto convex sets; reproducing-kernel Hilbert spaces; Gibbs' inequality, the chain rule and data processing for the KL divergence; the variance of a sum (107.22 has ingredients only); strict concavity of the entropy functions (107.25 has ingredients only); derivatives of the cumulant-generating function; the binomial random graph with its mass formula; Ionescu–Tulcea laws of interaction; the Banach fixed-point theorem and Neumann series (the abstract halves of the Bellman statements); change of measure (107.68 has ingredients only); conditional independence and Bayes' theorem; and the discrete Fourier transform. Absent are PAC learnability and the fundamental theorem, Rademacher complexity, the Bayes classifier and surrogate-loss comparisons, kernel ridge and nearest-neighbour rates, trees, boosting and belief propagation, every neural-network entry, stochastic block models and random-graph thresholds, bandits and reinforcement learning, differential privacy, fairness incompatibility and distribution-shift bounds. [Details in STRUCTURE107.md](STRUCTURE107.md).

## 108. Geometry of data: manifolds, topology, optimal transport, and kernels

**Thin.** For finite simple graphs Mathlib proves that the Laplacian \(L=D-A\) has the quadratic form \(\frac12\sum_{i\sim j}(x_i-x_j)^2\), is positive semidefinite, and has kernel dimension equal to the number of connected components (108.11, partly; weighted, normalized and random-walk Laplacians and the bipartite criterion are absent). Nothing else of the section is proved. Supporting material comprises Rayleigh quotients and the spectral theorem, Gram matrices and singular values, the inequalities between distance functions and Hausdorff distance (108.27 has ingredients only), the Gromov–Hausdorff distance, abstract and geometric simplicial complexes with the two definitions of the Euler characteristic (not shown to agree), Riemannian manifolds with their distance, reproducing-kernel Hilbert spaces, injectivity of characteristic functions, the Lévy–Prokhorov metric and Prokhorov's theorem, the strong law in Banach spaces, Hoeffding's inequality and covariance bilinear forms. Mathlib has no Wasserstein distance and no optimal transport, so all of 108B beyond these ingredients rests on TauCeti. Absent are Cheeger inequalities, diffusion maps and multidimensional scaling, Fréchet means on manifolds and shape spaces, persistence modules, barcodes and their stability, Čech and Rips complexes and the nerve theorem, homology inference, empirical transport rates and transport-map estimation, maximum mean discrepancy and kernel tests, kernel Stein discrepancies and random features. [Details in STRUCTURE108.md](STRUCTURE108.md).
