# TauCeti coverage of Sections 101–108

This file summarises, section by section, what TauCeti adds to Mathlib for the
mathematical content described in [`SYNOPSIS101.md`](SYNOPSIS101.md)–[`SYNOPSIS108.md`](SYNOPSIS108.md).
It is a digest of the TauCeti parts of the coverage inventories
[`STRUCTURE101.md`](STRUCTURE101.md)–[`STRUCTURE108.md`](STRUCTURE108.md), which give the
declarations, source links, and hypotheses, and classify every numbered synopsis
entry as covered, partly covered, or not covered by the two libraries together.
The companion file [MathlibCoverage.md](MathlibCoverage.md) summarises the Mathlib
coverage in the same way, and [GAPS.md](GAPS.md) selects and assesses the principal
missing results. Results that TauCeti imports from Mathlib are not attributed to
TauCeti here; where a TauCeti result specialises or repackages Mathlib material,
only the addition is described.

TauCeti's additions are larger than Mathlib's for this material, but they are
mostly distribution theory, information theory, optimal transport and matrix
analysis rather than statistical theorems. Statistical inference proper is
thinly covered. Six of the eight verdicts below are Thin; the two Partial
verdicts rest on the entropic transport and Schrödinger material of 104C and on
the Wasserstein barycenter, Fréchet mean and kernel embedding material of 108.

## Source baseline

TauCeti commit
[`a049b4264d2cf4dbf4720796f844a3a3764914a5`](https://github.com/TauCetiProject/TauCeti/tree/a049b4264d2cf4dbf4720796f844a3a3764914a5)
of 2026-10-18, compared with Mathlib
[`911003dd6dea5df215dff57f2717be762e11a6ca`](https://github.com/leanprover-community/mathlib4/tree/911003dd6dea5df215dff57f2717be762e11a6ca)
of the same date. The coverage was checked on 2026-11-01 by inspecting the
source of local checkouts; see the
[source conventions](STRUCTURE.md#source-baseline-and-conventions) of the series.
This is a later TauCeti revision than the one recorded in the sibling CKMA
inventories. A TauCeti result is counted as proved only when the cited
declaration does not rely on `sorry`, `admit`, or an added axiom, as far as can
be seen in its source. Roadmap targets, comments describing future work, and
declaration names alone are not counted. No local build or axiom-dependency
check was run. Statements here are summaries: the full hypotheses of the cited
declarations, as recorded in the STRUCTURE files, govern their use.

The classification of entries follows the uniform rule of
[STRUCTURE.md](STRUCTURE.md): an entry is partly covered when a library
declaration proves one of the claims the entry makes, or a special case of it;
an entry for which the libraries supply only ingredients, from which the
statement would follow by a further argument however short, is not covered.
Such *ingredients only* entries are mentioned below among the supporting
material, not as coverage.

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
- [103](#103-nonparametric-and-high-dimensional-inference) Nonparametric and high-dimensional inference — Thin
- [104](#104-bayesian-inference-and-stochastic-computation) Bayesian inference and stochastic computation — Partial
- [105](#105-linear-models-multivariate-analysis-experimental-design-and-causal-inference) Linear models, multivariate analysis, experimental design, and causal inference — Thin
- [106](#106-dependent-data-and-stochastic-models) Dependent data and stochastic models — Thin
- [107](#107-statistical-learning-and-machine-learning) Statistical learning and machine learning — Thin
- [108](#108-geometry-of-data-manifolds-topology-optimal-transport-and-kernels) Geometry of data: manifolds, topology, optimal transport, and kernels — Partial

Across the 535 numbered entries of Sections 101–108, the two libraries together
cover 4 entries, partly cover 48, and do not cover 483. TauCeti takes part in all
four covered entries: 104.28, 108.41 and 108.49 on its own, and 101.44 together
with Mathlib. It takes part in 37 of the partly covered entries, 31 on its own
and 6 (101.17, 101.27, 101.66, 104.21, 104.25, 106.20) together with Mathlib.

## 101. Statistical inference: foundations, decision theory, estimation, and testing

**Thin.** TauCeti completes the relative-entropy entry 101.44 (covered, with Mathlib): the divergence tensorizes over products, and the chain rule is identified with the averaged divergence of the conditional kernels. Its distribution library defines the chi-squared, Student \(t\) and Fisher \(F\) laws and proves the known-mean chi-squared law of a Gaussian sum of squares and the \(t\) and \(F\) ratio constructions (101.17, partly; the law of \(S^2\) and its independence from \(\bar X\) are absent). For an i.i.d. sample from any real law, atoms included, the \(k\)-th order statistic has the binomial-tail distribution function, equivalently a regularized incomplete beta value, and for uniform samples it is beta-distributed (101.21, partly; joint densities and rank laws are absent). The second moment of a Euclidean law as squared mean plus covariance trace is the bias–variance decomposition (101.27, partly), and Pinsker's inequality is proved without absolute continuity (101.66, partly). Supporting are one-parameter tilting of moment- and cumulant-generating functions with closure of the Gaussian, gamma, Poisson and binomial families under tilting, moment-generating-function determinacy near \(0\) (the analytic step of completeness), the probability integral transform (101.25 has ingredients only), the binomial tail, beta quantiles and stochastic order of binomial laws (the unstated Clopper–Pearson bound), the hypergeometric and beta-binomial laws, gamma laws of exponential sums (101.28 has ingredients only), the moment-generating function of Gaussian quadratic forms, convexity of the divergence, Csiszár's Pythagorean identity, the Donsker–Varadhan formula, and a large catalogue of classical laws. Nothing is added on sufficiency, Fisher information, tests and confidence sets, decision theory, admissibility or equivariance. [Details in STRUCTURE101.md](STRUCTURE101.md).

## 102. Asymptotic, semiparametric, and robust statistics

**Thin.** TauCeti's one asymptotic statistical theorem is the strong consistency of empirical Fréchet barycenters: for i.i.d. points of a separable pseudometric space with finite \(p\)-th moment, almost surely every cluster point of empirical \(p\)-barycenters is a population barycenter, the minimal empirical radius converges, and on a proper space the barycenters converge when the population barycenter is unique. The proof goes through almost-sure \(W_p\) convergence of empirical measures. This is a particular \(M\)-estimator (102.23, partly; the general criterion is absent). The remaining material is supporting: the quantile function with its Galois characterization and the exact laws of order statistics, the clipped law behind the trimmed mean, the chi-squared law of Gaussian sums of squares and the moment-generating function of Gaussian quadratic forms, affine images of multivariate Gaussians (the covariance \(Dg\,\Sigma\,Dg^{\mathsf T}\) of the delta method), the randomization coding of kernels, Gaussian tilting (the Gaussian side of Le Cam's third lemma in dimension one), a pointwise Hellinger–KL integrand inequality, Gaussian distribution functions and quantiles, the multinomial covariance behind Pearson's theorem, the Hermite basis of \(L^2(\gamma)\), and the sampling-with-replacement law, which is exactly the bootstrap resampling law given the sample. No limit theorem of the section is proved: nothing is added on the delta method, maximum likelihood, contiguity and local asymptotic normality, U-statistics, semiparametric efficiency, influence functions and robust estimation, higher-order expansions, or bootstrap consistency. [Details in STRUCTURE102.md](STRUCTURE102.md).

## 103. Nonparametric and high-dimensional inference

**Thin.** TauCeti's only entry is 103.31 (partly): Ky Fan's trace inequality bounds the variance captured by a rank-\(k\) orthogonal projection by the sum of the \(k\) largest eigenvalues, which is the finite-dimensional deterministic core of the optimality of principal components; attainment, uniqueness and the Hilbert-space case are not stated. Supporting material is substantial but stops short of statements: the probability integral transform and inverse transform sampling (distribution-freeness), \(L^p\) approximate identities (the bias half of \(L^1\) consistency of kernel density estimates), laws of order statistics (exact rank scores), the binomial law of Bernoulli sums (103.18 has ingredients only), the Prékopa–Leindler and Brunn–Minkowski inequalities, a Hilbert eigenbasis for compact symmetric operators (the deterministic Karhunen–Loève step), Pinsker's inequality and tensorization of the divergence (103.39 has ingredients only), Hamming minimum distance of codes, Schatten and Ky Fan norms, Gaussian conditioning, sample second-moment matrices with polynomial deviation bounds, Wishart laws, and the dimension-free Davis–Kahan \(\sin\Theta\) theorem with Weyl's bound (103.54 has ingredients only). Nothing is added on empirical processes, rank tests, kernel smoothing and splines, shape constraints, minimax lower bounds, sparse regression and recovery, multiple testing, covariance estimation or random-matrix asymptotics. [Details in STRUCTURE103.md](STRUCTURE103.md).

## 104. Bayesian inference and stochastic computation

**Partial.** The verdict rests on the entropic side of 104C; the rest of the section is thin. TauCeti defines the static and dynamic Schrödinger problems, proves existence and uniqueness of the minimizer, the reduction of the dynamic to the static problem, and the endpoint-density form of the bridge property (104.66, partly; the Brownian reference is absent). It proves the Pythagorean identity, minimality and uniqueness of potentials for couplings of product form (104.71, partly), the continuity equation for the time marginals of laws on curves and of plan interpolations, with the conditional-expectation velocity (104.67, partly), and the upper action bound with equality to \(W_2^2\) for optimal couplings (104.72, partly). Relative-entropy projection onto a prescribed marginal gives the half-bridges, and for iterative proportional fitting the telescoping identity, monotonicity and convergence of the marginal errors (104.77, partly; path-space iteration and convergence of couplings are absent). The JKO step has minimizers under abstract hypotheses, unique under generalized-geodesic convexity, with lower semicontinuity and coercivity of the Boltzmann entropy (104.43, partly). Inverse transform sampling and the probability integral transform are covered (104.28). Gaussian conditioning gives the known-variance normal posterior for one observation (104.4, partly), and TauCeti adds the sample-mean variance to 104.21 and the evidence identity for nonnegative potentials to 104.25 (both partly, with Mathlib). Supporting are the Beta, Gamma, Dirichlet and multinomial families with the beta-binomial and Gamma–Poisson marginals (104.7 has ingredients only), Dirichlet aggregation, EVI contraction, convexity of potential energy, the Gaussian \(W_2\) formula and multinomial moments (104.61 has ingredients only). Nothing is added on conjugate updates, posterior asymptotics, the Dirichlet process, Markov-chain sampler convergence, Langevin dynamics, displacement convexity of entropy, particle methods or score-based diffusion models. [Details in STRUCTURE104.md](STRUCTURE104.md).

## 105. Linear models, multivariate analysis, experimental design, and causal inference

**Thin.** TauCeti's multivariate distribution theory is the most developed material of the section, but it reaches entries only in part. Gaussian conditioning with affine images gives the conditional mean of random effects in the mixed model with \(\beta\) known (105.14, partly). The Gram sum of \(n\ge p\) independent \(N_p(0,\Sigma)\) vectors has the nonsingular Wishart density law (105.22, partly; \(\bar X\), \(S\) and Hotelling's \(T^2\) are absent), and the Wishart density, congruence, principal-submatrix marginals and the Bartlett decomposition are proved (105.31, partly; the Schur-complement law and the determinant law are absent). Independence of Gaussian blocks is equivalent to vanishing cross-covariance (105.29, partly), and Ky Fan's inequality bounds captured variance by the leading eigenvalues (105.30, partly; the Frobenius Eckart–Young theorem is not stated). Supporting are the chi-squared law of Gaussian squares and its convolution, the moment-generating function of Gaussian quadratic forms (one step from the central case of 105.15), the \(t\) and \(F\) ratio laws, the trace of an idempotent as its rank, the covariance matrix and Gaussian density, Courant–Fischer, operator-norm Eckart–Young, principal cosines, the Gamma–Beta relation, Wishart moments and transforms, weak union for conditional independence, concavity of \((\det A)^{1/n}\) (the D-criterion), finite iterative proportional fitting, sampling without replacement, the functional representation of conditional independence, the modified Bessel function \(I_\nu\), and the logistic derivative. Nothing is added on linear models and least squares, noncentral laws and Cochran's theorem, generalized linear models, multivariate tests, graphical Markov properties, designs, or causal identification. [Details in STRUCTURE105.md](STRUCTURE105.md).

## 106. Dependent data and stochastic models

**Thin.** TauCeti's contributions are three general theorems applied to entries in part. Gaussian conditioning gives the first Kalman measurement update (106.7, partly; the recursion is absent), the Gaussian one-step conditional laws of the innovations likelihood (106.13, partly), and the Gaussian form of simple kriging (106.20, partly, with Mathlib's projection theorem). Herglotz's theorem, positive definiteness on \(\mathbb Z\) equivalent to a spectral measure on the circle, gives the analytic half of the spectral representation (106.14, partly), and Bochner's theorem on \(\mathbb R^d\) the corresponding statement for covariance functions of random fields (106.24, partly; the random-field interpretation and the Matérn family are absent). The hazard representation \(S=e^{-\Lambda}\) for absolutely continuous failure times and the law of a minimum of independent times give part of 106.33 (cause-specific hazards are absent). Supporting are the path law of a Markov chain with its cylinder formula, \(L^2\) convergence of Birkhoff averages to the conditional expectation on the invariant \(\sigma\)-algebra, recurrence of stationary processes and i.i.d. excursions, the Kolmogorov decomposition of positive-definite kernels, Poisson moments, the Cauchy characteristic function, the Gumbel, Weibull and Pareto laws, distribution functions of extremes and order statistics (106.50 has ingredients only), the Moore–Penrose pseudoinverse and sample-mean errors. Nothing is added on stationary-process estimation, ARMA and GARCH, hidden Markov models, mixing, point processes, counting processes and survival estimators, sequential tests, change detection, or extreme-value limit theory. [Details in STRUCTURE106.md](STRUCTURE106.md).

## 107. Statistical learning and machine learning

**Thin.** TauCeti reaches two entries. Block Gaussian conditioning with a positive-definite observed block gives the Gaussian-process posterior mean and covariance at finitely many test points (107.34, partly; the kernel ridge identification is not stated). The graphon form of the Aldous–Hoover theorem is proved: every law on graphs on \(\mathbb N\) invariant under all permutations is a unique mixture of graphon sampling laws, with uniqueness up to cut distance zero, and graphons at cut distance zero have the same sampling laws and homomorphism densities (107.43, partly; the reduction from invariance under finite permutations and weak isomorphism by almost-everywhere equal pullbacks are not stated). Supporting are the Rademacher law, McDiarmid's bounded-differences inequality, empirical measures without uniform bounds, Kolmogorov feature maps of positive-definite kernels, exchangeability with de Finetti's theorem, the finite-sum form of the divergence (107.21 has ingredients only), the inverse-Wishart mean (107.31 has ingredients only), the Laplace law, Markov-chain path laws, tensorization of the divergence, Pinsker's inequality, the Davis–Kahan theorem, compactness of the graphon space, and the dissociated decomposition of exchangeable arrays. Nothing is added on learning rules and generalization bounds, classification theory, trees and ensembles, neural networks, block models and spectral recovery, bandits and reinforcement learning, differential privacy, fairness or distribution shift. [Details in STRUCTURE107.md](STRUCTURE107.md).

## 108. Geometry of data: manifolds, topology, optimal transport, and kernels

**Partial.** TauCeti supplies all of the section's coverage beyond the graph Laplacian. Wasserstein barycenters exist on proper spaces and are unique in \(\mathcal P_2(\mathbb R^d)\) when one law is absolutely continuous (108.41, covered), and empirical Wasserstein barycenters of i.i.d. random laws on a proper Polish space are consistent (108.49, covered). On the line the barycenter has the averaged quantile function, the quantile map is an isometry onto the nondecreasing classes, and \(\mathcal P_2(\mathbb R)\) is CAT(0) (108.45, partly); the Bures formula with a positive-definite source and the two-law Gaussian barycenter are proved (108.46, partly). Fréchet barycenters on metric spaces have compact mean sets and almost-sure consistency (108.14, partly), with uniqueness in CAT(0) spaces and existence and consistency in proper CAT(0) spaces (108.5, partly). Ky Fan's principle gives the optimal orthogonal Procrustes rotation over \(O(m)\) (108.16, partly). Entropic duality, complementary slackness and Sinkhorn half-steps (108.54, partly), the Wasserstein tangent space and the linearization bound (108.57, partly), the kernel mean embedding with the double-integral formula for \(\mathrm{MMD}^2\) (108.60, partly), and the characteristic property of universal kernels on compact metrizable spaces (108.68, partly) complete the list. Supporting are Riemannian exponential maps and Hopf–Rinow, Courant–Fischer, sin Θ bounds, Gabriel's theorem, the Čech–singular comparison, simplicial chains with Euler–Poincaré identities (108.31 has ingredients only), the Morse lemma, almost-sure empirical \(W_p\) convergence without rates, the Gromov–Wasserstein pseudodistance (108.43 has ingredients only), symmetric Schrödinger potentials, quantization errors, Brenier's theorem, Kantorovich–Rubinstein duality, Bochner's theorem and McDiarmid's inequality. Nothing is added on spectral embeddings, persistent homology and its stability and inference, statistical rates of transport, transport-map estimation, MMD tests, kernel Stein discrepancies or random features. [Details in STRUCTURE108.md](STRUCTURE108.md).
