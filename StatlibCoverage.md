# Statlib coverage of Sections 101–108

This file summarises, section by section, what Statlib adds to Mathlib for the
mathematical content described in [`SYNOPSIS101.md`](SYNOPSIS101.md)–[`SYNOPSIS108.md`](SYNOPSIS108.md).
It is a digest of the Statlib parts of the coverage inventories
[`STRUCTURE101.md`](STRUCTURE101.md)–[`STRUCTURE108.md`](STRUCTURE108.md), which give the
declarations, source links, and hypotheses, and classify every numbered synopsis
entry as covered, partly covered, or not covered by the three libraries together.
The companion files [MathlibCoverage.md](MathlibCoverage.md) and
[TauCetiCoverage.md](TauCetiCoverage.md) summarise the Mathlib and TauCeti
coverage in the same way, and [GAPS.md](GAPS.md) selects and assesses the
principal missing results. Results that Statlib imports from Mathlib, and
duplicates of Mathlib results in its `ForMathlib` directory, are not attributed
to Statlib here; where a Statlib result specialises or repackages Mathlib
material, only the addition is described. Statlib and TauCeti are developed
independently on top of Mathlib; where both prove a result, the overlap is
noted without preference.

Statlib is a library of statistical divergences and tests. Its strength is the
divergence layer: \(f\)-divergences, the squared Hellinger distance, Rényi and
Chernoff divergences, the Jensen–Shannon divergence, tensorization and the
conditional form of the Kullback–Leibler divergence, mutual information,
DeGroot's statistical information, and total variation in its variational,
density, and event forms. On this it builds binary testing in Bayes form, with
the Bayes risk of a test between two laws and its identification with total
variation, and testing lower bounds: the Bretagnolle–Huber inequality, a binary
Fano inequality, and sample-complexity bounds through Rényi divergences. It also
has likelihood ratios and divergences of i.i.d. laws stopped at a stopping time,
Wald's identity, e-variables and numeraires, definitions of contiguity and of
differentiability in quadratic mean, and a notation for potential responses.
It lacks sufficiency, Fisher information, tests of prescribed size and power,
\(p\)-values, confidence sets, estimators and their asymptotic theory, Shannon
entropy of finite distributions, linear models, and the geometric and
transport material of Section 108. Its contribution to the synopsis entries is
therefore mostly supporting. Six of the eight verdicts below are Thin and two
are None.

## Source baseline

Statlib commit
[`eeaac0283690efaa60c31115400cf561836baeb9`](https://github.com/stat-lib/statlib/tree/eeaac0283690efaa60c31115400cf561836baeb9)
of 2026-11-05, from <https://github.com/stat-lib/statlib>, whose own Mathlib pin
is Mathlib
[`6135ffb78e8bcd3fcc8ec02f3f82ea0b0737358b`](https://github.com/leanprover-community/mathlib4/tree/6135ffb78e8bcd3fcc8ec02f3f82ea0b0737358b)
of the same date, using Lean `v4.36.0-rc2`. The coverage was checked on
2026-11-06 by inspecting the source of a local checkout; see the
[source conventions](STRUCTURE.md#source-baseline-and-conventions) of the series.
A Statlib result is counted as proved only when the cited declaration does not
rely on `sorry`, `admit`, or an added axiom, as far as can be seen in its
source; no such use occurs in the Statlib source at this revision. The full Statlib library builds against this Mathlib pin. Plans
recorded in comments and declaration names alone are not counted. Statlib's
`sqHellinger` is half the squared Hellinger distance \(H^2\) of the synopses,
and the `tvDist` of two probability laws is twice the total-variation distance
\(\|P-Q\|_{\mathrm{TV}}\) of the synopses; statements below are given in the
synopsis convention unless a declaration is quoted. Statements here are
summaries: the full hypotheses of the cited declarations, as recorded in the
STRUCTURE files, govern their use.

The classification of entries follows the uniform rule of
[STRUCTURE.md](STRUCTURE.md): an entry is partly covered when a library
declaration proves one of the claims the entry makes, or a special case of it;
an entry for which the libraries supply only ingredients, from which the
statement would follow by a further argument however short, is not covered.
Such *ingredients only* entries are mentioned below among the supporting
material, not as coverage.

These are direct-coverage verdicts under the CKSD rule. CKMA does not consider
Statlib, and its verdicts for the other libraries are not numerically
comparable with these without reconciling the rules and source revisions; see
[Comparison with CKMA](STRUCTURE.md#comparison-with-ckma).

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
- [104](#104-bayesian-inference-and-stochastic-computation) Bayesian inference and stochastic computation — Thin
- [105](#105-linear-models-multivariate-analysis-experimental-design-and-causal-inference) Linear models, multivariate analysis, experimental design, and causal inference — None
- [106](#106-dependent-data-and-stochastic-models) Dependent data and stochastic models — Thin
- [107](#107-statistical-learning-and-machine-learning) Statistical learning and machine learning — Thin
- [108](#108-geometry-of-data-manifolds-topology-optimal-transport-and-kernels) Geometry of data: manifolds, topology, optimal transport, and kernels — None

Across the 537 numbered entries of Sections 101–108, the three libraries
together cover 5 entries, partly cover 55, and do not cover 477. Statlib takes
part in two covered entries: 101.66, together with TauCeti, and 101.44, which is
covered by Mathlib with TauCeti and for which Statlib also proves the product
rule, its \(n\)-fold form, and the averaged chain rule. It takes part in three
partly covered entries, 107.8 on its own and 101.33 and 104.9 together with
Mathlib.

## 101. Statistical inference: foundations, decision theory, estimation, and testing

**Thin.** Statlib supplies the testing half of 101.66 (covered, with TauCeti's Pinsker inequality): for probability laws the Bayes risk of testing \(P\) against \(Q\) with unit prior weights is \(1-\|P-Q\|_{\mathrm{TV}}\), it is the infimum of \(P\varphi+Q(1-\varphi)\) over randomized tests \(\varphi\), nonrandomized tests suffice, and the likelihood-ratio test of threshold one attains it, as an argmin estimator and hence a Bayes estimator by Mathlib's `IsArgminEstimator.isBayesEstimator`. For 101.44 (covered by Mathlib with TauCeti) Statlib proves the product rule for two factors, for finite products, and in the \(n\)-fold form \(D(\mu^{\otimes n}\|\nu^{\otimes n})=n\,D(\mu\|\nu)\), and the averaged chain rule through the conditional divergence of the disintegrations; it adds a chain rule through the posteriors and joint convexity of the divergence. For a dominated model with an argmin rule, the Bayes risk is the marginal expectation of the minimal posterior expected loss written with the Radon–Nikodym densities of the model (101.33, partly, with Mathlib). Supporting are the Bayes form of the likelihood-ratio test of two laws (101.14 has ingredients only; tests of prescribed size and uniqueness are not stated), measurable rules maximizing the posterior probability under the 0–1 loss on countable parameter spaces, concavity of the Bayes risk in the data-generating kernel and its homogeneity in the prior, invariance of every \(f\)-divergence under restriction to the \(\sigma\)-algebra generated by \(d\mu/d(\mu+\nu)\) (the divergence form of the sufficiency of the likelihood ratio, not a factorization theorem), refinements of the easy direction of Blackwell's theorem — monotonicity of the Bayes risk under forgetting a component, the splitting of the risk increase under a garbling, data processing for the binary Bayes risk and DeGroot's statistical information, and preservation of \(f\)-divergences under kernels with a Markov left inverse (101.62 has ingredients only) — the variational and density forms of total variation with its data-processing inequality, the Bretagnolle–Huber inequality, the event form \(\mathrm{etvDist}=2\sup_A(\mu(A)-\nu(A))\), and the inference-model structures packaging a family of laws, a target functional, data, a rule, and a loss. The two-factor product rule, the averaged chain rule, and the event form of total variation are also proved in TauCeti. Nothing is added on sufficiency, exponential families, Fisher information, tests of prescribed size and power, \(p\)-values, confidence sets, minimax theorems, admissibility, complete classes or equivariance, and Pinsker's inequality is not stated in Statlib. [Details in STRUCTURE101.md](STRUCTURE101.md).

## 102. Asymptotic, semiparametric, and robust statistics

**Thin.** Statlib reaches no entry, but it supplies two of the section's own definitions. Contiguity of a family \(Q_a\) with respect to \(P_a\), for probability measures on varying spaces indexed along a filter, is defined in five forms (`Contiguous1`–`Contiguous5`): by events along every finer filter or along the filter itself, through weak limits of likelihood-ratio laws, and by transfer of convergence in probability to zero. Only the equivalence of the first and the transfer form (`contiguous1_iff_contiguous4`) and the implication from the first to the event form along the filter (`Contiguous1.contiguous5`) are proved; the equivalences with the likelihood-ratio forms, which contain Le Cam's first lemma, are not proved and appear only as plans in comments (102.12 has ingredients only). Differentiability in quadratic mean within a set is defined by the \(L^2(\mu)\) estimate of 102.13, implies a Hadamard-type condition along local paths, and gives a score of mean zero, in particular at interior points (102.13 has ingredients only). Supporting are the squared Hellinger distance and the weak law of large numbers for pairwise independent, identically distributed integrable variables in a Banach space. Nothing is added on the delta method, maximum likelihood, local asymptotic normality, the divergence expansion, Le Cam's third lemma, the representation, convolution and minimax theorems, \(U\)-statistics, semiparametric efficiency, influence functions and robust estimation, or the expansions, resampling and invariance theorems of 102B. [Details in STRUCTURE102.md](STRUCTURE102.md).

## 103. Nonparametric and high-dimensional inference

**Thin.** Statlib reaches no entry; its contribution is the two-point and Fano layer of minimax lower bounds. Supporting are the testing identity \(\inf_\psi(P_0(\psi=1)+P_1(\psi=0))=1-\|P_0-P_1\|_{\mathrm{TV}}\), from the binary Bayes risk as an infimum over randomized tests and over measurable rejection regions, the Bretagnolle–Huber inequality in both forms, and the identity \(D(Q_0^{\otimes n}\|Q_1^{\otimes n})=n\,D(Q_0\|Q_1)\) (103.39 has ingredients only, with Pinsker's inequality from TauCeti; the two-point bound itself is not stated); mutual information as \(\mathrm{KL}(\rho\|\rho_1\otimes\rho_2)\), its conditional-divergence form and the decomposition \(\mathrm{KL}(\mu\otimes P\|\mu\times\xi)=I(\mu\otimes P)+\mathrm{KL}(P\circ\mu\|\xi)\), the bound \(\mathrm{kl}(R_\pi^P,R_\pi^0)\le I(\pi\otimes P)\) for losses in \([0,1]\), its two-model analogues for the divergence and every \(f\)-divergence, and a binary Fano inequality through the Jensen–Shannon divergence (103.40 has ingredients only; the \(M\)-ary bound is not stated); the pairwise testing bounds for the hypercube construction (103.46 has ingredients only; the reduction to edges is not stated); two-sided bounds for \(n\)-fold products of two simple hypotheses through the Rényi divergence of order \(1/2\), bearing on 103.13, whose composite alternatives are not treated; and the comparison \(\mathrm{sqHellinger}\le\tfrac12\mathrm{tvDist}\le\sqrt{\mathrm{sqHellinger}\,(2-\mathrm{sqHellinger})}\) of the squared Hellinger distance with total variation. The two-factor tensorization is also proved in TauCeti. Nothing is added on white-noise models and Sobolev balls, empirical processes, rank tests, kernel smoothing and splines, shape constraints and log-concave estimation, Hamming packing, sparse regression and recovery, multiple testing, covariance estimation or random-matrix asymptotics. [Details in STRUCTURE103.md](STRUCTURE103.md).

## 104. Bayesian inference and stochastic computation

**Thin.** Statlib reaches one entry. Under the 0–1 loss on a standard Borel parameter space, with a finite data kernel and a finite prior, a measurable rule maximizing the posterior probability almost everywhere is an argmin estimator, hence Bayes by Mathlib's Bayes-estimator framework, and on a countable parameter space such a rule exists; with the two models as parameter space this is the statement that a model of largest posterior probability is a Bayes decision (104.9, partly, with Mathlib; the Bayes-factor ratio is not stated). Supporting are differentiability in quadratic mean with its mean-zero score and the contiguity definitions (104.1 has ingredients only); the squared Hellinger distance and its comparison with total variation, the bound \(\pi\{\mathrm{false}\}^a\pi\{\mathrm{true}\}^{1-a}\exp(-(1-a)R_a(\mu,\nu))\) for the Bayes risk of testing two laws, and the sample size at which the risk of \(n\) independent observations falls below \(\delta\), all for simple hypotheses, whereas 104.18 and 104.19 need tests against complements of neighbourhoods; the chain rule for joint laws through the posterior kernels; tensorization over finite products, bearing on 104.36; the chain rule for the conditional divergence of a composition of two kernels, the inductive step for 104.73–104.75; and data processing for total variation, which bears on 104.68 only as supporting material. Tensorization is also proved in TauCeti. Nothing is added on conjugate updates, posterior asymptotics and the Bernstein–von Mises theorem, the Dirichlet process and posterior contraction, Monte Carlo and Markov-chain samplers, Langevin dynamics, particle methods, or the transport and Schrödinger material of 104C. [Details in STRUCTURE104.md](STRUCTURE104.md).

## 105. Linear models, multivariate analysis, experimental design, and causal inference

**None.** Statlib's only material for the section is notation and an abstract test. A potential response assigns a value to each intervention and unit (`PotentialResponse`), `PotentialResponse.select` gives the observed outcome \(Y_i=Y_i(A_i)\) under consistency, and same-unit substitution forms nested responses \(Y(a,M(a'))\) (105.61 has ingredients only, with TauCeti's functional representation of conditional independence); no probability structure, assignment mechanism, estimand or estimator is defined. Supporting is the Bayes test between two laws in likelihood-ratio form, the abstract two-class Bayes rule, whose evaluation for Gaussian class laws in 105.25 is not stated. Nothing is added on linear models and least squares, quadratic forms and Cochran's theorem, generalized linear models, multivariate distribution theory and tests, designs, survey sampling, randomization inference, identification formulas, mediation, or graphical causal models. [Details in STRUCTURE105.md](STRUCTURE105.md).

## 106. Dependent data and stochastic models

**Thin.** Statlib reaches no entry; its contribution is a sequential-sampling layer in 106B. Supporting are Wald's identity, in a general form for random times and in the i.i.d. form \(\mathbb E\sum_{n\le\tau}f(\omega_n)=\mathbb E[\tau+1]\int f\,d\mu\) for integrable stopping times, which with \(N=\tau+1\) is \(\mathbb ES_N=\mathbb EN\,\mathbb EZ\) and is stated in neither Mathlib nor TauCeti (106.41 has ingredients only); the likelihood ratio of i.i.d. laws restricted to the \(\sigma\)-algebra of a stopping time as a product of densities, its logarithm as a sum, and the divergence \(\mathbb E_\mu[\tau+1]\,\mathrm{KL}(\mu,\nu)\) of the stopped laws (106.37 has ingredients only); a Rényi-divergence bound for stopped laws, an information ingredient for detection-delay lower bounds; and e-variables, convex and closed under \(\liminf\), with products of e-variables for product measures, the independent-product case of the e-value construction in 106.38, and the existence and almost-sure uniqueness of the numeraire e-variable (106.40 has ingredients only). Nothing is added on time-series models and spectral estimation, state-space and hidden Markov models, mixing, spatial statistics and point processes, counting processes and survival estimators, the sequential probability ratio test, Wald's fundamental identity, Ville's inequality and conditional e-values, change detection, or extreme-value theory. [Details in STRUCTURE106.md](STRUCTURE106.md).

## 107. Statistical learning and machine learning

**Thin.** Statlib reaches one entry on its own. The Bayes test between the conditional laws of \(X\) given \(Y=0\) and \(Y=1\), with the law of \(Y\) as prior, is the rule \(1_{\{\eta\ge1/2\}}\) in likelihood-ratio form, it is an argmin and hence Bayes estimator for the 0–1 loss, and its Bayes risk is \(\mathbb E\min(\eta(X),1-\eta(X))\) (107.8, partly; the excess-risk identity, the plug-in bound and the margin bound are not stated). Supporting are the Jensen–Shannon divergence of weight \(\alpha\) as an \(f\)-divergence, with its vanishing criterion and variational form (107.32 has ingredients only); the divergence of i.i.d. laws stopped at a stopping time and Wald's identity, the single-arm forms of the bandit divergence decomposition (107.49 has ingredients only); the Bretagnolle–Huber inequality with tensorization over finite products (107.62 has ingredients only); the integral forms of total variation, which bound \(d_{\mathcal H\Delta\mathcal H}\) by `tvDist` for 107.68; data processing for total variation and for mutual information under componentwise kernels, bearing on 107.75; and the contiguity definitions, of which `Contiguous5` is the sequential form of the synopsis (107.42 has ingredients only). The two-factor tensorization is also proved in TauCeti. Nothing is added on Shannon entropy of finite distributions, learning rules and generalization bounds, classification theory beyond the Bayes rule, trees and ensembles, neural networks and the optimal discriminator, block models and Le Cam's first lemma, the bandit model and its multi-armed divergence decomposition, differential privacy, or distribution shift. [Details in STRUCTURE107.md](STRUCTURE107.md).

## 108. Geometry of data: manifolds, topology, optimal transport, and kernels

**None.** Statlib's only material for the section is the integral form of total variation: for finite measures and measurable \(f\) with \(|f|\le1\), \(\int f\,d\mu-\int f\,d\nu\le\) `tvDist μ ν`, with `tvDist μ ν` the supremum of these differences. Since every \(f\) of bounded-Lipschitz norm at most one satisfies \(|f|\le1\), this is supporting material for the inequality \(\beta\le2d_{\mathrm{TV}}\) of 108.69, which is not stated. Nothing is added on spectral embeddings, Fréchet means and shape analysis, topological data analysis, optimal transport and its statistics, or kernel methods and MMD. [Details in STRUCTURE108.md](STRUCTURE108.md).
