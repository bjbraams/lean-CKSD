# Structure 104: Bayesian inference and stochastic computation

Part of the [Mathlib, TauCeti, and Statlib coverage series](STRUCTURE.md).
[Mathematical inventory](SYNOPSIS104.md); [bibliographical scope](CKSD-bib.md#cks-104).

This file follows the thematic order and lettered subdivisions of the mathematical inventory. It records definitions, structures, and proved results, with supporting material identified separately. A topic heading locates the recorded statements; the **Synopsis entries** line at the end of each section states which numbered results are covered. Where the synopsis places numbered entries directly under a subdivision heading, before its first topic heading, they are sorted in a **Synopsis entries** line under that subdivision heading.

**Source baseline.** Mathlib `6135ffb78e8bcd3fcc8ec02f3f82ea0b0737358b` of 2026-11-05, TauCeti `afa08a3ed16fb167e35de371afb1eb03fbc5913a` of 2026-11-06, and Statlib `eeaac0283690efaa60c31115400cf561836baeb9` of 2026-11-05, checked against local checkouts on 2026-11-06. See the [revision and source conventions](STRUCTURE.md#source-baseline-and-conventions).

**Mathlib source areas.** `Mathlib.Probability.Kernel.Posterior`, `Mathlib.Probability.Decision`, `Mathlib.Probability.ConditionalProbability`, `Mathlib.Probability.CondVar`, `Mathlib.Probability.Moments`, `Mathlib.Probability.Kernel.Invariance`, `Mathlib.Probability.Kernel.Irreducible`, `Mathlib.Probability.Distributions`, `Mathlib.Probability.StrongLaw`, `Mathlib.Probability.CentralLimitTheorem`, `Mathlib.Probability.Martingale.Convergence`, `Mathlib.InformationTheory.KullbackLeibler`, `Mathlib.MeasureTheory.Measure.TotalVariation`, `Mathlib.MeasureTheory.Measure.LogLikelihoodRatio`, `Mathlib.MeasureTheory.Measure.Tilted`, `Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym`, `Mathlib.Analysis.InnerProductSpace.Reproducing`, `Mathlib.Topology.MetricSpace.CoveringNumbers`, `Mathlib.MeasureTheory.Constructions.KolmogorovExtension`.

**Namespaces.** Posterior kernels, risks, and Bayes estimators are in `ProbabilityTheory`, with kernels in `ProbabilityTheory.Kernel`. Relative entropy is `InformationTheory.klDiv`; log-likelihood ratios, tilted measures, and Radon–Nikodym derivatives are in `MeasureTheory` and `MeasureTheory.Measure`. TauCeti distributions are in `TauCeti.Probability`; its relative-entropy projections, entropic transport, Wasserstein spaces, internal energies, and continuity equations are in `TauCeti`, with the reweighting `fitLaw`, iterative proportional fitting, quantiles, and the Poincaré and logarithmic Sobolev inequalities in `MeasureTheory.Measure`, and its Markov-chain period, recurrence, and coupling results in `ProbabilityTheory.Kernel`. Statlib declarations cited here are in `ProbabilityTheory`, with differentiability in quadratic mean in `QMD` and contiguity in the root namespace.

<a id="structure-104a"></a>

## 104A. Foundations, Parametric Bayesian Theory, and Nonparametric Bayes

Mathlib has a measure-theoretic core for Bayesian statistics: the posterior as a Markov kernel characterized by disintegration of the joint law of parameter and data, its Radon–Nikodym form, and Bayes risks and Bayes estimators defined through it. TauCeti supplies the named parametric families (Beta, Gamma, Dirichlet, multinomial, Student \(t\), multivariate \(t\), chi-squared, multivariate Gaussian with its conditional laws), some of their mixtures, and one conjugate pair, a Gamma prior on the precision of a multivariate Gaussian. Statlib adds the 0–1 loss, under which a rule maximizing the posterior probability is Bayes, the squared Hellinger distance, and differentiability in quadratic mean with its mean-zero score. No conjugate update in exponential-family form, Fisher information, asymptotic posterior theorem, or nonparametric prior is formalized.

[Mathematical scope](SYNOPSIS104.md#synopsis-104a).

#### Mathlib

**The posterior kernel.** For a prior \(\mu\) on a standard Borel parameter space \(\Omega\) and a finite data kernel \(\kappa\) from \(\Omega\) to \(\mathcal X\), the posterior `posterior κ μ`, written \(\kappa^\dagger\mu\), is a Markov kernel from \(\mathcal X\) to \(\Omega\) such that the law of the data composed with the posterior recovers the joint law with coordinates swapped,
\[
(\kappa\circ\mu)\otimes\kappa^\dagger\mu=\mathop{\mathrm{swap}}{}_\ast(\mu\otimes\kappa)
\]
(`ProbabilityTheory.compProd_posterior_eq_map_swap`); it is unique almost everywhere among kernels with this property (`ae_eq_posterior_of_compProd_eq`). The posterior averages back to the prior, \(\kappa^\dagger\mu\circ\kappa\circ\mu=\mu\) (`posterior_comp_self`), and posteriors compose along a chain of kernels (`posterior_comp`). If \(\kappa(\omega)\ll\kappa\circ\mu\) for \(\mu\)-almost every \(\omega\), then for almost every \(x\) the posterior is the prior with density \(\omega\mapsto d\kappa(\omega)/d(\kappa\circ\mu)\,(x)\) (`posterior_eq_withDensity`); this is Bayes' formula with the marginal law \(\kappa\circ\mu\) as reference, and the domination hypothesis holds automatically for a countable parameter space (`posterior_eq_withDensity_of_countable`). For two models, encoded by the kernel `Kernel.boolKernel` on `Bool`, the posterior probability of each model is its prior probability times the density of its sampling law against the marginal (`posterior_boolKernel_apply_true`, `posterior_boolKernel_apply_false`; all in `Probability/Kernel/Posterior.lean`). The elementary form of Bayes' theorem for events is `ProbabilityTheory.cond_eq_inv_mul_cond_mul` (`Probability/ConditionalProbability.lean`).

**Risks and Bayes estimators.** For a loss \(\ell:\Theta\times\mathcal Y\to[0,\infty]\), the average risk of a randomized estimator, the Bayes risk (infimum over Markov kernels), and the minimax risk are defined (`ProbabilityTheory.avgRisk`, `bayesRisk`, `minimaxRisk`, `Probability/Decision/Risk/Defs.lean`). The Bayes risk is bounded below by the integral over the data of the infimum of posterior expected loss, and an estimator that is a measurable pointwise minimizer of posterior expected loss (`IsArgminEstimator`) attains it (`lintegral_iInf_posterior_le_bayesRisk`, `IsArgminEstimator.isBayesEstimator`, `bayesRisk_eq`, `Probability/Decision/BayesEstimator.lean`). Existence of such a measurable minimizer is left as a hypothesis (`HasArgminEstimator`). The maximal Bayes risk is at most the minimax risk, and both satisfy data-processing inequalities (`iSup_bayesRisk_le_minimaxRisk`, `bayesRisk_le_bayesRisk_comp`, `Probability/Decision/Risk/Basic.lean`). The Bayes-rule statements of decision theory proper belong to [SYNOPSIS101](SYNOPSIS101.md).

**Moments used in posterior summaries.** For a real random variable, \(\mathop{\mathrm{Var}}X\le\mathbb E X^2\) (`ProbabilityTheory.variance_le_expectation_sq`) and the variance is unchanged by subtracting a constant (`variance_sub_const`, `Probability/Moments/Variance.lean`), so \(\mathbb E(X-a)^2\ge\mathop{\mathrm{Var}}X\) for every \(a\). The conditional variance given a sub-σ-algebra is defined, and the law of total variance \(\mathbb E\mathop{\mathrm{Var}}(X\mid m)+\mathop{\mathrm{Var}}\mathbb E(X\mid m)=\mathop{\mathrm{Var}}X\) is proved for square-integrable \(X\) (`ProbabilityTheory.integral_condVar_add_variance_condExp`, `Probability/CondVar.lean`).

**Supporting material.** The Gaussian integral and the real and multivariate Gaussian laws (`Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean`, `ProbabilityTheory.gaussianReal`, `ProbabilityTheory.multivariateGaussian`, `Probability/Distributions/Gaussian/`), with the convolution of real Gaussians (`gaussianReal_conv_gaussianReal`), are the analytic inputs for normal models and Laplace approximation. The change-of-variables formula for Lebesgue integrals, which drives the Jacobian identity behind the invariance of the Jeffreys prior, is recorded in [CKMA Structure 04](../lean-CKMA/STRUCTURE04.md). Fisher information, differentiability in quadratic mean, local asymptotic normality, and exponential families as such are not defined in Mathlib.

#### TauCeti

**Conditional Gaussian laws.** For a Gaussian vector on \(\mathbb R^{\iota\sqcup\kappa}\) with any positive-semidefinite covariance \(S\), the regular conditional law of the first block given the second is Gaussian, with the affine conditional mean through the Moore–Penrose inverse of the observed block \(S_{22}\) and the generalized Schur complement as covariance (`TauCeti.Probability.condDistrib_multivariateGaussian`, [conditional Gaussian](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Probability/Distributions/Gaussian/Conditional/Basic.lean)). When \(S_{22}\) is positive definite these are the ordinary mean \(m_1+S_{12}S_{22}^{-1}(x_2-m_2)\) and covariance \(S_{11}-S_{12}S_{22}^{-1}S_{21}\) (`EuclideanSpace.gaussianCondMean_of_posDef`, `Matrix.gaussianCondCov_of_posDef`, same file). Applied to the jointly Gaussian pair \((\mu,X)\) of a normal prior and one normal observation, this yields the known-variance normal posterior of item 4; the reduction from the whole sample to \(\bar X\) is not stated.

**Student and chi-squared laws.** Student's \(t\) law is defined for \(\nu>0\) with its density, cumulative distribution function, quantiles, and moments, and a standard Gaussian divided by the square root of an independent chi-squared variable over its degrees of freedom has the \(t_\nu\) law (`TauCeti.Probability.studentTMeasure`, `TauCeti.Probability.hasLaw_studentT_of_gaussian_chiSquared`, [Student \(t\)](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Probability/Distributions/StudentT/ChiSquared.lean)). These are the laws in which the marginal posterior of item 4 is expressed; the Bayesian computation with the prior \(1/\sigma^2\) is not formalized.

**A Gamma–Gaussian conjugate pair.** For \(\nu>0\), a positive definite \(R\) on \(\mathbb R^d\), and \(a\in\mathbb R^d\), draw a precision \(\tau\) from the Gamma law of shape and rate \(\nu/2\) and then \(x\) from \(N(a,\tau^{-1}R)\). The joint law of \((\tau,x)\) equals the law obtained by drawing \(x\) from the multivariate \(t\) law with location \(a\), scale \(R\), and \(\nu\) degrees of freedom, and then \(\tau\) from the Gamma law of shape \((\nu+d)/2\) and rate \((\nu+q(x))/2\), where \(q(x)=(x-a)^\top R^{-1}(x-a)\); the identity is stated for integrals of every measurable \(F\ge0\) of \((\tau,x)\) (`TauCeti.Probability.lintegral_gammaMeasure_lintegral_multivariateGaussian`, with the pointwise density identity `TauCeti.Probability.gammaPDFReal_mul_multivariateGaussianPDFReal`, [multivariate \(t\) density](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Probability/Distributions/MultivariateT/PDF.lean)). By the almost-everywhere uniqueness of the posterior kernel under disintegration (Mathlib, above), this identifies the posterior of \(\tau\) after one observation. The model \(N(a,\tau^{-1}R)\), with \(a\) and \(R\) known, is a regular exponential family in \(\tau>0\) with \(T(x)=-q(x)/2\) and \(A(\tau)=-(d/2)\log\tau\). The prior is \(\exp(\tau\chi_0-\nu_0A(\tau))\) up to normalization with \(\nu_0=(\nu-2)/d\) and \(\chi_0=-\nu/2\), which satisfies the hypotheses of item 2 exactly when \(\nu>2\), and the posterior parameters \(\chi_0+T(x)\) and \(\nu_0+1\) are those of the stated Gamma law.

#### Statlib

Differentiability in quadratic mean of a family \(P_\theta\) dominated by \(\mu\) is defined within a set, by \(\|\sqrt{p_\vartheta}-\sqrt{p_\theta}-\tfrac12\dot\ell_\theta(\vartheta-\theta)\sqrt{p_\theta}\|_{L^2(\mu)}=o(\vartheta-\theta)\) with \(p_\theta=dP_\theta/d\mu\) (`QMD.HasQuadraticMeanDerivWithinAt`, [QMD](https://github.com/stat-lib/statlib/blob/eeaac0283690efaa60c31115400cf561836baeb9/Statlib/Inference/QMD.lean)). It implies a directional (Hadamard) form, under which the score has mean zero, \(\int\dot\ell_\theta h\,dP_\theta=0\), when the local paths stay in the set, in particular at interior points (`QMD.HasQuadraticMeanDerivWithinAt.hasHadamardQuadraticMeanDerivWithinAt`, `QMD.integral_score_eq_zero`, `QMD.integral_score_eq_zero_of_mem_nhds`). Contiguity of families of laws along a filter is defined in five forms; the equivalence of the event form, tested along every finer filter, with transfer of convergence in probability, and the implication from it to the event form tested along the filter itself, are proved (`Contiguous1`, `contiguous1_iff_contiguous4`, `Contiguous1.contiguous5`, [contiguity](https://github.com/stat-lib/statlib/blob/eeaac0283690efaa60c31115400cf561836baeb9/Statlib/Contiguity/Def.lean)), and the remaining equivalences are recorded only as unproved plans in comments. Fisher information, local asymptotic normality, and Le Cam's lemmas are not stated, so these are ingredients for item 1 only.

**Synopsis entries.** Partly covered: 104.2 (one observation from \(N(a,\tau^{-1}R)\) with a Gamma\((\nu/2,\nu/2)\) prior on the precision, a conjugate prior of the entry when \(\nu>2\), as the factorization of the joint law through the Gamma\(((\nu+d)/2,(\nu+q)/2)\) posterior, in TauCeti; the general exponential-family statement, propriety, and \(n\) observations are not stated), 104.4 (the known-variance case for a single observation, from the conditional Gaussian formula in TauCeti; the sufficiency reduction and the Student \(t\) posterior under the improper prior are absent). Not covered: 104.1 (ingredients only: differentiability in quadratic mean with mean-zero score, and contiguity, Statlib; local asymptotic normality and the theorem are absent), 104.3, 104.5.

### Posterior decisions, prediction, and comparison

[Mathematical scope](SYNOPSIS104.md#posterior-decisions-prediction-and-comparison).

#### Mathlib

**Posterior risk.** The Bayes-estimator framework above reduces Bayes estimation to pointwise minimization of posterior expected loss. For squared-error loss the minimization is the inequality \(\mathbb E(\theta-a)^2\ge\mathop{\mathrm{Var}}\theta\) applied to the posterior; this specialization is not stated. Prior-averaged coverage of a credible set follows from the disintegration identity `compProd_posterior_eq_map_swap` by integrating the indicator of \(\{(\theta,x):\theta\in C(x)\}\) both ways; it is not stated. Medians and the check loss as posterior minimizers are absent.

**Prediction.** The posterior predictive law is the composition of the posterior kernel with the sampling kernel, so its first display in item 8 is the definition of kernel composition. The variance decomposition is the law of total variance (`integral_condVar_add_variance_condExp`), applied to the joint law of parameter and future observation given the data; the conditional form is not stated separately.

**Model comparison.** With two models encoded by `Kernel.boolKernel`, the posterior model probabilities are \(\pi(\{i\})\,dP_i/d(\text{marginal})\) almost surely (`posterior_boolKernel_apply_true`, `posterior_boolKernel_apply_false`). Their ratio is the posterior odds identity of item 9, the Bayes factor appearing as the ratio of the two Radon–Nikodym derivatives against the marginal. The Bayes decision for \(0\)–\(1\) model-selection loss is an instance of `IsArgminEstimator.isBayesEstimator` on a two-point parameter space, not stated separately in Mathlib.

#### TauCeti

**Parametric families and prior predictive laws.** The Beta, Gamma, Poisson, binomial, multinomial, and Dirichlet laws are developed with densities or mass functions, moments, and parameter measurability ([distributions](https://github.com/TauCetiProject/TauCeti/tree/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Probability/Distributions)). Two of the marginal laws of item 7 are proved: the Beta mixture of binomial laws is the beta-binomial law with its Beta-function mass formula (`TauCeti.Probability.betaBinomialMeasure`, `TauCeti.Probability.betaBinomialMeasure_real_singleton`, [beta-binomial](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Probability/Distributions/BetaBinomial/Basic.lean)), and the Gamma mixture of Poisson laws is negative binomial (`TauCeti.Probability.bind_gammaMeasure_poissonMeasure`, [Gamma–Poisson](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Probability/Distributions/Gamma/Poisson.lean)). The posterior laws and the predictive probabilities \((a+S)/(a+b+n)\) and \((a_j+N_j)/(\sum_\ell a_\ell+n)\) are not derived. The Dirichlet mean \(a_i/a_0\) is proved (`TauCeti.Probability.integral_id_dirichletMeasure`, [Dirichlet moments](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Probability/Distributions/Dirichlet/Moments.lean)).

#### Statlib

**The 0–1 loss.** The loss \(\ell(\theta,z)=1\{\theta\ne z\}\) on a parameter space used as its own action space is `ProbabilityTheory.zeroOneLoss`. For a standard Borel parameter space, a finite data kernel, and a finite prior, a measurable rule \(f\) with \(\kappa^\dagger\mu(x)\{z\}\le\kappa^\dagger\mu(x)\{f(x)\}\) for all \(z\) and almost every \(x\) is an argmin estimator for the 0–1 loss, hence a Bayes estimator by Mathlib's `IsArgminEstimator.isBayesEstimator`; for a countable parameter space such a rule exists and the condition may be written with \(\pi\{z\}\,dP_z/d(P\circ\pi)\) (`ProbabilityTheory.isArgminEstimator_zeroOneLoss_of_posterior`, `ProbabilityTheory.isArgminEstimator_zeroOneLoss`, `ProbabilityTheory.hasArgminEstimator_zeroOneLoss`, [0–1 loss](https://github.com/stat-lib/statlib/blob/eeaac0283690efaa60c31115400cf561836baeb9/Statlib/ForMathlib/Probability/Decision/ZeroOneLoss.lean)). With the two models as parameter space and their marginal laws as the data kernel, this is the statement of item 9 that choosing a model of largest posterior probability is a Bayes decision.

**Synopsis entries.** Partly covered: 104.9 (posterior model probabilities for two models, Mathlib; that a model of largest posterior probability is a Bayes decision under 0–1 loss, Statlib with Mathlib's Bayes-estimator framework; the Bayes-factor ratio and the improper-prior remark are not stated). Not covered: 104.6 (ingredients only: the reduction to posterior expected loss and the variance inequality behind the squared-error case, Mathlib; the median and quantile statements and the coverage identity are not stated), 104.7 (ingredients only: the families and the beta-binomial and Gamma–Poisson marginals, TauCeti; the conjugate updates are absent), 104.8 (ingredients only: the law of total variance, Mathlib; the predictive \(t\) law is absent).

### Credible regions, point nulls, and hierarchical shrinkage

[Mathematical scope](SYNOPSIS104.md#credible-regions-point-nulls-and-hierarchical-shrinkage).

The conditional Gaussian formula of TauCeti and the Gaussian laws of Mathlib, recorded under 104A above, are the supporting material for the normal computations of items 11–13. No credible-region optimality, point-null Bayes factor, hierarchical posterior, James–Stein or empirical-Bayes estimator, Tweedie formula, or Robbins estimator was found. TauCeti's one-dimensional Gaussian integration by parts, recorded under 104C, is the identity behind the Tweedie formula and the Stein unbiased risk estimate.

#### Statlib

No relevant declarations were found.

**Synopsis entries.** Not covered: 104.10–104.14.

### Nonparametric Bayes, posterior asymptotics, and inverse problems

[Mathematical scope](SYNOPSIS104.md#nonparametric-bayes-posterior-asymptotics-and-inverse-problems).

#### Mathlib

**Supporting material.** Lévy's upward theorem, that \(\mathbb E[g\mid\mathcal F_n]\to\mathbb E[g\mid\mathcal F_\infty]\) almost surely for integrable \(g\) (`MeasureTheory.Integrable.tendsto_ae_condExp`, `Probability/Martingale/Convergence.lean`), is the martingale step in Doob's consistency theorem; the identification of the parameter as a limit of the data, which the proof also needs, is not stated. Relative entropy with its chain rule and data-processing inequality (`InformationTheory.klDiv`, `klDiv_compProd_eq_add`, `klDiv_map_le`, `InformationTheory/KullbackLeibler/`) and covering numbers of sets in a pseudo-metric space (`Metric.coveringNumber`, `Topology/MetricSpace/CoveringNumbers.lean`) are the quantities in Schwartz's theorem and the contraction-rate theorem. The Hellinger distance between measures, the second Kullback–Leibler moment \(V\), and test-based posterior bounds are not defined in Mathlib. The minimax risk is defined (above), but no Gaussian-sequence or white-noise model is. The Kolmogorov extension theorem constructs the projective limit of a projective family of finite measures on finite products of second-countable, completely pseudo-metrizable spaces, for an arbitrary index set (`MeasureTheory.projectiveLimit`, `MeasureTheory.isProjectiveLimit_projectiveLimit`, `MeasureTheory/Constructions/KolmogorovExtension.lean`); it is the measure-theoretic input to a construction of the Dirichlet process by its finite-dimensional laws.

#### TauCeti

**Dirichlet laws and exchangeability.** The finite-dimensional Dirichlet law is constructed by normalizing independent Gamma variables, with its simplex density, Beta block marginals, and the aggregation law: merging coordinates along a surjection gives the Dirichlet law with merged parameters (`TauCeti.Probability.dirichletMeasure`, `TauCeti.Probability.map_euclideanFiberSum_dirichletMeasure`, [aggregation](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Probability/Distributions/Dirichlet/Aggregation.lean)). Aggregation is the consistency condition that a Kolmogorov-type construction of the Dirichlet process would use. One step of finite stick breaking is proved: splitting off one coordinate of a Dirichlet vector with positive parameters gives a Beta\((a_0,\sum_{i\ne0}a_i)\) fraction independent of the renormalized remainder, which is Dirichlet with the remaining parameters, and conversely (`TauCeti.Probability.map_dirichletStickSplit_dirichletMeasure`, `TauCeti.Probability.map_dirichletStickInsert_prod_betaMeasure_dirichletMeasure`, [stick breaking](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Probability/Distributions/Dirichlet/StickBreaking.lean)). No Dirichlet process, infinite stick-breaking representation, or Pólya urn is formalized. De Finetti's theorem, which item 16 invokes, is proved in TauCeti and recorded in [CKMA Structure 06](../lean-CKMA/STRUCTURE06.md#gaussian-laws-infinite-divisibility-and-exchangeability).

#### Statlib

**Hellinger distance and tests (supporting).** The squared Hellinger distance `sqHellinger` is half the \(h^2\) of items 18 and 19, and for probability measures \(\mathrm{sqHellinger}\le\tfrac12\mathrm{tvDist}\le\sqrt{\mathrm{sqHellinger}\,(2-\mathrm{sqHellinger})}\) (`ProbabilityTheory.toReal_sqHellinger_le_tvDist_div_two`, `ProbabilityTheory.tvDist_div_two_le_sqrt_sqHellinger_mul`, [Hellinger and total variation](https://github.com/stat-lib/statlib/blob/eeaac0283690efaa60c31115400cf561836baeb9/Statlib/Divergence/Hellinger/TotalVariation.lean)). The Bayes risk of testing \(\mu\) against \(\nu\) is bounded by \(\pi\{\mathrm{false}\}^a\pi\{\mathrm{true}\}^{1-a}\exp(-(1-a)R_a(\mu,\nu))\) for probability measures and \(0<a<1\), with \(R_a\) the Rényi divergence (`ProbabilityTheory.bayesBinaryRisk_le_mul_exp_renyiDiv_of_isProbabilityMeasure`, [Rényi bounds](https://github.com/stat-lib/statlib/blob/eeaac0283690efaa60c31115400cf561836baeb9/Statlib/Testing/BinaryRenyi.lean)), and for \(n\) independent observations the risk is at most \(\delta\) once \(n(1-a)R_a(\mu,\nu)\) exceeds an explicit logarithm (`ProbabilityTheory.bayesBinaryRisk_pi_le_of_ofReal_le_mul_renyiDiv`, [sample complexity](https://github.com/stat-lib/statlib/blob/eeaac0283690efaa60c31115400cf561836baeb9/Statlib/Testing/SampleComplexityBounds.lean)). These are tests between two simple hypotheses; the tests against complements of neighbourhoods, uniformly over a composite alternative, required by items 18 and 19 are not constructed.

**Synopsis entries.** Not covered: 104.15 (ingredients only: Dirichlet aggregation and one step of finite stick breaking, TauCeti, and the Kolmogorov extension theorem, Mathlib; the Dirichlet process and its posterior are absent), 104.16–104.20.

<a id="structure-104b"></a>

## 104B. Monte Carlo, Langevin Dynamics, and Particle Methods

The coverage here is supporting: invariant and reversible kernels, inverse-transform sampling, the strong law and central limit theorem for independent samples, relative-entropy identities, and, in TauCeti, the metric theory of Wasserstein gradient flows, the Jordan–Kinderlehrer–Otto step, McCann's displacement convexity of internal energies, the coupling inequality for Markov chains, and the Poincaré and logarithmic Sobolev inequalities as definitions. Statlib has nothing specific to this subdivision. Markov chain samplers, Langevin diffusions, stochastic approximation, McKean–Vlasov systems, and particle filters are not defined in any of the three libraries. The general Markov-chain material of [CKMA Structure 08](../lean-CKMA/STRUCTURE08.md#markov-semigroups-martingale-problems-and-chains) (Ionescu–Tulcea path laws, \(\varphi\)-irreducibility, and TauCeti's Markov-chain path law) is the starting point for the chain-based entries.

### Monte Carlo and Markov chain Monte Carlo

[Mathematical scope](SYNOPSIS104.md#monte-carlo-and-markov-chain-monte-carlo).

#### Mathlib

**Change of measure.** For \(\mu\ll\nu\), \(\int(d\mu/d\nu)\,f\,d\nu=\int f\,d\mu\), and \((d\mu/d\nu)f\) is \(\nu\)-integrable exactly when \(f\) is \(\mu\)-integrable (`MeasureTheory.Measure.integral_rnDeriv_smul`, `MeasureTheory.Measure.integrable_rnDeriv_smul_iff`, `MeasureTheory/Measure/Decomposition/RadonNikodym.lean`). This is the identity \(\mathbb E_ph=\mathbb E_q[(p/q)h]\) of item 21. The strong law in Etemadi's form (`ProbabilityTheory.strong_law_ae`, `Probability/StrongLaw.lean`) applied to the numerator and denominator gives the almost-sure convergence of the self-normalized estimator, and additivity of variance under independence gives the variance formula; neither consequence is stated.

**Invariance and reversibility.** A measure \(\pi\) is invariant for a kernel \(\kappa\) when \(\pi\) composed with \(\kappa\) is \(\pi\); composites of \(\pi\)-invariant kernels are \(\pi\)-invariant, and a Markov kernel reversible for \(\pi\) (detailed balance on pairs of measurable sets) leaves \(\pi\) invariant (`ProbabilityTheory.Kernel.Invariant.comp`, `ProbabilityTheory.Kernel.IsReversible.invariant`, `Probability/Kernel/Invariance.lean`). These are the abstract final steps of items 22 and 23 (deterministic scans are composites); the Metropolis–Hastings and Gibbs kernels are not defined, and their reversibility or invariance is not proved.

**Relative entropy against a tilted reference.** For a probability measure \(q\ll\nu\) with integrable log-likelihood ratio, an integrable \(f\), and \(e^f\in L^1(\nu)\),
\[
\int\log\frac{dq}{d(\nu_f)}\,dq=\int\log\frac{dq}{d\nu}\,dq-\int f\,dq+\log\int e^f\,d\nu,
\]
where \(\nu_f\) is the tilted measure \(e^f\nu/\int e^f\,d\nu\) (`MeasureTheory.integral_llr_tilted_right`, `MeasureTheory/Measure/LogLikelihoodRatio.lean`; `MeasureTheory.Measure.tilted`, `MeasureTheory/Measure/Tilted.lean`). With \(\nu\) the prior and \(f\) the log-likelihood, \(\nu_f\) is the posterior and \(\int e^f\,d\nu\) the evidence, and the identity rearranges to item 25 in the form \(\log p(y)=\mathbb E_q\log p(y\mid\theta)-\mathop{\mathrm{KL}}(q\,\|\,\Pi)+\mathop{\mathrm{KL}}(q\,\|\,\Pi(\cdot\mid y))\). The identification of the tilted prior with the posterior kernel is the density form `posterior_eq_withDensity` of 104A, not stated as such.

**Conditioning reduces variance.** The tower property and the law of total variance (`integral_condVar_add_variance_condExp`) give the single-draw form of item 27: \(\mathbb E[H\mid U]\) has the mean of \(H\) and variance at most \(\mathop{\mathrm{Var}}H\). The central limit theorem for i.i.d. real variables (`ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub`, `Probability/CentralLimitTheorem.lean`) and Slutsky's theorem (`MeasureTheory/Function/ConvergenceInDistribution.lean`) are the ingredients of item 26, which is not assembled; the bivariate central limit theorem that it uses is not available in this form.

#### TauCeti

**Sample means and relative entropy.** The mean-square error of the mean of \(r\) pairwise independent square-integrable random vectors with common mean is \(r^{-2}\) times the sum of the individual errors (`TauCeti.integral_norm_finiteMean_sub_sq`, [sample means](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Probability/Moments/SampleMean.lean)); this is the variance statement of item 21 for the importance weights. In \([0,\infty]\) and without integrability hypotheses, for probability measures \(\mu,\nu\) and a measurable potential \(f\ge0\), \(\mathop{\mathrm{KL}}(\mu\,\|\,\nu_{-f})-\log Z=\int f\,d\mu+\mathop{\mathrm{KL}}(\mu\,\|\,\nu)\) with \(Z=\int e^{-f}d\nu\) (`TauCeti.klDiv_tilted_neg_add_ofReal_neg_log`, [tilted reference](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/InformationTheory/KullbackLeibler/Tilted.lean)); this is the evidence identity for likelihoods bounded by one.

#### Statlib

**Chain rule through the posterior (supporting).** For finite measures and kernels on a standard Borel parameter space, \(\mathrm{KL}(\mu\otimes\kappa\,\|\,\nu\otimes\eta)=\mathrm{KL}(\kappa\circ\mu\,\|\,\eta\circ\nu)+\mathrm{KL}(\kappa^\dagger\mu\,\|\,\eta^\dagger\nu\mid\kappa\circ\mu)\), the second term being the divergence between the posterior kernels averaged over the marginal law of the data (`ProbabilityTheory.klDiv_compProd_eq_add_condKL_posterior`, [conditional divergence](https://github.com/stat-lib/statlib/blob/eeaac0283690efaa60c31115400cf561836baeb9/Statlib/Divergence/KullbackLeibler/CondKL.lean)). It relates divergences of joint laws to those of posteriors; the evidence identity of item 25 is not derived from it.

**Synopsis entries.** Partly covered: 104.21 (the change-of-measure identity, Mathlib, and the sample-mean variance, TauCeti; the convergence of the self-normalized estimator is not stated), 104.22 (reversibility implies invariance, Mathlib; the Metropolis–Hastings kernel and its reversibility are absent), 104.25 (the identity in tilted-reference form, Mathlib and TauCeti; the variational reading over a family is not stated), 104.27 (one draw, from the law of total variance, Mathlib). Not covered: 104.23, 104.24, 104.26.

### Exact simulation and variance reduction

[Mathematical scope](SYNOPSIS104.md#exact-simulation-and-variance-reduction).

#### Mathlib

The geometric law, the covariance and its bilinearity, and the uniform law on an interval are available (`Probability/Distributions/Geometric.lean`, `Probability/Moments/Covariance.lean`, `Probability/Distributions/Uniform.lean`). Accept–reject sampling, control variates, and the negative correlation of \(h(U)\) and \(h(1-U)\) for monotone \(h\) are not stated.

#### TauCeti

**Inverse transform and probability integral transform.** The quantile function \(F^-(t)=\inf\{x:t\le F(x)\}\) of a probability law on the line is defined (`MeasureTheory.Measure.quantile`), with \(F^-(t)\le x\iff t\le F(x)\) for \(0<t<1\) (`MeasureTheory.Measure.quantile_le_iff`). It pushes Lebesgue measure on \((0,1)\) forward to the law (`MeasureTheory.Measure.map_quantile_volume_Ioo`), and the distribution function of an atomless law pushes it forward to the uniform law on \([0,1]\) (`MeasureTheory.Measure.cdf_map_eq_volume_restrict`, [quantiles](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Probability/Quantile.lean)). Atomlessness is continuity of \(F\).

#### Statlib

No relevant declarations were found.

**Synopsis entries.** Covered: 104.28 (TauCeti). Not covered: 104.29, 104.30.

### Convergence of Markov chain samplers

[Mathematical scope](SYNOPSIS104.md#convergence-of-markov-chain-samplers).

#### Mathlib

\(\varphi\)-irreducibility of a kernel is defined (`Probability/Kernel/Irreducible.lean`), and the trajectory law of a chain is the Ionescu–Tulcea construction ([CKMA Structure 08](../lean-CKMA/STRUCTURE08.md#markov-semigroups-martingale-problems-and-chains)). Harris recurrence, small sets, aperiodicity, uniform and geometric ergodicity, the ergodic theorem for Markov chains, and convergence in total variation are not stated. The Hamiltonian, the leapfrog map, and the volume preservation of symplectic or shear maps in this form are absent. The maximal ergodic theorem for a measure-preserving map, a weak-type \((1,1)\) bound for the supremum of Birkhoff averages, is in `Dynamics/BirkhoffSum/Maximal.lean` (`mul_measureReal_lt_birkhoffAverageSup_le_integral`); the pointwise ergodic theorem is not stated.

#### TauCeti

**Markov chains (supporting).** For a Markov kernel \(\kappa\), a Markovian coupling \(\eta\) of \(\kappa\) with itself, and a coupling \(\rho\) of initial laws \(\nu,\nu'\), the meeting-time coupling gives \(\mathrm{tvDist}(\nu\kappa^n,\nu'\kappa^n)\le2\,P(X_k\ne Y_k\text{ for all }k\le n)\), in Mathlib's normalization of `tvDist`, with the independent coupling as a special case (`ProbabilityTheory.Kernel.tvDist_pow_comp_le_of_isCoupling`, `ProbabilityTheory.Kernel.tvDist_pow_comp_le_parallelComp`, [coupling](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Probability/MarkovChain/Coupling.lean)). On spaces with measurable singletons the period of a state is defined and is constant on communicating classes, and an irreducible aperiodic kernel has \(\kappa^n(x,\{y\})>0\) for all large \(n\) ([period](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Probability/MarkovChain/Period.lean)); recurrence and transience of states are characterized through the Green function and are class properties ([recurrence](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Probability/MarkovChain/Recurrence.lean)). These are the inputs of the coupling proof of convergence to equilibrium for countable chains; that theorem, Harris recurrence, and ergodic theorems for chains are not stated.

#### Statlib

No relevant declarations were found.

**Synopsis entries.** Not covered: 104.31–104.35.

### Mean-field coordinate ascent

[Mathematical scope](SYNOPSIS104.md#mean-field-coordinate-ascent).

The tilted-reference identities recorded under Monte Carlo above, with TauCeti's tensorization of relative entropy over products (`TauCeti.klDiv_prod_prod_eq_add`, [chain rule](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/InformationTheory/KullbackLeibler/ChainRule.lean)), are the ingredients of the coordinate update; the update itself is not stated. Statlib proves the same tensorization for finite products (`ProbabilityTheory.klDiv_pi`, [conditional divergence](https://github.com/stat-lib/statlib/blob/eeaac0283690efaa60c31115400cf561836baeb9/Statlib/Divergence/KullbackLeibler/CondKL.lean)).

#### Statlib

No relevant declarations were found beyond the tensorization just recorded.

**Synopsis entries.** Not covered: 104.36.

### Langevin dynamics, sampling, and gradient flows

[Mathematical scope](SYNOPSIS104.md#langevin-dynamics-sampling-and-gradient-flows).

#### TauCeti

**Supporting gradient-flow theory.** The metric theory recorded in [CKMA Structure 39](../lean-CKMA/STRUCTURE39.md#metric-gradient-flows-and-synthetic-diffusion) applies: \(\mathrm{EVI}_\lambda\) solutions of a lower-semicontinuous energy contract at rate \(e^{-\lambda t}\) (`TauCeti.IsEVISolution.dist_le`, [EVI](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Analysis/GradientFlow/EVI/Basic.lean)), and the potential energy \(\int V\,d\rho\) of an \(m\)-strongly convex \(V\) is \(m\)-convex along Wasserstein geodesics and along generalized geodesics (`StrongConvexOn.geodesicallyConvex_potentialEnergy`, `StrongConvexOn.convexAlongGeneralizedGeodesics_potentialEnergy`, [potential energy](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/MeasureTheory/OptimalTransport/Wasserstein/PotentialEnergy.lean)). The conclusions about EVI solutions are conditional on their existence.

**Displacement convexity of internal energies (supporting).** McCann's theorem is proved on a real inner product space of finite dimension \(n\ge1\) with an additive Haar measure: if \(U(0)=0\) and \(s\mapsto s^nU(s^{-n})\) is convex and nonincreasing on \((0,\infty)\), a condition met by \(U(r)=r\log r\), then the internal energy \(\int U(d\mu/d\rho)\,d\rho\), with the singular part charged at the recession constant of \(U\), is convex along the displacement interpolation \(((1-t)\mathrm{id}+t\nabla F)_\ast\mu\) of an absolutely continuous \(\mu\), provided neither endpoint energy is \(-\infty\). For laws of finite second moment, the first absolutely continuous, it is convex along a quadratic Wasserstein geodesic joining them (`TauCeti.internalEnergy_map_smul_add_smul_gradient_le`, `TauCeti.WassersteinSpace.exists_isGeodesicSegment_convexAlong_internalEnergy`, [displacement convexity](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/MeasureTheory/OptimalTransport/Wasserstein/InternalEnergy/DisplacementConvexity.lean)). The Boltzmann entropy is the internal energy for \(U(r)=r\log r\) (`TauCeti.boltzmannEntropy`, [internal energy](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/MeasureTheory/OptimalTransport/Wasserstein/InternalEnergy/Basic.lean)), but its displacement convexity is not stated separately, and convexity along generalized geodesics is not proved. Together with the potential-energy result this is the convexity input of item 38. The Langevin diffusion and its Fokker–Planck equation, and the identification of that equation as a Wasserstein gradient flow, are not formalized.

Stochastic approximation is absent; Mathlib's martingale convergence theorems ([CKMA Structure 06](../lean-CKMA/STRUCTURE06.md#discrete-time-martingales)) are the nearest supporting material.

#### Statlib

No relevant declarations were found.

**Synopsis entries.** Not covered: 104.37, 104.38 (ingredients only: McCann's displacement convexity of internal energies, which include the entropy, and the \(m\)-convexity of the potential energy along geodesics, TauCeti; the Langevin diffusion and the contraction are absent), 104.39, 104.40.

### Entropy and discretization bias

[Mathematical scope](SYNOPSIS104.md#entropy-and-discretization-bias).

Relative Fisher information and the unadjusted Langevin chain are not defined. TauCeti defines the logarithmic Sobolev inequality in its functional form, recorded under the next heading. The Gaussian laws and the TauCeti closed form of the quadratic Wasserstein distance between Gaussian laws (`TauCeti.wassersteinEDist_two_multivariateGaussian`, [Gaussian transport](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/MeasureTheory/OptimalTransport/Wasserstein/Gaussian/Basic.lean)) are the nearest supporting material for item 42.

#### Statlib

No relevant declarations were found.

**Synopsis entries.** Not covered: 104.41, 104.42.

### Variational time stepping and functional inequalities

[Mathematical scope](SYNOPSIS104.md#variational-time-stepping-and-functional-inequalities).

#### TauCeti

**The JKO step.** On \(\mathcal P_p(X)\) of a complete separable metric space, the step \(\rho\mapsto\phi(\rho)+W_p^2(\rho,\rho_k)/(2\tau)\) has a minimizer for an energy that is narrowly lower semicontinuous along bounded sequences, coercive, and has tight bounded sublevel sequences (automatic on a proper space), and every law starts a JKO sequence (`TauCeti.WassersteinSpace.moreauYosidaResolvent_nonempty`, `TauCeti.WassersteinSpace.exists_forall_mem_moreauYosidaResolvent`, [JKO step](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/MeasureTheory/OptimalTransport/Wasserstein/Resolvent.lean)); the hypotheses are verified for the potential energy of a lower-semicontinuous potential bounded below (`TauCeti.WassersteinSpace.moreauYosidaResolvent_potentialEnergy_nonempty`). The minimizer is unique when the energy is \(m\)-convex along generalized geodesics and \(1+m\tau>0\) (`TauCeti.GeneralizedGeodesicallyConvex.subsingleton_moreauYosidaResolvent`, [uniqueness](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/MeasureTheory/OptimalTransport/Wasserstein/GeneralizedGeodesic/Convex.lean)). On a separable Hilbert space a JKO minimizer satisfies the Euler–Lagrange equation \(\int\langle x-y,\xi(x)\rangle\,d\gamma=-\tau D\) along vector-field perturbations ([Euler–Lagrange](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/MeasureTheory/OptimalTransport/Wasserstein/EulerLagrange.lean)). For the entropy part of \(\mathcal F\), the Boltzmann entropy is lower semicontinuous on \(\mathcal P_p(X)\) and has tight sublevel sets once a moment term is added, under an integrable confining weight (`TauCeti.WassersteinSpace.lowerSemicontinuous_boltzmannEntropy`, `TauCeti.WassersteinSpace.isTightMeasureSet_of_boltzmannEntropy_add_le`, [Boltzmann entropy](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/MeasureTheory/OptimalTransport/Wasserstein/BoltzmannEntropy.lean)). The application of the existence theorem to \(\mathcal F=\int\rho\log\rho+\int V\rho\) is not stated; uniqueness for it would need convexity of the entropy along generalized geodesics, which is not proved (McCann's theorem, recorded above, gives convexity along geodesics only); convergence of the scheme to the Fokker–Planck equation is absent. On an extended metric space, under coercivity, lower semicontinuity, compactness of bounded sublevels for an auxiliary convergence, and joint lower semicontinuity of the distance, generalized minimizing movements, limits of piecewise-constant JKO interpolants as the step tends to zero, exist and are \(1/2\)-Hölder on bounded intervals (`TauCeti.exists_isGeneralizedMinimizingMovement`, [minimizing movements](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Analysis/GradientFlow/MinimizingMovement.lean)); their identification with a solution of a partial differential equation is not stated.

**Functional inequalities (definitions).** A probability measure on a normed space satisfies the Poincaré inequality with constant \(C\) if \(\mathop{\mathrm{Var}}_\mu f\le C\int\|\nabla f\|^2d\mu\), and the logarithmic Sobolev inequality with constant \(C\) if \(\mathop{\mathrm{Ent}}_\mu(f^2)\le2C\int\|\nabla f\|^2d\mu\), for smooth test functions with the relevant integrability (`MeasureTheory.Measure.PoincareInequality`, `MeasureTheory.Measure.LogSobolevInequality`, [functional inequalities](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Probability/Concentration/PoincareLogSobolev.lean)); with \(f^2=d\mu/d\pi\) the latter is the form of the inequality used in items 41 and 44. Only monotonicity in the constant, scaling under dilations, and the failure of the Poincaré inequality for a two-point law are proved. The implication from the logarithmic Sobolev to the Poincaré inequality, the chi-squared divergence, and the Otto–Villani inequality are not formalized.

#### Statlib

No relevant declarations were found.

**Synopsis entries.** Partly covered: 104.43 (existence of JKO steps under abstract hypotheses, with lower semicontinuity and coercivity of the entropy, and uniqueness under generalized-geodesic convexity, TauCeti; neither uniqueness for \(\mathcal F\) nor convergence of the scheme). Not covered: 104.44 (ingredients only: the Poincaré and logarithmic Sobolev inequalities as definitions, TauCeti; the Langevin diffusion, the chi-squared divergence, and every implication of the entry are absent).

### Unadjusted, stochastic-gradient, and Metropolis-adjusted Langevin

[Mathematical scope](SYNOPSIS104.md#unadjusted-stochastic-gradient-and-metropolis-adjusted-langevin).

#### Statlib

No relevant declarations were found.

**Synopsis entries.** Not covered: 104.45–104.47.

### Kinetic Langevin dynamics

[Mathematical scope](SYNOPSIS104.md#kinetic-langevin-dynamics).

#### Statlib

No relevant declarations were found.

**Synopsis entries.** Not covered: 104.48.

### The ordinary differential equation method

[Mathematical scope](SYNOPSIS104.md#the-ordinary-differential-equation-method).

The flows of Lipschitz ordinary differential equations are in Mathlib (Picard–Lindelöf, recorded in the CKMA ordinary-differential-equations inventory); internally chain transitive sets and the stochastic recursion are not.

#### Statlib

No relevant declarations were found.

**Synopsis entries.** Not covered: 104.49, 104.50.

### Particle methods, data assimilation, and training dynamics

[Mathematical scope](SYNOPSIS104.md#particle-methods-data-assimilation-and-training-dynamics).

#### Mathlib

**Supporting material.** Vector-valued reproducing kernel Hilbert spaces are defined, with the reproducing property, density of kernel sections, positive semidefiniteness of the kernel, and Moore's construction from a positive semidefinite kernel (`RKHS`, `RKHS.kernel_ofKernel`, `Analysis/InnerProductSpace/Reproducing.lean`); this is the function space of the Stein variational velocity in item 54. McKean–Vlasov equations, interacting particle systems, ensemble Kalman methods, and particle filters are absent.

#### TauCeti

Kernel mean embeddings of measures for a positive-definite kernel, with the maximum mean discrepancy as the norm of their difference, are developed ([mean embeddings](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Analysis/PositiveDefinite/Kernel/MeanEmbedding.lean)); this is related kernel infrastructure, not a Stein discrepancy. The conditional Gaussian formula recorded under 104A is the Kalman update for one step, which belongs to [SYNOPSIS106](SYNOPSIS106.md); empirical Wasserstein convergence of i.i.d. samples is recorded in [CKMA Structure 39](../lean-CKMA/STRUCTURE39.md#optimal-transportation-and-wasserstein-geometry).

#### Statlib

No relevant declarations were found.

**Synopsis entries.** Not covered: 104.51–104.55.

### Quantitative chaos and nonlinear filtering

[Mathematical scope](SYNOPSIS104.md#quantitative-chaos-and-nonlinear-filtering).

The posterior kernel and its composition rule `posterior_comp` (104A) are the measure-theoretic form of one prediction–correction step; hidden Markov models and their filtering recursion are not defined.

#### Statlib

No relevant declarations were found.

**Synopsis entries.** Not covered: 104.56–104.58.

### Fluctuations, stability, and resampling of particle filters

[Mathematical scope](SYNOPSIS104.md#fluctuations-stability-and-resampling-of-particle-filters).

#### TauCeti

**Multinomial counts.** The multinomial law on count vectors of total \(N\) is defined, with exact masses, coordinate marginals that are binomial, and mean and covariance \(N(\mathop{\mathrm{diag}}w-ww^\top)\) (`TauCeti.Probability.multinomialMeasure`, `TauCeti.Probability.covMatrix_map_multinomialToEuclidean_multinomialMeasure`, [multinomial moments](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Probability/Distributions/Multinomial/Moments.lean)). The unbiasedness of multinomial resampling and its conditional variance \(N^{-1}\mathop{\mathrm{Var}}_w(f)\) follow from these moments by a linear computation, which is not stated. Residual and systematic resampling, and the Feynman–Kac particle model, are absent.

#### Statlib

No relevant declarations were found.

**Synopsis entries.** Not covered: 104.59, 104.60, 104.61 (ingredients only: the multinomial means and covariances that give the multinomial case, TauCeti; residual and systematic resampling are absent).

### Variational data assimilation

[Mathematical scope](SYNOPSIS104.md#variational-data-assimilation).

#### Statlib

No relevant declarations were found.

**Synopsis entries.** Not covered: 104.62.

<a id="structure-104c"></a>

## 104C. Score Matching, Diffusion Generative Models, and Schrödinger Bridges

Stochastic differential equations, time reversal, and score functions are not formalized, so the diffusion-model entries are not covered. The entropic side is well developed in TauCeti: relative-entropy projections onto prescribed marginals, the static and dynamic Schrödinger problems with existence, uniqueness, and the product form of the minimizer, iterative proportional fitting, and the continuity equation with barycentric velocity fields. These cover parts of items 66, 67, 71, 72, and 77, with the Brownian reference and the path-space disintegration left open.

[Mathematical scope](SYNOPSIS104.md#synopsis-104c).

#### Mathlib

**Supporting material.** The data-processing inequality for relative entropy under measurable maps and Markov kernels (`InformationTheory.klDiv_map_le`, `klDiv_comp_right_le`, `InformationTheory/KullbackLeibler/DataProcessing.lean`) is the marginalization step at the end of item 68. Itô calculus, Girsanov's theorem, and time reversal of diffusions are absent from Mathlib ([CKMA Structure 08](../lean-CKMA/STRUCTURE08.md#stochastic-integration-and-itôs-formula)).

#### TauCeti

**Pinsker's inequality.** \(d_{\mathrm{TV}}(\mu,\nu)^2\le\tfrac12\mathop{\mathrm{KL}}(\mu\,\|\,\nu)\) for probability measures, with \(d_{\mathrm{TV}}\) the usual distance in \([0,1]\), stated as \(\mathrm{etvDist}(\mu,\nu)^2\le2\mathop{\mathrm{KL}}(\mu\,\|\,\nu)\) for Mathlib's `etvDist`, which is \(2d_{\mathrm{TV}}\) (`TauCeti.etvDist_sq_le_two_mul_klDiv`, [Pinsker](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/InformationTheory/KullbackLeibler/Pinsker.lean)), is the final step of item 68.

**Girsanov's theorem for a constant drift (supporting).** For a Brownian motion \(W\) relative to a filtration, \(\theta\in\mathbb R\), and \(T\ge0\), under the tilted law with density \(\exp(\theta W_T-\theta^2T/2)\) the process \(W_t-\theta\min(t,T)\) is a Brownian motion relative to the same filtration (`TauCeti.Probability.IsFilteredPreBrownianReal.sub_mul_min_tilted_mul_eval`, `TauCeti.Probability.IsFilteredPreBrownianReal.isBrownianReal_sub_mul_min_tilted_mul_eval`, [Girsanov](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Probability/BrownianMotion/Girsanov.lean)). Stochastic integrals, and hence drifts depending on time and state as in item 68, are not available.

**The Schrödinger problem.** The static Schrödinger value \(\inf\{\mathop{\mathrm{KL}}(\pi\,\|\,R):\pi\in\Pi(\mu,\nu)\}\) is defined; for a finite reference and a finite source measure a finite value is attained by exactly one coupling, with no topological hypothesis (`TauCeti.schroedingerValue`, `TauCeti.existsUnique_isCoupling_klDiv_eq_schroedingerValue`, [entropic transport](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/MeasureTheory/OptimalTransport/Entropic/Basic.lean)). For a reference measure \(R\) on a space \(\Omega\) with an endpoint map \(e:\Omega\to X\times Y\), the dynamic value \(\inf\{\mathop{\mathrm{KL}}(P\,\|\,R):e_\ast P\in\Pi(\mu,\nu)\}\) equals the static value for the endpoint law \(e_\ast R\); a finite dynamic value is attained by exactly one measure, namely \(R\) reweighted by the static minimizer, and its density against \(R\) is \(d(e_\ast P)/d(e_\ast R)\circ e\), a function of the endpoints alone (`TauCeti.dynamicSchroedingerValue_eq_schroedingerValue`, `TauCeti.existsUnique_isCoupling_map_klDiv_eq_dynamicSchroedingerValue`, `TauCeti.rnDeriv_ae_eq_rnDeriv_map_comp_of_klDiv_eq_dynamicSchroedingerValue`, [dynamic problem](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/MeasureTheory/OptimalTransport/Entropic/Dynamic.lean)). The last statement is the density form of "the conditional path law given the endpoints is the reference bridge"; regular conditional laws of path measures given endpoints are not used. The Gibbs identity \(\int c\,d\pi+\varepsilon\mathop{\mathrm{KL}}(\pi\,\|\,\mu\otimes\nu)=\varepsilon\mathop{\mathrm{KL}}(\pi\,\|\,R_\varepsilon)-\varepsilon\log Z\), with \(R_\varepsilon\) the tilted product, relates entropic transport to the Schrödinger problem plan by plan (`TauCeti.lintegral_add_mul_klDiv_eq_mul_klDiv_tilted`, same entropic-transport file); the Brownian heat-kernel reference and the explicit decomposition in item 66 are not stated. Existence of bounded Schrödinger potentials for a reference with bounded log-density against \(\mu\otimes\nu\) is proved through a contracting Sinkhorn sweep ([Schrödinger system](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/MeasureTheory/OptimalTransport/Entropic/SchroedingerSystem.lean)).

#### Statlib

The data-processing inequality for total variation under Markov kernels and measurable maps is proved (`ProbabilityTheory.tvDist_comp_le`, `ProbabilityTheory.tvDist_map_le`, [total variation](https://github.com/stat-lib/statlib/blob/eeaac0283690efaa60c31115400cf561836baeb9/Statlib/Divergence/TotalVariation.lean)). Item 68 marginalizes the relative entropy instead, which is Mathlib's data processing above, so this is supporting only.

**Synopsis entries.** Partly covered: 104.66 (existence, uniqueness, reduction to the static problem, and the endpoint-density form of the bridge property, TauCeti; the Brownian reference and its quadratic-cost decomposition are absent). Not covered: 104.63–104.65, 104.68 (ingredients only: data processing for relative entropy, Mathlib, and Pinsker's inequality, TauCeti; the Girsanov bound for path laws is absent).

### Gaussian noising, endpoint constraints, and interpolants

[Mathematical scope](SYNOPSIS104.md#gaussian-noising-endpoint-constraints-and-interpolants).

#### TauCeti

**Endpoint potentials.** If a coupling \(\pi\) of \(\mu\) and \(\nu\) has density \(\exp(\varphi(x)+\psi(y))\) against a finite reference \(R\) on \(X\times Y\), with measurable \(\varphi\in L^1(\mu)\), \(\psi\in L^1(\nu)\), then every coupling \(\gamma\) satisfies \(\mathop{\mathrm{KL}}(\gamma\,\|\,R)=\mathop{\mathrm{KL}}(\gamma\,\|\,\pi)+\mathop{\mathrm{KL}}(\pi\,\|\,R)\), so \(\pi\) is the Schrödinger minimizer (`TauCeti.IsCoupling.klDiv_eq_klDiv_add_klDiv_of_eq_withDensity`, `TauCeti.IsCoupling.klDiv_eq_schroedingerValue_of_eq_withDensity`). When \(\mu\otimes\nu\ll R\), the potentials are unique up to one additive constant (`TauCeti.exists_ae_eq_add_const_of_withDensity_exp_eq`, [entropic transport](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/MeasureTheory/OptimalTransport/Entropic/Basic.lean)). On a path space with endpoint map \(e\), the measure with density \(\exp(\varphi(e_0)+\psi(e_1))\) against \(R\) attains the dynamic value (`TauCeti.klDiv_withDensity_exp_add_comp_eq_dynamicSchroedingerValue`, [dynamic problem](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/MeasureTheory/OptimalTransport/Entropic/Dynamic.lean)). The path-level Pythagorean identity of item 71 is an instance of Csiszár's identity \(\mathop{\mathrm{KL}}(\gamma\,\|\,R)=\mathop{\mathrm{KL}}(\gamma\,\|\,\pi)+\mathop{\mathrm{KL}}(\pi\,\|\,R)\) for \(\gamma\ll\pi\ll R\) with \(\int\log(d\pi/dR)\,d\gamma=\int\log(d\pi/dR)\,d\pi\) (`TauCeti.klDiv_eq_klDiv_add_klDiv`, [change of reference](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/InformationTheory/KullbackLeibler/ChangeOfReference.lean)), but that instance is not stated.

**Interpolants and the continuity equation.** The continuity equation \(\partial_t\mu_t+\nabla\cdot(\mu_tv_t)=0\) on a finite-dimensional real normed space is defined in the distributional sense (`TauCeti.IsContinuityEquation`). For a finite law on curves that are absolutely continuous with jointly measurable derivative \(V\) of finite expected length, the time marginals solve it with the barycentric velocity \(v_t(\gamma_t)=\mathbb E[V_t\mid t,\gamma_t]\) (conditional expectation for \(dt\otimes P\)), and \(\int\!\!\int\|v_t\|^p\,d\mu_t\,dt\le\mathbb E\!\int\|V_t\|^p\,dt\) for \(p\ge1\) (`TauCeti.exists_isContinuityEquation_map`, [continuity equation](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/MeasureTheory/OptimalTransport/ContinuityEquation/Basic.lean)). For a finite plan \(\pi\) with integrable displacement, the laws of \((1-t)x+ty\) solve it with velocity \(\mathbb E[y-x\mid t,(1-t)x+ty]\) and \(p\)-action at most \(\int\|y-x\|^p\,d\pi\); for an optimal coupling at finite \(W_p\), \(1<p<\infty\), on a strictly convex space, the velocity is the displacement itself and the action equals \(W_p^p\) (`TauCeti.exists_isContinuityEquation_map_smul_fst_add_smul_snd`, `TauCeti.exists_isContinuityEquation_map_smul_fst_add_smul_snd_of_isOptimalCoupling`, [plan interpolation](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/MeasureTheory/OptimalTransport/ContinuityEquation/PlanInterpolation.lean)). The displacement interpolation of an optimal coupling is a Wasserstein geodesic ([CKMA Structure 39](../lean-CKMA/STRUCTURE39.md#optimal-transportation-and-wasserstein-geometry)).

**The Benamou–Brenier formula.** For \(1\le p<\infty\), a curve \(t\mapsto\nu_t\) of finite measures on a finite-dimensional real normed space that is narrowly continuous on \([a,b]\), with \(\nu_a\) a probability measure, and that solves the continuity equation with velocity \(v\), satisfies \(W_p(\nu_a,\nu_b)^p\le(b-a)^{p-1}\int_a^b\!\int\|v_t\|^p\,d\nu_t\,dt\) (`TauCeti.IsContinuityEquation.wassersteinEDist_rpow_le`, [Benamou–Brenier](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/MeasureTheory/OptimalTransport/ContinuityEquation/BenamouBrenier.lean)). Consequently \(W_p(\mu_0,\mu_1)^p\) is the infimum of the action over such curves joining two probability measures, attained by the displacement interpolation of an optimal coupling when \(W_p(\mu_0,\mu_1)<\infty\) (`TauCeti.wassersteinEDist_rpow_eq_sInf_lintegral_isContinuityEquation`, `TauCeti.isLeast_lintegral_isContinuityEquation`). For \(p=2\) and the straight interpolant of a general coupling, the plan-interpolation result above supplies the continuity equation and the right inequality of item 72, and the time marginals are narrowly continuous, so the lower bound applies; this combination is not stated. The regression characterization of \(v_t\) and transport of \(\mu_0\) by the flow of \(v_t\) are not proved.

**Gaussian integration by parts (supporting).** For \(f:\mathbb R\to E\) differentiable everywhere, with \(E\) a Banach space, and with \((x-m)f(x)\) and \(f'\) integrable under \(N(m,v)\), \(\int(x-m)f(x)\,dN(m,v)=v\int f'\,dN(m,v)\), the variance \(v=0\) included (`TauCeti.Probability.integral_sub_smul_eq_smul_integral_deriv_gaussianReal`, with real and standard forms, [Gaussian integration by parts](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Probability/Distributions/Gaussian/IntegrationByParts.lean)). This is the one-dimensional Stein identity behind Tweedie's formula; the multivariate identity and the differentiation of Gaussian convolutions that Tweedie's formula also needs are not stated.

No Tweedie identity, Gaussian noising chain, or conditional covariance formula for Gaussian smoothing is formalized; the TauCeti conditional Gaussian formula of 104A gives the conditional law of \(Z_t\) given \(Z_0\) only after the chain is written as a jointly Gaussian vector, which is not done.

#### Statlib

No relevant declarations were found.

**Synopsis entries.** Partly covered: 104.67 (the continuity equation for the marginal laws with the conditional-expectation velocity, TauCeti; the least-squares characterization and the flow statement are absent), 104.71 (the Pythagorean identity, minimality, and uniqueness of potentials for endpoint couplings, and the dynamic minimizer of product form, TauCeti; the path-level identity is not stated), 104.72 (the right inequality, equality of the action with \(W_2^2\) for optimal couplings, and the Benamou–Brenier lower bound for narrowly continuous solutions of the continuity equation, TauCeti; the left inequality for the straight interpolant of a general coupling is not stated). Not covered: 104.69, 104.70.

### Training objectives and discrete-time samplers

[Mathematical scope](SYNOPSIS104.md#training-objectives-and-discrete-time-samplers).

Relative entropy between Gaussian laws, the chain rule for relative entropy over a Markov chain (available in TauCeti only for a single composition product, `TauCeti.klDiv_compProd_eq_add_lintegral`, [chain rule](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/InformationTheory/KullbackLeibler/ChainRule.lean)), and the conditional Gaussian formula of 104A are the supporting material; denoising score matching, the diffusion evidence bound, and sampler convergence are not stated.

#### Statlib

The chain rule for the conditional divergence of a composition of two kernels, \(\mathrm{KL}(\kappa_1\otimes\kappa_2,\eta_1\otimes\eta_2\mid\mu)=\mathrm{KL}(\kappa_1,\eta_1\mid\mu)+\mathrm{KL}(\kappa_2,\eta_2\mid\mu\otimes\kappa_1)\) (`ProbabilityTheory.condKL_compProd_kernel`, [conditional divergence](https://github.com/stat-lib/statlib/blob/eeaac0283690efaa60c31115400cf561836baeb9/Statlib/Divergence/KullbackLeibler/CondKL.lean)), is the inductive step of the chain rule over a Markov chain; the \(T\)-step identity and the evidence bound of item 74 are not stated.

**Synopsis entries.** Not covered: 104.73–104.75.

### Marginal-preserving dynamics and bridge iterations

[Mathematical scope](SYNOPSIS104.md#marginal-preserving-dynamics-and-bridge-iterations).

#### TauCeti

**Half-bridges.** For a finite measure \(\pi\) on \(\Omega\), a measurable \(f:\Omega\to X\), and a finite measure \(\mu\) on \(X\), the reweighting `π.fitLaw f μ` has density \(d\mu/d(f_\ast\pi)\circ f\) against \(\pi\); if \(\mu\ll f_\ast\pi\), \(f\) has law \(\mu\) under it. For every \(\sigma\) with \(f_\ast\sigma=\mu\), \(\mathop{\mathrm{KL}}(\sigma\,\|\,\pi)=\mathop{\mathrm{KL}}(\mu\,\|\,f_\ast\pi)+\mathop{\mathrm{KL}}(\sigma\,\|\,\pi.\mathrm{fitLaw}\,f\,\mu)\), with no further hypothesis; so the reweighting is the unique minimizer of \(\mathop{\mathrm{KL}}(\cdot\,\|\,\pi)\) under the constraint, with value \(\mathop{\mathrm{KL}}(\mu\,\|\,f_\ast\pi)\) (`MeasureTheory.Measure.fitLaw`, `MeasureTheory.Measure.rnDeriv_fitLaw`, `TauCeti.klDiv_eq_klDiv_map_add_klDiv_fitLaw`, `TauCeti.klDiv_fitLaw`, `TauCeti.klDiv_fitLaw_le`, `TauCeti.eq_fitLaw_of_klDiv_le`, [entropy projection](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/InformationTheory/KullbackLeibler/Projection.lean)). With \(f=X_0\) or \(f=X_T\) on path space these are the two half-bridges of item 77.

**Iterative proportional fitting.** On \(X\times Y\), starting from \(R\), one sweep fits the first and then the second marginal by `fitLaw`. For every coupling \(\sigma\) of \(\mu\) and \(\nu\), \(\mathop{\mathrm{KL}}(\sigma\,\|\,R)\) is the sum of the marginal errors met along \(n\) sweeps plus \(\mathop{\mathrm{KL}}(\sigma\,\|\,P^n)\), so \(\mathop{\mathrm{KL}}(\sigma\,\|\,P^n)\) is nonincreasing; the total marginal error is at most the Schrödinger value, and under finite-entropy feasibility the marginal errors tend to zero and every half-step enforces its marginal exactly (`MeasureTheory.Measure.proportionalFitting`, `TauCeti.klDiv_eq_sum_add_klDiv_proportionalFitting`, `TauCeti.klDiv_proportionalFitting_antitone`, `TauCeti.tsum_klDiv_le_schroedingerValue`, `TauCeti.tendsto_klDiv_fst_proportionalFitting`, `TauCeti.tendsto_klDiv_snd_fitLaw_proportionalFitting`, [proportional fitting](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/MeasureTheory/OptimalTransport/ProportionalFitting.lean)). Since the marginal errors are \(\mathop{\mathrm{KL}}(P^{k+1}\,\|\,P^k)\) by `TauCeti.klDiv_fitLaw`, this is the static form of the telescoping bound in item 77, and Pinsker's inequality turns the relative-entropy convergence of the marginals into convergence in total variation. Convergence of the couplings themselves to the Schrödinger minimizer, under the integrability condition of item 77, is not stated; neither is the iteration run on path space, although each of its half-steps is a `fitLaw` there. The marginal-preserving diffusions of item 76 require a Fokker–Planck theory that is absent.

#### Statlib

No relevant declarations were found.

**Synopsis entries.** Partly covered: 104.77 (half-bridges in general form, the telescoping identity, monotonicity, and convergence of the marginal errors for the static iteration, TauCeti; the path-space iteration and convergence of the couplings are absent). Not covered: 104.76.

## Missing from all three libraries

**Parametric Bayes.** The conjugate updates (items 2, 4, 7), the Jeffreys prior, and the hierarchical normal model need only the posterior density formula `posterior_eq_withDensity` and the TauCeti families; each is a computation of a normalizing constant, one or two steps from present material, except that Fisher information must first be defined. TauCeti's Gamma–Gaussian disintegration is the model for such a computation, for one observation and one conjugate pair. The Bernstein–von Mises theorem and the Laplace approximation need local asymptotic normality, which is absent; Statlib defines differentiability in quadratic mean and proves that the score has mean zero, and the total variation distance in which the conclusion is stated is Mathlib's `MeasureTheory.tvDist` (`MeasureTheory/Measure/TotalVariation/Defs.lean`, normalized to take values in \([0,2]\)). The gap is large. Highest-posterior-density regions need a bathtub (Neyman–Pearson type) lemma for densities, which is absent; Lindley's paradox and the James–Stein, Efron–Morris, Tweedie, and Robbins statements are explicit calculations with Gaussian or Poisson laws plus, for Robbins, the strong law, and are close to the existing distribution libraries.

**Nonparametric Bayes.** The Dirichlet process needs a construction of random measures on a standard Borel space, for which Mathlib's Kolmogorov extension theorem for arbitrary index sets, TauCeti's countable Kolmogorov extension, and TauCeti's Dirichlet aggregation are the natural inputs; the Sethuraman representation needs in addition the iteration of TauCeti's single stick-breaking step to an infinite sequence and the identification of the limit. Doob's consistency theorem is a few steps from Lévy's upward theorem, once the parameter is shown to be measurable with respect to the tail of the data. Schwartz's theorem and the Ghosal–Ghosh–van der Vaart rate need the Hellinger distance between measures, the existence of tests from covering numbers (Le Cam–Birgé), and prior-mass estimates; covering numbers are in Mathlib and the squared Hellinger distance, with its comparison with total variation and exponential bounds for tests of two simple hypotheses, is in Statlib; tests against composite alternatives and the prior-mass arguments are absent. The inverse-problem rates need the Gaussian sequence model and minimax lower bounds, of which only the definition of minimax risk exists.

**Monte Carlo and Markov chains.** The Metropolis–Hastings, Gibbs, slice, and Hamiltonian kernels can be defined with Mathlib kernels, and their invariance is one reversibility computation from `Kernel.IsReversible.invariant` away. The convergence theory (Harris recurrence, the ergodic theorem for Markov chains, geometric ergodicity under drift and minorization, and the Markov-chain central limit theorem) is absent and is the main prerequisite for items 24 and 31–34; TauCeti's Markov-chain path law, its coupling inequality, period, and recurrence theory for chains, and Mathlib's \(\varphi\)-irreducibility are the starting points. Accept–reject sampling needs only the geometric law and conditioning, and antithetic variates need Chebyshev's association inequality for monotone functions of one variable, which Mathlib has for finite sums and for the four-functions theorem on lattices but not for integrals on the line.

**Langevin dynamics and stochastic approximation.** Every Langevin entry needs stochastic differential equations, which none of the three libraries has; the discrete chains (unadjusted Langevin, stochastic-gradient Langevin, MALA) could be defined as kernels, but their analysis needs relative Fisher information, which is absent, and logarithmic Sobolev inequalities, which TauCeti defines without proving any consequence. On the Wasserstein side, TauCeti has the JKO step, generalized minimizing movements, EVI contraction, and McCann's displacement convexity of internal energies along geodesics, but not convexity of the entropy along generalized geodesics, convergence of the JKO scheme to a solution of the Fokker–Planck equation, or that equation as a gradient flow; these are the missing links for items 37, 38, 41, and 43. Robbins–Monro convergence needs the Robbins–Siegmund almost-supermartingale theorem, a short step from Mathlib's martingale convergence, and Benaïm's theorem needs asymptotic pseudotrajectories, which are far from present.

**Interacting particles and filtering.** Propagation of chaos and mean-field training need McKean–Vlasov stochastic equations, or at least coupling estimates in \(W_1\) for empirical measures; TauCeti's empirical Wasserstein convergence and Kantorovich–Rubinstein duality are the natural inputs. Filtering recursions (item 57) are a short application of the posterior kernel to a hidden Markov model, which is not defined; the particle-filter limit theorems and resampling schemes beyond multinomial are absent, as is the small-ball characterization of posterior modes in 4DVAR.

**Diffusion generative models.** Time reversal of diffusions, score functions, the Girsanov bound of item 68, and the Fokker–Planck equation are all absent and need stochastic calculus; TauCeti's Girsanov theorem covers only a constant drift. The purely Gaussian statements (Tweedie's identity, the Gaussian noising marginals, the reverse conditionals of item 74) are within reach of the existing Gaussian and conditional-Gaussian libraries; TauCeti's one-dimensional Gaussian integration by parts is the Stein identity they use, and its multivariate form is the missing lemma. Flow matching and stochastic interpolants are close to TauCeti's continuity-equation and Benamou–Brenier results; what is missing is the least-squares characterization of conditional expectation as a stated minimization, uniqueness for the continuity equation with a Lipschitz velocity, and the application of the Benamou–Brenier lower bound to the straight interpolant of a general coupling. For Schrödinger bridges the missing pieces are the Brownian path measure as a reference on path space, the disintegration of path measures given their endpoints, and convergence of the iterative-proportional-fitting couplings, which TauCeti proves for the marginals only.
