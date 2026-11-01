# Structure 102: Asymptotic, semiparametric, and robust statistics

Part of the [Mathlib and TauCeti coverage series](STRUCTURE.md).
[Mathematical inventory](SYNOPSIS102.md); [bibliographical scope](CKSD-bib.md#cks-102).

This file follows the thematic order and lettered subdivisions of the mathematical inventory. It records definitions, structures, and proved results, with supporting material identified separately. A topic heading locates the recorded statements; the **Synopsis entries** line at the end of each section states which numbered results are covered.

**Source baseline.** Mathlib `911003dd6dea5df215dff57f2717be762e11a6ca` and TauCeti `a049b4264d2cf4dbf4720796f844a3a3764914a5`, both of 2026-10-18, checked against local checkouts on 2026-11-01. See the [revision and source conventions](STRUCTURE.md#source-baseline-and-conventions).

**Mathlib source areas.** `Mathlib.MeasureTheory.Function.ConvergenceInDistribution`, `Mathlib.MeasureTheory.Function.ConvergenceInMeasure`, `Mathlib.MeasureTheory.Measure.LevyProkhorovMetric`, `Mathlib.Probability.CentralLimitTheorem`, `Mathlib.Probability.CramerWold`, `Mathlib.Probability.Distributions.Gaussian`, `Mathlib.Probability.Moments`, `Mathlib.Probability.CondVar`, `Mathlib.Probability.Decision`, `Mathlib.MeasureTheory.Measure.LogLikelihoodRatio`, `Mathlib.MeasureTheory.Measure.Tilted`, `Mathlib.MeasureTheory.Measure.CharacteristicFunction`, `Mathlib.MeasureTheory.Function.ConditionalExpectation`, `Mathlib.InformationTheory.KullbackLeibler`, `Mathlib.Analysis.InnerProductSpace.Projection`, `Mathlib.Analysis.Calculus.FDeriv`, `Mathlib.Analysis.Matrix.Order`, `Mathlib.Topology.Sion`, `Mathlib.Geometry.Manifold.Riemannian`.

**Namespaces.** Mathlib declarations are mainly in `ProbabilityTheory` and `MeasureTheory`; KL divergence is in `InformationTheory`, and the decision-theoretic risk notions are in `ProbabilityTheory`. TauCeti declarations are mostly in `TauCeti` and `TauCeti.Probability`, with extensions of `MeasureTheory.Measure` (quantiles, censoring, truncation) and `ProbabilityTheory`.

Neither library contains statistical asymptotics in the sense of this section: there is no notion of a statistical model indexed by a parameter with a sample size, of an estimator sequence, of Fisher information, of differentiability in quadratic mean, of contiguity, or of influence functions, and no delta method, Edgeworth expansion, or bootstrap theorem. What exists is the probabilistic and analytic infrastructure on which such a development would rest: convergence in distribution with Slutsky's theorem and the continuous-mapping theorem, the one-dimensional central limit theorem, the Cramér–Wold device, multivariate Gaussian laws and their affine images, chi-squared laws of Gaussian sums of squares, quantile functions and laws of order statistics, KL divergence, exponential tilting, conditional expectation and conditional variance, and a decision-theoretic risk vocabulary. The weak-convergence infrastructure is recorded in detail in [CKMA Structure 06](../lean-CKMA/STRUCTURE06.md), and the empirical-process infrastructure in [CKMA Structure 07](../lean-CKMA/STRUCTURE07.md); it is summarized here only as it bears on the entries.

<a id="structure-102a"></a>

## 102A. First-Order Asymptotics, Statistical Experiments, and Semiparametric and Robust Inference

Supporting material for this subdivision consists of the limit theorems and Gaussian calculus of CKMA Structure 06, the KL divergence and log-likelihood ratio, conditional expectation as an \(L^2\) projection, and TauCeti's quantile, order-statistic, and empirical-measure developments. One genuine statistical consistency theorem is present, for empirical Fréchet barycenters (TauCeti); it is recorded under the general-criteria heading.

### Parametric estimators and tests

[Mathematical scope](SYNOPSIS102.md#parametric-estimators-and-tests).

#### Mathlib

**Convergence in distribution and in probability (supporting).** `TendstoInDistribution X l Z μ μ'` allows each \(X_i\) to live on its own probability space \((\Omega_i,\mu_i)\), so sequences of statistics under varying laws \(P_{\theta_n}^n\) fit the definition (`MeasureTheory/Function/ConvergenceInDistribution.lean`). The continuous-mapping theorem (`TendstoInDistribution.continuous_comp`), the statement that \(Y_n-X_n\to0\) in probability transfers the limit (`tendstoInDistribution_of_tendstoInMeasure_sub`), and Slutsky's theorem (`TendstoInDistribution.prodMk_of_tendstoInMeasure_const`, `TendstoInDistribution.continuous_comp_prodMk_of_tendstoInMeasure_const`) are the steps from which the delta method is usually assembled; their exact hypotheses are recorded in CKMA Structure 06. Differentiability is Fréchet differentiability, with the little-\(o\) characterization `hasFDerivAt_iff_isLittleO_nhds_zero` (`Analysis/Calculus/FDeriv/Basic.lean`). No result combines these into the delta method (102.1): there is no lemma converting a deterministic \(o(\|h\|)\) remainder into an \(o_P\) remainder along a tight sequence, and stochastic order symbols \(O_P\), \(o_P\) are not defined.

**Normal limits (supporting).** The one-dimensional central limit theorem for i.i.d. square-integrable variables, \((\sqrt n)^{-1}\sum_{k<n}(X_k-\mathbb E X_0)\Rightarrow N(0,\mathop{\mathrm{Var}}X_0)\) (`tendstoInDistribution_inv_sqrt_mul_sum_sub`, `Probability/CentralLimitTheorem.lean`), and the Cramér–Wold device on finite-dimensional inner product spaces (`tendstoInDistribution_iff_tendstoInDistribution_inner`, `Probability/CramerWold.lean`). The multivariate central limit theorem, needed for every vector statement of this heading, is not stated, although it follows from these two results together with the characterization of Gaussian measures by their one-dimensional projections. The multivariate Gaussian `multivariateGaussian μ S` on `EuclideanSpace ℝ ι`, with its characteristic function (`charFun_multivariateGaussian`), and the Gaussian property of images under continuous linear maps (`isGaussian_map_of_measurable`) are in `Probability/Distributions/Gaussian/Multivariate.lean` and `Probability/Distributions/Gaussian/Basic.lean`.

**Likelihood (supporting).** The log-likelihood ratio of two measures is `llr μ ν = log (dμ/dν)`, with measurability, the identity \(e^{\mathrm{llr}}=d\mu/d\nu\) almost everywhere, and its behaviour under tilting (`exp_llr`, `integral_llr_tilted_left`, `MeasureTheory/Measure/LogLikelihoodRatio.lean`). There is no parametric family of densities, score, or Fisher information; maximum likelihood (102.2, 102.3), Z-estimators (102.4), one-step estimators (102.5), and the three classical tests (102.11) have no counterpart.

**Quantiles and order statistics (supporting).** Mathlib has the distribution function `ProbabilityTheory.cdf` (`Probability/CDF.lean`) but no quantile function, no empirical distribution function, and no order statistics. U-statistics, L-statistics, and the Hájek projection (102.8–102.10) are absent. The \(L^2\) conditional expectation is constructed as an orthogonal projection (`condExpL2`, `MeasureTheory/Function/ConditionalExpectation/CondexpL2.lean`); this is the projection operation used in the definition of the Hájek projection, but the projection onto the space of additive statistics is not formed.

#### TauCeti

**Quantiles (supporting).** The quantile function `MeasureTheory.Measure.quantile` of a real law, with the Galois characterization \(F^{-1}(t)\le x\iff t\le F(x)\) for \(0<t<1\) (`quantile_le_iff`) and inverse transform sampling (`map_quantile_volume_Ioo`) ([quantiles](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/Probability/Quantile.lean)). The definition \(\inf\{x:t\le F(x)\}\) is the one used in 102.7. For an i.i.d. sample from any real law, the \(k\)-th order statistic has the binomial-tail distribution function and is the image under the quantile function of a Beta\((k+1,n-k)\) variable (`TauCeti.Probability.cdf_map_orderStatistic_pi`, `TauCeti.Probability.map_orderStatistic_pi_eq_map_betaMeasure_quantile`, [order statistics](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/Probability/Distributions/OrderStatistic.lean)). These exact finite-\(n\) laws are the classical starting point for the asymptotics of sample quantiles (102.6, 102.7), but no limit theorem for them is proved.

**Clipping (supporting).** The law of a real random variable projected onto \([l,r]\) is decomposed into its two endpoint atoms and its interior part, with distribution function, quantiles, and all moments (`MeasureTheory.Measure.map_coe_projIcc`, `MeasureTheory.Measure.integral_pow_map_coe_projIcc`, [censoring](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/Probability/Distributions/Censoring.lean)). This is the clipped variable whose variance is the trimmed-mean asymptotic variance in 102.10; the identification is not made.

**Chi-squared limits (supporting).** The square of a standard Gaussian has the \(\chi^2_1\) law, and the sum of squares of \(k\) independent \(N(0,v)\) coordinates has the law of \(v\chi^2_k\) (`TauCeti.Probability.gaussianReal_map_sq`, `TauCeti.Probability.map_sum_sq_pi_gaussianReal`, `TauCeti.Probability.iIndepFun.hasLaw_sum_sq_gaussian`, [Gaussian squares](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/Probability/Distributions/Gaussian/ChiSquared.lean)). The moment-generating function of a Gaussian quadratic form \(\langle x,\Theta x\rangle\) under \(N(0,S)\) is \(\det(1-2t\,\Theta S)^{-1/2}\) on its exact domain ([quadratic forms](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/Probability/Distributions/Gaussian/QuadraticForm.lean)). The affine image of \(N(m,S)\) under \(x\mapsto Lx+c\), for rectangular \(L\), is \(N(Lm+c,LSL^\top)\) (`TauCeti.Probability.map_affine_multivariateGaussian`, [affine images](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/Probability/Distributions/Gaussian/Affine.lean)); this is the covariance formula \(Dg\,\Sigma\,Dg^\top\) of the delta method on the Gaussian side. The statement that \(Z^\top\Sigma^{-1}Z\sim\chi^2_k\) for \(Z\sim N(0,\Sigma)\), and the noncentral chi-squared law, are not stated.

**Synopsis entries.** Not covered: 102.1–102.11.

### Limits of experiments

[Mathematical scope](SYNOPSIS102.md#limits-of-experiments).

#### Mathlib

**Absolute continuity and likelihood ratios (supporting).** Absolute continuity of measures, Radon–Nikodym derivatives, Lebesgue decomposition, and `llr` are the finite-sample objects of which contiguity (102.12) is the asymptotic version; contiguity itself, Le Cam's first and third lemmas (102.12, 102.14), and local asymptotic normality are not defined. Quadratic-mean differentiability and the Hellinger distance are not defined. The KL divergence `klDiv` (an extended nonnegative real, with the mass correction for finite measures), Gibbs' inequality in the form `klDiv_eq_zero_iff`, the chain rule, and data processing (`klDiv_map_le`) are in `InformationTheory/KullbackLeibler/`; the second-order expansion of \(D(P_{\theta+h}\|P_\theta)\) in 102.13 is not stated.

**Gaussian shift and decision theory (supporting).** The Gaussian shift experiment \(N(h,I^{-1})\) is available as `multivariateGaussian h S`. `Probability/Decision/Risk/Defs.lean` defines, for a data-generating kernel \(P:\Theta\to\mathcal X\) and a loss \(\ell:\Theta\times\mathcal Y\to[0,\infty]\), the average risk `avgRisk`, the Bayes risk `bayesRisk`, and the minimax risk `minimaxRisk` over randomized estimators (Markov kernels \(\mathcal X\to\mathcal Y\)); `bayesRisk_le_minimaxRisk` is in `Probability/Decision/Risk/Basic.lean`, and Bayes estimators as posterior argmins are in `Probability/Decision/BayesEstimator.lean`. These are finite-sample, single-experiment notions; there is no local asymptotic minimax statement (102.17), no Anderson's lemma for bowl-shaped losses, and no convolution theorem (102.16). The Loewner order on matrices is the scoped partial order \(A\le B\iff B-A\) positive semidefinite (`Matrix.instPartialOrder`, `Analysis/Matrix/Order.lean`).

#### TauCeti

**Randomization (supporting).** Every probability measure on a standard Borel space is the law of a jointly measurable function of one uniform variable and the measure (`TauCeti.Probability.unitIntervalCoding`, `TauCeti.Probability.map_infinitePi_volume_unitIntervalCoding`, [randomization](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/Probability/Kernel/Randomization.lean)). This is the construction by which a Markov kernel becomes a randomized statistic \(T(X,U)\), as in the definition before 102.15; the representation theorem itself is absent.

**Gaussian tilting (supporting).** Exponential tilting of \(N(m,v)\) by \(e^{tx}\) gives \(N(m+vt,v)\) (`TauCeti.Probability.gaussianReal_tilted_mul`, [tilted laws](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/Probability/Distributions/Tilted.lean)). In the limit experiment this is the mean shift of Le Cam's third lemma (102.14) in dimension one: the law of the limit log-likelihood \(N(-\sigma^2/2,\sigma^2)\) tilted by \(e^{\lambda}\) is \(N(\sigma^2/2,\sigma^2)\). The bivariate statement and the passage to the limit are not stated. The pointwise comparison \((\sqrt u-\sqrt a)^2\le u\log(u/a)-u+a\) of the Hellinger and relative-entropy integrands is proved (`TauCeti.sq_sqrt_sub_sqrt_le_mul_log_sub_mul_log_sub`, [supporting line of \(x\log x\)](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/Analysis/SpecialFunctions/Log/MulLog.lean)), but no Hellinger distance is defined.

**Synopsis entries.** Not covered: 102.12–102.18.

### Local tests and asymptotic relative efficiency

[Mathematical scope](SYNOPSIS102.md#local-tests-and-asymptotic-relative-efficiency).

#### Mathlib

No test, power function, or relative-efficiency notion is defined. The total variation of a signed measure (`MeasureTheory.SignedMeasure.totalVariation`, `MeasureTheory/VectorMeasure/Decomposition/Jordan.lean`) supplies the total-variation hypothesis of 102.21. The Gaussian law on the line, with its density, is in `Probability/Distributions/Gaussian/Real.lean`.

#### TauCeti

**Standard normal quantities (supporting).** The Gaussian distribution function in closed form through `TauCeti.Real.erf`, its derivative the Gaussian density, and the upper tail through `erfc` (`TauCeti.Probability.cdf_gaussianReal_eq`, `TauCeti.Probability.hasDerivAt_cdf_gaussianReal`, [Gaussian cdf](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/Probability/Distributions/Gaussian/Cdf.lean)), and Gaussian quantiles ([Gaussian quantiles](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/Probability/Distributions/Gaussian/Quantile.lean)) give \(\Phi\) and \(z_\alpha\) of 102.19 and 102.21. The Laplace, logistic, and uniform laws of 102.22 are defined with their densities in [the TauCeti distribution library](https://github.com/TauCetiProject/TauCeti/tree/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/Probability/Distributions); the integrals \(\int f^2\) and the efficiency values are not computed.

**Synopsis entries.** Not covered: 102.19–102.22.

### General criteria, moment methods, and nonlinear limits

[Mathematical scope](SYNOPSIS102.md#general-criteria-moment-methods-and-nonlinear-limits).

#### Mathlib

**Supporting material.** Convergence in distribution, Slutsky, and the one-dimensional central limit theorem, as above. Second-order Taylor expansion of real functions with Lagrange remainder (`taylor_mean_remainder_lagrange`, `Analysis/Calculus/Taylor.lean`). There is no general \(M\)-estimation theorem, no argmax continuous-mapping theorem (102.33), no space \(\ell^\infty(K)\) of bounded functions with weak convergence of non-measurable maps (outer expectations, as in 102.25 and 102.33), and no Hadamard differentiability (102.28).

**The particular case of 102.27.** For i.i.d. square-integrable \(X_k\) with mean zero, the central limit theorem gives \(\sqrt n\,\bar X\Rightarrow N(0,\sigma^2)\), and the continuous-mapping theorem applied to \(x\mapsto x^2\) gives \(n\bar X^2\Rightarrow Y^2\) with \(Y\sim N(0,\sigma^2)\). With TauCeti's `map_sum_sq_pi_gaussianReal` (one coordinate) the limit is the law of \(\sigma^2\chi^2_1\). This consequence is not stated as such. The general second-order delta method is not stated.

#### TauCeti

**Strong consistency of empirical Fréchet barycenters.** Let \(Y_0,Y_1,\ldots\) be i.i.d. with law \(\mu\) in a separable pseudometric space, with finite \(p\)-th moment, \(1\le p<\infty\). Almost surely, for every sequence \(b_n\) that is eventually a Fréchet \(p\)-barycenter of the empirical measure of \(Y_0,\ldots,Y_n\), that is, a minimizer of \(x\mapsto\bigl(\frac1{n+1}\sum_{i\le n}d(x,Y_i)^p\bigr)^{1/p}\), every cluster point of \((b_n)\) is a Fréchet barycenter of \(\mu\); the minimal empirical radius converges to the minimal radius of \(\mu\) (`TauCeti.isFrechetBarycenter_of_mapClusterPt_empiricalMeasure_ae`, `TauCeti.tendsto_iInf_frechetRadius_empiricalMeasure_ae`, [empirical barycenters](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/MeasureTheory/Measure/FrechetMean/Empirical.lean)). On a proper metric space every such sequence has a subsequence converging to a barycenter of \(\mu\), and when \(\mu\) has only one barycenter the whole sequence converges to it almost surely (`TauCeti.exists_isFrechetBarycenter_tendsto_comp_empiricalMeasure_ae`, `TauCeti.tendsto_of_isFrechetBarycenter_empiricalMeasure_ae`, same file). The proof goes through almost-sure convergence of empirical measures in the \(p\)-Wasserstein distance (`TauCeti.tendsto_wassersteinEDist_empiricalMeasure_ae`, [Varadarajan's theorem](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/MeasureTheory/OptimalTransport/Wasserstein/Empirical.lean)) and the deterministic stability of barycenters under Wasserstein convergence ([stability](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/MeasureTheory/Measure/FrechetMean/Stability.lean)). This is an \(M\)-estimator with criterion \(m_\theta(x)=-d(\theta,x)^p\): a particular case of 102.23, with almost-sure rather than in-probability conclusions, exact rather than approximate minimizers, and the separation condition replaced by compactness and uniqueness. The general theorem 102.23 is not stated.

**Multinomial covariance (supporting).** The multinomial law on count vectors is defined over the probability simplex, and its covariance matrix is computed as \(n(\mathop{\mathrm{diag}}p-pp^\top)\) (`TauCeti.Probability.covMatrix_map_multinomialToEuclidean_multinomialMeasure`, [multinomial moments](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/Probability/Distributions/Multinomial/Moments.lean)). Together with a multivariate central limit theorem and the chi-squared law of a Gaussian quadratic form of a projection, this is the content of Pearson's theorem (102.31); neither of the last two steps is present.

**Synopsis entries.** Partly covered: 102.23 (strong consistency of empirical Fréchet barycenters in TauCeti, a particular \(M\)-estimator; the general uniform-convergence and separation criterion is not stated). Not covered: 102.24–102.26, 102.27 (ingredients only: only the particular case \(n\bar X^2\Rightarrow\sigma^2\chi^2_1\), which follows in two steps from the Mathlib central limit theorem, continuous mapping, and TauCeti's chi-squared law of Gaussian squares; the general second-order delta method is absent), 102.28–102.33.

### Semiparametric models and missing data

[Mathematical scope](SYNOPSIS102.md#semiparametric-models-and-missing-data).

#### Mathlib

No semiparametric model, tangent space, efficient score, or missing-data structure is defined. Supporting material: orthogonal projection onto a closed subspace of a Hilbert space, with the Pythagorean identity \(\|x\|^2=\|P_Sx\|^2+\|P_{S^\perp}x\|^2\) (`norm_sq_eq_add_norm_sq_projection`, `Analysis/InnerProductSpace/Projection/Basic.lean`), which is the operation that defines the efficient score; conditional expectation with the pull-out property and the tower property (`condExp_condExp_of_le`, `MeasureTheory/Function/ConditionalExpectation/Basic.lean`), from which the unbiasedness computation in 102.37 follows; Gibbs' inequality for KL divergence, which is the analytic core of the monotonicity of EM (102.36). None of 102.34–102.37 is stated.

#### TauCeti

No relevant declarations were found. The I-projection with its Pythagorean identity for KL divergence ([relative-entropy projection](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/InformationTheory/KullbackLeibler/Projection.lean)) is a projection onto a linear family of measures, not onto a tangent space of scores.

**Synopsis entries.** Not covered: 102.34–102.37.

### Pathwise derivatives and orthogonal estimation

[Mathematical scope](SYNOPSIS102.md#pathwise-derivatives-and-orthogonal-estimation).

#### Mathlib

The Hilbert-space projection and Pythagorean identity above give the abstract identity \(P\phi^2=P\phi_{\mathrm{eff}}^2+P(\phi-\phi_{\mathrm{eff}})^2\) of 102.38 once \(\phi_{\mathrm{eff}}\) is identified as the projection of \(\phi\) onto the tangent space; that identification, pathwise differentiability, and the canonical gradients of the mean and of quantiles are absent. Cross-fitting (102.39) and the partially linear model (102.40) are absent.

#### TauCeti

No relevant declarations were found.

**Synopsis entries.** Not covered: 102.38–102.40.

### Adaptation, missing information, and multiple imputation

[Mathematical scope](SYNOPSIS102.md#adaptation-missing-information-and-multiple-imputation).

#### Mathlib

**Conditional moments.** The tower property `condExp_condExp_of_le`: for \(m_1\le m_2\le m_0\) with \(\mu\) σ-finite on \(m_2\), \(\mu[\mu[f\mid m_2]\mid m_1]=\mu[f\mid m_1]\) almost everywhere. With \(m_1=\sigma(Y_{\mathrm{obs}})\) and \(m_2=\sigma(Y_{\mathrm{obs}},Y_{\mathrm{mis}})\) this is the first identity of 102.43. The conditional variance `condVar` relative to a sub-σ-algebra is defined, with \(\mathop{\mathrm{Var}}[X\mid m]=\mathbb E[X^2\mid m]-\mathbb E[X\mid m]^2\) almost everywhere (`condVar_ae_eq_condExp_sq_sub_sq_condExp`), and the law of total variance is proved in unconditional form: for \(X\in L^2\) of a probability measure, \(\mathbb E\mathop{\mathrm{Var}}[X\mid m]+\mathop{\mathrm{Var}}\mathbb E[X\mid m]=\mathop{\mathrm{Var}}X\) (`integral_condVar_add_variance_condExp`, `Probability/CondVar.lean`). The second identity of 102.43 is its conditional version given \(Y_{\mathrm{obs}}\), which is not stated; nor are the conditional mean and variance of the combining-rule quantities \(\bar\theta\) and \(T\).

No adaptive estimator (102.41), observed or missing information, Louis's formula, or EM rate (102.42) is present.

#### TauCeti

No relevant declarations were found. The mean-square error of a sample mean of pairwise independent square-integrable vectors, \(\mathbb E\|\bar X-m\|^2=r^{-2}\sum_k\mathbb E\|X_k-m\|^2\) (`TauCeti.integral_norm_finiteMean_sub_sq`, [sample means](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/Probability/Moments/SampleMean.lean)), is the elementary computation behind the factor \(D^{-1}B_\infty\) in 102.43, in unconditional form.

**Synopsis entries.** Partly covered: 102.43 (the first identity is the Mathlib tower property; the second is proved only in unconditional form, as the law of total variance; the combining-rule moments are absent). Not covered: 102.41, 102.42.

### Robust statistics

[Mathematical scope](SYNOPSIS102.md#robust-statistics).

#### Mathlib

No influence function, gross-error sensitivity, breakdown point, or \(M\)-functional is defined. Sion's minimax theorem, for a function on a product of convex sets, one of them compact, that is lower semicontinuous and quasiconvex in one variable and upper semicontinuous and quasiconcave in the other (`Sion.exists_isSaddlePointOn`, `Topology/Sion.lean`), is the kind of saddle-point statement of which Huber's minimax property in 102.44 is a concrete instance; Huber's saddle point is not derived from it, and the variance functional \(V(\psi,G)\) is not defined.

#### TauCeti

**Quantiles and contamination (supporting).** The quantile function and its Galois characterization (above) are the tools for the median bounds of 102.46; the quantile of a mixture \((1-\varepsilon)F+\varepsilon H\) is not computed. The Gaussian distribution function and density (above) supply \(\Phi\), \(\varphi\), and the Huber constant equation of 102.44 as real functions; the optimization statements are absent. Laws of order statistics (above) give the exact finite-sample law of the sample median, not its breakdown point.

**Synopsis entries.** Not covered: 102.44–102.46.

### Von Mises expansions and regression \(M\)-estimators

[Mathematical scope](SYNOPSIS102.md#von-mises-expansions-and-regression-m-estimators).

#### Mathlib

No Hadamard derivative of statistical functionals, Brownian bridge, or regression \(M\)-estimator is defined. Mathlib defines Brownian motion through its finite-dimensional laws (`Probability/BrownianMotion/Basic.lean`); the Brownian bridge \(B^0\circ F\) and the empirical process are not defined. Convex functions and their one-sided derivatives are developed in `Analysis/Convex/`, the setting of the convexity argument behind 102.48, but no convex-process limit theorem is stated.

#### TauCeti

No relevant declarations were found.

**Synopsis entries.** Not covered: 102.47, 102.48.

<a id="structure-102b"></a>

## 102B. Higher-Order Asymptotics, Resampling, and Information Geometry

Supporting material consists of the Taylor expansion of characteristic functions, exponential tilting and the cumulant-generating function, Hermite polynomials as an orthonormal basis of \(L^2(\gamma)\), the Lévy–Prokhorov metrization of weak convergence, TauCeti's sampling-with-replacement law, and Riemannian metrics on manifolds. No expansion, resampling theorem, or invariance theorem of the subdivision is stated.

[Mathematical scope](SYNOPSIS102.md#synopsis-102b) for items 102.49–102.58, which in the synopsis precede the first topic heading of this subdivision.

#### Mathlib

**Characteristic functions and expansions (supporting).** If a probability measure on \(\mathbb R\) has a moment of order \(n\), its characteristic function is \(C^n\), with iterated derivatives at the origin \(i^k\int x^k\,d\mu\), and its Taylor polynomial at the origin is recorded; for a centred variable with unit variance the second-order expansion \(1-t^2/2+o(t^2)\) is `taylor_charFun_two` (`MeasureTheory/Measure/CharacteristicFunction/TaylorExpansion.lean`). These are the expansions from which Edgeworth series (102.49, 102.50) are derived; there is no smoothing inequality, no nonlattice or Cramér condition, and no Berry–Esseen theorem.

**Tilting (supporting).** The tilted measure `Measure.tilted μ f` with density \(e^f/\int e^f\,d\mu\) (`MeasureTheory/Measure/Tilted.lean`), and the identities that under \(e^{tX}\mu/\mathbb Ee^{tX}\) the mean and variance of \(X\) are \(K'(t)\) and \(K''(t)\), for \(t\) in the interior of the exponential-integrability set (`integral_tilted_mul_self`, `variance_tilted_mul`, `Probability/Moments/Tilted.lean`). These are the identities used at \(\hat s\) in the saddlepoint approximation (102.55); the local limit theorem for densities is not stated.

**Weak convergence in probability (supporting).** The Lévy–Prokhorov distance `levyProkhorovDist` metrizes convergence in distribution of probability measures on a separable pseudometrizable space (`LevyProkhorov.eq_convergenceInDistribution`, `MeasureTheory/Measure/LevyProkhorovMetric.lean`). A bootstrap consistency statement, convergence in probability of the random distance between a conditional law and a fixed limit, can be phrased with it; no Kolmogorov or bounded-Lipschitz distance is defined, and no bootstrap theorem (102.51, 102.52) is stated. The limit \((1+t/n)^n\to e^t\) is `Real.tendsto_one_add_div_pow_exp` (`Analysis/SpecialFunctions/Complex/LogBounds.lean`).

**Riemannian metrics (supporting).** Riemannian bundles and Riemannian manifolds, with the induced distance, are in `Topology/VectorBundle/Riemannian.lean` and `Geometry/Manifold/Riemannian/Basic.lean` (`IsRiemannianManifold`). The Fisher–Rao metric on the open simplex, congruent embeddings, and Čencov's theorem (102.58) are absent.

The jackknife (102.53), empirical likelihood (102.56), and subsampling (102.57) have no counterpart.

#### TauCeti

**Generating functions of tilted laws (supporting).** The moment- and cumulant-generating functions of a tilted measure are the shifted and recentred originals, \(\mathop{\mathrm{cgf}}_{t}(s)=K(t+s)-K(t)\) on the translated domain (`TauCeti.mgf_tilted_mul`, `TauCeti.cgf_tilted_mul`, [tilted generating functions](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/Probability/Moments/Tilted.lean)).

**Hermite polynomials (supporting).** The normalized Hermite polynomials \(H_n/\sqrt{n!}\) form an orthonormal basis of \(L^2(\gamma)\) for the standard Gaussian \(\gamma\) (`TauCeti.gaussianHermiteHilbertBasis`, [Hermite basis](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/Probability/Distributions/Gaussian/Hermite/Basis.lean)). The Edgeworth correction \(\varphi(x)(x^2-1)\) of 102.49 is \(\varphi(x)H_2(x)\) for the second probabilists' Hermite polynomial, but no expansion is stated.

**Resampling law (supporting).** For a finite population \(x:\kappa\to\alpha\), drawing \(|\iota|\) independent uniform indices and reading off the selected entries has the law of \(|\iota|\) independent draws from the empirical measure of \(x\), and for a random population the sampling-with-replacement law is the mixture over the population law of these product empirical laws (`TauCeti.Probability.pi_empiricalMeasureOfFintype_eq_map_uniformOn`, `TauCeti.Probability.sampleWithReplacement_eq_bind_pi_empiricalMeasureOfFintype`, [finite sampling](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/Probability/PopulationSampling/Finite.lean)). This is exactly the bootstrap resampling law of 102.51 and 102.52 conditional on the sample, with the collision bound \(\binom{|\iota|}2/|\kappa|\) comparing sampling with and without replacement. No limit theorem for the resampled statistic is proved. The probability simplex appears as a measurable space and as the parameter set of the multinomial and Dirichlet laws, without a metric structure.

**Synopsis entries.** Not covered: 102.49–102.53, 102.55–102.58.

### Bootstrap for smooth functionals

[Mathematical scope](SYNOPSIS102.md#bootstrap-for-smooth-functionals).

#### Mathlib

No relevant declarations were found beyond the convergence-in-distribution and Lévy–Prokhorov material above; Hadamard differentiability and conditional weak convergence in probability are absent.

#### TauCeti

No relevant declarations were found.

**Synopsis entries.** Not covered: 102.59.

### Accuracy and failure of the bootstrap

[Mathematical scope](SYNOPSIS102.md#accuracy-and-failure-of-the-bootstrap).

#### Mathlib

The limit \((1-1/n)^n\to e^{-1}\) in 102.61 is the case \(t=-1\) of `Real.tendsto_one_add_div_pow_exp`. Neither the conditional atom of the bootstrap maximum nor any coverage statement for bootstrap intervals (102.60) is present.

#### TauCeti

The law of the sample maximum of an i.i.d. sample is the case \(k=n-1\) of the order-statistic law above, and for the uniform law on \([0,1]\) it is Beta\((n,1)\) (`TauCeti.Probability.map_orderStatistic_pi_uniformMeasure`). Its exponential limit, and the bootstrap statements of 102.61, are not stated.

**Synopsis entries.** Not covered: 102.60, 102.61.

## Missing from both libraries

Essentially the whole of Section 102 is missing. The following groups the principal results by the infrastructure that would be needed, in roughly increasing distance from what exists.

- **Stochastic order symbols and the delta method (102.1, 102.27, 102.28).** The ingredients are present in Mathlib: Slutsky's theorem, continuous mapping, transfer of limits under \(o_P(1)\) perturbations, Fréchet derivatives with little-\(o\) remainders, and, in TauCeti, affine images of multivariate Gaussians. What is missing is a definition of \(O_P\) and \(o_P\) along a sequence of probability spaces, with the lemma that \(o(\|h\|)\) composed with an \(O_P(r_n^{-1})\) sequence is \(o_P(r_n^{-1})\). After that, the finite-dimensional delta method is a few steps; the second-order delta method needs in addition the Peano form of the second-order Taylor expansion in several variables. The functional delta method needs Hadamard differentiability and weak convergence in \(\ell^\infty\), which are absent.
- **Multivariate central limit theorem.** Not stated, but one step from the Mathlib Cramér–Wold device and the one-dimensional theorem. It is a prerequisite for nearly every vector statement of 102A (102.3, 102.4, 102.11, 102.13, 102.31, 102.32).
- **Gaussian quadratic forms and chi-squared limits (102.11, 102.20, 102.31, 102.32).** TauCeti has the chi-squared law of sums of squared independent Gaussians and the mgf of Gaussian quadratic forms. The statements \(Z^\top\Sigma^{-1}Z\sim\chi^2_k\) and \(\|\Pi Z\|^2\sim\chi^2_r\) for an orthogonal projection \(\Pi\) of rank \(r\) are short consequences (via `map_affine_multivariateGaussian` and the standard Gaussian's invariance under orthogonal maps) but are not stated; the noncentral chi-squared law and the chi-bar-squared law are absent. Pearson's theorem then needs only the multivariate central limit theorem and TauCeti's multinomial covariance.
- **Parametric models, likelihood, and Fisher information (102.2–102.5, 102.11, 102.26).** There is no structure for a dominated family \(\{p_\theta\}\) with score and information. The KL divergence and Gibbs' inequality, which drive Wald's consistency proof and the identification of \(\theta^\star\) in 102.26, are present; uniform laws of large numbers over compact parameter sets are absent. A general \(M\)-estimation consistency theorem (102.23) would generalize TauCeti's Fréchet-barycenter consistency, whose proof via Wasserstein convergence of empirical measures does not transfer directly; the standard route needs a uniform law of large numbers (Glivenko–Cantelli class), which neither library has.
- **Quantiles, order statistics, U- and L-statistics (102.6–102.10, 102.29, 102.30).** TauCeti's quantile function, its Galois property, and the Beta representation of order statistics are a good starting point for 102.6 via the uniform case; the empirical distribution function and Glivenko–Cantelli theorem are absent. The Hájek projection needs only the orthogonal projection in \(L^2\) of a product space onto additive functions, which can be built from Mathlib's conditional expectation; U-statistics and the Hoeffding decomposition need symmetric kernels on product spaces, absent. Degenerate U-statistics need, in addition, the eigenfunction expansion of a symmetric Hilbert–Schmidt integral kernel in \(L^2(P\otimes P)\) and a limit theorem for the resulting Gaussian chaos; neither is stated.
- **Contiguity, local asymptotic normality, and limits of experiments (102.12–102.20).** These need contiguity, the Hellinger distance and quadratic-mean differentiability, and Le Cam's lemmas. The finite-sample objects (absolute continuity, likelihood ratios, KL divergence, Gaussian tilting, Mathlib's decision-theoretic minimax risk) exist; the asymptotic theory is several layers away. Anderson's lemma for bowl-shaped losses needs the Brunn–Minkowski or Prékopa–Leindler inequality, which TauCeti has in [its Lebesgue-measure files](https://github.com/TauCetiProject/TauCeti/tree/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/MeasureTheory/Measure/Lebesgue/BrunnMinkowski), and would be a moderate step. The representation and convolution theorems need Le Cam's theory of weak convergence of experiments and are far away.
- **Asymptotic relative efficiency (102.19, 102.21, 102.22).** The efficacy formulas of 102.22 for the normal, Laplace, uniform, and logistic laws are explicit integrals of defined densities and could be computed directly; the theorems connecting efficacy to Pitman efficiency need local asymptotic normality of test statistics under local alternatives, absent.
- **Semiparametric efficiency and missing data (102.34–102.43).** Tangent spaces, efficient scores, and pathwise derivatives need a theory of differentiable paths of measures in Hellinger or quadratic-mean sense, absent. The algebraic parts are close to existing material: double robustness (the first half of 102.37) is a computation with the tower and pull-out properties of conditional expectation; ignorability (102.35) is a factorization of the likelihood; monotonicity of EM (the first half of 102.36) is Gibbs' inequality; the conditional law of total variance (for 102.43) is a short generalization of Mathlib's unconditional statement.
- **Robust statistics (102.44–102.48).** Influence functions are Gâteaux derivatives along contamination paths and could be defined directly; the median influence function and the contamination bounds of 102.46 are elementary with TauCeti's quantile API. Breakdown points are combinatorial and absent. Huber's minimax property needs a concrete variational argument for the variance functional; Mathlib's Sion theorem does not apply directly. Regression \(M\)-estimators need convexity lemmas for random convex processes, absent.
- **Higher-order expansions (102.49, 102.50, 102.55).** Edgeworth expansions need Esseen's smoothing inequality and Fourier inversion for measures with integrable characteristic functions; neither is stated (CKMA Structure 06 records that the inversion formula is not stated for measures, and that the Berry–Esseen theorem is absent). The saddlepoint approximation needs, in addition, a local limit theorem for densities. The tilting identities and the Hermite basis are present.
- **Resampling (102.51–102.53, 102.56, 102.57, 102.59–102.61).** TauCeti's sampling-with-replacement law is the bootstrap law; what is missing is conditional weak convergence in probability, a distance (Kolmogorov or bounded Lipschitz) on laws to state it, and the limit theorems themselves, the simplest of which (102.51) would follow from a Lindeberg central limit theorem for triangular arrays, absent. The failure for the sample maximum (102.61) is an elementary computation of the conditional atom, combined with the extreme-value limit of the uniform maximum, both absent but close.
- **Information geometry (102.58).** Mathlib's Riemannian manifolds are the general framework; the Fisher–Rao metric on the simplex, congruent Markov embeddings, and Čencov's characterization are absent.
