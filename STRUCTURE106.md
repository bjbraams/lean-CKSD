# Structure 106: Dependent data and stochastic models

Part of the [Mathlib and TauCeti coverage series](STRUCTURE.md).
[Mathematical inventory](SYNOPSIS106.md); [bibliographical scope](CKSD-bib.md#cks-106).

This file follows the thematic order and lettered subdivisions of the mathematical inventory. It records definitions, structures, and proved results, with supporting material identified separately. A topic heading locates the recorded statements; the **Synopsis entries** line at the end of each section states which numbered results are covered.

**Source baseline.** Mathlib `911003dd6dea5df215dff57f2717be762e11a6ca` and TauCeti `a049b4264d2cf4dbf4720796f844a3a3764914a5`, both of 2026-10-18, checked against local checkouts on 2026-11-01. See the [revision and source conventions](STRUCTURE.md#source-baseline-and-conventions).

**Mathlib source areas.** `Mathlib.Probability.Martingale`, `Mathlib.Probability.Process`, `Mathlib.Probability.CentralLimitTheorem`, `Mathlib.Probability.Moments`, `Mathlib.Probability.Distributions` (Gaussian, multivariate Gaussian, exponential, Poisson, Pareto), `Mathlib.Probability.Kernel`, `Mathlib.InformationTheory.KullbackLeibler`, `Mathlib.MeasureTheory.Function.ConvergenceInDistribution`, `Mathlib.Analysis.InnerProductSpace.Projection`, `Mathlib.Analysis.InnerProductSpace.GramMatrix`, `Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho`, `Mathlib.Analysis.InnerProductSpace.MeanErgodic`, `Mathlib.Analysis.Fourier.AddCircle`, `Mathlib.Analysis.SpecialFunctions.Complex.LogBounds`, `Mathlib.Analysis.SpecialFunctions.Bessel`, `Mathlib.LinearAlgebra.Matrix.SchurComplement`.

**Namespaces.** Martingales, filtrations, stopping times, and conditional expectation are `MeasureTheory`; laws, moments, and kernels are `ProbabilityTheory`, with nested `Kernel`. Orthogonal projection is `Submodule.starProjection`, and Gram matrices are `Matrix.gram`. TauCeti declarations cited here are in `TauCeti` and `TauCeti.Probability`; the Cauchy random-variable lemmas extend `ProbabilityTheory`, and the conditional Gaussian mean and covariance are `EuclideanSpace.gaussianCondMean` and `Matrix.gaussianCondCov`.

Searches of both libraries for autocovariance, spectral density, periodogram, Wold, Yule–Walker, ARMA, GARCH, Kalman filtering, hidden Markov models, mixing coefficients, block bootstrap, kriging, variograms, Matérn covariances, point processes, counting processes, compensators, Kaplan–Meier, Nelson–Aalen, Cox regression, sequential probability ratio tests, Wald's identity, Ville's inequality, e-values, confidence sequences, CUSUM, Anscombe's theorem, regular variation, domains of attraction, the extremal index, and the Hill estimator found no development of these subjects. What is recorded below is general probability and Hilbert-space infrastructure, with three substantive TauCeti contributions: Herglotz's and Bochner's theorems, Gaussian conditioning, and the hazard representation of a survival function.

<a id="structure-106a"></a>

## 106A. Time Series, Stochastic Processes, and Spatial Data

Neither library defines a weakly stationary process, an autocovariance function, or a spectral density of a process. The recorded material is the \(L^2\) and Gaussian infrastructure from which such a theory would be built: covariance and variance of finite sums, orthogonal projection and Gram–Schmidt orthogonalization, Gaussian conditioning, positive-definite functions on \(\mathbb Z\) and \(\mathbb R^d\), the mean ergodic theorem, and the path law of a Markov chain. The general probability, martingale, and Markov-chain foundations are described in [CKMA Structure 06](../lean-CKMA/STRUCTURE06.md) and [CKMA Structure 08](../lean-CKMA/STRUCTURE08.md).

Items 106.1–106.11 precede the first topic heading of the synopsis and are inventoried here.

[Mathematical scope](SYNOPSIS106.md#synopsis-106a).

#### Mathlib

**Limit theorems (supporting, item 1).** The only central limit theorem is the i.i.d. one in dimension one: if the \(X_k\) are independent, identically distributed, and square-integrable, then \(n^{-1/2}\sum_{k<n}(X_k-\mathbb EX_0)\) converges in distribution to the centered Gaussian of variance \(\mathop{\mathrm{Var}}X_0\) (`tendstoInDistribution_inv_sqrt_mul_sum_sub`, `Probability/CentralLimitTheorem.lean`). There is no triangular-array, Lindeberg, or martingale-difference version. Lévy's continuity theorem, the Cramér–Wold device, and Slutsky's lemma, which a proof of item 1 by characteristic functions would use, are recorded in [CKMA Structure 06](../lean-CKMA/STRUCTURE06.md#characteristic-functions-and-classical-distributional-limits). Discrete-time martingales, Doob's decomposition, and conditional expectation are recorded in [CKMA Structure 06](../lean-CKMA/STRUCTURE06.md#discrete-time-martingales), and the Azuma–Hoeffding inequality in [CKMA Structure 07](../lean-CKMA/STRUCTURE07.md).

**Hilbert-space prediction (supporting, items 2, 7).** The orthogonal projection onto a subspace with an orthogonal projection, in particular onto a complete subspace, minimizes the distance: \(\|y-Py\|=\inf_{x\in U}\|y-x\|\) (`Submodule.starProjection_minimal`, `Analysis/InnerProductSpace/Projection/Basic.lean`), and the minimizer exists for every complete subspace (`Submodule.exists_norm_eq_iInf_of_complete_subspace`, `Analysis/InnerProductSpace/Projection/Minimal.lean`). Applied in \(L^2(\mathbb P)\) to the closed linear span of past values this is the best linear predictor \(P_{t-1}X_t\) of the synopsis, but the innovation sequence, the remote past, and the Wold decomposition are not formed. Gram–Schmidt orthogonalization of a family indexed by a well-founded locally finite linear order produces pairwise orthogonal vectors with the same initial spans (`gramSchmidt_orthogonal`, `mem_span_gramSchmidt`, `Analysis/InnerProductSpace/GramSchmidtOrtho.lean`); in \(L^2\) these are the finite-sample innovations \(X_t-\hat X_t\).

**Multivariate Gaussian laws (supporting, items 3, 5, 7).** The multivariate Gaussian on \(\mathbb R^\iota\) with given mean and positive semidefinite covariance matrix is `multivariateGaussian` (`Probability/Distributions/Gaussian/Multivariate.lean`); its affine images and the independence of jointly Gaussian components with zero cross-covariance are recorded in [CKMA Structure 06](../lean-CKMA/STRUCTURE06.md#gaussian-laws-infinite-divisibility-and-exchangeability). Schur-complement identities for block matrices are in `LinearAlgebra/Matrix/SchurComplement.lean`. No Fisher information is defined.

**Markov kernels (supporting, items 8, 19).** Kernels, their compositions, invariant measures, reversibility, \(\varphi\)-irreducibility, and the Ionescu–Tulcea construction of trajectory laws are recorded in [CKMA Structure 08](../lean-CKMA/STRUCTURE08.md#markov-semigroups-martingale-problems-and-chains) (`Probability/Kernel/Invariance.lean`, `Probability/Kernel/Irreducible.lean`, `Probability/Kernel/IonescuTulcea/Traj.lean`).

**Stationarity and ergodic averages (supporting, items 9, 11).** Von Neumann's mean ergodic theorem: for a continuous linear map of norm at most one on a real or complex Hilbert space, the Birkhoff averages converge strongly to the orthogonal projection onto the fixed space (`ContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection`, `Analysis/InnerProductSpace/MeanErgodic.lean`). For a weakly stationary sequence the shift on the closed span of the \(X_t\) is unitary, so this gives \(L^2\) convergence of \(\bar X_n\); this specialization is not stated. Strong mixing coefficients, long-memory asymptotics, and resampling are absent.

#### TauCeti

**Gaussian conditioning (item 7).** For a random vector with law \(N(m,S)\) on \(\mathbb R^{\iota\sqcup\kappa}\), with \(S\) positive semidefinite and the observed block \(S_{22}\) positive definite, the regular conditional distribution of the first block given the second is, almost everywhere, the Gaussian kernel with mean \(m_1+S_{12}S_{22}^{-1}(x_2-m_2)\) and covariance \(S_{11}-S_{12}S_{22}^{-1}S_{21}\) ([Gaussian conditioning](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/Probability/Distributions/Gaussian/Conditional.lean), `TauCeti.Probability.condDistrib_multivariateGaussian`, with the parameters `EuclideanSpace.gaussianCondMean` and `Matrix.gaussianCondCov`). For \(t=1\), taking the first block to be \(x_1\) and the second to be \(y_1=H_1x_1+v_1\), the joint covariance has \(S_{22}=\Sigma_1\), \(S_{12}=P_{1\mid0}H_1^\top\), and the theorem gives the first measurement update of item 7: mean \(x_{1\mid0}+K_1(y_1-H_1x_{1\mid0})\) and covariance \(P_{1\mid0}-K_1H_1P_{1\mid0}\). This specialization is not stated, and the recursion in \(t\), which requires conditioning on a growing observation vector, is not developed.

**Markov chain path laws (supporting, items 8, 19).** The path law of a time-homogeneous Markov chain with initial law \(\nu\) and transition kernel \(\kappa\) is constructed on \(\alpha^{\mathbb N}\), with the Markov property and, on a space with measurable singletons, the cylinder formula \(\mathbb P(X_0=w_0,\ldots,X_n=w_n)=\nu\{w_0\}\prod_{i<n}\kappa(w_i)\{w_{i+1}\}\) ([Markov chains](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/Probability/Process/MarkovChain.lean), `TauCeti.Probability.markovChainLaw`, `TauCeti.Probability.markovChainLaw_map_prefix_succ_eq_compProd`, `TauCeti.Probability.markovChainLaw_map_prefix_apply_singleton`). This is the likelihood of an observed finite chain. Hidden states, emission densities, and the forward recursion of item 8 are not formed.

**Ergodic averages (supporting, items 9, 11, 12).** For a measure-preserving map \(T\) with \(\sigma\)-finite trimmed measure on the invariant \(\sigma\)-algebra \(\mathcal I\), and \(f\) integrable and square-integrable, the Birkhoff averages converge in \(L^2\) to \(\mathbb E[f\mid\mathcal I]\) ([mean ergodic theorem for conditional expectations](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/Probability/Ergodic/CondExpProjection.lean), `TauCeti.Probability.tendsto_eLpNorm_birkhoffAverage_sub_condExp`). Applied to the shift on the path space of a strictly stationary sequence this is the \(L^2\) law of large numbers for the sample mean. Further ergodic material is in [CKMA Structure 10](../lean-CKMA/STRUCTURE10.md).

**Synopsis entries.** Partly covered: 106.7 (the conditional law at \(t=1\) is an instance of TauCeti's Gaussian conditioning theorem, not stated in filtering form; the recursion, the prediction step, and the independence and factorization of the innovations are absent). Not covered: 106.1–106.6, 106.8–106.11.

### Mean estimation and innovation likelihoods

[Mathematical scope](SYNOPSIS106.md#mean-estimation-and-innovation-likelihoods).

#### Mathlib

The variance of a finite sum of square-integrable real random variables is the double sum of covariances, \(\mathop{\mathrm{Var}}\sum_{i\in s}X_i=\sum_{i,j\in s}\mathop{\mathrm{Cov}}(X_i,X_j)\) (`variance_sum'`, `variance_sum`, `Probability/Moments/Variance.lean`), and covariance is bilinear over finite sums (`covariance_sum_sum`, `Probability/Moments/Covariance.lean`). For a stationary sequence this gives \(n\mathop{\mathrm{Var}}\bar X_n=\sum_{|h|<n}(1-|h|/n)\gamma(h)\) after reindexing, which is not stated; the limit \(\sum_h\gamma(h)\) then follows by dominated convergence under absolute summability. The central limit theorem for linear processes is absent. The Gaussian density on \(\mathbb R\) is in `Probability/Distributions/Gaussian/Real.lean`.

#### TauCeti

The conditional law of \(X_t\) given \(X_1,\ldots,X_{t-1}\), for a nondegenerate Gaussian vector, is Gaussian with affine mean \(\hat X_t\) and Schur-complement variance \(v_t\), by `TauCeti.Probability.condDistrib_multivariateGaussian` above. The independence of the innovations and the factorization of the joint density into the one-step conditional densities are not stated. For independent samples, the mean-square error of a sample mean is \(r^{-2}\sum_k\mathbb E\|X_k-m\|^2\) under pairwise independence ([sample means](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/Probability/Moments/SampleMean.lean), `TauCeti.integral_norm_finiteMean_sub_sq`); this is the independent case of item 12.

**Synopsis entries.** Partly covered: 106.13 (each one-step conditional law is Gaussian with the stated mean and variance, by TauCeti's Gaussian conditioning; the independence of the innovations, the likelihood formula, and the Kalman identification are absent). Not covered: 106.12.

### Spectral representation and linear prediction

[Mathematical scope](SYNOPSIS106.md#spectral-representation-and-linear-prediction).

#### Mathlib

Fourier series on the circle: the Fourier coefficients of an \(L^2\) function form an orthonormal expansion, and Parseval's identity holds (`hasSum_fourier_series_L2`, `tsum_sq_fourierCoeff`, `Analysis/Fourier/AddCircle.lean`). This is the setting for a spectral density with square-summable autocovariances; no spectral measure of a process is constructed. The Gram matrix of vectors in an inner-product space is Hermitian and positive semidefinite (`Matrix.gram`, `Matrix.posSemidef_gram`, `Analysis/InnerProductSpace/GramMatrix.lean`), so an autocovariance function is nonnegative definite; the Toeplitz structure is not formed. The Durbin–Levinson recursion and Kolmogorov's formula are absent; the Szegő infimum theorem is recorded as not covered in [CKMA Structure 42](../lean-CKMA/STRUCTURE42.md).

#### TauCeti

Herglotz's theorem: a function \(\varphi:\mathbb Z\to\mathbb C\) is positive definite, \(\sum_{i,j}c_i\bar c_j\varphi(n_i-n_j)\ge0\) for every finite family, if and only if \(\varphi(n)=\int_{\mathbb T}z^n\,d\mu(z)\) for a finite positive measure \(\mu\) on the unit circle ([Herglotz](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/Analysis/Bochner/Herglotz.lean), `TauCeti.exists_isFiniteMeasure_integral_zpow_eq`, `TauCeti.isPositiveDefiniteSub_iff_exists_isFiniteMeasure_integral_zpow_eq`). The proof is by Fejér means and Prokhorov's theorem on the circle. The same statement for an arbitrary discrete abelian group, with a measure on the Pontryagin dual, is `TauCeti.isPositiveDefiniteSub_iff_exists_pontryaginMeasureTransform_eq` ([discrete groups](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/Analysis/Bochner/DiscreteGroup.lean)). The Herglotz file does not state uniqueness of \(\mu\); it follows from injectivity of the Fourier–Stieltjes transform on finite measures ([CKMA Structure 28](../lean-CKMA/STRUCTURE28.md)). The positive-definiteness condition is on \(\varphi(n_i-n_j)\) with complex coefficients, which contains the Hermitian property. A positive-definite kernel is realized as a Gram kernel \(K(a,b)=\langle\Phi(a),\Phi(b)\rangle\) in a minimal Hilbert space ([Kolmogorov decomposition](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/Analysis/PositiveDefinite/Kernel/Kolmogorov.lean), `Matrix.PosSemidef.kolmogorovFeature`, `Matrix.PosSemidef.inner_kolmogorovFeature`); this is the Hilbert-space half of "every nonnegative definite function is an autocovariance", without a probability space. Hardy-space Toeplitz operators are developed analytically ([Toeplitz](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/Analysis/Fourier/Hardy/Toeplitz.lean)); they are not connected to prediction.

**Synopsis entries.** Partly covered: 106.14 (Herglotz's equivalence between positive definiteness on \(\mathbb Z\) and the spectral representation, written with a measure on the circle rather than a distribution function on \((-\pi,\pi]\); the realization as the autocovariance of a stationary process, the density for absolutely summable \(\gamma\), and the ARMA spectral density are absent). Not covered: 106.15, 106.16.

### ARMA estimation, conditional heteroscedasticity, and Markov chains

[Mathematical scope](SYNOPSIS106.md#arma-estimation-conditional-heteroscedasticity-and-markov-chains).

#### Mathlib

No ARMA, Whittle, or GARCH material was found. The kernel and trajectory infrastructure for finite Markov chains is as in the opening part of this subdivision. The ergodic theorem for finite Markov chains, \(n_i/n\to\pi_i\), is not stated (see [CKMA Structure 08](../lean-CKMA/STRUCTURE08.md#markov-semigroups-martingale-problems-and-chains)).

#### TauCeti

The Markov-chain path law and its cylinder formula, above, give the likelihood \(\nu\{x_0\}\prod_{i,j}p_{ij}^{n_{ij}}\) of a finite-state chain. The maximization giving \(\hat p_{ij}=n_{ij}/n_i\) is not carried out. A stationary process on a countable state space is recurrent, in the sense that almost surely every state it visits is visited infinitely often ([recurrence](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/Probability/Recurrent/Basic.lean), `TauCeti.Probability.recurrent_of_measurePreserving_shift`), and excursions from a recurrent state are i.i.d. ([excursions](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/Probability/Process/Excursion/MarkovChain.lean)); these are the regeneration ingredients of the ergodic theorem cited in item 19, which itself is not stated.

**Synopsis entries.** Not covered: 106.17–106.19.

### Spatial data, point patterns, and Gaussian processes

[Mathematical scope](SYNOPSIS106.md#spatial-data-point-patterns-and-gaussian-processes).

#### Mathlib

Best linear prediction is orthogonal projection, `Submodule.starProjection_minimal`, as above. The finite-dimensional normal equations \(K a=k_0\) and the error formula \(k(s_0,s_0)-k_0^\top K^{-1}k_0\) are not stated. A Gaussian process is a process with Gaussian finite-dimensional laws (`IsGaussianProcess`, `Probability/Distributions/Gaussian/IsGaussianProcess/Def.lean`); no Gaussian process with a prescribed covariance kernel is constructed, and equivalence and singularity of Gaussian measures (Feldman–Hájek) are not found ([CKMA Structure 09](../lean-CKMA/STRUCTURE09.md)). The scalar Poisson law is `poissonMeasure` (`Probability/Distributions/Poisson/Basic.lean`); Poisson point processes are absent ([CKMA Structure 06](../lean-CKMA/STRUCTURE06.md#poisson-random-measures)).

#### TauCeti

For a centered Gaussian vector \((X(s_0),X(s_1),\ldots,X(s_n))\) with \(K\) positive definite, Gaussian conditioning (`TauCeti.Probability.condDistrib_multivariateGaussian`) gives the conditional law of \(X(s_0)\) as Gaussian with mean \(k_0^\top K^{-1}(X(s_1),\ldots,X(s_n))^\top\) and variance \(k(s_0,s_0)-k_0^\top K^{-1}k_0\); this is the Gaussian half of item 20. The Poisson law's mean and variance are computed ([Poisson](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/Probability/Distributions/Poisson/Basic.lean), `TauCeti.Probability.integral_id_map_cast_poissonMeasure`, `TauCeti.Probability.variance_id_map_cast_poissonMeasure`), which gives the unbiasedness and variance \(\lambda/|W|\) in item 22 once \(N(W)\sim\mathop{\mathrm{Poisson}}(\lambda|W|)\) is given; the point process, the likelihood, the UMVU property, and the normal limit are absent. The Moore–Penrose pseudoinverse on inner-product spaces ([Moore–Penrose](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/Analysis/InnerProductSpace/MoorePenrose.lean)) is supporting linear algebra for generalized least squares; the universal-kriging predictor is not formed.

**Synopsis entries.** Partly covered: 106.20 (the Gaussian statement, as an instance of TauCeti's Gaussian conditioning; the minimality among linear predictors is the abstract projection theorem of Mathlib, without the explicit coefficient and error formulas). Not covered: 106.21–106.23.

### Covariance models for random fields

[Mathematical scope](SYNOPSIS106.md#covariance-models-for-random-fields).

#### Mathlib

Bessel functions of the first kind are defined, \(J_a(x)=(x/2)^a\,{}_0F_1(-;a+1;-(x/2)^2)/\Gamma(a+1)\) (`Complex.besselJ`, `Analysis/SpecialFunctions/Bessel.lean`); the modified Bessel function \(\mathcal K_\nu\) of the Matérn family is not defined, and the file lists Bessel functions of the second kind as future work. The identity \(\mathop{\mathrm{Var}}\sum_jc_jZ(x_j)=\sum_{j,k}c_jc_k\mathop{\mathrm{Cov}}(Z(x_j),Z(x_k))\) underlying item 25 is `variance_sum` with scalar multiples. Mean-square differentiability is not defined.

#### TauCeti

Bochner's theorem on a finite-dimensional real inner-product space \(V\), in particular on \(\mathbb R^d\): a function \(F:V\to\mathbb C\) is continuous and positive definite if and only if \(F(v)=\int e^{-2\pi i\langle v,q\rangle}\,d\mu(q)\) for a unique finite positive Borel measure \(\mu\) ([Bochner](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/Analysis/Bochner/BochnerTheorem.lean), `TauCeti.bochner`, `TauCeti.bochner_euclideanSpace`, `TauCeti.bochner_probabilityMeasure`; the transform uses the Fourier convention `fourierAtom`). The equivalence with being the autocovariance of a mean-square continuous field is not stated. The Cauchy law has characteristic function \(e^{ix_0t-\gamma|t|}\) ([Cauchy](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/Probability/Distributions/Cauchy/Basic.lean), `TauCeti.Probability.charFun_cauchyMeasure`), so the exponential covariance \(e^{-\alpha|x|}\), the Matérn case \(\nu=1/2\), is a characteristic function on \(\mathbb R\) with Cauchy spectral measure; the Gaussian covariance is likewise the characteristic function of a Gaussian law. The general Matérn family, the moment criterion for mean-square differentiability, and conditionally negative definite functions are absent.

**Synopsis entries.** Partly covered: 106.24 (Bochner's theorem on \(\mathbb R^d\) as a statement about continuous positive-definite functions; the random-field interpretation, the differentiability criterion, and the Matérn family beyond the exponential case on \(\mathbb R\) are absent). Not covered: 106.25.

### Likelihood and second-order structure of point patterns

[Mathematical scope](SYNOPSIS106.md#likelihood-and-second-order-structure-of-point-patterns).

Neither library defines point processes, product densities, Palm distributions, or Campbell's formula. The scalar Poisson law and the Radon–Nikodym derivative of measures (`Probability/Density.lean`) are the nearest supporting material.

**Synopsis entries.** Not covered: 106.26, 106.27.

<a id="structure-106b"></a>

## 106B. Survival Analysis, Sequential Analysis, and Extreme Values

The recorded material in this subdivision is distributional: the hazard representation of a survival function, laws of the maximum and minimum of independent variables, the Gumbel, Weibull, Pareto, and exponential laws, Doob's maximal inequality, and the binomial-to-Poisson limit. There is no counting-process, sequential-testing, or extreme-value limit theory.

### Survival analysis and counting processes

[Mathematical scope](SYNOPSIS106.md#survival-analysis-and-counting-processes).

#### Mathlib

Counting processes, compensators, predictable variation, and the Skorokhod space \(D[0,\tau]\) are not defined. The predictable \(\sigma\)-algebra, stopping times, and the local-property framework, which are the first layer of such a theory, are recorded in [CKMA Structure 08](../lean-CKMA/STRUCTURE08.md#continuous-time-martingales-and-quadratic-variation).

#### TauCeti

For a probability measure on \(\mathbb R\) with distribution function \(F\) and survival \(S=1-F\), if \(F\) is absolutely continuous on the interval between \(a\) and \(x\), \(S>0\) there, and \(F'=f\) almost everywhere, then \(S(x)=S(a)\exp\bigl(-\int_a^xf/S\bigr)\); for a law carried by \([0,\infty)\) that is absolutely continuous with respect to Lebesgue measure, \(S(x)=\exp(-\int_0^x\lambda)\) whenever \(S(x)>0\), with hazard \(\lambda=f/S\), and the cumulative hazard \(-\log S\) has derivative \(\lambda\) where \(F\) is differentiable ([hazard rates](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/Probability/Hazard.lean), `TauCeti.Probability.one_sub_cdf_eq_mul_exp_neg_integral`, `TauCeti.Probability.one_sub_cdf_eq_exp_neg_integral_rnDeriv`, `TauCeti.Probability.hasDerivAt_neg_log_one_sub_cdf`). This is supporting material: it identifies the estimand \(\Lambda\) of item 28 and the relation \(S=e^{-\Lambda}\) for continuous laws, but no estimator is defined.

**Synopsis entries.** Not covered: 106.28–106.30.

### Censoring likelihood and competing causes

[Mathematical scope](SYNOPSIS106.md#censoring-likelihood-and-competing-causes).

#### Mathlib

No material on right censoring or competing risks was found.

#### TauCeti

For an independent finite family of real random variables with laws \(\mu_i\), the minimum has distribution function \(1-\prod_i(1-F_i)\) and the maximum \(\prod_iF_i\) ([extremes of independent families](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/Probability/Distributions/Relations.lean), `TauCeti.Probability.cdf_min_indep`, `TauCeti.Probability.cdf_max_indep`); the minimum of independent exponential variables is exponential with the summed rate ([exponential laws](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/Probability/Distributions/Exponential/Basic.lean), `TauCeti.Probability.hasLaw_min_expMeasure_of_indepFun`, `TauCeti.Probability.hasLaw_min_iid_expMeasure`). The survival of \(\tilde T=\min(T,C)\) is therefore \(S_TS_C\) under independent censoring, but the joint law of \((\tilde T,\delta)\) is not computed. The hazard representation of the previous heading gives \(S=\exp(-\Lambda)\) for the all-cause hazard of an absolutely continuous failure time; with \(\Lambda=\sum_j\Lambda_j\) this is the first identity of item 33, but cause-specific hazards are not defined. TauCeti's file on censoring ([censoring](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/Probability/Distributions/Censoring.lean)) concerns projection of a variable onto an interval, which replaces tails by endpoint atoms; it is a different notion from random right censoring.

**Synopsis entries.** Partly covered: 106.33 (the identity \(S=e^{-\Lambda}\) for an absolutely continuous failure time and the law of a minimum of independent latent times, in TauCeti; cause-specific hazards, cumulative incidence, its estimator, and the non-identifiability statement are absent). Not covered: 106.31, 106.32.

### Counting-process martingales and regression for hazards

[Mathematical scope](SYNOPSIS106.md#counting-process-martingales-and-regression-for-hazards).

Neither library defines counting-process martingales, stochastic integrals against them, or the Doob–Meyer decomposition in continuous time ([CKMA Structure 08](../lean-CKMA/STRUCTURE08.md#stochastic-integration-and-itôs-formula)). Weak convergence in \(D[0,\tau]\) is absent.

**Synopsis entries.** Not covered: 106.34–106.36.

### Sequential analysis, change detection, and anytime-valid inference

[Mathematical scope](SYNOPSIS106.md#sequential-analysis-change-detection-and-anytime-valid-inference).

#### Mathlib

Doob's maximal inequality: for a nonnegative submartingale \((f_k)\) on a finite measure space and \(\varepsilon\ge0\), \(\varepsilon\,\mu\{\max_{k\le n}f_k\ge\varepsilon\}\le\int_{\{\max_{k\le n}f_k\ge\varepsilon\}}f_n\,d\mu\) (`maximal_ineq`, `Probability/Martingale/OptionalStopping.lean`). A nonnegative martingale is a nonnegative submartingale, so for a nonnegative martingale with \(\mathbb EM_0\le1\) this gives \(\mathbb P(\max_{k\le n}M_k\ge1/\alpha)\le\alpha\) for every \(n\), and Ville's bound for the supremum over all \(n\) follows by monotone continuity of measure; neither step is stated. The supermartingale form, which is what e-processes require, is not derived; for a supermartingale the inequality would follow from optional stopping at the bounded hitting time \(\min(n,\tau_{1/\alpha})\), which Mathlib provides for submartingales and so, by negation, for supermartingales (`Probability/Martingale/OptionalStopping.lean`, `Probability/Process/HittingTime.lean`). That a product of conditionally mean-at-most-one factors is a supermartingale is not stated. The Kullback–Leibler divergence `klDiv` (`InformationTheory/KullbackLeibler/Basic.lean`) supports the quantities \(\mathbb E_i\log(f_1/f_0)\). Sequential tests, Wald's identity, and the Brownian bridge are absent; Donsker's invariance principle is not proved ([CKMA Structure 06](../lean-CKMA/STRUCTURE06.md#functional-limits-and-empirical-distributions)).

#### TauCeti

No relevant declarations were found. TauCeti's martingale files concern reverse martingales and Lévy's downward theorem ([CKMA Structure 06](../lean-CKMA/STRUCTURE06.md#discrete-time-martingales)).

**Synopsis entries.** Partly covered: 106.38 (Doob's maximal inequality for nonnegative submartingales gives Ville's bound for nonnegative martingales on each finite horizon; the supermartingale case, the supremum over an infinite horizon, and the e-value consequences are not stated). Not covered: 106.37, 106.39, 106.40.

### Wald's identity, random sample sizes, and fixed-width intervals

[Mathematical scope](SYNOPSIS106.md#walds-identity-random-sample-sizes-and-fixed-width-intervals).

#### Mathlib

Optional sampling is available only for bounded stopping times ([CKMA Structure 06](../lean-CKMA/STRUCTURE06.md#discrete-time-martingales)), and Wald's identity is absent there. The moment- and cumulant-generating functions, with \(\mathop{\mathrm{mgf}}\) of an independent sum the product of the factors (`Probability/Moments/Basic.lean`), are the ingredients of Wald's fundamental identity. Random-index central limit theorems are absent.

#### TauCeti

Student's \(t\) law and the chi-squared law are constructed with their densities and distribution functions ([distributions](https://github.com/TauCetiProject/TauCeti/tree/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/Probability/Distributions)); these are the reference laws of Stein's two-stage procedure. The independence of the sample mean and sample variance of a normal sample was not found.

**Synopsis entries.** Not covered: 106.41–106.43.

### Optimal change detection

[Mathematical scope](SYNOPSIS106.md#optimal-change-detection).

No CUSUM, Shiryaev, or Shiryaev–Roberts material, and no optimal-stopping theory, was found in either library ([CKMA Structure 08](../lean-CKMA/STRUCTURE08.md#optimal-stopping)). The Kullback–Leibler divergence `klDiv` defines the constant \(I\) of item 44.

**Synopsis entries.** Not covered: 106.44, 106.45.

### Extreme-value statistics

[Mathematical scope](SYNOPSIS106.md#extreme-value-statistics).

#### Mathlib

The exponential and Pareto laws are constructed with their densities (`Probability/Distributions/Exponential.lean`, `Probability/Distributions/Pareto.lean`). Regular variation, domains of attraction, and the generalized extreme-value and generalized Pareto families are not defined.

#### TauCeti

The Gumbel law in the maximum convention, with location \(m\) and scale \(s>0\), is the law of \(m-s\log E\) for a rate-one exponential \(E\), with distribution function \(\exp(-e^{-(x-m)/s})\), quantile, moment-generating and characteristic functions ([Gumbel](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/Probability/Distributions/Gumbel/Basic.lean), `TauCeti.Probability.gumbelMeasure`, `TauCeti.Probability.cdf_gumbelMeasure_eq`; [transforms](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/Probability/Distributions/Gumbel/Transforms.lean)). This is \(G_0\) of item 46 as a law. The Weibull law ([Weibull](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/Probability/Distributions/Weibull/Basic.lean), `TauCeti.Probability.weibullMeasure`) and Pareto moments and distribution function ([Pareto](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/Probability/Distributions/Pareto/Basic.lean)) supply the other parametric families up to reparametrization; the Fréchet law and the generalized Pareto law \(H_{\gamma,\sigma}\) are not defined as such. The maximum of \(n\) i.i.d. variables has distribution function \(F^n\) (`TauCeti.Probability.cdf_max_iid`, above), and the \(k\)-th order statistic of an i.i.d. sample has a binomial-tail distribution function and is the quantile transform of a beta variable ([order statistics](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/Probability/Distributions/OrderStatistic.lean), `TauCeti.Probability.cdf_map_orderStatistic_pi`); this is supporting material for the Hill estimator, which is not defined.

**Synopsis entries.** Not covered: 106.46–106.49.

### Exceedances and block maxima

[Mathematical scope](SYNOPSIS106.md#exceedances-and-block-maxima).

#### Mathlib

If \(n\,a_n\to t\) for real \(a_n\), then \((1+a_n)^n\to e^t\) (`Real.tendsto_one_add_pow_exp_of_tendsto`, `Analysis/SpecialFunctions/Complex/LogBounds.lean`). The Poisson limit theorem: if \(np_n\to r\), then for each \(k\) the binomial probability \(\binom nkp_n^k(1-p_n)^{n-k}\) tends to \(e^{-r}r^k/k!\) (`tendsto_choose_mul_pow_of_tendsto_mul_atTop`, `Probability/Distributions/Poisson/PoissonLimitThm.lean`).

#### TauCeti

With \(\mathbb P(M_n\le u)=F(u)^n\) from `TauCeti.Probability.cdf_max_iid` and \(a_n=-(1-F(u_n))\), Mathlib's limit gives \(\mathbb P(M_n\le u_n)\to e^{-\tau}\) when \(n(1-F(u_n))\to\tau<\infty\), and the Poisson limit theorem gives the pointwise limit of the binomial law of the number of exceedances. Neither consequence is stated, and the converse, the case \(\tau=\infty\), and the existence criterion for the levels \(u_n\) are absent. No likelihood theory for the generalized extreme-value family is present.

**Synopsis entries.** Not covered: 106.50 (ingredients only: the finite-sample formula \(F(u_n)^n\) and the analytic and binomial–Poisson limits that give the forward direction for finite \(\tau\); the statement is not assembled, and the converse and the existence criterion are absent), 106.51.

## Missing from both libraries

**Stationary processes and spectral theory.** The basic objects are absent: a weakly stationary process, its autocovariance, spectral distribution, and spectral density. TauCeti's Herglotz theorem supplies the spectral measure of a positive-definite sequence, so items 106.14 and 106.16 begin from there; the realization of a positive-definite function as the autocovariance of a Gaussian process needs Kolmogorov extension on \(\mathbb Z\), which TauCeti proves for countable index sets ([CKMA Structure 06](../lean-CKMA/STRUCTURE06.md)), together with a Gaussian projective family indexed by \(\mathbb Z\). The Wold decomposition (106.2) is a Hilbert-space statement about the shift on the closed span of the process; orthogonal projection and Gram–Schmidt are in Mathlib, but the Wold decomposition of an isometry is not. Kolmogorov's formula (106.16) needs the Szegő infimum theorem, which is absent ([CKMA Structure 42](../lean-CKMA/STRUCTURE42.md)). The Durbin–Levinson recursion (106.15) is finite-dimensional linear algebra on Toeplitz Gram matrices and is close to the existing projection and Gram-matrix material.

**Asymptotics of time-series estimators.** Items 106.1, 106.3–106.6, 106.12, 106.17, and 106.19 all require central limit theorems for dependent data: the martingale central limit theorem, or the linear-process central limit theorem, neither of which is present. Mathlib's i.i.d. central limit theorem, Lévy continuity, and Cramér–Wold are the starting point; a Lindeberg-type theorem for triangular arrays is the first missing step, and the conditional version for martingale differences is a further substantial step. The Fisher-information statements (106.5, 106.17) need a theory of Fisher information, which neither library defines. GARCH stationarity (106.18) needs a strong law for stationary ergodic sequences, that is, the pointwise ergodic theorem, which is absent; TauCeti's mean ergodic theorem gives only \(L^2\) convergence ([CKMA Structure 10](../lean-CKMA/STRUCTURE10.md)). Mixing coefficients and the block bootstrap (106.11), long-memory asymptotics (106.9), and likelihood inference for diffusions (106.10, which needs stochastic integration and Girsanov's theorem, absent per [CKMA Structure 08](../lean-CKMA/STRUCTURE08.md)) are further away.

**Filtering and state-space models.** The Kalman recursion (106.7) and the innovations likelihood (106.13) are within reach: TauCeti's Gaussian conditioning theorem is the one-step update, and an induction over \(t\) with the Gaussian affine-image and independence results of Mathlib would give the full recursion and the factorization. The hidden-Markov forward recursion (106.8) is a finite computation from the TauCeti Markov-chain path law together with a conditionally independent emission kernel; it is one construction away.

**Spatial statistics and point processes.** Simple and universal kriging (106.20, 106.23) are finite-dimensional least-squares statements, close to the existing projection and Schur-complement material. Stein's theorem (106.21) needs equivalence of Gaussian measures (Feldman–Hájek), which is absent ([CKMA Structure 09](../lean-CKMA/STRUCTURE09.md)). The Matérn family needs the modified Bessel function \(\mathcal K_\nu\), absent from Mathlib, after which positive definiteness follows from TauCeti's Bochner theorem and a Fourier-transform computation. Valid semivariograms (106.25) need the Lévy–Khintchine-type representation of conditionally negative definite functions (Schoenberg), not present. Poisson point processes, their likelihoods, and second-order summaries (106.22, 106.26, 106.27) need a construction of Poisson random measures, which neither library has.

**Survival analysis and counting processes.** Items 106.28–106.36 need counting processes, continuous-time compensators and martingales, stochastic integrals with respect to them, and weak convergence in the Skorokhod space; none of these exists. The finite-sample algebra of the Kaplan–Meier, Nelson–Aalen, and log-rank statistics could be formalized independently, and the observed-data density of item 106.31 is an elementary computation from the joint law of \((T,C)\), starting from TauCeti's law of a minimum and its hazard representation; the limit theorems are far away.

**Sequential analysis.** Ville's inequality for nonnegative supermartingales (106.38) is one step from Mathlib's optional stopping and hitting times, and the confidence-sequence inversion (106.40) is then immediate. Wald's identity and the bounds of the sequential probability ratio test (106.37, 106.41) need optional stopping at unbounded stopping times with integrable sample size, which is absent. Anscombe's theorem (106.42) and the Chow–Robbins rule (106.43) need random-index limit theorems. The CUSUM bridge limit (106.39) needs Donsker's theorem. Optimality of CUSUM and of the Shiryaev procedures (106.44, 106.45) needs optimal-stopping theory, which is absent.

**Extreme values.** The forward direction of the Poisson approximation (106.50) is a short assembly of existing TauCeti and Mathlib lemmas. Regular variation, the Fisher–Tippett–Gnedenko classification (106.46), threshold excesses (106.47), and the Hill estimator (106.49) need a theory of regularly varying functions, which neither library has; the convergence-of-types lemma is also absent. The extremal index (106.48) needs mixing conditions for dependent sequences. Likelihood for block maxima (106.51) needs general maximum-likelihood asymptotics for a nonregular parametric family, not present.
