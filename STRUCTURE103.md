# Structure 103: Nonparametric and high-dimensional inference

Part of the [Mathlib and TauCeti coverage series](STRUCTURE.md).
[Mathematical inventory](SYNOPSIS103.md); [bibliographical scope](CKSD-bib.md#cks-103).

This file follows the thematic order and lettered subdivisions of the mathematical inventory. It records definitions, structures, and proved results, with supporting material identified separately. A topic heading locates the recorded statements; the **Synopsis entries** line at the end of each section states which numbered results are covered. The synopsis places a block of numbered entries at the head of each subdivision, before its first topic heading; these are treated in a section directly under the subdivision heading.

**Source baseline.** Mathlib `911003dd6dea5df215dff57f2717be762e11a6ca` and TauCeti `a049b4264d2cf4dbf4720796f844a3a3764914a5`, both of 2026-10-18, checked against local checkouts on 2026-11-01. See the [revision and source conventions](STRUCTURE.md#source-baseline-and-conventions).

**Mathlib source areas.** `Mathlib.Probability.Decision`, `Mathlib.MeasureTheory.Measure.TotalVariation`, `Mathlib.InformationTheory.KullbackLeibler`, `Mathlib.InformationTheory.Hamming`, `Mathlib.Topology.MetricSpace.CoveringNumbers`, `Mathlib.Probability.CentralLimitTheorem`, `Mathlib.Probability.CramerWold`, `Mathlib.Probability.Moments.CovarianceBilin`, `Mathlib.Probability.BrownianMotion`, `Mathlib.Probability.Distributions.Gaussian`, `Mathlib.Analysis.InnerProductSpace.Reproducing`, `Mathlib.Analysis.InnerProductSpace.Projection.Minimal`, `Mathlib.Analysis.Calculus.BumpFunction.Convolution`, `Mathlib.Analysis.Matrix`.

**Namespaces.** Risks of estimators are `ProbabilityTheory` (`avgRisk`, `bayesRisk`, `minimaxRisk`). The total variation distance is `MeasureTheory.tvDist`, and the Kullback–Leibler divergence is `InformationTheory.klDiv`. Reproducing-kernel Hilbert spaces are the class `RKHS`, with declarations in the namespace `RKHS`. Covering and packing numbers are `Metric.coveringNumber` and `Metric.packingNumber`; the Hamming distance is `hammingDist`. TauCeti declarations are mostly in `TauCeti` and `TauCeti.Probability`; its quantile function is `MeasureTheory.Measure.quantile`, and its matrix and operator results extend `Matrix`, `LinearMap.IsSymmetric`, `ContinuousLinearMap`, and `Submodule`.

<a id="structure-103a"></a>

## 103A. Ranks, Smoothing, Shape Constraints, Minimax Estimation, and Functional Data

Neither library defines empirical distribution functions as estimators, ranks of a sample, rank statistics, kernel density or regression estimators, smoothing splines, isotonic or log-concave estimators, or functional-data models. What is present is distributional infrastructure for real samples (order statistics, the probability integral transform, the binomial law of counts), the central limit theorem in dimension one, Brownian motion, approximate identities in \(L^p\), reproducing-kernel Hilbert spaces, the Hilbert projection theorem, and spectral theory of compact symmetric operators. The underlying probability is recorded in [CKMA Structure 06](../lean-CKMA/STRUCTURE06.md), and concentration, covering numbers, and VC dimension in [CKMA Structure 07](../lean-CKMA/STRUCTURE07.md).

[Mathematical scope](SYNOPSIS103.md#synopsis-103a).

#### Mathlib

**Limit theory and Brownian motion (supporting).** The central limit theorem is proved in dimension one: for independent identically distributed real variables with mean \(\mu\) and variance \(v\), \(n^{-1/2}\bigl(\sum_{k<n}X_k-n\mu\bigr)\) converges in distribution to \(N(0,v)\) (`ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub`, `Probability/CentralLimitTheorem.lean`). The Cramér–Wold theorem reduces convergence in distribution in a finite-dimensional real inner product space to that of all scalar projections (`tendstoInDistribution_iff_tendstoInDistribution_inner`, `Probability/CramerWold.lean`), but the multivariate central limit theorem is not stated. Pre-Brownian and Brownian motion on \([0,\infty)\) are defined through their finite-dimensional laws (`IsPreBrownianReal`, `IsBrownianReal`, `Probability/BrownianMotion/Basic.lean`; see [CKMA Structure 08](../lean-CKMA/STRUCTURE08.md)). The Brownian bridge, the Kolmogorov distribution, weak convergence in \(\ell^\infty\), and the empirical process are absent, so the limit laws of items 1, 11, and 17 have no formal counterpart.

**Convolution with shrinking kernels (supporting).** If \(g\) is locally integrable and \(\varphi_i\) are normalized smooth bump functions whose outer radii tend to zero with bounded ratio of outer to inner radius, then \(\varphi_i*g\to g\) almost everywhere (`ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable`, `Analysis/Calculus/BumpFunction/Convolution.lean`); at points of continuity the convergence is pointwise (`ContDiffBump.convolution_tendsto_right_of_continuous`). This is the deterministic bias part of kernel smoothing for smooth compactly supported kernels; the estimator \(\hat f_h\) and its variance are not formalized.

**Reproducing-kernel Hilbert spaces (supporting).** A reproducing-kernel Hilbert space is a Hilbert space with a continuous injection into functions on \(\mathcal X\), possibly vector-valued (`RKHS`, `Analysis/InnerProductSpace/Reproducing.lean`). The kernel functions \(k_x\) satisfy \(\langle f,k_xv\rangle=\langle f(x),v\rangle\) (`RKHS.inner_kerFun`), their span is dense (`RKHS.kerFun_dense`), the kernel is positive semidefinite (`RKHS.posSemidef_kernel`), and every positive semidefinite kernel arises from an RKHS (`RKHS.OfKernel`, `RKHS.kernel_ofKernel`; Moore's theorem). Sums of RKHSs are treated in `Analysis/InnerProductSpace/Reproducing/Operations.lean`. The representer theorem (item 8) is not stated. It follows from the reproducing property and the Hilbert projection theorem by projecting onto the span of \(k_{X_1},\ldots,k_{X_n}\), but no penalized empirical criterion is formalized.

**Projection onto convex sets (supporting).** In a real inner product space a nonempty complete convex set has a unique nearest point to every vector (`exists_norm_eq_iInf_of_complete_convex`), characterized by the variational inequality (`norm_eq_iInf_iff_real_inner_le_zero`, `Analysis/InnerProductSpace/Projection/Minimal.lean`). This gives existence and uniqueness of the projection \(P_K\) onto a closed convex cone, used in item 12, and of the isotonic projection of item 21; the face decomposition of polyhedral cones and the chi-bar-squared law are absent.

#### TauCeti

**Distribution-free transforms (supporting).** The probability integral transform is proved: for an atomless probability measure \(\nu\) on \(\mathbb R\), the distribution function pushes \(\nu\) to the uniform law on \([0,1]\) (`MeasureTheory.Measure.cdf_map_eq_volume_restrict`, [quantile](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/Probability/Quantile.lean)). Inverse transform sampling holds for every real probability law: the quantile function pushes the uniform law on \((0,1)\) to \(\mu\) (`MeasureTheory.Measure.map_quantile_volume_Ioo`). These are the facts behind the distribution-freeness assertions of items 1 and 17; the reduction of \(\sup_x|F_n(x)-F(x)|\) to the uniform case is not stated.

**Kernel mean embeddings (supporting).** For a real positive-definite kernel, the mean embedding \(\int\Phi\,d\mu\) into the feature space is defined; the squared distance between embeddings is the kernel energy of \(\mu-\nu\), and for a continuous universal kernel on a compact metrizable space the embedding is injective on finite Borel measures ([mean embedding](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/Analysis/PositiveDefinite/Kernel/MeanEmbedding.lean)). This is RKHS infrastructure, not the representer theorem.

**Approximate identities in \(L^p\) (supporting).** For \(1\le p<\infty\), Banach-valued \(f\in L^p\) of an additive Haar measure on a finite-dimensional real normed space, and normalized smooth bumps whose outer radii tend to zero, \(\|\varphi_i*f-f\|_p\to0\) (`TauCeti.tendsto_eLpNorm_normed_convolution_sub`, [approximate identity](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/MeasureTheory/Function/Lp/ApproximateIdentity.lean)). With \(p=1\) this is the bias half of the universal \(L^1\) consistency in item 5, for smooth bump kernels only; the stochastic half is absent.

**Synopsis entries.** Not covered: 103.1–103.13.

### Rank scores, rank correlation, and goodness of fit

[Mathematical scope](SYNOPSIS103.md#rank-scores-rank-correlation-and-goodness-of-fit).

#### Mathlib

No relevant declarations were found beyond the one-dimensional central limit theorem recorded above. Neither U-statistics, ranks, nor Fisher information for location are defined.

#### TauCeti

**Order statistics (supporting).** For independent real entries with a common law \(\mu\), the \(k\)th order statistic has distribution function equal to a binomial tail, equivalently a regularized incomplete beta function of \(F(t)\), atoms included (`TauCeti.Probability.cdf_map_orderStatistic_pi`, `TauCeti.Probability.cdf_map_orderStatistic_pi_eq_regularizedIncompleteBeta`). For unit uniform entries the \(k\)th order statistic (from \(0\)) has the beta law with parameters \(k+1\) and \(n-k\) (`TauCeti.Probability.map_orderStatistic_pi_uniformMeasure`), and every order statistic of an i.i.d. sample is the quantile function applied to a beta variable (`TauCeti.Probability.map_orderStatistic_pi_eq_map_betaMeasure_quantile`, [order statistics](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/Probability/Distributions/OrderStatistic.lean)). Thus the exact scores \(a_N(i)=\mathbb E\varphi(U_{N(i)})\) of item 14 are integrals against known beta laws; the scores themselves, rank statistics, and their moments are not formalized.

**Synopsis entries.** Not covered: 103.14–103.17.

### Exact ranks, smoothing bias, and shape constraints

[Mathematical scope](SYNOPSIS103.md#exact-ranks-smoothing-bias-and-shape-constraints).

#### Mathlib

Mathlib defines the binomial law (`Probability/Distributions/Binomial.lean`, `Probability/ProbabilityMassFunction/Binomial.lean`) and Hölder conditions (`HolderWith`, `HolderOnWith`), which are the ingredients of the Hölder classes \(\Sigma(\beta,L)\) of item 22; no estimation statement over these classes is present. The Hilbert projection theorem above gives existence and uniqueness of the weighted isotonic projection of item 21 once the weighted inner product and the monotone cone are set up; neither the max–min formula nor the greatest-convex-minorant description is stated.

#### TauCeti

**Binomial counts.** A finite sum of independent \(\{0,1\}\)-valued variables, each Bernoulli with the same success probability \(p\), has the binomial law with as many trials as summands (`TauCeti.Probability.iIndepFun.hasLaw_sum_bernoulli`), and under a product of copies of a probability measure \(\mu\) the number of coordinates in a measurable set \(s\) is binomial with success probability \(\mu(s)\) (`TauCeti.Probability.hasLaw_card_filter_mem_pi`, [binomial](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/Probability/Distributions/Binomial/Basic.lean)). Binomial tails are expressed as regularized incomplete beta values (`TauCeti.Probability.binomial_tail_eq_regularizedIncompleteBeta`, [binomial tails](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/Probability/Distributions/Binomial/Tail.lean)). Applied to the indicators \(1_{\{X_i>\theta_0\}}\), which are Bernoulli\((1/2)\) for an atomless law with median \(\theta_0\), this gives the null law of the sign statistic, without an identical-distribution assumption; the passage from the median hypothesis to the Bernoulli\((1/2)\) indicators and the size statement are not stated as such.

**Synopsis entries.** Not covered: 103.18 (ingredients only: the binomial law of a sum of independent Bernoulli\((1/2)\) indicators, TauCeti; the sign statistic and its size are not stated), 103.19–103.22.

### Bandwidth selection, linear smoothers, and density rates

[Mathematical scope](SYNOPSIS103.md#bandwidth-selection-linear-smoothers-and-density-rates).

#### Mathlib

No relevant declarations were found. Higher-order kernels, the cross-validation identities, local polynomial regression, natural cubic splines, and the value–second-derivative representation are absent. The Assouad lower bound of item 26 is not available (see item 46).

#### TauCeti

No relevant declarations were found beyond the approximate-identity convergence recorded for 103A.

**Synopsis entries.** Not covered: 103.23–103.26.

### Risk bounds under shape constraints

[Mathematical scope](SYNOPSIS103.md#risk-bounds-under-shape-constraints).

#### Mathlib

No relevant declarations were found. Log-concave densities, the Hellinger distance between densities, and the log-concave projection are not defined.

#### TauCeti

The Prékopa–Leindler and Brunn–Minkowski inequalities are proved ([Prékopa–Leindler](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/MeasureTheory/Integral/PrekopaLeindler.lean); see [CKMA Structure 07](../lean-CKMA/STRUCTURE07.md#product-spaces-entropy-and-geometric-concentration)). They are the standard route to stability of log-concavity under marginals and convolution, which is not derived, and they do not bear on the estimators of items 27 and 28.

**Synopsis entries.** Not covered: 103.27, 103.28.

### Functional data analysis

[Mathematical scope](SYNOPSIS103.md#functional-data-analysis).

#### Mathlib

**Covariance operators (supporting).** For a measure \(\mu\) on a real Hilbert space with \(\mathrm{id}\in L^2(\mu)\), the covariance bilinear form and the covariance operator \(C\) with \(\langle Cx,y\rangle=\mathop{\mathrm{Cov}}(\langle X,x\rangle,\langle X,y\rangle)\) are defined, and \(C\) is positive (`ProbabilityTheory.covarianceBilin`, `ProbabilityTheory.covarianceOperator`, `ProbabilityTheory.isPositive_covarianceOperator`, `Probability/Moments/CovarianceBilin.lean`). Compactness and the trace-class property of \(C\) are not proved. Gaussian measures on Banach spaces, with mean and covariance form, are recorded in [CKMA Structure 06](../lean-CKMA/STRUCTURE06.md#gaussian-laws-infinite-divisibility-and-exchangeability). No central limit theorem in infinite-dimensional Hilbert space is stated.

#### TauCeti

**Spectral decomposition (supporting).** A compact symmetric operator on a Hilbert space admits a Hilbert basis of eigenvectors, without separability, and for an injective one all eigenvalues of that basis are nonzero (`ContinuousLinearMap.exists_hilbertBasis_forall_hasEigenvector`, `ContinuousLinearMap.exists_hilbertBasis_forall_hasEigenvector_ne_zero`, [spectral decompositions](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/Analysis/InnerProductSpace/Spectrum.lean)). Combined with a compactness proof for the covariance operator this would give the eigen-expansion underlying the Karhunen–Loève expansion of item 29; the random series and its convergence are not stated.

**Ky Fan's inequality.** For a symmetric operator \(T\) on a finite-dimensional real or complex inner product space with eigenvalues \(\lambda_0\ge\lambda_1\ge\cdots\), and any orthonormal family \(w_1,\ldots,w_k\), \(\sum_i\mathop{\mathrm{re}}\langle Tw_i,w_i\rangle\le\lambda_0+\cdots+\lambda_{k-1}\) (`LinearMap.IsSymmetric.sum_re_inner_apply_self_le_sum_eigenvalues`, [Ky Fan](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/Analysis/InnerProductSpace/KyFan.lean)). Applied to \(T=C\), this is the finite-dimensional deterministic core of item 31, since \(\mathbb E\|X-\mu-P_V(X-\mu)\|^2=\mathop{\mathrm{tr}}C-\mathop{\mathrm{tr}}(P_VC)\). Attainment by the leading eigenvectors is immediate in finite dimension but not stated, and the uniqueness assertion and the Hilbert-space, trace-class case are absent. Courant–Fischer and Weyl's perturbation bound are in [Courant–Fischer](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/Analysis/InnerProductSpace/CourantFischer.lean); see [CKMA Structure 13](../lean-CKMA/STRUCTURE13.md).

**Synopsis entries.** Partly covered: 103.31 (finite-dimensional form of the inequality through Ky Fan's trace inequality, TauCeti; the expectation formulation, attainment, uniqueness, and the Hilbert-space case are not stated). Not covered: 103.29, 103.30.

### Functional linear regression

[Mathematical scope](SYNOPSIS103.md#functional-linear-regression).

#### Mathlib

No relevant declarations were found. Sobolev spaces on domains are defined in Mathlib (`Analysis/Distribution/Sobolev.lean`), but no regression model on \(L^2[0,1]\) is formalized.

#### TauCeti

No relevant declarations were found.

**Synopsis entries.** Not covered: 103.32.

<a id="structure-103b"></a>

## 103B. High-Dimensional and Large-Scale Inference

The decision-theoretic frame (risks, Bayes and minimax risk over Markov-kernel estimators), the total variation and Kullback–Leibler divergences, Pinsker's inequality, Hamming distance, covering and packing numbers, sub-Gaussian tail bounds, and an extensive body of matrix perturbation theory are present. No estimator of high-dimensional statistics (thresholding, the lasso, basis pursuit, nuclear-norm regression, thresholded covariance, neighbourhood selection, or the graphical lasso) is defined, and no multiple-testing procedure is formalized.

[Mathematical scope](SYNOPSIS103.md#synopsis-103b).

#### Mathlib

No declaration concerning the Gaussian sequence model, the lasso, penalized model selection, information criteria, false-discovery control, or sample-covariance eigenvalue asymptotics was found. Sub-Gaussian moment-generating bounds and the Gaussian tail estimate, which give the noise events of items 34 and 50 after a union bound, are in `Probability/Moments/SubGaussian.lean` ([CKMA Structure 07](../lean-CKMA/STRUCTURE07.md#exponential-moments-and-scalar-deviations)). The Marchenko–Pastur and Tracy–Widom laws are absent from both libraries ([CKMA Structure 07](../lean-CKMA/STRUCTURE07.md#spectral-laws-and-edges)).

#### TauCeti

**Gaussian quadratic forms (supporting).** The square of a standard Gaussian has the chi-squared law with one degree of freedom, and a finite sum of squares of independent standard Gaussians has the chi-squared law with as many degrees of freedom as summands (`TauCeti.Probability.gaussianReal_map_sq`, `TauCeti.Probability.iIndepFun.hasLaw_sum_sq_gaussian`, [Gaussian squares](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/Probability/Distributions/Gaussian/ChiSquared.lean)). Moment-generating functions of Gaussian quadratic forms are computed ([quadratic forms](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/Probability/Distributions/Gaussian/QuadraticForm.lean)). The law of \(\|P_S\xi\|^2\) for a projection \(P_S\) onto a \(k\)-dimensional subspace, which gives both the optimism identity and the overfitting probability of item 36, is not stated.

**Sample second moments and entrywise bounds (supporting).** The empirical second-moment matrix of a finite sample is defined and shown Hermitian and positive semidefinite ([sample second moment](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/Analysis/Matrix/SampleSecondMoment.lean)); Chebyshev-type entrywise deviation bounds are transferred to eigenvalues and operator norms with polynomial, not exponential, probability bounds ([matrix concentration](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/Probability/Moments/MatrixConcentration.lean)). The Wishart laws are exact laws of Gaussian Gram matrices ([Wishart](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/Probability/Distributions/Wishart/Basic.lean); see [CKMA Structure 06](../lean-CKMA/STRUCTURE06.md#gaussian-laws-infinite-divisibility-and-exchangeability)). None of this reaches the edge asymptotics of item 38.

**Synopsis entries.** Not covered: 103.33–103.38.

### Lower bounds, regularization, and multiplicity

[Mathematical scope](SYNOPSIS103.md#lower-bounds-regularization-and-multiplicity).

#### Mathlib

**Risk and minimax risk (supporting).** For a data-generating Markov kernel \(P\) from parameters to data and a loss \(\ell:\Theta\times\mathcal Y\to[0,\infty]\), the average risk of a Markov-kernel estimator, the Bayes risk for a prior, and the minimax risk are defined (`ProbabilityTheory.avgRisk`, `ProbabilityTheory.bayesRisk`, `ProbabilityTheory.minimaxRisk`, `Probability/Decision/Risk/Defs.lean`). The Bayes risk for any prior is at most the minimax risk (`ProbabilityTheory.bayesRisk_le_minimaxRisk`, `ProbabilityTheory.iSup_bayesRisk_le_minimaxRisk`), and both risks can only increase when the data are passed through a further kernel or measurable map (`ProbabilityTheory.bayesRisk_le_bayesRisk_comp`, `ProbabilityTheory.minimaxRisk_le_minimaxRisk_comp`, `Probability/Decision/Risk/Basic.lean`). Bayes estimators as posterior argmins are in `Probability/Decision/BayesEstimator.lean`. The decision-theoretic material is described in [Structure 101](STRUCTURE101.md). The lower bound of a minimax risk by a prior on two points or on a finite separated set is the frame of items 39 and 40, but neither reduction to testing is stated.

**Total variation and divergence (supporting).** The total variation distance between finite measures is defined as the total mass of \(|\mu-\nu|\), so between probability measures it takes values in \([0,2]\), twice the synopsis convention \(\|P_0-P_1\|_{\mathrm{TV}}\); it is a metric, and equals \(\int|d\mu/d\nu-1|\,d\nu\) under absolute continuity (`MeasureTheory.tvDist`, `MeasureTheory.tvDist_triangle`, `MeasureTheory.tvDist_eq_integral_abs_rnDeriv_of_ac`, `MeasureTheory/Measure/TotalVariation/Defs.lean`, `MeasureTheory/Measure/TotalVariation/Basic.lean`). For a Hahn decomposition \(s\) of \(\mu-\nu\) the distance is computed on \(s\) and its complement (`MeasureTheory.IsHahnDecomposition.tvDist_eq`), which identifies the optimal test of two simple hypotheses; the identity \(\inf_\psi(P_0(\psi=1)+P_1(\psi=0))=1-\|P_0-P_1\|_{\mathrm{TV}}\) is not stated. The Kullback–Leibler divergence, Gibbs' inequality, the chain rule for compositions with kernels, and data processing are in `InformationTheory/KullbackLeibler/` ([CKMA Structure 06](../lean-CKMA/STRUCTURE06.md#large-deviation-principles)).

#### TauCeti

**Pinsker's inequality.** For probability measures on any measurable space, with natural logarithms and without absolute continuity, \(2(\mu(s)-\nu(s))^2\le\mathrm{KL}(\mu\|\nu)\) for every measurable \(s\), and \(|\mu-\nu|(\Omega)^2\le2\,\mathrm{KL}(\mu\|\nu)\), which is \(\|\mu-\nu\|_{\mathrm{TV}}\le\sqrt{\mathrm{KL}(\mu\|\nu)/2}\) in the synopsis convention (`TauCeti.two_mul_sq_measureReal_sub_le_klDiv`, `TauCeti.totalVariation_sq_le_two_mul_klDiv`, [Pinsker](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/InformationTheory/KullbackLeibler/Pinsker.lean)). The total variation here is that of the signed measure \(\mu-\nu\) (`SignedMeasure.totalVariation`), not Mathlib's `tvDist`; the two are not identified in the cited files.

**Tensorization.** For probability measures, \(\mathrm{KL}(\mu\otimes\mu'\|\nu\otimes\nu')=\mathrm{KL}(\mu\|\nu)+\mathrm{KL}(\mu'\|\nu')\) (`TauCeti.klDiv_prod_prod`, with the finite-measure form `TauCeti.klDiv_prod_prod_eq_add`, [chain rule](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/InformationTheory/KullbackLeibler/ChainRule.lean)). The \(n\)-fold identity \(D(Q_0^{\otimes n}\|Q_1^{\otimes n})=nD(Q_0\|Q_1)\) for `Measure.pi` follows by induction but is not stated. Convexity of the divergence in both arguments is in [convexity](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/InformationTheory/KullbackLeibler/Convex.lean). Mutual information, and hence Fano's inequality (item 40), is not defined in either library.

**Synopsis entries.** Not covered: 103.39 (ingredients only: the auxiliary facts of the item: Pinsker's inequality and two-factor tensorization of the divergence, TauCeti; the two-point lower bound itself is not stated), 103.40–103.44.

### Packings and hypercube lower bounds

[Mathematical scope](SYNOPSIS103.md#packings-and-hypercube-lower-bounds).

#### Mathlib

**Hamming distance and packing numbers (supporting).** The Hamming distance on finite products is defined with its metric structure (`hammingDist`, `InformationTheory/Hamming.lean`). Packing numbers of subsets of pseudo-metric spaces, the greatest cardinality of an \(\varepsilon\)-separated subset, and their comparison with covering numbers are in `Topology/MetricSpace/CoveringNumbers.lean` ([CKMA Structure 07](../lean-CKMA/STRUCTURE07.md#metric-entropy-gaussian-comparison-and-chaining)). The Varshamov–Gilbert bound is the statement that the packing number of \(\{0,1\}^m\) in Hamming distance at scale \(m/8\) is at least \(2^{m/8}\); it is not stated. Mathlib's `Combinatorics/SetFamily/DualVC.lean` contains an Assouad bound on the dual VC dimension, unrelated to Assouad's lemma of item 46.

#### TauCeti

The Hamming minimum distance of a code is developed for coding theory ([minimum distance](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/InformationTheory/Coding/MinimumDistance/Basic.lean), [Hamming support](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/InformationTheory/Hamming.lean)); no existence bound for codes of given minimum distance, such as Gilbert–Varshamov, is proved.

**Synopsis entries.** Not covered: 103.45–103.47.

### Exact and stable sparse recovery

[Mathematical scope](SYNOPSIS103.md#exact-and-stable-sparse-recovery).

#### Mathlib

No relevant declarations were found. The \(\ell^1\) norm on finite-dimensional spaces (`PiLp 1`), matrices, kernels of linear maps, and the Hilbert projection theorem are available, but restricted isometry constants, the restricted nullspace property, basis pursuit, and incoherence conditions are not defined.

#### TauCeti

No relevant declarations were found. The restricted isometry property for sub-Gaussian matrices is not covered ([CKMA Structure 07](../lean-CKMA/STRUCTURE07.md#matrix-concentration-and-high-dimensional-geometry)).

**Synopsis entries.** Not covered: 103.48–103.50.

### Low-rank and structured covariance estimation

[Mathematical scope](SYNOPSIS103.md#low-rank-and-structured-covariance-estimation).

#### Mathlib

Matrix norms, including the \(\ell^\infty\) operator norm and the Frobenius norm, are in `Analysis/Matrix/Normed.lean`; positive definite matrices, determinants, and Schur complements are in `Analysis/Matrix/PosDef.lean` and `LinearAlgebra/Matrix/SchurComplement.lean`. These are supporting; no trace regression, thresholding operator, or graphical-model estimator is defined.

#### TauCeti

**Norms (supporting).** Unitarily invariant seminorms, including Ky Fan, Schatten, and Frobenius norms, are developed for linear maps between finite-dimensional inner product spaces ([unitarily invariant seminorms](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/Analysis/InnerProductSpace/UnitarilyInvariantSeminorm/Basic.lean), [Schatten](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/Analysis/InnerProductSpace/UnitarilyInvariantSeminorm/Schatten.lean)); the nuclear norm is the Schatten \(1\)-norm. See [CKMA Structure 13](../lean-CKMA/STRUCTURE13.md). If every entry of an \(m\times n\) matrix has norm at most \(\varepsilon\), its Euclidean operator norm is at most \(\sqrt{mn}\,\varepsilon\) (`Matrix.norm_toEuclideanLin_le_of_entry_le`, [entrywise bound](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/Analysis/Matrix/EntrywiseOpNorm.lean)). This is a dimension-dependent bound; the sparsity-adapted bound \(\|M\|_{\mathrm{op}}\le\|M\|_{\max}\|A\|_{\mathrm{op}}\) for a matrix supported on the pattern \(A\), used in item 52, is not stated.

**Gaussian conditioning (supporting).** For a jointly Gaussian vector whose conditioning block has positive definite covariance, the conditional law of one block given the other is Gaussian with affine mean and Schur-complement covariance (`TauCeti.Probability.condDistrib_multivariateGaussian`, [Gaussian conditioning](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/Probability/Distributions/Gaussian/Conditional.lean)). The identification of the regression coefficients of one coordinate on the others with \(-\Theta_{jk}/\Theta_{jj}\), which underlies neighbourhood selection, is not stated.

**Synopsis entries.** Not covered: 103.51–103.53.

### Principal components in high dimensions

[Mathematical scope](SYNOPSIS103.md#principal-components-in-high-dimensions).

#### Mathlib

The spectral theorem for symmetric endomorphisms of finite-dimensional inner product spaces, with eigenvalues in decreasing order (`LinearMap.IsSymmetric.eigenvalues_antitone`, `Analysis/InnerProductSpace/Spectrum.lean`), and the Rayleigh-quotient characterization of extreme eigenvalues (`Analysis/InnerProductSpace/Rayleigh.lean`) are supporting.

#### TauCeti

**Davis–Kahan.** Let \(A,B\) be bounded operators on an inner product space, \(U\) invariant under \(A\), and \(W\) invariant under the symmetric \(B\). If \(\mathop{\mathrm{re}}\langle Au,u\rangle\ge(c+g)\|u\|^2\) on \(U\) and \(\mathop{\mathrm{re}}\langle Bw,w\rangle\le c\|w\|^2\) on \(W\), then \(g\|P_WP_U\|\le\|B-A\|\); no completeness or finite dimension is assumed (`Submodule.mul_norm_starProjection_comp_starProjection_le_norm_sub`, with the gap forms `Submodule.mul_directedProjectionGap_le_norm_sub` and `Submodule.mul_projectionGap_le_norm_sub`, [dimension-free sin Θ](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/Analysis/InnerProductSpace/Projection/SinTheta.lean)). Versions in every unitarily invariant seminorm, including a residual form \(\delta N(P_{U^\perp}X)\le N(AX-XM)\), are in [sin Θ](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/Analysis/InnerProductSpace/UnitarilyInvariantSeminorm/SinTheta/Basic.lean) and [corollaries](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/Analysis/InnerProductSpace/UnitarilyInvariantSeminorm/SinTheta/Corollaries.lean). Weyl's bound \(|\lambda_k(T)-\lambda_k(S)|\le\|T-S\|\) is `LinearMap.IsSymmetric.abs_eigenvalue_sub_eigenvalue_le_norm` ([Courant–Fischer](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/Analysis/InnerProductSpace/CourantFischer.lean)).

With \(A=\Sigma\), \(B=\Sigma+P\), \(U=\mathrm{span}\,\theta^*\), and \(W\) the span of the non-leading eigenvectors of \(\Sigma+P\), Weyl's bound gives the separation hypothesis with \(g=\nu-\|P\|_{\mathrm{op}}\), and the theorem bounds the sine of the angle between \(\hat\theta\) and \(\theta^*\) by \(\|P\|_{\mathrm{op}}/(\nu-\|P\|_{\mathrm{op}})\). This is a Davis–Kahan bound of the same type as the first part of item 54, with \(\|P\|_{\mathrm{op}}\) in place of the residual \(\|(I-\theta^*\theta^{*\top})P\theta^*\|_2\) and with the angle in place of \(\|\hat\theta-\theta^*\|_2\); that specialization, the uniqueness of the leading eigenvector, and the spiked-model probability bound are not stated. More detail is in [CKMA Structure 13](../lean-CKMA/STRUCTURE13.md).

**Synopsis entries.** Not covered: 103.54 (ingredients only: the operator-norm Davis–Kahan \(\sin\Theta\) theorem and Weyl's bound, TauCeti; the eigenvector bound in the stated residual form and the spiked-model bound are not stated), 103.55.

## Missing from both libraries

**Empirical processes and goodness of fit.** Items 1 and 17 need the empirical distribution function as an estimator, the Brownian bridge, weak convergence in \(\ell^\infty(\mathbb R)\), and Donsker's theorem; the Dvoretzky–Kiefer–Wolfowitz inequality also needs its own combinatorial proof. TauCeti's probability integral transform and Mathlib's Brownian motion are the starting points, but the functional limit theory is several layers away (see [CKMA Structure 06](../lean-CKMA/STRUCTURE06.md#functional-limits-and-empirical-distributions)).

**Rank methods.** Ranks of a sample, uniformity of the rank vector under exchangeability with no ties, linear rank statistics and their moments, U-statistics, and the Hájek projection are all absent. The uniformity of ranks is one step from the permutation invariance of product measures together with the atomlessness of the law (ties have probability zero); the moment formulas for \(T_N\), the Wilcoxon and Kendall null moments, and the exact sign-test size are then finite combinatorics. Asymptotic normality needs a central limit theorem for triangular arrays or for sampling without replacement, which is not present; Mathlib's central limit theorem is for i.i.d. real sums only. Locally most powerful rank tests and Pitman efficiencies (items 14, 15) need Fisher information for location and local asymptotic normality, which are absent ([Structure 102](STRUCTURE102.md)).

**Smoothing.** Kernel density and regression estimators, their bias–variance expansions, cross-validation, local polynomials, and smoothing splines are absent. The bias part of item 5 is available for smooth bump kernels (TauCeti's \(L^p\) approximate identity); the stochastic part needs an \(L^1\) or Vapnik–Chervonenkis-type uniform law for the empirical measure, also absent. The leave-one-out identity for linear smoothers in item 23 is an elementary matrix identity and is one step from Mathlib's matrix algebra. The representer theorem of item 8 is a short consequence of Mathlib's `RKHS` reproducing property and the Hilbert projection theorem; the natural-cubic-spline case needs Sobolev functions on an interval with the spline characterization, which is not present.

**Minimax rates and lower bounds.** Mathlib's `minimaxRisk` and `bayesRisk` provide the frame, and `tvDist`, `klDiv`, Pinsker (TauCeti), and product tensorization (TauCeti) provide the divergences. Le Cam's two-point bound (item 39) is a short argument from the Hahn-decomposition formula for `tvDist` once the test-affinity identity is stated, and the two total-variation conventions (Mathlib's `tvDist` and the signed-measure total variation in TauCeti's Pinsker theorem) are reconciled. Fano's method (item 40) needs mutual information and the data-processing form of Fano's inequality; Mathlib's divergence data processing is the starting point. The Varshamov–Gilbert bound (item 45) is a counting argument over Hamming balls, one step from Mathlib's `hammingDist` and `Metric.packingNumber` once the size of Hamming balls is bounded. Assouad's lemma (item 46) is a direct combination of two-point bounds over the hypercube. The rate theorems built on these (Pinsker's theorem, items 9, 13, 22, 26, 27, 28, 32, 33, 47) are further removed: they need the Gaussian sequence and white-noise models, Sobolev and Hölder ellipsoids, and explicit estimators, none of which is formalized.

**Sparse regression and recovery.** The lasso and its oracle inequalities (items 34, 41, 42, 50), basis pursuit (items 48, 49), and debiasing (item 43) need definitions of the estimators as convex minimizers on \(\mathbb R^p\) and the deterministic cone arguments. These deterministic parts are finite-dimensional convex analysis and linear algebra, not far from existing infrastructure (subdifferentials in TauCeti, [CKMA Structure 12](../lean-CKMA/STRUCTURE12.md)). The probabilistic parts need maxima of sub-Gaussian variables (one union bound from Mathlib's sub-Gaussian tail) and the restricted isometry property of random matrices, which requires covering arguments not present ([CKMA Structure 07](../lean-CKMA/STRUCTURE07.md)).

**Model selection and multiple testing.** Penalized model selection (items 35, 47) needs Gaussian concentration for projections onto many subspaces. AIC and BIC (item 36) need the chi-squared law of \(\|P_S\xi\|^2\), which is one step from TauCeti's chi-squared law of a sum of squares by rotation invariance of the standard Gaussian. The Benjamini–Hochberg and Benjamini–Yekutieli theorems (items 37, 44) are finite combinatorial–probabilistic arguments on \(p\)-values; no \(p\)-value or multiple-testing notion is defined in either library.

**Covariance, graphs, and random matrices.** Thresholded covariance estimation (item 52) needs a sparsity-adapted operator-norm bound (a Schur-test or Gershgorin-type estimate) and entrywise sub-exponential concentration of \(\hat\Sigma\); TauCeti has only polynomial entrywise bounds. Nuclear-norm trace regression (item 51) and the graphical-model results (item 53) need the corresponding estimators and restricted strong convexity, and are far from existing material. The spiked-covariance, Marchenko–Pastur, and Tracy–Widom results (items 38, 55) need asymptotic random-matrix theory, absent from both libraries.

**Functional data.** Compactness and trace-class property of Mathlib's `covarianceOperator` would combine with TauCeti's eigenbasis theorem to give the deterministic eigen-expansion of item 29; the Karhunen–Loève series, a Hilbert-space central limit theorem, perturbation expansions for empirical eigenfunctions (item 30), and functional linear regression (item 32) are absent. TauCeti's Davis–Kahan theorem is the natural starting point for the \(O_P(n^{-1/2})\) eigenfunction bound.
