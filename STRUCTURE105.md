# Structure 105: Linear models, multivariate analysis, experimental design, and causal inference

Part of the [Mathlib, TauCeti, and Statlib coverage series](STRUCTURE.md).
[Mathematical inventory](SYNOPSIS105.md); [bibliographical scope](CKSD-bib.md#cks-105).

This file follows the thematic order and lettered subdivisions of the mathematical inventory. It records definitions, structures, and proved results, with supporting material identified separately. A topic heading locates the recorded statements; the **Synopsis entries** line at the end of each section states which numbered results are covered.

**Source baseline.** Mathlib `6135ffb78e8bcd3fcc8ec02f3f82ea0b0737358b` of 2026-11-05, TauCeti `afa08a3ed16fb167e35de371afb1eb03fbc5913a` of 2026-11-06, and Statlib `eeaac0283690efaa60c31115400cf561836baeb9` of 2026-11-05, checked against local checkouts on 2026-11-06. See the [revision and source conventions](STRUCTURE.md#source-baseline-and-conventions).

**Mathlib source areas.** `Mathlib.Probability.Distributions.Gaussian`, `Mathlib.Probability.Moments` (covariance, moment- and cumulant-generating functions, tilting), `Mathlib.Probability.Independence.Conditional`, `Mathlib.Probability.Kernel` (conditional distributions, posterior), `Mathlib.Probability.Decision`, `Mathlib.Probability.CentralLimitTheorem`, `Mathlib.Probability.CramerWold`, `Mathlib.MeasureTheory.Function.ConvergenceInDistribution`, `Mathlib.Analysis.InnerProductSpace.Projection`, `Mathlib.Analysis.InnerProductSpace.SingularValues`, `Mathlib.Analysis.Matrix`, `Mathlib.LinearAlgebra.Matrix` (positive definiteness, Schur complements, rank, Woodbury), `Mathlib.LinearAlgebra.Trace`, `Mathlib.Combinatorics.Configuration`, `Mathlib.Combinatorics.SimpleGraph.LapMatrix`, `Mathlib.RingTheory.Polynomial.ShiftedLegendre`, `Mathlib.Analysis.SpecialFunctions.Artanh`.

**Namespaces.** `ProbabilityTheory` for Gaussian laws, covariance, conditional independence (`CondIndepFun`), conditional distributions (`condDistrib`), posterior kernels, and Bayes risk; `MeasureTheory` for convergence in distribution; `Matrix` and `Matrix.PosDef` for matrix algebra; `Submodule` for orthogonal projections (`Submodule.starProjection`); `Configuration` for incidence geometries; `SimpleGraph` for graphs and Laplacians. TauCeti declarations for distributions are in `TauCeti.Probability`; its spectral and matrix results extend `LinearMap`, `LinearMap.IsSymmetric`, `LinearMap.IsPositive`, `ContinuousLinearMap`, `Submodule`, and `Matrix`, and its Gaussian projection laws also extend `ProbabilityTheory.HasLaw`. The Statlib declarations cited here are the potential-response notation `PotentialResponse`, at the root namespace, and the binary Bayes test in `ProbabilityTheory`.

The section is statistical in a sense that none of the three libraries yet addresses. No linear model, least-squares estimator, analysis-of-variance decomposition, generalised linear model, design, assignment mechanism, or directed graphical model is defined in any of them; Statlib supplies only a notation for potential responses. What is present is distributional and linear-algebraic infrastructure: Gaussian laws with their affine images and projection laws, central and noncentral chi-squared and Fisher \(F\) laws, Student \(t\), Beta, Wishart and von Mises–Fisher laws, orthogonal projections, Schur complements, and variational eigenvalue theory. The entries below record that infrastructure under the headings where it would be used.

<a id="structure-105a"></a>

## 105A. Regression, Multivariate Analysis, and Graphical Models

The linear and generalised linear model, quadratic forms and the analysis of variance, the Wishart law and classical multivariate tests, and undirected graphical models are grouped here. The Gaussian, chi-squared and Wishart distribution theory described in [CKMA Structure 06](../lean-CKMA/STRUCTURE06.md) and the matrix analysis of [CKMA Structure 13](../lean-CKMA/STRUCTURE13.md) are the principal supporting material; TauCeti statements are cited here at the later revision recorded above.

### Regression, generalised linear models, and mixtures

[Mathematical scope](SYNOPSIS105.md#regression-generalised-linear-models-and-mixtures).

#### Mathlib

No linear model, least-squares estimator, or exponential dispersion family is defined. The following is supporting material.

**Projections.** For a complete subspace \(K\) of an inner product space, the orthogonal projection \(P_K\) (`Submodule.starProjection`) is the nearest-point map: \(\|y-P_Ky\|\) is the distance from \(y\) to \(K\) (`Submodule.starProjection_minimal`), and \(y-P_Ky\) is characterized by orthogonality to \(K\) (`Submodule.norm_eq_iInf_iff_real_inner_eq_zero`, `Analysis/InnerProductSpace/Projection/Minimal.lean`, `Analysis/InnerProductSpace/Projection/Basic.lean`). The projection is idempotent and self-adjoint (`Submodule.isIdempotentElem_starProjection`). This is the geometric content of least squares onto the column space of a design; the identification of the fitted values \(X\hat\beta\) with \(PY\), and the normal equations, are not stated.

**Exponential families.** For a real random variable \(X\) and \(t\) in the interior of the set where \(e^{tX}\) is integrable, the mean and variance of \(X\) under the exponentially tilted measure \(\mu.\mathrm{tilted}(tX)\) are the first and second derivatives of the cumulant-generating function at \(t\) (`ProbabilityTheory.integral_tilted_mul_self`, `ProbabilityTheory.variance_tilted_mul`, `Probability/Moments/Tilted.lean`), and the moment- and cumulant-generating functions are analytic there (`Probability/Moments/MGFAnalytic.lean`). With \(b\) the cumulant-generating function of the dominating measure, this is \(\mathbb EY=b'(\theta)\) and \(\mathop{\mathrm{Var}}Y=b''(\theta)\) for the one-parameter natural exponential family with \(a(\varphi)=1\); the dispersion parameter, link functions, and the regression structure are absent.

**Limit theory.** The scalar central limit theorem for i.i.d. square-integrable summands (`ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub`, `Probability/CentralLimitTheorem.lean`), the Cramér–Wold reduction of convergence in distribution in a finite-dimensional inner product space to its scalar projections (`tendstoInDistribution_iff_tendstoInDistribution_inner`, `Probability/CramerWold.lean`), the continuous mapping theorem and Slutsky's theorem (`TendstoInDistribution.continuous_comp`, `TendstoInDistribution.prodMk_of_tendstoInMeasure_const`, `MeasureTheory/Function/ConvergenceInDistribution.lean`) are the ingredients from which the asymptotic normality statements of items 3–5 would be assembled, together with the M-estimation theory of [SYNOPSIS102](SYNOPSIS102.md). They are recorded in [CKMA Structure 06](../lean-CKMA/STRUCTURE06.md).

#### TauCeti

The real Gaussian square is chi-squared on one degree of freedom, and the sum of squares of the coordinates of a product of \(N(0,v)\) laws on a finite index set is \(v\) times the chi-squared law on that many degrees of freedom (`TauCeti.Probability.gaussianReal_map_sq`, `TauCeti.Probability.map_sum_sq_pi_gaussianReal`, [Gaussian squares](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Probability/Distributions/Gaussian/ChiSquared.lean)).

**Gaussian projections.** For a standard Gaussian vector \(Y\) on a finite-dimensional real inner product space and a subspace \(K\), the squared length \(\|P_KY\|^2\) has the chi-squared law on \(\dim K\) degrees of freedom; the projections onto pairwise orthogonal subspaces are jointly independent, and their squared lengths have the product of the chi-squared laws with the respective dimensions (`Submodule.map_norm_sq_starProjection_stdGaussian`, `TauCeti.Probability.iIndepFun_norm_sq_orthogonalProjectionOnto_stdGaussian`, `TauCeti.Probability.map_norm_sq_orthogonalProjectionOnto_stdGaussian_pi`, with the random-variable forms `ProbabilityTheory.HasLaw.norm_sq_orthogonalProjectionOnto_stdGaussian` and `ProbabilityTheory.HasLaw.pi_norm_sq_orthogonalProjectionOnto_stdGaussian`, [Gaussian projections](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Probability/Distributions/Gaussian/Projection.lean)). With \(K\) the column space of \(X\) and its orthogonal complement, this is item 2 for \(\mu=0\) and \(\sigma=1\): \(\|PY\|^2\sim\chi^2_r\), independent of \(\|(I-P)Y\|^2\sim\chi^2_{n-r}\). The noncentral case and the law of the least-squares estimator are not stated.

**Noncentral chi-squared law.** The noncentral chi-squared law of real degree \(k\ge0\) and noncentrality \(\lambda\ge0\) is defined as the Poisson\((\lambda/2)\) mixture of the chi-squared laws on \(k+2j\) degrees of freedom, with its density through the modified Bessel function \(I_\nu\), distribution function, moments, moment-generating function, additivity under convolution, and stochastic monotonicity in both parameters (`TauCeti.Probability.noncentralChiSquaredMeasure`, [noncentral chi-squared](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Probability/Distributions/NoncentralChiSquared/Basic.lean); `TauCeti.Probability.noncentralChiSquaredPDFReal_eq_besselI`, [density](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Probability/Distributions/NoncentralChiSquared/PDF.lean); `TauCeti.Probability.cdf_noncentralChiSquaredMeasure_le`, [stochastic order](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Probability/Distributions/NoncentralChiSquared/StochasticOrder.lean)). The squared norm of an \(N_n(m,I_n)\) vector has the noncentral chi-squared law on \(n\) degrees of freedom with noncentrality \(\|m\|^2\) (`TauCeti.Probability.map_norm_sq_multivariateGaussian_noncentral`, [Gaussian form](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Probability/Distributions/NoncentralChiSquared/Gaussian.lean)); its projected form \(\|PY\|^2/\sigma^2\) with noncentrality \(\|P\mu\|^2/\sigma^2\) is not stated. The modified Bessel function \(I_\nu\) of the first kind is defined with its series and derivative formula (`Real.besselI`, `Real.hasDerivAt_besselI`, [Bessel I](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Analysis/SpecialFunctions/BesselI.lean)).

Finite multivariate Gaussian mixtures have laws, densities and moment formulas (`TauCeti.Probability.multivariateGaussianMixtureMeasure`, `TauCeti.Probability.multivariateGaussianMixturePDFReal`, [Gaussian mixtures](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Probability/Distributions/Gaussian/Mixture/Multivariate.lean)). Identifiability and unboundedness of the unconstrained likelihood in item 6 are not stated. A mixture with one atom also has its distribution function, moments and transforms computed ([atom mixtures](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Probability/Distributions/AtomMixture.lean)). The quantile function of a real law, its Galois characterization, and inverse transform sampling are proved ([quantile](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Probability/Quantile.lean)); the check-function characterization of quantiles and quantile regression are absent.

#### Statlib

No relevant declarations were found.

**Synopsis entries.** Partly covered: 105.2 (the case \(\mu=0\), \(\sigma=1\): \(\|PY\|^2\) and \(\|(I-P)Y\|^2\) are independent chi-squared variables on \(r\) and \(n-r\) degrees of freedom, through TauCeti's Gaussian projection laws; the noncentral law for general \(\mu\), the scaling by \(\sigma^2\), and the law of the least-squares estimator are not stated). Not covered: 105.1, 105.3–105.7.

### Linear-model reductions and diagnostics

[Mathematical scope](SYNOPSIS105.md#linear-model-reductions-and-diagnostics).

#### Mathlib

Supporting matrix algebra only. The Woodbury identity \((A+UCV)^{-1}=A^{-1}-A^{-1}U(C^{-1}+VA^{-1}U)^{-1}VA^{-1}\), under invertibility of \(A\), \(C\) and \(C^{-1}+VA^{-1}U\), is proved (`Matrix.add_mul_mul_inv_eq_sub`, `LinearAlgebra/Matrix/NonsingularInverse.lean`; the `⅟` version in `LinearAlgebra/Matrix/Invertible.lean`). Its rank-one case is the Sherman–Morrison formula behind the deletion identities of item 11; the deletion formulas themselves are not stated. Block determinant and inverse formulas through the Schur complement, and positive (semi)definiteness of a block matrix in terms of the Schur complement (`Matrix.det_fromBlocks₁₁`, `LinearAlgebra/Matrix/SchurComplement.lean`; `Matrix.PosDef.fromBlocks₁₁`, `LinearAlgebra/Matrix/PosDef.lean`), are the algebra of partial regression (item 9). The rank of \(A^{\mathsf T}A\) equals that of \(A\) over a linearly ordered field (`Matrix.rank_transpose_mul_self`, `LinearAlgebra/Matrix/Rank.lean`), which gives invertibility of \(X^{\mathsf T}X\) under full column rank.

The trace of a projection onto a free submodule \(p\) along a free complement is the rank of \(p\) (`LinearMap.IsProj.trace`, `LinearAlgebra/Trace.lean`); applied to the hat matrix it gives \(\sum_ih_i=\mathop{\mathrm{tr}}H=p\).

#### TauCeti

The trace of any idempotent endomorphism of a finite free module over a local ring is the rank of its range (`LinearMap.trace_eq_finrank_range_of_isIdempotentElem`, [idempotent trace](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/LinearAlgebra/Trace/Idempotent.lean)), which removes the need to exhibit the complement.

For a multivariate Gaussian vector with positive-semidefinite covariance, the regular conditional law of one block given the other is Gaussian with mean \(m_1+S_{12}S_{22}^{+}(x_2-m_2)\) and generalized Schur-complement covariance \(S_{11}-S_{12}S_{22}^{+}S_{21}\), where \(S_{22}^{+}\) is the Moore–Penrose pseudoinverse of the observed block (`TauCeti.Probability.condDistrib_multivariateGaussian`, with `EuclideanSpace.gaussianCondMean` and `Matrix.gaussianCondCov`, [Gaussian conditioning](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Probability/Distributions/Gaussian/Conditional/Basic.lean); `Matrix.covariancePseudoInverse`, [pseudoinverse](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Analysis/Matrix/CovariancePseudoInverse.lean)). When \(S_{22}\) is positive definite, the pseudoinverse is \(S_{22}^{-1}\) and the parameters take their classical form (`EuclideanSpace.gaussianCondMean_of_posDef`, `Matrix.gaussianCondCov_of_posDef`). A centred Gaussian vector is carried by a rectangular linear map to the Gaussian of covariance \(MSM^{\mathsf T}\) (`TauCeti.Probability.map_affine_multivariateGaussian`, [affine images](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Probability/Distributions/Gaussian/Affine.lean)). In the mixed model of item 14, with \(\beta\) known and \((u,\varepsilon)\) jointly Gaussian, \((u,Y)\) is the image of \((u,\varepsilon)\) under a linear map with \(\mathop{\mathrm{Cov}}(u,Y)=GZ^{\mathsf T}\) and \(\mathop{\mathrm{Cov}}Y=V\); the conditioning theorem then gives the conditional law of \(u\) given \(Y\), whose mean is \(GZ^{\mathsf T}V^{-1}(Y-X\beta)\). The translation between `condDistrib` and conditional expectation is Mathlib's.

#### Statlib

No relevant declarations were found.

**Synopsis entries.** Partly covered: 105.14 (the Gaussian conditional-mean identity, with \(\beta\) known, through TauCeti's Gaussian conditioning and affine-image theorems; the best-linear-unbiased-prediction property with \(\hat\beta_V\) substituted is not stated). Not covered: 105.8–105.13.

### Quadratic forms and the analysis of variance

[Mathematical scope](SYNOPSIS105.md#quadratic-forms-and-the-analysis-of-variance).

#### Mathlib

Supporting material only. Two random variables with a jointly Gaussian law and zero covariance are independent, and the same holds for jointly Gaussian families with vanishing cross-covariances (`HasGaussianLaw.indepFun_of_covariance_eq_zero`, `HasGaussianLaw.iIndepFun_of_covariance_eq_zero`, `Probability/Distributions/Gaussian/HasGaussianLaw/Independence.lean`). For \(Y\sim N_n(\mu,\sigma^2I)\) and orthogonal projections \(P_1,\dots,P_k\) with mutually orthogonal ranges, the vectors \(P_iY\) are jointly Gaussian with vanishing cross-covariances, so this is the independence half of items 2, 10 and 17 once that Gaussian computation is supplied. The multivariate Gaussian law with given mean and positive-semidefinite covariance matrix is `ProbabilityTheory.multivariateGaussian` (`Probability/Distributions/Gaussian/Multivariate.lean`). The orthogonal decomposition of a vector by mutually orthogonal subspaces, with Pythagoras' identity (`norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero`, `Analysis/InnerProductSpace/Basic.lean`), is the algebraic form of the sum-of-squares splitting in item 17.

#### TauCeti

**Gaussian quadratic forms.** For a centred multivariate Gaussian with matrix parameter \(S\) and a real symmetric matrix \(\Theta\), the quadratic statistic \(x\mapsto\langle x,\Theta x\rangle\) has a finite exponential moment of order \(t\) if and only if \(I-2t\,S^{1/2}\Theta S^{1/2}\) is positive definite, and there its moment-generating function is \(\det(I-2t\,\Theta S)^{-1/2}\) for positive-semidefinite \(S\) (`TauCeti.Probability.mem_integrableExpSet_inner_toEuclideanLin_multivariateGaussian_iff`, `TauCeti.Probability.mgf_inner_toEuclideanLin_multivariateGaussian`, [quadratic forms](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Probability/Distributions/Gaussian/QuadraticForm.lean)). The chi-squared law of \(k\) degrees of freedom, for real \(k\ge0\), is the Gamma law of shape \(k/2\) and rate \(1/2\), with its moment-generating function \((1-2t)^{-k/2}\) on \(t<1/2\) and additivity of the degrees of freedom under convolution (`TauCeti.Probability.chiSquaredMeasure`, `TauCeti.Probability.mgf_id_chiSquaredMeasure`, `TauCeti.Probability.chiSquaredMeasure_conv_chiSquaredMeasure`, [chi-squared](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Probability/Distributions/ChiSquared/Basic.lean)). When \(\Theta S\) is idempotent of rank \(r\), the first determinant equals \((1-2t)^{-r/2}\); with the analytic-continuation tools of `Probability/Moments/ComplexMGF.lean` in Mathlib, this is one step from the central case \(\mu=0\) of the first assertion of item 15. That step, the noncentral case, the Craig–Sakamoto criterion, and Cochran's theorem are not stated.

**Derived laws.** If \(Z\) is standard Gaussian and \(V\) is an independent chi-squared variable on \(\nu>0\) degrees of freedom, then \(Z/\sqrt{V/\nu}\) has the Student law \(t_\nu\); if \(X\) and \(Y\) are independent chi-squared variables on \(m,n>0\) degrees of freedom, then \((X/m)/(Y/n)\) has the Fisher law \(F_{m,n}\) (`TauCeti.Probability.hasLaw_studentT_of_gaussian_chiSquared`, [Student t](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Probability/Distributions/StudentT/ChiSquared.lean); `TauCeti.Probability.hasLaw_fisherSnedecor_of_chiSquared`, [Fisher F](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Probability/Distributions/FisherSnedecor/ChiSquared.lean)). These are the final steps of items 10, 11, 17 and 18 once the numerator and denominator have been identified as independent central chi-squared variables. The noncentral \(F\) law is defined, with density, distribution function, quantiles and moments, and a noncentral chi-squared variable divided by an independent central one, each over its degrees of freedom, has that law (`TauCeti.Probability.noncentralFMeasure`, `TauCeti.Probability.hasLaw_noncentralF_of_noncentralChiSquared`, [noncentral F](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Probability/Distributions/NoncentralF/Basic.lean)); the strict monotonicity of the power of the \(F\) test in the noncentrality is not stated.

**Independence of linear images.** For a multivariate Gaussian with positive-semidefinite covariance \(S\), the linear images \(AY\) and \(BY\) are independent if and only if \(ASB^{\mathsf T}=0\) (`TauCeti.Probability.indepFun_matrix_multivariateGaussian_iff`, [Gaussian independence](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Probability/Distributions/Gaussian/Independence.lean)). Together with the projection laws recorded under the first heading, this is supporting material for the independence part of item 15; the quadratic forms \(Y^{\mathsf T}AY\) themselves are not treated.

#### Statlib

No relevant declarations were found.

**Synopsis entries.** Not covered: 105.15 (ingredients only: the moment-generating function of a Gaussian quadratic form, the chi-squared laws of squared Gaussian projections, the noncentral chi-squared law of \(\|Y\|^2\) for identity covariance, and the independence criterion for linear images, in TauCeti; the laws of \(Y^{\mathsf T}AY\), Craig–Sakamoto and Cochran are not stated), 105.16–105.19.

### Fitting and assessing generalised linear models

[Mathematical scope](SYNOPSIS105.md#fitting-and-assessing-generalised-linear-models).

#### Mathlib

No relevant declarations were found. The logistic function is `Real.sigmoid` (`Analysis/SpecialFunctions/Sigmoid.lean`), with its monotonicity and range; Fisher scoring, iteratively reweighted least squares, and the deviance are not defined.

#### TauCeti

The logit is a right inverse of the sigmoid on \((0,1)\), and the derivative of the sigmoid is \(\sigma(1-\sigma)\) (`Real.sigmoid_log_div_one_sub`, `Real.sigmoid_mul_one_sub_sigmoid`, [logit](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Analysis/SpecialFunctions/Sigmoid.lean)). These are the variance weights of the logistic model in item 20; nothing further is present.

#### Statlib

No relevant declarations were found.

**Synopsis entries.** Not covered: 105.20, 105.21.

### Multivariate analysis, invariance, and graphical models

[Mathematical scope](SYNOPSIS105.md#multivariate-analysis-invariance-and-graphical-models).

#### Mathlib

Supporting material. Conditional independence of random variables given a third is `ProbabilityTheory.CondIndepFun`, with characterizations through conditional expectations of indicators of preimages (`ProbabilityTheory.condIndepFun_iff_condExp_inter_preimage_eq_mul`, `Probability/Independence/Conditional.lean`). Simple graphs, their cliques, and connectivity are developed in `Combinatorics/SimpleGraph` (`SimpleGraph.IsClique`, `Combinatorics/SimpleGraph/Clique.lean`); no Markov property relative to a graph is defined. The posterior kernel of a Markov kernel and a prior, and the Bayes risk of an estimation problem, are defined; an argmin estimator of the posterior expected loss is a Bayes estimator (`ProbabilityTheory.posterior`, `Probability/Kernel/Posterior.lean`; `ProbabilityTheory.IsArgminEstimator.isBayesEstimator`, `Probability/Decision/BayesEstimator.lean`). Applied to \(0\)–\(1\) loss on two classes this gives the abstract Bayes classifier; its evaluation for Gaussian class laws in item 25 is not stated.

#### TauCeti

**Wishart law as a Gram law.** The Gaussian-Gram Wishart law `TauCeti.Probability.wishartGramMeasure ν S` is, by definition, the law on symmetric matrices of \(\sum_{r<\nu}X_rX_r^{\mathsf T}\) for \(\nu\) independent \(N_p(0,S)\) vectors, for every natural \(\nu\) and every matrix \(S\) (`TauCeti.Probability.hasLaw_wishartGram_gaussian`, [Wishart](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Probability/Distributions/Wishart/Basic.lean)). For \(S\) positive definite and \(\nu\ge p\) it coincides with the classical density law `TauCeti.Probability.nonsingularWishartMeasure` and is almost surely positive definite (`TauCeti.Probability.wishartGramMeasure_eq_nonsingularWishartMeasure`, `TauCeti.Probability.hasLaw_wishartGram_gaussian_nonsingularWishartMeasure`, `TauCeti.Probability.ae_posDef_wishartGramMeasure`, [agreement](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Probability/Distributions/Wishart/Agreement.lean)). Its mean is \(\nu S\) and its entrywise covariance is \(\nu(S_{ik}S_{jl}+S_{il}S_{jk})\) ([Wishart moments](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Probability/Distributions/Wishart/Moments.lean)). The independence of the sample mean and the sample covariance, the law \((n-1)S\sim W_p(n-1,\Sigma)\), and Hotelling's \(T^2\) are not stated.

**Multivariate Beta laws.** For independent Gamma variables of common rate, the ratio \(X/(X+Y)\) is Beta-distributed and independent of the sum (`TauCeti.Probability.map_div_add_prod_gammaMeasure`, [Gamma–Beta](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Probability/Distributions/Gamma/Beta.lean)). This is the univariate case of the Beta factors in Wilks's lambda; the matrix-variate Beta law and the product representation of item 23 are absent.

**Gaussian blocks.** For a multivariate Gaussian with positive-semidefinite covariance, two complementary coordinate blocks are independent if and only if the cross-covariance block vanishes (`TauCeti.Probability.indepFun_sumEquivProd_multivariateGaussian_iff`, [multivariate Gaussian](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Probability/Distributions/Gaussian/Multivariate.lean)). With the Gaussian conditioning theorem recorded above, this is the supporting material for the precision-matrix criterion of item 26, which is not stated. Weak union and related manipulations of Mathlib's conditional independence are proved (`TauCeti.Probability.condIndep_of_condIndep_of_le_of_le`, `TauCeti.Probability.iCondIndep_of_condIndep_compl`, [conditional independence](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Probability/Independence/Conditional.lean)); the intersection property for positive densities, on which the equivalence of the Markov properties rests, is not.

**Directional laws.** The von Mises–Fisher law on the unit sphere of a finite-dimensional real inner product space is defined as an exponential tilt of the uniform law, with natural parameter \(\eta=\kappa\mu\) (`TauCeti.Probability.vonMisesFisherMeasure`, [von Mises–Fisher](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Probability/Distributions/VonMisesFisher/Basic.lean)). In dimension \(d\ge2\) and for \(\kappa>0\) it has density \(\exp(\kappa\langle\mu,x\rangle)/(\Gamma(d/2)(\kappa/2)^{1-d/2}I_{d/2-1}(\kappa))\) with respect to the uniform law, and mean \((I_{d/2}(\kappa)/I_{d/2-1}(\kappa))\,\mu\) (`TauCeti.Probability.vonMisesFisherMeasure_eq_withDensity_besselI`, [normalizer](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Probability/Distributions/VonMisesFisher/Normalizer.lean); `TauCeti.Probability.integral_coe_vonMisesFisherMeasure`, [moments](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Probability/Distributions/VonMisesFisher/Moments.lean)). On the circle, the von Mises law with mean direction \(m\) and \(\kappa\ge0\) has trigonometric moments \(\mathbb E[e^{in\theta}]=e^{inm}I_{|n|}(\kappa)/I_0(\kappa)\) (`TauCeti.Probability.integral_fourier_vonMisesMeasure`, `TauCeti.Probability.norm_integral_fourier_one_vonMisesMeasure`, [von Mises](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Probability/Distributions/VonMises/Basic.lean)); for \(n=1\) this is \(\mathbb E[e^{i(\theta-m)}]=I_1(\kappa)/I_0(\kappa)\), equivalently \(\mathbb E\cos(\theta-m)=I_1(\kappa)/I_0(\kappa)\) and \(\mathbb E\sin(\theta-m)=0\). The likelihood of a sample, the maximum-likelihood estimator of the mean direction, and the likelihood equation for \(\kappa\) are not stated.

#### Statlib

Supporting material only. The Bayes test between two hypotheses in likelihood-ratio form (`ProbabilityTheory.binaryArgminEstimator`, [binary tests](https://github.com/stat-lib/statlib/blob/eeaac0283690efaa60c31115400cf561836baeb9/Statlib/Testing/Binary.lean)) is the abstract two-class Bayes rule; its evaluation for Gaussian class laws in item 25 is not stated.

**Synopsis entries.** Partly covered: 105.22 (the Gram sum of \(n\ge p\) independent \(N_p(0,\Sigma)\) vectors has the Wishart density law, TauCeti; the sampling theory of \(\bar X\) and \(S\) and Hotelling's \(T^2\) are absent), 105.27 (the circular moment \(\mathbb E\cos(X-\mu)=I_1(\kappa)/I_0(\kappa)\), in the equivalent complex form of TauCeti's first trigonometric moment of the von Mises law; the maximum-likelihood statements are absent). Not covered: 105.23–105.26.

### Covariance geometry and multivariate reduction

[Mathematical scope](SYNOPSIS105.md#covariance-geometry-and-multivariate-reduction).

#### Mathlib

Covariance of real random variables and the covariance bilinear form of a measure on a Hilbert space are defined (`Probability/Moments/Covariance.lean`, `Probability/Moments/CovarianceBilin.lean`). Singular values of a linear map between finite-dimensional inner product spaces are defined (`LinearMap.singularValues`, `Analysis/InnerProductSpace/SingularValues.lean`), and the spectral theorem for Hermitian matrices is `Matrix.IsHermitian.spectral_theorem` (`Analysis/Matrix/Spectrum.lean`). These are described in [CKMA Structure 13](../lean-CKMA/STRUCTURE13.md).

#### TauCeti

**Covariance matrices.** The matrix of coordinate covariances of a measure on a Euclidean space is `TauCeti.covMatrix`; it agrees with Mathlib's covariance bilinear form under a finite second moment and is then positive semidefinite (`TauCeti.covarianceBilin_eq_covMatrix`, `TauCeti.posSemidef_covMatrix`, [covariance](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Probability/Moments/Covariance.lean)), and it recovers the covariance parameter of a multivariate Gaussian (`TauCeti.Probability.covMatrix_multivariateGaussian`). A multivariate Gaussian with positive-definite covariance has the classical density \((2\pi)^{-d/2}(\det S)^{-1/2}\exp(-\tfrac12\langle x-m,S^{-1}(x-m)\rangle)\) (`TauCeti.Probability.multivariateGaussian_eq_withDensity`, [Gaussian density](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Probability/Distributions/Gaussian/Density.lean)). This is the likelihood of item 28; its maximization over mean and covariance is not stated.

**Principal components.** Ky Fan's trace inequality: for a symmetric \(T\) on an \(n\)-dimensional inner product space and an orthonormal family \((w_i)\) of \(k\) vectors, \(\sum_i\mathop{\mathrm{re}}\langle Tw_i,w_i\rangle\) is at most the sum of the \(k\) largest eigenvalues (`LinearMap.IsSymmetric.sum_re_inner_apply_self_le_sum_eigenvalues`, [Ky Fan](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Analysis/InnerProductSpace/KyFan.lean)). With \(P=\sum_iw_iw_i^{\mathsf T}\), the left side is \(\mathop{\mathrm{tr}}(P\Sigma)\), so captured variance over rank-\(k\) orthogonal projections is bounded by \(\lambda_1+\dots+\lambda_k\). For a positive operator the bound is attained: some orthonormal family of \(k\) vectors gives \(\sum_i\mathop{\mathrm{re}}\langle w_i,Aw_i\rangle\) equal to the sum of the \(k\) largest singular values, which for a covariance operator are its \(k\) largest eigenvalues (`LinearMap.IsPositive.exists_orthonormal_sum_re_inner_eq_kyFanSum`, with `LinearMap.kyFanSum`); the file does not identify the maximizing family with leading eigenvectors. The Courant–Fischer characterization is also proved (`LinearMap.IsSymmetric.eigenvalues_eq_iSup_iInf_re_inner`, [Courant–Fischer](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Analysis/InnerProductSpace/CourantFischer.lean)). The Eckart–Young theorem is proved in the operator-norm form: the distance from \(T\) to maps of rank at most \(n\) is the \(n\)th singular value (`ContinuousLinearMap.singularValue_eq_linearMap_singularValues`, [Eckart–Young](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Analysis/OperatorIdeal/ApproximationNumber/EckartYoung.lean)). The singular-value Hoffman–Wielandt inequality \(\sum_i(\sigma_i(A)-\sigma_i(B))^2\le\|A-B\|_F^2\) for linear maps between finite-dimensional spaces is proved (`LinearMap.sum_sq_singularValues_sub_le_sq_frobenius_apply_sub_min`, [Hoffman–Wielandt](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Analysis/InnerProductSpace/HoffmanWielandt/Singular.lean)); for \(B\) of rank at most \(k\) it gives the lower bound \(\sum_{i\ge k}\sigma_i(A)^2\) in the Frobenius form of item 30, but that specialization, its attainment by the truncated singular value decomposition, and the reconstruction-error identity \(\sum_{j>k}\lambda_j\) are not stated.

**Canonical correlations.** Principal cosines of two subspaces are defined as the singular values of \(P_VP_U\), and for the range of an isometry they are the singular values of the cosine embedding (`Submodule.principalCosines`, `Submodule.principalCosines_range_eq_singularValues`, [principal angles](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Analysis/InnerProductSpace/Projection/PrincipalAngle.lean)). Sample canonical correlations are the principal cosines between the two centred column spaces; the population statement of item 29 is not formulated. For a jointly Gaussian pair, independence is equivalent to vanishing of \(\Sigma_{UV}\) (the block criterion above), and with positive-definite \(\Sigma_{UU}\), \(\Sigma_{VV}\) this is vanishing of all singular values of \(\Sigma_{UU}^{-1/2}\Sigma_{UV}\Sigma_{VV}^{-1/2}\).

#### Statlib

No relevant declarations were found.

**Synopsis entries.** Partly covered: 105.29 (the Gaussian independence criterion in cross-covariance form, TauCeti; the variational characterization and invariance are absent), 105.30 (the maximum of \(\mathop{\mathrm{tr}}(P\Sigma)\) over rank-\(k\) projections is \(\lambda_1+\dots+\lambda_k\), as the Ky Fan bound with its attainment for positive operators, TauCeti; the identification of the maximizer with the leading eigenvectors, the reconstruction error, and the Frobenius-norm Eckart–Young theorem are not stated). Not covered: 105.28.

### Wishart structure and correlation coefficients

[Mathematical scope](SYNOPSIS105.md#wishart-structure-and-correlation-coefficients).

#### Mathlib

The inverse hyperbolic tangent is `Real.artanh` (`Analysis/SpecialFunctions/Artanh.lean`), and the delta-method ingredients are the continuous mapping and Slutsky theorems recorded under the first heading. No sample correlation coefficient is defined.

#### TauCeti

**Density.** The nonsingular Wishart law of real degree \(n>p-1\) and positive-definite scale \(S\) has density \((\det A)^{(n-p-1)/2}\exp(-\tfrac12\mathop{\mathrm{tr}}(S^{-1}A))/(2^{np/2}(\det S)^{n/2}\Gamma_p(n/2))\) on the positive-definite cone against the Lebesgue measure on symmetric matrices normalized on the coordinate unit cube (`TauCeti.Probability.nonsingularWishartMeasure`, [nonsingular Wishart](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Probability/Distributions/Wishart/Nonsingular.lean)); at a natural degree \(n\ge p\) it is the Gram law of \(n\) independent \(N_p(0,S)\) vectors (agreement theorem above). Below that degree, or for singular \(S\), the Gram law is singular with respect to that Lebesgue measure (`TauCeti.Probability.mutuallySingular_wishartGramMeasure_symmetricLebesgue`).

**Congruence and marginals.** For every \(q\times p\) matrix \(M\) and positive-semidefinite \(S\), congruence \(A\mapsto MAM^{\mathsf T}\) carries the Gram law of scale \(S\) to the Gram law of scale \(MSM^{\mathsf T}\) (`TauCeti.Probability.map_symmetricCongruenceLinearMap_wishartGramMeasure`). For the density law, a matrix \(M\) of full row rank carries scale \(S\) to \(MSM^{\mathsf T}\), and every principal submatrix of a Wishart matrix is Wishart of the same degree with the corresponding submatrix of the scale (`TauCeti.Probability.map_symmetricCongruenceLinearMap_nonsingularWishartMeasure`, `TauCeti.Probability.map_symmetricCongruenceLinearMap_submatrix_one_nonsingularWishartMeasure`, [marginals](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Probability/Distributions/Wishart/Marginal.lean)). Degrees add under convolution (`TauCeti.Probability.wishartGramMeasure_conv_wishartGramMeasure`).

**Bartlett decomposition.** For the standard nonsingular Wishart law of real degree \(n>p-1\) and its Cholesky factorization \(A=LL^{\mathsf T}\) with \(L\) lower triangular with positive diagonal, the on-or-below-diagonal entries of \(L\) are independent, \(L_{ii}^2\) is chi-squared on \(n-i\) degrees of freedom for \(i=0,\dots,p-1\), and the strictly lower entries are standard Gaussian (`TauCeti.Probability.bartlett_nonsingularWishartMeasure`, [Bartlett](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Probability/Distributions/Wishart/Bartlett.lean)). With \(T=L^{\mathsf T}\) and \(1\)-based indexing this is the decomposition of item 31, for real degree.

**Determinant and Schur complements.** For positive-definite \(S\) and real degree \(n>p-1\), \(\det W\) has the law of \(\det S\) times a product of independent chi-squared variables on \(n,n-1,\dots,n-p+1\) degrees of freedom (`TauCeti.Probability.map_det_nonsingularWishartMeasure`, `TauCeti.Probability.hasLaw_det_nonsingularWishartMeasure`, [determinant](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Probability/Distributions/Wishart/Determinant.lean)), with the real-power moments of \(\det W\). If \(W\) is Wishart of scale \(S^{-1}\), the reciprocal \(((W^{-1})_{ii})^{-1}\), which is the Schur complement in \(W\) of the principal block away from \(i\), is \((S_{ii})^{-1}\) times a chi-squared variable on \(n-p+1\) degrees of freedom (`TauCeti.Probability.map_inv_inv_apply_nonsingularWishartMeasure`, [inverse-Wishart marginals](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Probability/Distributions/Wishart/Inverse/Marginal.lean)). This is the case \(k=1\) of the Schur-complement law \(W_k(n-p+k,\Sigma_{11\cdot2})\); the case of general \(k\) and the independence of \(W_{11\cdot2}\) and \((W_{12},W_{22})\) are not stated.

The \(t_{N-2}\) law of the null correlation statistic in item 32 would follow from the Student construction recorded under the quadratic-forms heading once the conditional representation of \(r\) given one coordinate is established; it is not stated.

#### Statlib

No relevant declarations were found.

**Synopsis entries.** Partly covered: 105.31 (density, rectangular congruence, marginal \(W_{22}\), the Bartlett decomposition, the determinant law, and the Schur-complement law for a block of size one, TauCeti; the Schur-complement law for general \(k\) and its independence of \((W_{12},W_{22})\) are absent). Not covered: 105.32.

### Tests on covariance structure and multivariate hypotheses

[Mathematical scope](SYNOPSIS105.md#tests-on-covariance-structure-and-multivariate-hypotheses).

#### Mathlib

No relevant declarations were found. Likelihood-ratio statistics are not defined beyond the log-likelihood ratio of two measures (`MeasureTheory.llr`, `MeasureTheory/Measure/LogLikelihoodRatio.lean`), and no group-invariance theory for tests is present.

#### TauCeti

The Wishart characteristic function and the exact domain and value of the moment-generating function of trace statistics \(A\mapsto\mathop{\mathrm{tr}}(\Theta A)\) are proved ([transforms](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Probability/Distributions/Wishart/Transforms.lean), [characteristic function](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Probability/Distributions/Wishart/CharFun.lean)). They are supporting material for the moments of \(\det A\) and \(\mathop{\mathrm{tr}}A\) in the sphericity statistic; no test statistic of items 33–35 is formulated.

#### Statlib

No relevant declarations were found.

**Synopsis entries.** Not covered: 105.33–105.35.

### Decomposable graphical models

[Mathematical scope](SYNOPSIS105.md#decomposable-graphical-models).

#### Mathlib

No relevant declarations were found. Chordal graphs, perfect orderings of cliques, and separators are not defined.

#### TauCeti

Iterative proportional fitting is defined for measures on a product of two spaces, as alternating reweighting toward two prescribed marginals; each half-step is the relative-entropy projection onto measures with one prescribed marginal, with a Pythagorean identity (`MeasureTheory.Measure.fitLaw`, [I-projection](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/InformationTheory/KullbackLeibler/Projection.lean); `MeasureTheory.Measure.proportionalFitting`, [proportional fitting](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/MeasureTheory/OptimalTransport/ProportionalFitting.lean)). On finite spaces it is the Sinkhorn iteration, which converges for strictly positive data ([finite IPF](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/MeasureTheory/OptimalTransport/Finite/ProportionalFitting.lean)). This is the two-marginal discrete scheme; iterative proportional scaling of a Gaussian covariance over the cliques of a graph is not treated.

#### Statlib

No relevant declarations were found.

**Synopsis entries.** Not covered: 105.36.

<a id="structure-105b"></a>

## 105B. Experimental Design, Survey Sampling, and Causal Inference

Optimal and combinatorial design, finite-population survey sampling, randomization inference, potential-outcome identification and estimation, sensitivity analysis, and directed graphical causal models are grouped here. Apart from scattered combinatorial and convex-analytic ingredients and Statlib's notation for potential responses, none of this material is formalized in the three libraries; the conditional-independence and kernel infrastructure of Mathlib, recorded in [CKMA Structure 06](../lean-CKMA/STRUCTURE06.md), is the nearest support for the identification formulas.

### Experimental design

[Mathematical scope](SYNOPSIS105.md#experimental-design).

#### Mathlib

Supporting material only. The Laplacian matrix of a finite simple graph is defined, and the number of connected components equals the dimension of its kernel (`SimpleGraph.lapMatrix`, `SimpleGraph.card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix`, `Combinatorics/SimpleGraph/LapMatrix.lean`). The information matrix \(C=R-NK^{-1}N^{\mathsf T}\) of a block design is a weighted Laplacian of the treatment concurrence multigraph, so item 39 is the weighted analogue of this theorem; the weighted version and the block-design matrices are absent. The uniform probability on a finite set (`ProbabilityTheory.uniformOn`, `Probability/UniformOn.lean`) is the randomization distribution of a completely randomized assignment; no randomization test is formulated. Real Hadamard matrices are defined, with the Sylvester construction and the divisibility \(4\mid n\) (`Matrix.IsHadamard`, `LinearAlgebra/Matrix/HadamardMatrix.lean`); orthogonal arrays are not.

#### TauCeti

The function \(A\mapsto(\det A)^{1/n}\) is concave on the positive-semidefinite \(n\times n\) real matrices, and Minkowski's determinant inequality holds (`Matrix.concaveOn_det_rpow`, [Minkowski determinant](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Analysis/Matrix/MinkowskiDeterminant.lean)). This is the concavity of the D-criterion used in item 37; the equivalence theorem, the information matrix \(M(\xi)\) of a design measure, and its directional derivatives are not stated.

#### Statlib

No relevant declarations were found.

**Synopsis entries.** Not covered: 105.37–105.41.

### Optimality of block and polynomial designs

[Mathematical scope](SYNOPSIS105.md#optimality-of-block-and-polynomial-designs).

#### Mathlib

A configuration of points and lines is nondegenerate when every line misses some point, every point misses some line, and two distinct points lie on at most one common line; if moreover every two points lie on a line, then there are at least as many lines as points (`Configuration.HasLines.card_le`, `Combinatorics/Configuration.lean`). For a balanced incomplete block design with \(\lambda=1\) and \(k<v\), the blocks satisfy these hypotheses, so this is Fisher's inequality \(b\ge v\) in that case. The case \(\lambda\ge2\), which needs the linear-algebra argument through \(NN^{\mathsf T}=(r-\lambda)I+\lambda J\), is not stated. The shifted Legendre polynomials on \([0,1]\) are defined with their explicit coefficients and reflection symmetry (`Polynomial.shiftedLegendre`, `RingTheory/Polynomial/ShiftedLegendre.lean`); the D-optimal design of item 43 is not stated.

#### TauCeti

No relevant declarations were found beyond the determinant concavity recorded under the preceding heading.

#### Statlib

No relevant declarations were found.

**Synopsis entries.** Not covered: 105.42 (ingredients only: Fisher's inequality for \(\lambda=1\), Mathlib; the general inequality and the A-, D-, E- and universal optimality statements are absent), 105.43.

### Latin squares and regular fractions

[Mathematical scope](SYNOPSIS105.md#latin-squares-and-regular-fractions).

#### Mathlib

No Latin square, orthogonal array, or fractional factorial is defined. As supporting material, the projective plane over a field \(K\) is constructed from \(\mathbb P(K^3)\) (`Combinatorics/Configuration.lean`), a finite projective plane of order \(q\) has \(q^2+q+1\) points and lines (`Configuration.ProjectivePlane.card_points`), and a Galois field of order \(p^n\) exists for every prime \(p\) and \(n\ge1\) (`GaloisField`, `GaloisField.card`, `FieldTheory/Finite/GaloisField.lean`). A complete set of \(s-1\) mutually orthogonal Latin squares of prime-power order \(s\) is classically built from these; that construction and the bound \(k\le s-1\) are absent.

#### TauCeti

No relevant declarations were found.

#### Statlib

No relevant declarations were found.

**Synopsis entries.** Not covered: 105.44, 105.45.

### Survey sampling and finite populations

[Mathematical scope](SYNOPSIS105.md#survey-sampling-and-finite-populations).

#### Mathlib

A sampling design is representable by a probability measure on the finite
type of subsets; no new general model structure is needed. Finite sums,
indicator expectations, and the covariance expansion of a variance are
available (`ProbabilityTheory.variance_sum`,
`Mathlib/Probability/Moments/Variance.lean`). The uniform law
`ProbabilityTheory.uniformOn` (`Mathlib/Probability/UniformOn.lean`) and
subset counts (`Finset.card_powersetCard`,
`Mathlib/Data/Finset/Powerset.lean`) supply simple random sampling. The
Horvitz–Thompson estimator, inclusion-probability variance estimators,
finite-population correction, and Neyman allocation are not stated.

#### TauCeti

`TauCeti.Probability.sampleWithoutReplacement` in
`TauCeti/Probability/PopulationSampling/Finite.lean` represents uniform
sampling without replacement, as described under *Experiments,
identification, and estimation*. It does not state the sample-mean
variance, general unequal-probability estimation, or stratified allocation.

#### Statlib

No relevant declarations were found.

**Synopsis entries.** Not covered: 105.72, 105.73 (ingredients only: finite-sum moment identities and uniform sampling without replacement; the statistical formulas require the finite arguments in GAPS_EASY.md).

### Experiments, identification, and estimation

[Mathematical scope](SYNOPSIS105.md#experiments-identification-and-estimation).

#### Mathlib

No potential-outcome model is defined. Supporting material: conditional independence (`ProbabilityTheory.CondIndepFun`, `Probability/Independence/Conditional.lean`), regular conditional distributions (`ProbabilityTheory.condDistrib`, `Probability/Kernel/CondDistrib.lean`), and conditional expectation (`MeasureTheory/Function/ConditionalExpectation`). The identification formulas of items 47, 48 and 50 are short computations with these objects but are not stated.

#### TauCeti

Sampling without replacement from a finite population is defined as the law of the population read along an independent uniform injective selection (`TauCeti.Probability.sampleWithoutReplacement`, [finite population sampling](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Probability/PopulationSampling/Finite.lean)), with comparison bounds to sampling with replacement. A completely randomized experiment selects the treated units in this way; the finite-population variance formula for the sample mean under sampling without replacement, from which Neyman's theorem (item 46) follows, is not stated. Conditionally independent random variables can be represented as measurable functions of the conditioning variable and separate independent uniform noises (`ProbabilityTheory.CondIndepFun.exists_independent_coding`, [conditional randomization](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Probability/Kernel/ConditionalRandomization.lean)).

#### Statlib

A potential response is a function assigning a value to each intervention and unit (`PotentialResponse`, [potential responses](https://github.com/stat-lib/statlib/blob/eeaac0283690efaa60c31115400cf561836baeb9/Statlib/Causal/PotentialResponse.lean)), and `PotentialResponse.select` evaluates each unit at the treatment assigned to it, giving the observed outcome \(Y_i=Y_i(A_i)\) under consistency. The file supplies notation and definitional lemmas only; no probability structure, assignment mechanism, estimand, or estimator is defined.

**Synopsis entries.** Not covered: 105.46–105.50.

### Stratified, paired, and regression-adjusted experiments

[Mathematical scope](SYNOPSIS105.md#stratified-paired-and-regression-adjusted-experiments).

#### Mathlib

No relevant declarations were found.

#### TauCeti

No relevant declarations were found beyond the finite-population sampling law recorded under the preceding heading.

#### Statlib

No relevant declarations were found.

**Synopsis entries.** Not covered: 105.51–105.53.

### Treated-unit effects and instrumental variables

[Mathematical scope](SYNOPSIS105.md#treated-unit-effects-and-instrumental-variables).

#### Mathlib

No relevant declarations were found. The strong law of large numbers (`ProbabilityTheory.strong_law_ae`, `Probability/StrongLaw.lean`), the central limit theorem, the Cramér–Wold reduction, and Slutsky's theorem recorded under 105A are the ingredients of the consistency and asymptotic normality of two-stage least squares in item 55.

#### TauCeti

No relevant declarations were found.

#### Statlib

No relevant declarations were found.

**Synopsis entries.** Not covered: 105.54, 105.55.

### Efficiency, partial identification, and design-based identification

[Mathematical scope](SYNOPSIS105.md#efficiency-partial-identification-and-design-based-identification).

#### Mathlib

No relevant declarations were found.

#### TauCeti

No relevant declarations were found.

#### Statlib

No relevant declarations were found.

**Synopsis entries.** Not covered: 105.56–105.59.

### Sensitivity to unmeasured confounding and mediation

[Mathematical scope](SYNOPSIS105.md#sensitivity-to-unmeasured-confounding-and-mediation).

#### Mathlib

No relevant declarations were found.

#### TauCeti

The functional representation of conditionally independent variables by independent noises, recorded under *Experiments, identification, and estimation*, is the measure-theoretic form of the structural model at the end of item 61; the cross-world independences and the mediation formula are not stated.

#### Statlib

Same-unit substitution of potential responses (`PotentialResponse.comp`, [potential responses](https://github.com/stat-lib/statlib/blob/eeaac0283690efaa60c31115400cf561836baeb9/Statlib/Causal/PotentialResponse.lean)) forms the nested response \(Y(a,M(a'))\) of item 61 from a mediator response and an outcome response evaluated at the same unit. This is notation only; the independence assumptions and the mediation formula are not stated.

**Synopsis entries.** Not covered: 105.60, 105.61 (ingredients only: the functional representation of conditional independence by independent noises, in TauCeti, and the nested-response notation, in Statlib).

### Graphical interventions

[Mathematical scope](SYNOPSIS105.md#graphical-interventions).

#### Mathlib

Directed graphs are defined as relations on a vertex type (`Digraph`, `Combinatorics/Digraph/Basic.lean`), and quivers carry paths (`Combinatorics/Quiver`); directed acyclic graphs, parent and descendant sets, \(d\)-separation, and Markov equivalence are not defined. Composition of Markov kernels and the Ionescu–Tulcea construction (`Probability/Kernel/Composition`, `Probability/Kernel/IonescuTulcea`) provide the measure-theoretic form of a recursive factorization along a topological order, and hence of the truncated factorization defining \(\mathop{\mathrm{do}}(X=x)\) and of the longitudinal \(g\)-formula of item 65; none of these causal statements is formulated.

#### TauCeti

Weak union and the complement criterion for conditional independence (recorded under *Multivariate analysis, invariance, and graphical models*) are among the semigraphoid rules used for \(d\)-separation arguments; no directed Markov property is stated.

#### Statlib

No relevant declarations were found.

**Synopsis entries.** Not covered: 105.62–105.67.

### Structural counterfactuals and time-varying treatments

[Mathematical scope](SYNOPSIS105.md#structural-counterfactuals-and-time-varying-treatments).

#### Mathlib

No relevant declarations were found.

#### TauCeti

No relevant declarations were found.

#### Statlib

No relevant declarations were found.

**Synopsis entries.** Not covered: 105.68, 105.69.

### Causal discovery

[Mathematical scope](SYNOPSIS105.md#causal-discovery).

#### Mathlib

No relevant declarations were found.

#### TauCeti

No relevant declarations were found.

#### Statlib

No relevant declarations were found.

**Synopsis entries.** Not covered: 105.70, 105.71.

## Missing from all three libraries

**Survey sampling (items 72, 73).** The generic finite probability and
covariance infrastructure is present, and TauCeti represents uniform
sampling without replacement. Inclusion-probability estimators, their
design variance and variance estimators, stratified sampling formulas,
and Neyman allocation are missing. These are short finite derivations
from that infrastructure; see [GAPS_EASY.md](GAPS_EASY.md).

**Linear model and least squares (items 1, 2, 7–12, 19).** None of the three libraries defines the linear model \(Y=X\beta+\varepsilon\), a least-squares or generalized-least-squares estimator, or estimability. Mathlib's orthogonal projection and nearest-point theorems, the Woodbury identity, Schur complements, and the trace-equals-rank theorem for idempotents supply the algebra; Gauss–Markov (item 1) is a short argument from them once linear unbiased estimators are formalized. The normal sampling theory of item 2 is present in TauCeti for \(\mu=0\), \(\sigma=1\) through the Gaussian projection laws; the general case needs the noncentral law of \(\|PY\|^2\), which follows from TauCeti's noncentral law of \(\|Y\|^2\) for identity covariance by an orthonormal change of coordinates adapted to the column space, and the law of the least-squares estimator is an affine image of a Gaussian vector.

**Quadratic forms and analysis of variance (items 10, 15–18).** TauCeti defines the noncentral chi-squared and noncentral \(F\) laws, with the ratio construction of the latter, but no law of a quadratic form \(Y^{\mathsf T}AY\) is stated. The central case of the first part of item 15 is one step from TauCeti's moment-generating function of a Gaussian quadratic form and the chi-squared moment-generating function; Craig–Sakamoto and Cochran need in addition a factorization of the joint moment-generating function, which is not stated. Given these, the exact \(F\) test (item 10), the balanced layouts (item 17), and the one-way variance components (item 18) are routine but long, and the invariance optimality of the \(F\) test (item 16) needs a theory of invariant tests that does not exist in any of the three libraries; its first assertion, monotonicity of the power in the noncentrality, would start from TauCeti's noncentral \(F\) law.

**Generalised linear models and asymptotics (items 3–6, 13, 20, 21).** The exponential dispersion family, link functions, Fisher information, and M-estimator asymptotics are absent; Mathlib's tilted-measure identities give \(\mathbb EY=b'(\theta)\) and \(\mathop{\mathrm{Var}}Y=b''(\theta)\), and its scalar central limit theorem with Cramér–Wold and Slutsky gives the limit-theorem framework, but no vector central limit theorem is stated as such. Quantile regression needs the check-function characterization of quantiles, which is absent although TauCeti has the quantile function. Identifiability of Gaussian mixtures needs an analytic argument on characteristic functions that is not present.

**Classical multivariate analysis (items 22–35).** TauCeti's Wishart theory is the most developed part: density, congruence, marginals, moments, transforms, the Bartlett decomposition, the determinant law, and the Schur-complement law for a block of size one. Missing are the independence of \(\bar X\) and \(S\) for Gaussian samples, the Schur-complement theorem of item 31 for general block size with its independence statement (whose proof would combine Gaussian conditioning with the Gram representation), Hotelling's \(T^2\), the matrix-variate Beta law and Wilks's lambda, the asymptotic expansions of Box and Bartlett, eigenvalue asymptotics for principal components, the correlation sampling theory, and factor analysis. Item 30 is close: the Ky Fan inequality and its attainment for positive operators are present, and the identification of the maximizer with leading eigenvectors and the reconstruction-error identity are short; the lower bound of the Frobenius-norm Eckart–Young–Mirsky theorem is one step from TauCeti's singular-value Hoffman–Wielandt inequality, and its attainment by the truncated singular value decomposition is a further short computation. For item 27, TauCeti has the von Mises–Fisher density and mean; the likelihood of a sample and its maximization over the mean direction are missing.

**Graphical models (items 26, 36, 62, 67, 70, 71).** None of the three libraries defines a Markov property relative to an undirected or directed graph, and \(d\)-separation, chordal graphs, and Markov equivalence are absent. The Hammersley–Clifford theorem needs Möbius inversion over vertex subsets (Mathlib's incidence algebra, `Combinatorics/Enumerative/IncidenceAlgebra.lean`, supplies Möbius inversion on locally finite orders) together with conditional densities; the Gaussian precision-matrix criterion is close to TauCeti's Gaussian conditioning theorem, since the conditional covariance of a pair given the rest is the inverse of the corresponding \(2\times2\) block of the precision matrix.

**Experimental design (items 37–45).** Kiefer–Wolfowitz needs the information matrix of a design measure and a directional-derivative argument; TauCeti's concavity of \((\det A)^{1/n}\) is the starting point. Block designs, their information matrices, and connectedness (item 39) are absent, though the latter is the weighted analogue of Mathlib's Laplacian kernel theorem. Fisher's inequality is present only for \(\lambda=1\). Latin squares, orthogonal arrays, regular fractions, and the finite-field construction of mutually orthogonal Latin squares are absent, though Galois fields and finite projective planes are present.

**Randomization inference and potential outcomes (items 38, 46–59, 66).** No randomization test, design-based estimator, or potential-outcome model with an assignment mechanism is defined; Statlib's potential responses are notation without probability structure. Neyman's variance formula needs the covariance of indicators under sampling without replacement, a short finite computation from TauCeti's sampling-without-replacement law; the stratified and paired results then follow. The identification formulas of items 47, 48, 50, 54, 57, 58, and 59 are each a few lines from Mathlib's conditional independence and conditional expectation, but none is stated. The doubly robust and efficiency results (items 49, 56) depend on the semiparametric theory of [SYNOPSIS102](SYNOPSIS102.md), which is also absent.

**Causal graphs and counterfactuals (items 60, 61, 63–65, 68, 69).** Structural causal models, interventions, the back-door and front-door formulae, the do-calculus and its completeness, the \(g\)-formula, marginal structural models, probabilities of causation, and the Cornfield and E-value inequalities are absent. Mathlib's kernel composition and TauCeti's functional representation of conditional independence are the natural measure-theoretic starting point for structural models; Statlib's potential-response notation, with same-unit substitution for nested responses, is a starting point for counterfactual statements but carries no probability structure. The Cornfield inequality is an elementary inequality among conditional probabilities and needs no new infrastructure.
