# Credits and source baseline

The mathematical scope is the project's [SYNOPSIS.md](SYNOPSIS.md),
[GAPS.md](GAPS.md), and [GAPS_EASY.md](GAPS_EASY.md). The coverage documents
identify the mathematical sources and upstream declarations in detail.

The library baseline is fixed by the project configuration:

- Mathlib `6135ffb78e8bcd3fcc8ec02f3f82ea0b0737358b`.
- TauCeti `afa08a3ed16fb167e35de371afb1eb03fbc5913a`.
- Statlib `eeaac0283690efaa60c31115400cf561836baeb9`.
- Lean `v4.36.0-rc2`.

The code uses Mathlib's measure theory, Markov kernels, conditional
expectations, statistical risk framework, independent random variables,
Gaussian measures, differentiation, Hilbert projections, categories of
modules, and `Lp` spaces. A real risk or moment adapter in CKSD does not
claim a new upstream definition or a new theorem.

Specific proof reuse includes:

- The Gaussian projection and residual independence theorem uses TauCeti's
  `Gaussian/Projection.lean` and `Gaussian/Affine.lean`; the nested central F law
  uses `FisherSnedecor/ChiSquared.lean`. The Wishart determinant law uses
  `Wishart/Agreement.lean` and `Wishart/Determinant.lean`, under
  `TauCeti/Probability/Distributions/`.
- Strict monotonicity of the noncentral F upper tail uses TauCeti's
  `noncentralChiSquaredMeasure_conv_noncentralChiSquaredMeasure`, support
  theorems for central and noncentral chi-squared laws, and
  `hasLaw_noncentralF_of_noncentralChiSquared`. The local coupling adds an
  independent noncentral chi-squared increment and exhibits a set of positive
  probability on which the F threshold is crossed.
- The barycentric-velocity action bound uses TauCeti's
  `exists_isContinuityEquation_map_smul_fst_add_smul_snd` and
  `IsContinuityEquation.wassersteinEDist_rpow_le`, together with its continuity
  theorem for push-forward probability laws. The passage from slice conditional
  expectations to the product conditional expectation uses Mathlib's
  `ae_eq_condExp_of_forall_setIntegral_eq`, Fubini's theorem, and conditional
  Jensen inequalities.
- The singleton-limit-set convergence lemma uses Mathlib's compactness criterion
  `IsCompact.tendsto_nhds_of_unique_mapClusterPt`. The stochastic approximation
  equilibrium corollary also depends on the admitted limit-set theorem, as
  recorded by the compiled axiom inventory.
- The MMD weak-convergence criterion uses Mathlib's continuity of product
  probability laws, continuity of bounded continuous integrals, and Prokhorov's
  compactness theorem for uniformly tight families. The zero-distortion isometry
  theorem uses its measure-support and isometry APIs. The Wasserstein Karcher
  equation follows from the local proved transport-energy descent inequality.
- `minimizer_mem_span_of_feature_vectors` uses Mathlib's complete
  finite-dimensional span, orthogonal projection, and norm bounds.
- `LandscapeLp.ae_tendsto_sampleAverage` specializes Mathlib's
  `ProbabilityTheory.strong_law_ae` (the Banach-space Etemadi strong law).
- `hasDerivAt_predictions_of_gradient_flow` uses Mathlib's Fréchet/ordinary
  derivative chain rule and linearity.
- The half-bridge results and `klDiv_bridgeIterate_step` use TauCeti's
  entropy projection `Measure.fitLaw`, its marginal law, uniqueness, and
  Pythagorean identity from
  `TauCeti/InformationTheory/KullbackLeibler/Projection.lean`.
- `totalVariationDistance_map_le_sqrt_klDiv` uses Mathlib's divergence data
  processing and TauCeti's event form of Pinsker's inequality from
  `TauCeti/InformationTheory/KullbackLeibler/Pinsker.lean`.
- `realSinkhornDivergence_nonneg` uses TauCeti's nonnegativity theorem in
  `TauCeti/MeasureTheory/OptimalTransport/Entropic/SinkhornDivergence.lean`.
- The Gaussian-mixture model reuses TauCeti's general finite multivariate
  Gaussian mixture law, density, probability instance, and density theorem
  from `TauCeti/Probability/Distributions/Gaussian/Mixture/Multivariate.lean`.
- `integral_le_of_generalized_neyman_pearson` uses Mathlib's bounded
  integrable products, integral monotonicity, and finite-sum integral.
  The UMVU covariance characterization uses Mathlib's variance/covariance
  expansions and quadratic discriminant inequality; the Scheffé geometric
  identity uses its inner-product inequalities and supremum API.
- The compact argmax and M-estimator consistency proofs use Mathlib's
  compact extreme-value theorem, event monotonicity, and filter limits.
  Isotonic least-squares existence and uniqueness use the Hilbert-space
  projection theorem for a closed convex monotone cone. These proofs are
  independent of the admitted distributional limits and isotonic block formula.
- The Horvitz–Thompson and Sen–Yates–Grundy identities use Mathlib's
  Bochner integral of indicator functions, finite-sum integrals, and the
  variance second-moment formula. Finite randomization p-value validity
  uses existence of a minimum on a finite set.
- Robbins' count-ratio consistency specializes Mathlib's
  `ProbabilityTheory.strong_law_ae_real` to singleton indicators.
  Leapfrog volume preservation uses Mathlib's measure-preserving skew
  products and translation invariance. The Gibbs-generator identity uses
  `integral_eq_zero_of_hasDerivAt_of_integrable`; entropy decay uses
  Mathlib's derivative and monotonicity API with an integrating factor.
- Wald's identity adapts Rémy Degenne's stopped-sum theorem in
  `Statlib/Testing/Sequential/Wald.lean`, together with Statlib's
  tail-sum formula. The module header records the exact imported source.
- The extrinsic-mean criterion uses TauCeti's covariance-trace identity
  `integral_norm_sub_sq_eq_norm_integral_sub_sq_add_trace_covMatrix` from
  `TauCeti/Probability/Moments/Covariance.lean`. The Hilbert feature-average
  approximation uses its
  `integral_norm_finiteMean_sub_sq_le_of_forall_le` from
  `TauCeti/Probability/Moments/SampleMean.lean` and Mathlib's integral
  first-moment method.
- Classification-risk identities use Mathlib's Bochner integral arithmetic;
  surrogate calibration uses its convex secant-slope and derivative inequalities.
  Finite-class risk concentration specializes its bounded-variable sub-Gaussian
  moment-generating-function theorem and Chernoff bounds, with a finite union bound.
  The characteristic-kernel independence criterion uses its equivalence
  between independence and the product law of a pair of random variables.
- Section 101: Rao–Blackwell uses Mathlib's `ConvexOn.map_integral_le` and
  `ConvexOn.slope_mono_adjacent`; Basu's theorem uses
  `indepFun_iff_measure_inter_preimage_eq_mul` and the kernel product integrals
  `Measure.integral_compProd` and `StronglyMeasurable.integral_kernel`; the
  complete-class theorem uses `geometric_hahn_banach_open`; Neyman structure uses
  `ae_eq_condExp_of_forall_setIntegral_eq`. The joint order-statistic density uses
  TauCeti's `TauCeti.Probability.map_orderStatistics_pi`, `TauCeti.pi_withDensity`, and
  `TauCeti.measurableSet_setOf_strictMono` from
  `TauCeti/MeasureTheory/Measure/PiWithDensity.lean`. The Neyman–Pearson and
  Karlin–Rubin proofs reuse the local generalized Neyman–Pearson inequality.
- Section 102: the contiguity, Le Cam third-lemma, and local-power proofs use Mathlib's
  Portmanteau theorem (`ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'`,
  `ProbabilityMeasure.tendsto_iff_forall_integral_tendsto`), Radon–Nikodym integrals,
  and dominated convergence. The efficient location score uses Mathlib's orthogonal
  projections. The likelihood-test formulations use TauCeti's `chiSquaredMeasure` and
  `noncentralChiSquaredMeasure`; the semiparametric formulations use Statlib's
  `QMD.HasQuadraticMeanDerivWithinAt` through the local adapter.
- Section 103: the lasso, PCA, thresholded-covariance, Assouad, and rank-statistic proofs
  use Mathlib's orthonormal-basis and Bessel inequalities, `Matrix.toEuclideanCLM`, and
  finite-sum integrals. The Grenander, Tracy–Widom, and graphical-lasso formulations use
  Mathlib's `IsBrownianReal`, `HasSubgaussianMGF`, and `closedConvexHull`; their
  constants follow Wainwright (2019), Theorem 11.12 and Proposition 11.9, and
  Samworth–Shah, Theorem 9.26.
- Section 104: the Tweedie, score-matching, and Fokker–Planck proofs use Mathlib's
  differentiation under the integral and
  `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`. The Dirichlet-process mean
  uses TauCeti's `dirichletMeasure` and `integral_eval_dirichletMeasure`. The
  functional-inequality, JKO, and continuity-equation formulations use TauCeti's
  `PoincareInequality`, `LogSobolevInequality`, `WassersteinSpace`,
  `moreauYosidaResolvent`, `boltzmannEntropy`, `potentialEnergy`,
  `IsContinuityEquation`, and `wassersteinEDist`.
- Section 105: the canonical-correlation proofs use Mathlib's `CFC.sqrt`,
  `Matrix.PosSemidef.inv_sqrt`, and `Matrix.charpoly_mul_comm`, together with TauCeti's
  `indepFun_matrix_multivariateGaussian_iff`. The Wald-ratio identity uses
  `IndepFun.integral_fun_mul_eq_mul_integral`. The $F$-test and GLM formulations use
  TauCeti's `noncentralFMeasure`, `fisherSnedecorMeasure`, and `chiSquaredMeasure`.
- Section 106: Ville's inequality adapts Kexing Ying's optional-stopping theory in
  Mathlib (`Submartingale.expected_stoppedValue_mono`, `hittingBtwn`). The
  long-run-variance limit uses `tendsto_tsum_of_dominated_convergence` and Mathlib's
  covariance bilinearity. The Kalman formulation uses TauCeti's
  `TauCeti.Probability.multivariateGaussianPDF` from
  `TauCeti/Probability/Distributions/Gaussian/Density.lean`.
- Section 107: the graphon-mixture theorem specializes TauCeti's
  `InfiniteExchangeableGraphLaw.existsUnique_bind_infiniteSampleLawOnSpace` and
  `SimpleGraph.measure_ext_of_map_restrictFin`. The Laplace-mechanism results use
  TauCeti's `TauCeti.Probability.laplaceMeasure`. Composition of private mechanisms uses
  Mathlib's layer-cake formula `lintegral_eq_lintegral_meas_lt`; the Bellman fixed point
  uses `ContractingWith.fixedPoint`; Hedge uses `hasSubgaussianMGF_of_mem_Icc`.
  Random-graph formulations use Mathlib's `SimpleGraph.binomialRandom`.
- Section 108: the Schoenberg criterion and MMD proofs use Mathlib's matrix and
  product-integral API; the Stein identity uses
  `integral_eq_zero_of_hasDerivAt_of_integrable`. The topological formulations use
  TauCeti's singular chains and homology, `manifoldMorseIndex`, and `IsMorse`, and
  Mathlib's `PreAbstractSimplicialComplex` and `GromovHausdorff.ghDist`; the
  sinkhorn lower bound uses TauCeti's entropic-cost and coupling lemmas.
- Section 101, further proofs: the Gaussian sampling laws use TauCeti's
  `HasLaw.iIndepFun_orthogonalProjectionOnto_stdGaussian`,
  `HasLaw.norm_sq_orthogonalProjectionOnto_stdGaussian`, and
  `TauCeti.Probability.hasLaw_studentT_of_gaussian_chiSquared`; the marginal
  order-statistic density uses `cdf_map_orderStatistic_pi_eq_regularizedIncompleteBeta`
  and TauCeti's beta-law CDF; Gaussian integration by parts uses Mathlib's
  `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`.
- Section 102, further proofs: the delta method, Cramér's MLE theorem, and the Hadamard
  delta method use Mathlib's bounded-Lipschitz and closed-set Portmanteau theorems,
  `ProbabilityTheory.strong_law_ae`, and the central limit theorem
  `ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub`. The Huber bound uses
  TauCeti's `TauCeti.Probability.hasDerivAt_gaussianPDFReal` and
  `TauCeti.Probability.integral_sq_gaussianReal`, with Mathlib's improper fundamental
  theorem of calculus.
- Section 103, further proofs: Fano's inequality uses Statlib's
  `ProbabilityTheory.klDiv_eq_klDiv_boolMeasure_add_add`
  (`Statlib/Divergence/KullbackLeibler/Event.lean`) and its Bernoulli divergence lemmas
  (`Statlib/ForMathlib/InformationTheory/KullbackLeibler/Bernoulli.lean`). The
  distribution-free goodness-of-fit laws use TauCeti's quantile coupling
  (`TauCeti/Probability/Quantile.lean`), `MeasureTheory.Measure.continuous_cdf_of_noAtoms`,
  and `TauCeti.Probability.uniformMeasure`. The eigenvector bound uses Mathlib's
  `IsSelfAdjoint.hasEigenvector_of_isMaxOn`.
- Section 104, further proofs: the log-Sobolev-to-Poincaré implication uses TauCeti's
  `TauCeti/Probability/Concentration/PoincareLogSobolev.lean` and
  `TauCeti/MeasureTheory/Integral/Entropy.lean`; the Pólya-urn and Metropolis ergodic
  limits use Mathlib's Borel–Cantelli lemma, harmonic-number bounds, and
  `tendsto_div_of_monotone_of_exists_subseq_tendsto_div`.
- Section 105, further proofs: the Latin-square and block-design results use Mathlib's
  `GaloisField.card` and matrix-rank lemmas; the canonical-correlation and multivariate
  root statistics use `Matrix.IsHermitian.spectral_theorem` and the L² operator norm.
- Section 106, further proofs: the stationary Gaussian process uses Mathlib's Kolmogorov
  extension (`projectiveLimit`, `IsProjectiveLimit.unique`) and `IsGaussian.ext`; the
  exceedance count uses TauCeti's `iIndepFun.hasLaw_card_filter_mem` and
  `poissonBinomialMeasure_const`; Anscombe's theorem reuses the Section 102 Slutsky and
  central-limit adapters.
- Section 107, further proofs: the stability and Rademacher bounds use TauCeti's
  `TauCeti.Probability.hasSubgaussianMGF_of_bounded_differences`
  (`TauCeti/Probability/McDiarmid.lean`) and Mathlib's `HasSubgaussianMGF.measure_ge_le`;
  Exp3 uses `condExp_mul_of_stronglyMeasurable_left`.
- Section 108, further proofs: the Čech–Rips inclusion uses Mathlib's
  `geometric_hahn_banach_point_closed`; the Gaussian transport maps use the continuous
  functional calculus (`Commute.cfc_nnreal`, `CFC.sqrt_unique`); random Fourier features
  use `HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun`; transport descent uses TauCeti's
  `TauCeti.isCoupling_map_prodMk_of_aemeasurable` and `TauCeti.wassersteinEDist_le`.
- Section 101, round three: the factorization theorem uses the Halmos–Savage
  countable-mixture domination with Mathlib's `condDistrib`, `compProd_map_condDistrib`,
  `Measure.condKernel`, and `Measure.withDensity_compProd`; completeness of a full-rank
  exponential family uses TauCeti's `TauCeti.Measure.ext_of_mgf`
  (`TauCeti/Probability/Moments/Determinacy.lean`) and Mathlib's `Measure.ext_of_charFun`.
- Section 102, round three: the Z-estimator theorem follows van der Vaart, *Asymptotic
  Statistics*, Theorem 5.21, with a local chaining bound; the Bahadur representation
  follows Ghosh (1971); local asymptotic normality follows van der Vaart, Theorem 7.2. The
  likelihood-ratio, Wald, and score limits use Mathlib's `Measure.infinitePi` and
  `iIndepFun_infinitePi`, and TauCeti's `gaussianReal_map_sq_noncentral` and
  `noncentralChiSquaredMeasure_zero_noncentrality`
  (`TauCeti/Probability/Distributions/NoncentralChiSquared/Gaussian.lean`).
- Section 103, round three: stable recovery under the restricted isometry property follows
  Foucart and Rauhut (2013), Theorems 4.20, 4.22, and 6.13, with an elementary proof of the
  square-root lifting inequality in place of Lemma 6.14. The Grenander maximum-likelihood
  proof uses Mathlib's concave slope inequalities.
- Section 104, round three: the Laplace approximation uses TauCeti's multivariate Gaussian
  density (`TauCeti/Probability/Distributions/Gaussian/Density.lean`) and Mathlib's
  `ContDiffAt.isSymmSndFDerivAt`; particle-filter consistency uses
  `ProbabilityTheory.variance_sum_pi`.
- Section 105, round three: the global directed Markov property, the back-door and
  front-door formulae, the do-calculus rules, and the decomposable factorization follow
  Lauritzen (1996), Section 3.2 and the decomposable-model chapter, and Pearl (2009),
  Sections 3.3–3.4, using Mathlib's simple-graph walks and cliques.
- Section 106, round three: the Kalman filter uses TauCeti's `map_affine_multivariateGaussian`,
  `multivariateGaussian_conv_multivariateGaussian`, and
  `indepFun_matrix_of_hasLaw_multivariateGaussian_iff`, with Mathlib's
  `condDistrib_ae_eq_of_measure_eq_compProd`; the Wold decomposition uses Mathlib's
  `LinearMap.extendOfNorm`, Bessel's inequality `Orthonormal.inner_products_summable`, and
  TauCeti's `Finsupp.norm_linearCombination_eq_of_inner_eq`, following the construction of
  its `kolmogorovIsometry`.
- Section 107, round three: the bandit and privacy lower bounds use Statlib's
  Bretagnolle–Huber inequality `exp_neg_klDiv_le_two_sub_tvDist`, its total-variation
  lemmas (`tvDist_comp_le`, `integral_sub_integral_le_tvDist`, `etvDist_eq_two_mul_iSup_sub`),
  and `klDiv_pi`; the local-privacy contraction uses Mathlib's
  `InformationTheory.klDiv_eq_lintegral_klFun_of_ac`; UCB uses Mathlib's Hoeffding bound
  `HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun`.
- Section 108, round three: Gromov–Hausdorff stability of Rips persistence uses Mathlib's
  `GromovHausdorff.ghDist_eq_hausdorffDist`; Wasserstein stability uses the Minkowski
  inequality `ENNReal.Lp_add_le`.

The posterior-contraction formulations reuse Statlib's squared Hellinger
divergence from `Statlib/Divergence/Hellinger/Basic.lean`. Extreme-value
formulations reuse TauCeti's order statistics, GEV and generalized Pareto
laws, including its threshold-excess construction. The multivariate test
statistics reuse Mathlib's Hermitian eigenvalues, continuous functional
calculus, and covariance matrices; the exact-law formulations use TauCeti's
Wishart Gram laws and Mathlib's beta law. Graphical-model and approximation
formulations use Mathlib's simple graphs, Fourier transform, sigmoid,
finite-dimensional linear algebra, and continuous linear maps.

The distribution, order-statistic, Wishart, Wasserstein, and entropic
constructions imported from TauCeti retain its conventions and attribution.
The asymptotic framework imports Statlib's `Contiguous5` interface from
`Statlib/Contiguity/Def.lean` and proves its equivalence with CKSD's
measure-sequence adapter. `HasQuadraticMeanDerivAt` specializes Statlib's
`QMD.HasQuadraticMeanDerivWithinAt` from `Statlib/Inference/QMD.lean`.
These interfaces do not certify the likelihood-ratio characterizations in
Statlib's contiguity roadmap.

The section-level theorem formulations use this project's `Suggested101.lean`–
`Suggested108.lean` drafts as a source. Module headers and declaration
docstrings identify the mathematical catalogue entry and any narrower scope.

The population covariance matrix adapter uses `TauCeti.covMatrix` from
`TauCeti/Probability/Moments/Covariance.lean`. The square-root lifting inequality
specializes Mathlib's `Real.rpow_add_le_add_rpow`; maximal-invariant factorization
uses Mathlib's `Function.factorsThrough_iff`. These adapters retain the upstream
hypotheses and conventions at the pinned revisions.

The Gaussian Bures formula for positive semidefinite covariances uses TauCeti's
positive-definite formula, weak continuity of Gaussian laws and the Wasserstein
moment criterion, together with Mathlib's continuity of the CFC square root.
Normalized factor-loading uniqueness uses TauCeti's
`conjTranspose_mul_self_eq_iff_exists_unitary_mul` from
`Analysis/Matrix/GramFactorization/Uniqueness.lean` and Mathlib's uniqueness of
strictly monotone finite enumerations. The Gaussian likelihood criterion uses
Mathlib's spectral theorem, eigenvalue positivity and scalar logarithm inequalities.

Kinetic Gibbs invariance uses TauCeti's `stdGaussian_eq_withDensity` and
`integral_fderiv_apply_eq_zero_of_hasCompactSupport`. The proof writes the generator
in weighted divergence form for the phase-space density and integrates each
coordinate derivative against product Lebesgue measure.

The order-two Hoeffding decomposition and exact variance use Mathlib's finite-product
integration and law-transfer lemmas, `variance_sum_pi`, and covariance identities.
The degenerate pair-sum calculation integrates out a coordinate that occurs in
only one of two distinct pairs.

Mean-square stability of optimal transport maps uses Mathlib's Vitali theorem and
TauCeti's Wasserstein moment-tail criterion, stability and compactness of optimal
plans, Brenier uniqueness, and graph-plan convergence in measure.

The Euclidean central limit theorem uses Mathlib's Cramér–Wold theorem and scalar
IID central limit theorem, with TauCeti's covariance-matrix identities. The
finite-rank degenerate U-statistic limit combines this joint CLT with Mathlib's
strong law for weighted score squares and the proved Slutsky adapters. The
projected empirical-mean limit uses the same Euclidean CLT and CKSD's delta method.

The exact noncentral F law uses the completed Gaussian projection/residual
independence theorem, TauCeti's shifted standard-Gaussian norm law from
`Probability/Distributions/NoncentralChiSquared/Gaussian.lean`, and its independent
noncentral-chi-squared/chi-squared ratio characterization of the noncentral F law.

Upstream definitions replace local duplicates, with bridge lemmas where CKSD keeps a
statistical adapter:

- Mathlib: `Measure.conv` for convolution laws; `TendstoInMeasure` through
  `tendstoInProbabilityConst_iff_tendstoInMeasure`; `tvDist` through
  `tvDist_eq_two_mul_totalVariationDistance`; `Matrix.rowStochastic` for Markov
  transition matrices; `poissonMeasure` through `poissonMass_coe`; `bernoulliMeasure` for
  Bernoulli bandit arms; `HolderOnWith` and `HolderWith` for Hölder classes; `hammingDist`
  in Assouad's lemma and local privacy; `Maximal` for maximal cliques; `Set.projIcc` for
  clipping; `Real.negMulLog` for finite entropies; `Relator.BiUnique` for diagram matchings;
  `exists_eq_ciSup_of_finite`, `Measurable.iSup`, `Integrable.of_mem_Icc`,
  `Finite.exists_le`, `EquivLike.range_comp`, `SimpleGraph.Walk.exists_boundary_dart`,
  `ContinuousLinearMap.isStarProjection_iff_eq_starProjection_range`,
  `Finset.sum_mul_sq_le_sq_mul_sq`, `Finset.sq_sum_div_le_sum_sq_div`,
  `Matrix.PosSemidef.mul_mul_conjTranspose_same`, `Real.rpow_add_le_add_rpow`,
  `Real.tendsto_one_add_pow_exp_of_tendsto` and `Measure.pi_map_pi` in the corresponding
  proofs.
- TauCeti: `Probability.uniformMeasure` for the uniform law on the unit interval;
  `Measure.quantile`, `le_cdf_quantile`, `lt_quantile_iff` and `Measure.map_quantile_volume_Ioo`
  for tail quantiles and probability-integral transforms; `MeasurableEquiv.map_withDensity` in
  Gaussian conditioning; `map_affine_multivariateGaussian` for stationary Gaussian
  finite-dimensional laws; `noncentralFMeasure_zero_noncentrality`, which gives the central
  F law as the zero-noncentrality case of the nested F theorem; `covMatrix` and
  `Matrix.PosSemidef.kernelMeanEmbedding` with `norm_kernelMeanEmbedding_sub_sq`, which
  identify the squared MMD with a squared embedding distance; and `Measure.fitLaw`,
  `klDiv_fitLaw` and `eq_fitLaw_of_klDiv_le` in the Schrödinger-bridge half steps.
- Statlib: `InformationTheory.klBerReal` for Bernoulli divergences in bandit lower bounds,
  and `etvDist_eq_two_mul_iSup_sub` for the total-variation bridge.
