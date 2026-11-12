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
  `IsCompact.tendsto_nhds_of_unique_mapClusterPt`. The stochastic-approximation
  limit-set theorem uses TauCeti's preconnected omega-limit sets, Mathlib's
  Grönwall estimates, and local compactness arguments to construct internal
  chains of the limiting flow. Its equilibrium corollary has no admitted dependencies.
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
- The two-stage least-squares limit theorems use TauCeti's `TauCeti.measurable_matrix_inv` and
  `TauCeti.measurable_matrix_mul` from `TauCeti/Analysis/Matrix/MeasurableSpace.lean`.
- The connectivity estimates for the binomial random graph use TauCeti's measurable-singleton
  instance on simple graphs from `TauCeti/Combinatorics/SimpleGraph/Measurable.lean`, which with
  Mathlib's measurable space on `SimpleGraph V` makes every set of graphs on a finite vertex type
  measurable.
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

- Mathlib: `Measure.conv` for convolution laws; `TendstoInDistribution` and
  `TendstoInMeasure` for convergence in distribution and in probability, with the
  portmanteau theorem, the Lipschitz-function criterion and the continuous-mapping and
  Slutsky lemmas; convergence in `ProbabilityMeasure` for weak convergence of laws;
  `IsTightMeasureSet` through `isBoundedInProbability_iff_isTightMeasureSet`; `variance`,
  `covariance` and `ProbabilityTheory.cdf`; `tvDist` through
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

Proofs of the classical limit and lower-bound theorems rest on the following upstream results.

- Mathlib: the strong law (`strong_law_ae`, `strong_law_ae_real`); Lévy's continuity theorem
  (`ProbabilityMeasure.tendsto_iff_tendsto_charFun`), `charFun_multivariateGaussian` and
  `Measure.ext_of_charFun`; the Cramér–Wold device (`TendstoInDistribution.of_inner`); the
  portmanteau theorem (`ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'`);
  martingale convergence (`Submartingale.ae_tendsto_limitProcess`,
  `supermartingale_of_setIntegral_succ_le`) for the Robbins–Siegmund argument; conditional
  expectation (`condExp_condExp_of_le`, `condExp_mul_of_aestronglyMeasurable_left`,
  `condExp_bilin_of_aestronglyMeasurable_left`,
  `condIndepFun_iff_condExp_inter_preimage_eq_mul`) for propensity scores;
  `hasFDerivAt_integral_of_dominated_of_fderiv_le` and `IsLocalMax.hasFDerivAt_eq_zero` for
  exponential-family likelihood equations; `det_add_replicateCol_mul_replicateRow` for the
  Kiefer–Wolfowitz theorem; `integral_gaussian`, `mgf_id_gaussianReal` and
  `integral_llr_tilted_right` for Gaussian computations; tree lemmas
  (`SimpleGraph.IsTree.dist_eq_dist_add_one_of_adj`, `IsAcyclic.eq_penultimate_of_adj_end`,
  `IsAcyclic.mem_support_of_ne_mem_support_of_adj_of_isPath`) for belief propagation and
  junction trees; `Real.volume_pi_ball` and `Real.volume_Icc_pi` for quantization bounds.
- TauCeti: `stdGaussian_map_norm_sq` for the chi-squared limit of Pearson's statistic;
  `map_inner_multivariateGaussian` in two-stage least squares; `gaussianReal_tilted_mul` and
  Pinsker's inequality `two_mul_sq_measureReal_sub_le_klDiv` in Gaussian lower bounds;
  `Measure.continuous_cdf_of_noAtoms` in bootstrap consistency; the Wasserstein rearrangement,
  pushforward and quantization results (`wassersteinEDist_eq_eLpNorm_quantile_sub`,
  `wassersteinEDist_map_le_mul`, `hasFiniteMoment_iff_memLp_quantile`,
  `eLpNorm_infEDist_le_wassersteinEDist`) for distance-to-measure stability and quantization.
- Statlib: `klDiv_pi` for divergences of product laws.

The triangular-array and martingale central limit theorems
(`CKSD/Asymptotics/Lindeberg/Basic.lean`, `CKSD/Asymptotics/MartingaleCLT/Basic.lean`) follow
Billingsley's characteristic-function proof of the Lindeberg–Feller theorem and B. M. Brown,
*Martingale central limit theorems*, Ann. Math. Statist. 42 (1971), with Hall and Heyde,
*Martingale Limit Theory and Its Application* (1980), §3.2. Further proofs use these upstream
results.

- Mathlib: Lévy's continuity theorem (`TendstoInDistribution.of_tendsto_charFun`) and
  `taylor_isLittleO_univ`; the conditional-expectation pull-out
  `condExp_stronglyMeasurable_bilin_of_bound`; conditional laws
  (`condIndepFun_iff_map_prod_eq_prod_condDistrib_prod_condDistrib`,
  `condDistrib_ae_eq_of_measure_eq_compProd`, `Kernel.compProd_eq_iff`); Lévy's upward theorem
  `Integrable.tendsto_ae_condExp` and `exists_measurableEmbedding_real` in Doob's consistency
  theorem; `geometric_hahn_banach_of_nonempty_interior_point`,
  `Convex.interior_nonempty_iff_affineSpan_eq_top` and `LowerSemicontinuousOn.exists_isMinOn`
  for maximum-likelihood existence; `Matrix.det_add_mul`, `Polynomial.eq_of_infinite_eval_eq` and
  `IsHermitian.roots_charpoly_eq_eigenvalues` for the Craig–Sakamoto theorem;
  `hasFDerivAt_integral_of_dominated_loc_of_lip'` and `Measure.addHaar_affineSubspace` for
  semidiscrete transport; `Module.Basis.indexEquiv` for uniqueness of interval decompositions;
  `ContDiffBump` for test functions; the `SimpleGraph` tree and walk API for chordal graphs.
- TauCeti: Bernstein's inequality `iIndepFun.measureReal_abs_sum_ge_le_of_abs_le` for chaining;
  `indepFun_matrix_multivariateGaussian_iff` and
  `mgf_inner_toEuclideanLin_multivariateGaussian_sqrt` for Gaussian quadratic forms; the
  inverse-Wishart mean `integral_id_inverseWishartMeasure` for ridgeless regression;
  `mgf_sum_mul_sq_pi_gaussianReal` for chi-squared tails; `indepFun_of_measurable_blockSigma` and
  `strong_law_ae_infinitePi` for infinite product models;
  `exists_finset_isCover_of_subset_closedBall` for random features;
  `wassersteinEDist_rpow_eq_transportCost` and `le_transportCost` for semidiscrete transport;
  `norm_prod_sub_prod_le_sum_norm_sub` for products of characteristic functions;
  `abs_sub_taylorWithinEval_le` for kernel-density bias.
- Statlib: `MeasureTheory.lintegral_fintype_prod_eq_prod` and `klDiv_pi_const` in sparse minimax
  bounds.

Further proofs use these upstream results.

- Mathlib: analytic functions and `fderiv` of parametric integrals and the covariance API for
  analyticity of the log-partition function; the mean value theorem for the inverse of the mean
  parametrization; `ProbabilityTheory.strong_law_ae`, the iid CLT
  `tendstoInDistribution_inv_sqrt_mul_sum_sub`, the Cramér–Wold device
  `TendstoInDistribution.of_inner` and Slutsky's lemma
  (`TendstoInDistribution.continuous_comp_prodMk_of_tendstoInMeasure_const`) throughout; Lévy's
  continuity theorem with `charFun_gaussianReal` and `charFun_multivariateGaussian` for the
  wide-network Gaussian limit and the particle-filter CLTs; `SimpleGraph.binomialRandom`,
  `ProbabilityTheory.tendsto_choose_mul_pow_atTop` and
  `Int.alternating_sum_range_choose_eq_choose` for random-graph thresholds; Hoeffding's
  inequality `HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun` and
  `toReal_klDiv_of_measure_eq` for Schwartz consistency; the cumulant calculus
  `analyticOnNhd_cgf` and `iteratedDeriv_two_cgf_eq_integral` for canonical GLMs;
  `ConvexOn.lipschitzOnWith_of_abs_le` and
  `Convex.exists_subset_interior_convexHull_finset_of_isCompact` for the convexity lemma;
  absolutely continuous functions and Lebesgue differentiation
  (`AbsolutelyContinuousOnInterval.const_of_ae_hasDerivAt_zero`,
  `IntervalIntegrable.ae_hasDerivAt_integral`) for the Kaplan–Meier estimator;
  `condExp_indep_eq` and `indep_iSup_of_disjoint` for sample autocorrelations;
  `tendsto_tsum_of_dominated_convergence` for the periodogram; manifold immersions and Haar
  measure for sampling on submanifolds; `Metric.hausdorffDist_le_of_mem_dist` for k-means.
- TauCeti: McDiarmid's inequality and continuity of translation in `L¹` for the Devroye $L^1$
  theorem; quantiles for the UMP interval test; the matrix functional calculus and the Brouwer
  fixed-point theorem for the Gaussian Wasserstein barycenter; the Kantorovich–Rubinstein duality
  and Gaussian densities for smoothed empirical measures; matrix normal and Wishart laws
  (`map_mul_mul_add_matrixNormalMeasure`, `wishartGramMeasure_eq_nonsingularWishartMeasure`),
  `hasLaw_studentT_of_gaussian_chiSquared`, `hasLaw_fisherSnedecor_of_chiSquared` and
  `HasLaw.iIndepFun_orthogonalProjectionOnto_stdGaussian` for multivariate sample laws;
  `map_sum_sq_pi_gaussianReal` and `chiSquaredMeasure_two` for periodogram limits;
  `abs_prod_sub_prod_le_sum_abs_sub` for the Kaplan–Meier product; `strong_law_ae_infinitePi` and
  `pi_withDensity` for evidence bounds; `map_affine_multivariateGaussian` for convex regression.

The Dirichlet-process results (`CKSD/Bayes/StickBreaking.lean`,
`CKSD/Bayes/DirichletConjugacy.lean`) follow Sethuraman, *A constructive definition of
Dirichlet priors*, Statist. Sinica 4 (1994), and Ghosal and van der Vaart, *Fundamentals of
Nonparametric Bayesian Inference* (2017), Ch. 4. They use TauCeti's Dirichlet laws
(`dirichletMeasure`, `map_dirichletStickInsert_prod_betaMeasure_dirichletMeasure`,
`map_euclideanFiberSum_dirichletMeasure`, `dirichletMeasure_eq_map_withDensity_dirichletChartPDF`)
and Mathlib's `Kernel.ae_eq_of_compProd_eq`, `memPartition` and `natGeneratingSequence` for
countably generated spaces, and `tendsto_iff_forall_lipschitz_integral_tendsto`.


## Decision, smoothing, testing, and likelihood proofs

- Finite statistical minimax uses Mathlib's real `L²` spaces, Radon–Nikodym integration,
  Markov kernels, compact extreme-value theorem, and `geometric_hahn_banach_open`.
  `CKSD/Inference/FiniteDecision.lean` uses TauCeti's
  `surjective_inclusionInDoubleDual_of_uniformConvexSpace` and
  `isCompact_toWeakSpace_of_isClosed_of_convex_of_isBounded` for weak compactness of
  randomized action probabilities. `CKSD/Inference/ConvexGames.lean` supplies the
  finite-dimensional separation argument.
- Gaussian smoothing and the stochastic-interpolant score identity use Mathlib's
  Schwartz seminorm bounds, differentiation under the integral, and characterization
  of conditional expectation by set integrals. `CKSD/Bayes/GaussianSmoothing.lean`
  uses TauCeti's `SchwartzMap.gaussian`, `stdGaussian_eq_withDensity_norm`, and
  `Measure.map_affine_withDensity` for the Gaussian density and affine change of variables.
- The Holley–Stroock comparison in `CKSD/Bayes/BoundedPerturbation.lean` uses
  Mathlib's measure domination and Bochner integrals, with TauCeti's entropy and
  logarithmic Sobolev predicates. The sharp factor is `exp (b - a)`. The
  unperturbed Bakry–Émery inequality uses TauCeti's Prékopa–Leindler theorem,
  Mathlib's differentiation under the integral, and dominated convergence.
  Logarithmic regularization and smooth cutoffs extend the interpolation
  inequality to the stated smooth test functions; the sharp constant is `1/m`.
- Quantitative evidence concentration uses Mathlib's `variance_sum_pi` and
  `meas_ge_le_variance_div_sq`, together with Tonelli's theorem and change of
  density. The shrinking-ball estimate is in `CKSD/Bayes/EvidenceConcentration.lean`.
- Hellinger geometry uses Statlib's Radon–Nikodym affinity formula for
  `sqHellinger`, Mathlib's Radon–Nikodym chain rules, and the Cauchy–Schwarz
  inequality for integrals. Robust Hellinger-ball testing uses TauCeti's Bernstein
  inequality `iIndepFun.measureReal_sum_ge_le_of_ae_le`. The posterior-contraction
  proof combines these tests with finite sieve covers, the evidence estimate,
  and a change-of-measure bound on the tested posterior numerator.
- Gaussian-mixture identifiability uses TauCeti's
  `mgf_inner_multivariateGaussianMixtureMeasure`. The local linear-independence
  proof uses Mathlib's `MvPolynomial.funext`, symmetric linear maps, finite-support
  coefficients, and real exponential limits to separate Gaussian parameter pairs.
- The spectral characterization of characteristic kernels uses Mathlib's
  `Measure.ext_of_charFun`, `continuous_charFun`, Schwartz Fourier inversion,
  and `ContDiffBump`, with TauCeti's
  `fourierInv_eq_re_of_map_neg_eq_conj` and
  `Probability.integral_withDensity_ofReal`. The spectral-gap direction constructs
  two distinct probability laws from a real even Fourier bump.
- Canonical GLM deviance asymptotics use the local convex quadratic approximation
  and minimum-value convergence, Mathlib's central limit theorem and orthogonal
  projections, and TauCeti's Gaussian projection and chi-squared laws. The generic
  convex-likelihood argument is in `CKSD/LinearModels/ConvexLikelihood.lean`.

- The simple covariance-eigenvalue central limit law combines TauCeti's operator Weyl
  inequality and population-gap eigenvector alignment from
  `TauCeti/Analysis/InnerProductSpace/YuWangSamworth/Eigenvector.lean`, following
  Yu, Wang and Samworth, *Biometrika* 102 (2015), Corollary 1. That imported module
  records its Kitware implementation provenance. Local entrywise covariance estimates
  and Mathlib's scalar central limit theorem give the first-order stochastic expansion;
  TauCeti's Gaussian centered fourth moment gives the variance `2 λ²`.
- The stochastic-approximation APT proof uses Mathlib's square-integrable martingale
  convergence theorem, conditional expectations, summable `L²` increments, and integral
  Gronwall estimates. Predictable clipping localizes the noise without an initial
  second-moment assumption. The local interpolation and approximate-ODE estimates are
  in `CKSD/Bayes/StochasticApproximationPath.lean`.
- Mean-field coupling uniqueness uses Mathlib's Fubini theorem and TauCeti's integral
  Gronwall estimate. The continuous-path forcing-map inverse uses Mathlib's measurable
  embedding theorem for continuous injective maps between Polish spaces. Countable
  Brownian-coordinate laws use Mathlib's Brownian finite-dimensional distribution API.
  Quantitative interaction fluctuations use TauCeti's Hilbert-space Bienaymé identity
  `integral_norm_sum_sq_of_pairwise_indepFun` from `Probability/Moments/SampleMean.lean`,
  separating the self-interaction term. Deterministic averaged coupling, Fubini, and
  extended-integral bounds give the uniform mean-square estimate.
- Energy distance uses TauCeti's layer-cake integral and Gaussian absolute first moment,
  with Mathlib's CDF right continuity, Fubini theorem, and uniqueness of characteristic
  functions. Gaussian projection averaging reduces finite-dimensional norm distances
  to the one-dimensional CDF identity, including zero-dimensional spaces.
- Distance covariance uses TauCeti's positive definite kernel feature maps and kernel
  mean embeddings. Local double-centering algebra uses Mathlib's product integrals and
  square-integrable products. Separation with fixed marginals follows from bounded
  weighted marginal measures, the energy-distance criterion, and measure equality on
  rectangles.

- Exact Wilks determinant-ratio laws use TauCeti's Wishart density agreement,
  convolution and determinant moments, its Beta moments, and
  `TauCeti.Measure.ext_of_forall_integral_pow_eq_of_support` from
  `TauCeti/Probability/Moments/CompactDeterminacy.lean`. The local determinant
  tilt changes the first Wishart degree by twice the natural moment order.
- The nonlinear path-space construction uses Mathlib's complete Bochner `L¹`
  spaces, continuous-map norms and Banach fixed points. The deterministic
  Picard argument adapts Mathlib's Picard–Lindelöf factorial estimates and
  TauCeti's Carathéodory iteration argument; stability and uniqueness use
  TauCeti's integral Grönwall theorem and first-Wasserstein coupling bounds.
  Countable rational-coordinate reconstruction gives measurable continuous
  path versions and consistent compact paths glue to a global process.
  Integrable Brownian forcing bounds use TauCeti's geometric Brownian
  running-maximum estimates applied to the positive and negative exponentials.
- Growing-shape Beta limits use Mathlib's log-convexity and recurrence of Gamma,
  TauCeti's compact moment convergence theorem, and Mathlib's CDF criterion
  for weak convergence. Natural-shift Gamma multiplication uses TauCeti's
  `Real.prod_range_add_mul_Gamma` and Mathlib's finite-product equivalence
  `finProdFinEquiv`.
- Spherical Wishart trace laws use TauCeti's matrix moment-generating function,
  Gamma transform, and `TauCeti.Measure.ext_of_mgf`. Mathlib's finite AM–GM
  inequality bounds the determinant-to-trace ratio. Determinant tilting,
  inverse Gamma moments, and the natural-shift Gamma multiplication identity
  identify its Beta-product moments, including the scale normalization.
- General propagation of chaos uses TauCeti's
  `tendsto_wassersteinEDist_empiricalMeasure_ae` from
  `TauCeti/MeasureTheory/OptimalTransport/Wasserstein/Empirical.lean` on the
  space of continuous paths. Mathlib supplies convergence of laws under
  almost-sure convergence and independence of finite coordinate families.
  The local synchronous coupling estimate bounds every particle path by the
  empirical first-Wasserstein discrepancy of independent nonlinear paths.
- The Gaussian block-independence likelihood-ratio proof follows Muirhead,
  *Aspects of Multivariate Statistical Theory*, Theorems 11.2.3–11.2.4,
  printed pp. 532–534 (physical PDF pp. 558–560 in the local 2005 copy).
  A natural determinant tilt, independent Wishart diagonal blocks, and
  inverse determinant moments identify the Beta-product law. Anderson,
  *An Introduction to Multivariate Statistical Analysis*, third edition,
  Theorems 9.3.1–9.3.3, printed pp. 387–388 (PDF pp. 405–406), supplies
  a complementary regression interpretation. TauCeti supplies Gaussian
  block independence, Wishart moments, compact moment determinacy, and
  multivariate Gamma identities.
- The conditional-kernel step of the LAN representation argument follows
  van der Vaart, *Asymptotic Statistics*, Theorem 7.10 and its proof,
  printed pp. 98–99 (PDF pp. 114–115). The local
  `Asymptotics/RepresentationKernel.lean` proves the common randomization
  kernel for a family of tilted joint laws using Mathlib's conditional
  kernels, disintegration and weighted kernel products. The full LAN
  representation theorem remains admitted.

- The strongly convex ULA Wasserstein bound uses the coupling principle in
  Chewi, *Log-Concave Sampling*, August 20, 2026, Theorem 4.1.2, with the
  invariant mechanical Hamiltonian comparison of Section 5.2.1, printed
  p. 147 (PDF p. 159), and Exercise 5.5, printed p. 170 (PDF p. 182).
  TauCeti supplies Hamiltonian flows and their symplectic variation,
  determinant one for alternating-form isometries, Gaussian densities and
  moments, and Wasserstein push-forward bounds. Mathlib supplies Jacobian
  change of variables, integral inequalities, and exponential estimates.
  The proof has universal constants `c = 1/4`, `C = 12`, treats infinite
  initial Wasserstein distances, and adds no moment assumptions.
- Particle oscillation contraction, normalized semigroup telescoping and
  conditional sampling estimates follow Del Moral, *Feynman–Kac Formulae*
  (2004), Proposition 4.3.3, Lemma 7.3.3 and Theorem 7.4.4, printed
  pp. 140–142, 223–225 and 244–246. Mathlib supplies Hoeffding's
  sub-Gaussian bound, independent sums, product integration, and real
  `lpNorm` inequalities. An exponential domination estimate controls
  arbitrary real moment orders with an explicit factorial constant.
- Mean-field comparison uses TauCeti's continuity-equation endpoint identity,
  first-Wasserstein action bound, globally Lipschitz ODE flows and smooth
  Lipschitz approximation. Smooth approximate backward tests identify
  narrowly continuous weak solutions without assuming moments of the
  comparison curve. Mathlib supplies characteristic-function uniqueness,
  Hahn–Banach supporting functionals and Bochner integration; TauCeti's
  Kantorovich–Rubinstein weak duality gives the vector-valued expectation
  bound used for the interaction drift.
  The characteristic interpretation follows Carmona–Delarue, *Probabilistic
  Theory of Mean Field Games with Applications*, Volume I, Theorem 6.49,
  printed pp. 608–609 (PDF pp. 626–627). Its general measurable-velocity
  superposition theorem is not asserted locally: the bounded Lipschitz
  representation needed here is proved through backward transport tests.
  Iid bounded-speed characteristic paths and synchronous particle coupling,
  followed by a countable intersection of integer horizons, give the training
  empirical limit simultaneously on every compact nonnegative time interval.

- The LAN representation theorem follows van der Vaart, *Asymptotic Statistics*,
  Theorem 7.10, printed pp. 98–99 (PDF pp. 114–115). Joint weak-limit extraction
  uses Mathlib and TauCeti tightness and compactness. Gaussian likelihood tilts
  use TauCeti's density, affine image, and moment-generating-function formulas.
  The likelihood-transfer proof retains singular alternatives: its normalized
  limit forces the missing Radon–Nikodym mass to vanish. The metric Slutsky
  adapter for varying spaces and laws adapts Rémy Degenne's Mathlib
  `MeasureTheory.tendstoInDistribution_of_tendstoInMeasure_sub`, retaining its
  Apache 2.0 attribution in `Asymptotics/LANApproximation.lean`.
- Each discrete JKO step for a continuous nonnegative potential has a unique
  minimizer. The direct method and ordinary-mixture uniqueness follow the
  argument of Santambrogio, *Optimal Transport for Applied Mathematicians*,
  Proposition 8.5, printed p. 294 (PDF p. 318). That passage uses a compact
  domain; on Euclidean space the local proof uses Gaussian entropy reference
  measures and narrow lower semicontinuity along second-moment-bounded
  families. TauCeti supplies abstract resolvent existence, entropy change of
  reference, strict KL mixture convexity, and Wasserstein mixture convexity.
  This discrete-step result does not assert convergence of the full JKO scheme.
- Gaussian location completeness reuses the project's proved exponential-family
  completeness and TauCeti's Gaussian tilt formulas. The kernel convolution
  result is van der Vaart, Proposition 8.4 and Theorem 8.8, printed
  pp. 113–115 (PDF pp. 129–131). That reference gives a Bayesian argument;
  the local proof uses completeness and almost-everywhere kernel identification.
  The local translation-invariance argument is
  the Fubini argument behind Mathlib's regular ergodic group action;
  probability-measure-valued kernels use TauCeti's Giry/Borel and separability
  results. TauCeti's probability-measure extensionality theorem converts
  almost-everywhere equality of fixed-set evaluations to equality of kernels.
- Gaussian Anderson concentration and bowl-shaped-loss domination correspond to
  van der Vaart, Lemma 8.5 and Proposition 8.6, printed pp. 113–114
  (PDF pp. 129–130). The local proof applies TauCeti's Prékopa–Leindler
  central-slice theorem to Gaussian measures, using log-concavity and the
  covariance square-root map. Mathlib's layer-cake formula treats unbounded
  and infinite-valued losses. The convolution-risk corollary averages the
  shift-risk inequality; it does not assume finite moments of the residual law.
- The diffusion regularity lemmas use Mathlib's one-sided derivative and
  undefined-Bochner-integral conventions. They isolate jump trajectories
  with zero right derivatives and scalar components recovering a nonmeasurable
  time coefficient. They are obstruction lemmas, rather than formal
  constructions of complete Gaussian stochastic counterexamples.
- Blackwell's finite-parameter comparison theorem uses the finite-matrix
  separation idea of Blackwell–Girshick, *Theory of Games and Statistical
  Decisions*, Theorem 12.2.2, printed pp. 328–330 (PDF pp. 342–344).
  The general observation-space argument uses bounded likelihood vectors,
  finite quantization and a compact joint-law limit, followed by Mathlib's
  standard-Borel disintegration. Mathlib supplies compactness of finite laws
  of fixed mass on a compact space; TauCeti supplies the weak compactness
  used for finite decision rules. Strasser, *Mathematical Theory of Statistics*,
  Section 55, printed pp. 278–283 (PDF pp. 290–295), distinguishes operator
  randomizations from stochastic-kernel representations. The local proof
  retains an arbitrary measurable source and a standard-Borel target.
- The MALA lower-bound declaration permits choosing the curvature scale
  after the step size and requested accuracy. Its Gaussian construction
  uses an exact acceptance-ratio calculation, a bounded Gaussian noise
  event and a finite-time mass-retention estimate. Conditioning on an
  upper-quartile halfspace gives a four-warm initial law. Gaussian Gibbs
  normalization reuses the local smoothing density and TauCeti's Gaussian
  quantiles. Chewi, *Log-Concave Sampling*, Theorem 7.6.5, printed p. 210
  (PDF p. 222), concerns normalized curvature; that stronger normalization
  is not asserted by this local declaration.
- The semiparametric quadratic-mean hypotheses use a common sigma-finite
  dominating measure, ensuring that the Radon–Nikodym terms represent the
  probability densities. The reference-measure diagnostic lemmas use
  Mathlib's totalized `rnDeriv` and Statlib's displayed QMD definition:
  an atomless law has zero derivative relative to uncountable counting
  measure, and identically zero chosen densities make the bare remainder
  condition vacuous. Only these generic obstructions are formalized;
  the complete Gaussian-path statistical counterexample is not packaged
  as a Lean theorem.
- Wasserstein barycenter first variation follows Panaretos–Zemel, *An Invitation
  to Statistics in Wasserstein Space*, Theorem 3.1.14, printed p. 67
  (PDF p. 78). The local proof differentiates a compact coupling minimum,
  using a quadratic-envelope lemma, coupling lift through measurable maps,
  and Brenier uniqueness. TauCeti supplies optimal plans, gluing, coupling
  compactness and lower semicontinuity under common Lusin sets. This retains
  measurable square-integrable displacement fields without imposing continuity.
