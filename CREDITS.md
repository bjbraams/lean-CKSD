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

- `minimizer_mem_span_of_feature_vectors` uses Mathlib's complete
  finite-dimensional span, orthogonal projection, and norm bounds.
- `ae_tendsto_landscape_sampleAverage` specializes Mathlib's
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
