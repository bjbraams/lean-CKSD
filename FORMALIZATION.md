# CKSD formalization

The public entry point is [CKSD.lean](CKSD.lean). Every project declaration is in
`namespace CKSD` or one of its subnamespaces. The module names follow topics, while
the stable identifiers of [GAPS.md](GAPS.md) connect code to the mathematical catalogue.

There are **756 definitions, abbreviations, structures, and inductive types**
and **1292 theorem statements**: **1080 proved**,
**0 conditional** (the proof is complete but uses an admitted result), and
**212 admitted**. Definitions contain no admissions. A compiled axiom audit
checks that proved results do not depend on `sorryAx`; only the usual Lean classical
axioms occur in their dependency closures.

The index contains all **296 selected gap families**. **294**
have at least one scoped theorem statement and **2** still need
a theorem formulation. All **110 entries** of [GAPS_EASY.md](GAPS_EASY.md)
have at least one scoped statement. This does **not** mean that all their short-derivation
scopes are formalized or proved. Finite-dimensional, finite-class, scalar, deterministic,
or algebraic restrictions in a declaration must be retained when reading its status.

A statement below is linked even when its proof is admitted. **No full-family coverage
classification is inferred from these links.** The mathematical synopsis and the
Mathlib/TauCeti/Statlib coverage counts retain their own meaning and source baseline.

## Modules

- Section 101: [Inference](CKSD/Inference.lean); definitions and results in `CKSD/Inference/`.
- Section 102: [Asymptotics](CKSD/Asymptotics.lean); definitions and results in `CKSD/Asymptotics/`.
- Section 103: [Nonparametric](CKSD/Nonparametric.lean); definitions and results in `CKSD/Nonparametric/`.
- Section 104: [Bayes](CKSD/Bayes.lean); definitions and results in `CKSD/Bayes/`.
- Section 105: [LinearModels](CKSD/LinearModels.lean); definitions and results in `CKSD/LinearModels/`.
- Section 106: [Processes](CKSD/Processes.lean); definitions and results in `CKSD/Processes/`.
- Section 107: [Learning](CKSD/Learning.lean); definitions and results in `CKSD/Learning/`.
- Section 108: [Geometry](CKSD/Geometry.lean); definitions and results in `CKSD/Geometry/`.

The `Basic` modules provide common definitions. The other files contain thematic
definitions and results; direct files under `CKSD/` assemble those modules.
`Suggested101.lean`–`Suggested108.lean` are compatibility import modules.

## Reuse and conventions

Mathlib measures, kernels, conditional expectations, linear maps, projections, categories,
and `Lp` spaces are reused. TauCeti supplies distribution and transport constructions;
Statlib supplies the probability-measure contiguity interface. Some section drafts use
real-moment or measure-valued statistical adapters; their docstrings specify integrability
and normalization conventions. See [CREDITS.md](CREDITS.md) for provenance.

Dependency revisions and the Lean toolchain are recorded in `lakefile.toml`,
`lake-manifest.json`, and `lean-toolchain`. The build output is `.lake/build-CKSD`.

## Validation

Run from the project root:

```sh
lake build > /tmp/cksd-build.log 2>&1
python3 scripts/check_formalization.py
python3 scripts/check_lean_files.py
git diff --check
```

The inventory checker compiles an axiom audit, checks declaration names and source links,
and compares this index and [formalization.json](formalization.json) with the source.
Use `--write` to regenerate the two index files after changes. The individual-file checker
checks every project Lean module with both implicit-variable options disabled.

## Catalogue

### Section 101

- **101.1 Factorization theorem.**
  [CKSD.isSufficientStatistic_iff_exists_factorization](CKSD/Inference/ExponentialFamily.lean#L31) (proved; scope in docstring).
  [CKSD.exists_factorization_of_isSufficientStatistic](CKSD/Inference/Factorization.lean#L213) (proved; scope in docstring).
  [CKSD.isSufficientStatistic_of_factorization](CKSD/Inference/Factorization.lean#L249) (proved; scope in docstring).
- **101.2 Minimal sufficiency.**
  [CKSD.likelihood_ratio_statistic_minimal_sufficient](CKSD/Inference/ExponentialFamily.lean#L198) (proved; scope in docstring).
- **101.4 Structure of a full-rank exponential family.**
  [CKSD.convex_laplace_integrability_domain](CKSD/Inference/ExponentialFamily.lean#L45) (proved; scope in docstring).
  [CKSD.analyticOnNhd_cumulant_and_fderiv_eq_moments](CKSD/Inference/ExponentialFamily.lean#L240) (admitted; scope in docstring).
- **101.5 Completeness in a full-rank exponential family.**
  [CKSD.isCompleteStatistic_exponential_family](CKSD/Inference/ExponentialFamily.lean#L57) (proved; scope in docstring).
- **101.6 Pitman–Koopman–Darmois theorem, monotone form.**
  [CKSD.exists_exponential_family_of_monotone_sufficient_statistics](CKSD/Inference/ExponentialFamily.lean#L226) (admitted; scope in docstring).
- **101.7 Rao–Blackwell theorem.**
  [CKSD.exists_rao_blackwell_estimator](CKSD/Inference/Estimation.lean#L32) (proved; scope in docstring).
- **101.8 Lehmann–Scheffé theorem.**
  [CKSD.ae_eq_of_isCompleteStatistic_of_isUnbiasedEstimator](CKSD/Inference/Estimation.lean#L95) (proved; scope in docstring).
- **101.9 Basu's theorem.**
  [CKSD.indepFun_of_isSufficientStatistic_of_isBoundedlyCompleteStatistic](CKSD/Inference/Estimation.lean#L111) (proved; scope in docstring).
- **101.10 Information inequality.**
  [CKSD.sq_div_information_le_variance](CKSD/Inference/Estimation.lean#L150) (proved; scope in docstring).
- **101.12 Characterization of UMVU estimators.**
  [CKSD.is_minimum_variance_unbiased_iff_covariance_eq_zero](CKSD/Inference/Estimation.lean#L188) (proved; scope in docstring).
- **101.13 Completeness of the order statistic.**
  [CKSD.isSymmetricallyComplete_of_complete_convex_family](CKSD/Inference/Families.lean#L81) (admitted; scope in docstring).
- **101.14 Neyman–Pearson lemma.**
  [CKSD.exists_neyman_pearson_test](CKSD/Inference/Testing.lean#L33) (proved; scope in docstring).
- **101.15 Karlin–Rubin theorem.**
  [CKSD.isUniformlyMostPowerfulTest_of_monotone_likelihood_ratio](CKSD/Inference/Testing.lean#L275) (proved; scope in docstring).
- **101.17 Gaussian sampling distributions.**
  [CKSD.gaussian_sample_mean_residual_laws](CKSD/Inference/Testing.lean#L536) (proved; scope in docstring).
- **101.21 Distribution of order statistics.**
  [CKSD.map_orderStatistics_eq_withDensity](CKSD/Inference/Families.lean#L93) (proved; scope in docstring).
  [CKSD.map_orderStatistic_eq_withDensity](CKSD/Inference/Families.lean#L152) (proved; scope in docstring).
  [CKSD.sorting_permutation_uniform_and_indep](CKSD/Inference/Families.lean#L259) (proved; scope in docstring).
- **101.32 Value of a finite statistical game.**
  [CKSD.exists_statistical_game_saddle_point](CKSD/Inference/Decision.lean#L28) (admitted; scope in docstring).
- **101.37 Complete classes.**
  [CKSD.exists_admissible_bayes_risk_le_of_closed_convex](CKSD/Inference/Decision.lean#L39) (proved; scope in docstring).
- **101.39 Hunt–Stein theorem, compact form.**
  [CKSD.exists_equivariant_rule_risk_eq_average](CKSD/Inference/Decision.lean#L131) (proved; scope in docstring).
- **101.40 Pitman estimator of location.**
  [CKSD.pitmanEstimator_minimum_equivariant_risk_of_nonneg](CKSD/Inference/Families.lean#L560) (proved; scope in docstring).
  [CKSD.pitmanEstimator_minimum_equivariant_risk](CKSD/Inference/Families.lean#L649) (proved; scope in docstring).
- **101.42 Mean parameterization.**
  [CKSD.exists_analytic_inverse_exponential_family_mean](CKSD/Inference/Decision.lean#L207) (admitted; scope in docstring).
- **101.43 Conditional exponential families.**
  [CKSD.exists_kernel_conditional_exponential_family](CKSD/Inference/ConditionalExponentialFamily.lean#L245) (proved; scope in docstring).
- **101.45 Two-sided tests in a one-parameter exponential family.**
  [CKSD.isUniformlyMostPowerfulUnbiasedTest_of_two_tail_moment_constraints](CKSD/Inference/InvariantTesting.lean#L219) (proved; scope in docstring).
- **101.46 Conditional tests with a nuisance parameter.**
  [CKSD.isUniformlyMostPowerfulUnbiasedTest_conditional_two_sided](CKSD/Inference/ConditionalExponentialFamily.lean#L307) (admitted; scope in docstring).
  [CKSD.isUniformlyMostPowerfulUnbiasedTest_conditional_one_sided](CKSD/Inference/ConditionalExponentialFamily.lean#L327) (admitted; scope in docstring).
- **101.47 Generalized Neyman–Pearson lemma.**
  [CKSD.integral_le_of_generalized_neyman_pearson](CKSD/Inference/InvariantTesting.lean#L30) (proved; scope in docstring).
- **101.49 Neyman structure.**
  [CKSD.condExp_eq_const_of_similar_test](CKSD/Inference/InvariantTesting.lean#L402) (proved; scope in docstring).
- **101.50 Uniformly most powerful tests of a two-sided hypothesis.**
  [CKSD.exists_ump_interval_test](CKSD/Inference/Families.lean#L701) (admitted; scope in docstring).
- **101.53 Karlin–Rubin complete class theorem.**
  [CKSD.exists_one_sided_test_risk_le](CKSD/Inference/Families.lean#L715) (proved; scope in docstring).
- **101.54 Least favorable distributions.**
  [CKSD.most_powerful_of_mixture_null](CKSD/Inference/Families.lean#L843) (proved; scope in docstring).
- **101.55 Reduction by a maximal invariant.**
  [CKSD.invariant_iff_factors_through_maximal_invariant](CKSD/Inference/InvariantTesting.lean#L425) (proved; scope in docstring).
- **101.56 Normal tests as uniformly most powerful invariant tests.**
  [CKSD.mean_scale_ratio_eq_iff](CKSD/Inference/Families.lean#L867) (proved; scope in docstring).
- **101.57 Estimation of a normal mean.**
  [CKSD.james_stein_risk_eq_and_lt](CKSD/Inference/Gaussian.lean#L32) (admitted; scope in docstring).
- **101.58 Blyth's method.**
  [CKSD.isAdmissibleRisk_of_blyth](CKSD/Inference/Families.lean#L881) (proved; scope in docstring).
- **101.60 Scheffé's method.**
  [CKSD.scheffe_contrast_supremum](CKSD/Inference/Gaussian.lean#L186) (proved; scope in docstring).
- **101.62 Blackwell's theorem.**
  [CKSD.isMoreInformative_iff_isGarbling](CKSD/Inference/Families.lean#L947) (admitted; scope in docstring).
- **101.64 Stein's identity and unbiased risk estimation.**
  [CKSD.gaussian_integration_by_parts](CKSD/Inference/Gaussian.lean#L62) (proved; scope in docstring).
- **101.69 Existence of an exponential-family maximum.**
  [CKSD.exists_exponential_family_mle_iff_mem_interior_convex_support](CKSD/Inference/Gaussian.lean#L149) (admitted; scope in docstring).
  [CKSD.exponential_family_mle_unique_and_mean_eq](CKSD/Inference/Gaussian.lean#L166) (admitted; scope in docstring).

### Section 102

- **102.1 Delta method.**
  [CKSD.tendstoInDistribution_delta_method](CKSD/Asymptotics/Estimators.lean#L287) (proved; scope in docstring).
- **102.2 Consistency of maximum likelihood.**
  [CKSD.tendstoInProbabilityConst_mle_of_compact](CKSD/Asymptotics/MEstimators.lean#L176) (proved; scope in docstring).
- **102.3 Asymptotic normality of maximum likelihood.**
  [CKSD.mle_asymptotic_linearization_and_normality](CKSD/Asymptotics/Estimators.lean#L946) (proved; scope in docstring).
- **102.4 Z-estimators.**
  [CKSD.z_estimator_asymptotic_linearization_and_normality](CKSD/Asymptotics/Estimators.lean#L1992) (proved; scope in docstring).
- **102.6 Sample quantiles.**
  [CKSD.tendstoInDistribution_sampleQuantile](CKSD/Asymptotics/Estimators.lean#L1537) (proved; scope in docstring).
- **102.7 Bahadur representation of sample quantiles.**
  [CKSD.tendstoInProbabilityConst_bahadur_remainder](CKSD/Asymptotics/Estimators.lean#L1460) (proved; scope in docstring).
- **102.8 Nondegenerate $U$-statistics.**
  [CKSD.tendstoInDistribution_uStatistic_of_nondegenerate](CKSD/Asymptotics/Estimators.lean#L310) (admitted; scope in docstring).
- **102.11 Likelihood-ratio, Wald, and score tests.**
  [CKSD.tendstoWeakly_likelihoodRatio_wald_score_chiSquared](CKSD/Asymptotics/LikelihoodTests.lean#L662) (proved; scope in docstring).
  [CKSD.tendstoWeakly_likelihoodRatio_wald_score_noncentralChiSquared](CKSD/Asymptotics/LikelihoodTests.lean#L745) (proved; scope in docstring).
- **102.12 Contiguity.**
  [CKSD.isContiguous_of_integral_likelihood_ratio_limit_eq_one](CKSD/Asymptotics/Experiments.lean#L131) (proved; scope in docstring).
- **102.13 Local asymptotic normality of smooth models.**
  [CKSD.local_asymptotic_normality_of_differentiable_in_quadratic_mean](CKSD/Asymptotics/Experiments.lean#L300) (proved; scope in docstring).
- **102.14 Le Cam's third lemma.**
  [CKSD.tendstoWeakly_of_log_likelihood_ratio](CKSD/Asymptotics/Experiments.lean#L258) (proved; scope in docstring).
- **102.15 Asymptotic representation theorem.**
  [CKSD.exists_gaussian_shift_kernel_of_local_limits](CKSD/Asymptotics/Framework.lean#L94) (admitted; scope in docstring).
- **102.16 Convolution theorem.**
  [CKSD.exists_convolution_of_isRegularEstimator](CKSD/Asymptotics/Framework.lean#L108) (admitted; scope in docstring).
- **102.17 Local asymptotic minimax theorem.**
  [CKSD.gaussian_risk_le_local_asymptotic_minimax](CKSD/Asymptotics/Framework.lean#L120) (admitted; scope in docstring).
- **102.21 Pitman efficiency and Noether's theorem.**
  [CKSD.tendsto_local_normal_power](CKSD/Asymptotics/Experiments.lean#L274) (proved; scope in docstring).
- **102.23 Consistency of $M$-estimators.**
  [CKSD.tendstoInProbabilityConst_m_estimator](CKSD/Asymptotics/AsymptoticTheory.lean#L38) (proved; scope in docstring).
- **102.24 Asymptotic normality of $M$-estimators.**
  [CKSD.m_estimator_asymptotic_linearization_and_normality](CKSD/Asymptotics/MEstimators.lean#L311) (admitted; scope in docstring).
- **102.25 Rate of convergence of $M$-estimators.**
  [CKSD.isBoundedInProbability_rate_m_estimator](CKSD/Asymptotics/RatesOfConvergence.lean#L52) (proved; scope in docstring).
- **102.28 Functional delta method.**
  [CKSD.tendstoInDistribution_of_hasHadamardFDerivAt](CKSD/Asymptotics/Framework.lean#L134) (proved; scope in docstring).
- **102.29 Hoeffding decomposition.**
  [CKSD.uStatistic_hoeffding_decomposition_and_variance](CKSD/Asymptotics/AsymptoticTheory.lean#L74) (admitted; scope in docstring).
- **102.30 Degenerate quadratic $U$-statistics.**
  [CKSD.tendstoInDistribution_uStatistic_of_finite_rank_degenerate](CKSD/Asymptotics/AsymptoticTheory.lean#L90) (admitted; scope in docstring).
- **102.31 Pearson's multinomial tests.**
  [CKSD.tendstoInDistribution_pearson_statistic](CKSD/Asymptotics/AsymptoticTheory.lean#L104) (admitted; scope in docstring).
- **102.33 Argmax theorem.**
  [CKSD.tendstoInProbabilityConst_argmax_of_compact](CKSD/Asymptotics/AsymptoticTheory.lean#L115) (proved; scope in docstring).
- **102.34 Semiparametric convolution bound.**
  [CKSD.exists_convolution_of_isRegularAlongPaths](CKSD/Asymptotics/Semiparametric.lean#L80) (admitted; scope in docstring).
  [CKSD.isRegularAlongPaths_gaussian_iff_asymptotically_linear](CKSD/Asymptotics/Semiparametric.lean#L102) (admitted; scope in docstring).
- **102.39 Cross-fitted estimation of a missing mean.**
  [CKSD.crossFittedAverage_missingMean_asymptotically_linear](CKSD/Asymptotics/Semiparametric.lean#L140) (admitted; scope in docstring).
- **102.41 Adaptive estimation of a center of symmetry.**
  [CKSD.efficientScore_locationScore_eq](CKSD/Asymptotics/Semiparametric.lean#L244) (proved; scope in docstring).
  [CKSD.exists_adaptive_estimator_center_of_symmetry](CKSD/Asymptotics/Semiparametric.lean#L303) (admitted; scope in docstring).
- **102.44 $M$-estimators and the Huber minimax property.**
  [CKSD.integral_huberScore_sq_le](CKSD/Asymptotics/HigherOrder.lean#L158) (proved; scope in docstring).
- **102.48 Asymptotics of regression $M$-estimators.**
  [CKSD.regression_m_estimator_asymptotic_linearization_and_normality](CKSD/Asymptotics/MEstimators.lean#L356) (admitted; scope in docstring).
- **102.49 One-term Edgeworth expansion.**
  [CKSD.uniform_edgeworth_expansion](CKSD/Asymptotics/HigherOrder.lean#L257) (admitted; scope in docstring).
- **102.50 Edgeworth expansion for smooth functions of means.**
  [CKSD.exists_edgeworth_expansion_smooth_function_of_means](CKSD/Asymptotics/Expansions.lean#L40) (admitted; scope in docstring).
- **102.51 Bootstrap of the mean.**
  [CKSD.tendstoInProbabilityConst_bootstrap_mean_kolmogorovDistance](CKSD/Asymptotics/HigherOrder.lean#L271) (admitted; scope in docstring).
- **102.52 Bootstrap of the empirical distribution function.**
  [CKSD.tendstoInProbability_bootstrapBoundedLipschitzDistance](CKSD/Asymptotics/Bootstrap.lean#L66) (admitted; scope in docstring).
- **102.55 Saddlepoint approximation.**
  [CKSD.saddlepoint_approximation_sampleAverage_density](CKSD/Asymptotics/Expansions.lean#L66) (admitted; scope in docstring).
- **102.58 Čencov's theorem.**
  [CKSD.fisherRaoMetric_congruent_embedding](CKSD/Asymptotics/Framework.lean#L276) (proved; scope in docstring).
- **102.60 Second-order accuracy of the studentized bootstrap.**
  [CKSD.studentized_bootstrap_mean_second_order_accuracy](CKSD/Asymptotics/Bootstrap.lean#L85) (admitted; scope in docstring).

### Section 103

- **103.1 Kolmogorov–Smirnov statistic.**
  [CKSD.measure_kolmogorovSmirnovStatistic_gt_le](CKSD/Nonparametric/Estimation.lean#L30) (admitted; scope in docstring).
- **103.4 Kernel density asymptotics.**
  [CKSD.tendstoInDistribution_kernelDensityEstimator](CKSD/Nonparametric/Estimation.lean#L39) (admitted; scope in docstring).
- **103.5 Universal $L^1$ consistency.**
  [CKSD.ae_tendsto_integral_abs_kernelDensityEstimator_sub](CKSD/Nonparametric/Estimation.lean#L59) (admitted; scope in docstring).
- **103.7 Stone's theorem.**
  [CKSD.tendsto_nadarayaWatson_prediction_error_probability](CKSD/Nonparametric/SmoothingRates.lean#L33) (admitted; scope in docstring).
- **103.8 Representer theorem.**
  [CKSD.minimizer_mem_span_of_feature_vectors](CKSD/Nonparametric/Estimation.lean#L71) (proved; scope in docstring).
- **103.9 Pinsker's theorem and the Sobolev rate.**
  [CKSD.tendsto_gaussianSequenceMinimaxRisk_div_linear](CKSD/Nonparametric/Models.lean#L55) (admitted; scope in docstring).
- **103.11 Grenander estimator.**
  [CKSD.grenanderEstimator_isMaximumLikelihood](CKSD/Nonparametric/Grenander.lean#L450) (proved; scope in docstring).
  [CKSD.tendstoInDistribution_grenanderEstimator](CKSD/Nonparametric/Grenander.lean#L820) (admitted; scope in docstring).
- **103.14 Score-generating functions and locally most powerful rank tests.**
  [CKSD.linear_rank_statistic_mean_and_variance](CKSD/Nonparametric/Estimation.lean#L147) (proved; scope in docstring).
- **103.17 Cramér–von Mises and two-sample Kolmogorov–Smirnov limits.**
  [CKSD.map_cramerVonMisesStatistic_eq_uniform](CKSD/Nonparametric/GoodnessOfFit.lean#L70) (proved; scope in docstring).
  [CKSD.map_twoSampleKolmogorovSmirnovStatistic_eq_uniform](CKSD/Nonparametric/GoodnessOfFit.lean#L233) (proved; scope in docstring).
- **103.22 Hölder regression rates.**
  [CKSD.holderRegressionMinimaxRisk_bounds](CKSD/Nonparametric/SmoothingRates.lean#L85) (admitted; scope in docstring).
  [CKSD.fixedDesignLocalConstant_risk_le](CKSD/Nonparametric/SmoothingRates.lean#L202) (proved; scope in docstring).
- **103.26 Minimax rates of density estimation.**
  [CKSD.finiteKernelDensityEstimator_risk_le](CKSD/Nonparametric/SmoothingRates.lean#L498) (proved; scope in docstring).
  [CKSD.holderDensityPointwiseMinimaxRisk_lower_bound](CKSD/Nonparametric/SmoothingRates.lean#L642) (admitted; scope in docstring).
- **103.27 Risk of isotonic regression.**
  [CKSD.existsUnique_isIsotonicRegressionEstimator](CKSD/Nonparametric/ShapeAndSelection.lean#L55) (proved; scope in docstring).
  [CKSD.isIsotonicRegressionEstimator_isotonicLeastSquares](CKSD/Nonparametric/ShapeAndSelection.lean#L183) (proved; scope in docstring).
  [CKSD.isotonicGaussianRisk_le](CKSD/Nonparametric/ShapeAndSelection.lean#L296) (admitted; scope in docstring).
  [CKSD.isotonicGaussianMinimaxRisk_lower_bound](CKSD/Nonparametric/ShapeAndSelection.lean#L306) (admitted; scope in docstring).
- **103.28 Log-concave maximum likelihood.**
  [CKSD.existsUnique_isLogConcaveProjection](CKSD/Nonparametric/LogConcave.lean#L81) (admitted; scope in docstring).
  [CKSD.existsUnique_logConcaveMLE_tent](CKSD/Nonparametric/LogConcave.lean#L95) (admitted; scope in docstring).
  [CKSD.logConcaveMLE_hellingerRisk_le](CKSD/Nonparametric/LogConcave.lean#L106) (admitted; scope in docstring).
  [CKSD.logConcave_minimax_hellingerRisk_lower_bound](CKSD/Nonparametric/LogConcave.lean#L117) (admitted; scope in docstring).
- **103.29 Karhunen–Loève expansion and the Hilbertian central limit theorem.**
  [CKSD.tendstoInDistribution_hilbert_sampleAverage](CKSD/Nonparametric/HighDimensional.lean#L30) (admitted; scope in docstring).
- **103.30 Principal components of the empirical covariance.**
  [CKSD.leading_empirical_covariance_eigenvalue_asymptotics](CKSD/Nonparametric/EmpiricalCovariance.lean#L43) (admitted; scope in docstring).
  [CKSD.isBoundedInProbability_leading_empirical_eigenvector_error](CKSD/Nonparametric/EmpiricalCovariance.lean#L67) (admitted; scope in docstring).
- **103.31 Optimality of functional principal components.**
  [CKSD.pca_reconstruction_risk_bound](CKSD/Nonparametric/HighDimensional.lean#L59) (proved; scope in docstring).
- **103.33 Sparse minimax rate.**
  [CKSD.sparseGaussianMinimaxRisk_bounds](CKSD/Nonparametric/Models.lean#L120) (admitted; scope in docstring).
- **103.34 Lasso under compatibility.**
  [CKSD.lasso_cone_and_error_bounds](CKSD/Nonparametric/HighDimensional.lean#L180) (proved; scope in docstring).
- **103.35 Penalized model selection.**
  [CKSD.selectedProjectionRisk_oracle_bound](CKSD/Nonparametric/ShapeAndSelection.lean#L334) (admitted; scope in docstring).
- **103.37 Benjamini–Hochberg procedure.**
  [CKSD.benjamini_hochberg_false_discovery_rate_le](CKSD/Nonparametric/HighDimensional.lean#L421) (proved; scope in docstring).
- **103.38 Tracy–Widom law and spiked covariance.**
  [CKSD.tendsto_largestSampleCovarianceEigenvalue_tracyWidom](CKSD/Nonparametric/TracyWidom.lean#L71) (admitted; scope in docstring).
  [CKSD.ae_tendsto_largestEigenvalue_spiked_subcritical](CKSD/Nonparametric/TracyWidom.lean#L92) (admitted; scope in docstring).
  [CKSD.ae_tendsto_largestEigenvalue_spiked_supercritical](CKSD/Nonparametric/TracyWidom.lean#L104) (admitted; scope in docstring).
- **103.39 Le Cam's two-point method.**
  [CKSD.le_cam_two_point_lower_bound](CKSD/Nonparametric/LowerBounds.lean#L55) (proved; scope in docstring).
- **103.40 Fano's method.**
  [CKSD.fano_lower_bound](CKSD/Nonparametric/LowerBounds.lean#L130) (proved; scope in docstring).
- **103.45 Varshamov–Gilbert bound.**
  [CKSD.exists_hamming_packing](CKSD/Nonparametric/LowerBounds.lean#L232) (proved; scope in docstring).
- **103.46 Assouad's lemma.**
  [CKSD.assouad_lower_bound](CKSD/Nonparametric/LowerBounds.lean#L348) (proved; scope in docstring).
- **103.48 Restricted nullspace and exact recovery.**
  [CKSD.nullspace_property_iff_basis_pursuit_unique](CKSD/Nonparametric/LowerBounds.lean#L454) (proved; scope in docstring).
  [CKSD.nullspace_property_of_hasRestrictedIsometry](CKSD/Nonparametric/LowerBounds.lean#L575) (proved; scope in docstring).
- **103.49 Stable recovery under restricted isometry.**
  [CKSD.robust_nullspace_property_of_hasRestrictedIsometry](CKSD/Nonparametric/LowerBounds.lean#L1083) (proved; scope in docstring).
  [CKSD.basis_pursuit_error_bound_of_hasRestrictedIsometry](CKSD/Nonparametric/LowerBounds.lean#L1392) (proved; scope in docstring).
- **103.52 Thresholded covariance estimation.**
  [CKSD.norm_thresholded_covariance_sub_le](CKSD/Nonparametric/LowerBounds.lean#L1594) (proved; scope in docstring).
- **103.53 Gaussian graphical model selection.**
  [CKSD.neighbourhoodSelection_graph_recovery](CKSD/Nonparametric/GraphicalModels.lean#L82) (admitted; scope in docstring).
  [CKSD.graphicalLasso_frobenius_error_bound](CKSD/Nonparametric/GraphicalModels.lean#L121) (admitted; scope in docstring).
- **103.54 Perturbation of the leading eigenvector.**
  [CKSD.leading_eigenvector_residual_bound](CKSD/Nonparametric/GoodnessOfFit.lean#L349) (proved; scope in docstring).

### Section 104

- **104.1 Bernstein–von Mises theorem.**
  [CKSD.bernstein_von_mises_normal_location](CKSD/Bayes/Posterior.lean#L208) (admitted; scope in docstring).
- **104.5 Laplace approximation and the BIC.**
  [CKSD.tendsto_laplace_approximation](CKSD/Bayes/Posterior.lean#L388) (proved; scope in docstring).
- **104.10 Highest posterior density regions.**
  [CKSD.volume_highest_density_region_le](CKSD/Bayes/Posterior.lean#L32) (proved; scope in docstring).
- **104.14 Tweedie's formula and Robbins' estimator.**
  [CKSD.normal_posterior_mean_tweedie](CKSD/Bayes/Posterior.lean#L62) (proved; scope in docstring).
  [CKSD.poisson_posterior_mean_eq_mass_ratio](CKSD/Bayes/Posterior.lean#L149) (proved; scope in docstring).
  [CKSD.ae_tendsto_robbins_estimator](CKSD/Bayes/Posterior.lean#L164) (proved; scope in docstring).
- **104.15 Dirichlet process.**
  [CKSD.ae_isDirichletProcessLaw_posterior](CKSD/Bayes/DirichletProcess.lean#L100) (admitted; scope in docstring).
  [CKSD.ae_integral_posterior_eq_polyaPredictiveLaw](CKSD/Bayes/DirichletProcess.lean#L112) (proved; scope in docstring).
  [CKSD.isDirichletProcess_stickBreaking](CKSD/Bayes/DirichletProcess.lean#L140) (admitted; scope in docstring).
- **104.16 Pólya urn scheme and distinct values.**
  [CKSD.integral_distinctObservationCount_polya](CKSD/Bayes/PolyaUrn.lean#L121) (proved; scope in docstring).
  [CKSD.ae_tendsto_distinctObservationCount_div_log_polya](CKSD/Bayes/PolyaUrn.lean#L473) (proved; scope in docstring).
- **104.17 Doob's consistency theorem.**
  [CKSD.ae_isPosteriorConsistent_of_identifiable](CKSD/Bayes/Nonparametric.lean#L70) (admitted; scope in docstring).
- **104.18 Schwartz's theorem.**
  [CKSD.tendstoInProbabilityConst_posterior_compl_of_kl_support](CKSD/Bayes/PosteriorContraction.lean#L47) (admitted; scope in docstring).
- **104.19 Contraction rate of Ghosal, Ghosh, and van der Vaart.**
  [CKSD.exists_posterior_hellinger_contraction](CKSD/Bayes/PosteriorContraction.lean#L71) (admitted; scope in docstring).
- **104.20 Linear inverse problems.**
  [CKSD.minimax_rate_inverseProblem](CKSD/Bayes/InverseProblems.lean#L57) (admitted; scope in docstring).
  [CKSD.tendsto_gaussianSeqPosterior_contraction](CKSD/Bayes/InverseProblems.lean#L404) (proved; scope in docstring).
- **104.22 Metropolis–Hastings.**
  [CKSD.metropolisTransition_stochastic_and_detailed_balance](CKSD/Bayes/MonteCarlo.lean#L30) (proved; scope in docstring).
- **104.24 Central limit theorem for Markov chain Monte Carlo.**
  [CKSD.tendstoInDistribution_finite_markov_chain_sum](CKSD/Bayes/MonteCarlo.lean#L79) (admitted; scope in docstring).
- **104.31 Convergence of Metropolis–Hastings.**
  [CKSD.eventually_abs_metropolisTransition_pow_sub_le](CKSD/Bayes/MonteCarlo.lean#L283) (proved; scope in docstring).
  [CKSD.ae_tendsto_sampleAverage_metropolis](CKSD/Bayes/MonteCarlo.lean#L752) (proved; scope in docstring).
- **104.32 Independence and random-walk samplers.**
  [CKSD.independence_sampler_totalVariationDistance_le](CKSD/Bayes/MonteCarlo.lean#L170) (proved; scope in docstring).
- **104.35 Hamiltonian Monte Carlo.**
  [CKSD.leapfrogStep_iterate_measurePreserving_and_reversible](CKSD/Bayes/MonteCarlo.lean#L221) (proved; scope in docstring).
- **104.37 Invariant measure and gradient-flow structure.**
  [CKSD.integral_langevin_generator_eq_zero](CKSD/Bayes/Dynamics.lean#L30) (proved; scope in docstring).
- **104.38 Contraction under strong convexity.**
  [CKSD.dist_synchronous_langevin_le_exp](CKSD/Bayes/Dynamics.lean#L57) (proved; scope in docstring).
- **104.39 Iteration complexity of Langevin Monte Carlo.**
  [CKSD.exists_ula_iteration_complexity](CKSD/Bayes/LangevinSampling.lean#L73) (admitted; scope in docstring).
- **104.40 Robbins–Monro convergence and averaging.**
  [CKSD.ae_tendsto_robbins_monro](CKSD/Bayes/Dynamics.lean#L122) (admitted; scope in docstring).
- **104.41 Entropy dissipation of Langevin flow.**
  [CKSD.entropy_le_exp_of_log_sobolev](CKSD/Bayes/Dynamics.lean#L141) (proved; scope in docstring).
- **104.43 Jordan–Kinderlehrer–Otto theorem.**
  [CKSD.jko_scheme_tendsto_fokkerPlanck](CKSD/Bayes/FunctionalInequalities.lean#L450) (admitted; scope in docstring).
- **104.44 Convergence of the Langevin diffusion under functional inequalities.**
  [CKSD.poincareInequality_iff_chiSqDiv_langevin_le](CKSD/Bayes/FunctionalInequalities.lean#L45) (admitted; scope in docstring).
  [CKSD.logSobolevInequality_iff_klDiv_langevin_le](CKSD/Bayes/FunctionalInequalities.lean#L57) (admitted; scope in docstring).
  [CKSD.wasserstein_sq_langevin_le_of_logSobolev](CKSD/Bayes/FunctionalInequalities.lean#L69) (admitted; scope in docstring).
  [CKSD.poincareInequality_of_logSobolevInequality](CKSD/Bayes/FunctionalInequalities.lean#L412) (proved; scope in docstring).
  [CKSD.poincare_and_logSobolev_of_bounded_perturbation](CKSD/Bayes/FunctionalInequalities.lean#L420) (admitted; scope in docstring).
- **104.45 Langevin Monte Carlo under a logarithmic Sobolev inequality.**
  [CKSD.exists_klDiv_ula_le_of_logSobolev](CKSD/Bayes/LangevinSampling.lean#L91) (admitted; scope in docstring).
  [CKSD.exists_wasserstein_ula_le_of_stronglyConvex](CKSD/Bayes/LangevinSampling.lean#L106) (admitted; scope in docstring).
- **104.47 Mixing of Metropolis-adjusted Langevin.**
  [CKSD.exists_mala_mixing_time_le](CKSD/Bayes/LangevinSampling.lean#L121) (admitted; scope in docstring).
  [CKSD.exists_mala_mixing_time_ge](CKSD/Bayes/LangevinSampling.lean#L138) (admitted; scope in docstring).
- **104.48 Invariance, contraction, and hypocoercivity.**
  [CKSD.integral_kineticGenerator_eq_zero](CKSD/Bayes/KineticLangevin.lean#L73) (admitted; scope in docstring).
  [CKSD.exists_kineticGenerator_not_symmetric](CKSD/Bayes/KineticLangevin.lean#L83) (admitted; scope in docstring).
  [CKSD.kineticCouplingNorm_synchronous_le](CKSD/Bayes/KineticLangevin.lean#L96) (admitted; scope in docstring).
  [CKSD.exists_kinetic_hypocoercive_decay_of_poincare](CKSD/Bayes/KineticLangevin.lean#L112) (admitted; scope in docstring).
  [CKSD.exists_kinetic_entropic_hypocoercive_decay](CKSD/Bayes/KineticLangevin.lean#L133) (admitted; scope in docstring).
- **104.49 Benaïm's limit-set theorem.**
  [CKSD.ae_isInternallyChainTransitive_limitSet](CKSD/Bayes/StochasticApproximation.lean#L59) (admitted; scope in docstring).
  [CKSD.ae_tendsto_equilibrium_of_chainTransitive](CKSD/Bayes/StochasticApproximation.lean#L81) (admitted; scope in docstring).
  [CKSD.ae_asymptotic_pseudotrajectory](CKSD/Bayes/StochasticApproximation.lean#L104) (admitted; scope in docstring).
- **104.51 Propagation of chaos.**
  [CKSD.exists_unique_mcKeanVlasov_and_particleSystem](CKSD/Bayes/MeanField.lean#L91) (admitted; scope in docstring).
  [CKSD.tendstoWeakly_particle_paths](CKSD/Bayes/MeanField.lean#L107) (admitted; scope in docstring).
- **104.53 Mean-field training.**
  [CKSD.meanFieldRisk_eq](CKSD/Bayes/MeanField.lean#L172) (proved; scope in docstring).
  [CKSD.exists_meanField_limit](CKSD/Bayes/MeanField.lean#L253) (admitted; scope in docstring).
- **104.55 Consistency of the particle filter.**
  [CKSD.tendstoInProbabilityConst_particle_average](CKSD/Bayes/ParticleAndDiffusion.lean#L750) (proved; scope in docstring).
- **104.56 A quantitative interaction model.**
  [CKSD.exists_lintegral_sup_particle_sub_le](CKSD/Bayes/MeanField.lean#L132) (admitted; scope in docstring).
- **104.58 Unbiased particle likelihood.**
  [CKSD.integral_particleLikelihood_eq](CKSD/Bayes/ParticleAndDiffusion.lean#L229) (proved; scope in docstring).
- **104.59 Central limit theorem for Feynman–Kac particle models.**
  [CKSD.tendstoInDistribution_particle_average](CKSD/Bayes/ParticleLimits.lean#L45) (admitted; scope in docstring).
  [CKSD.tendstoInDistribution_particle_likelihood](CKSD/Bayes/ParticleLimits.lean#L58) (admitted; scope in docstring).
- **104.60 Uniform-in-time particle approximation.**
  [CKSD.exists_uniform_particle_moment_bound](CKSD/Bayes/ParticleLimits.lean#L72) (admitted; scope in docstring).
- **104.63 Anderson's time reversal and the probability-flow equation.**
  [CKSD.probabilityFlow_isContinuityEquation_and_map](CKSD/Bayes/DiffusionModels.lean#L48) (admitted; scope in docstring).
- **104.64 Score matching.**
  [CKSD.score_matching_risk_identity](CKSD/Bayes/Dynamics.lean#L173) (proved; scope in docstring).
- **104.68 Score error and total variation.**
  [CKSD.totalVariationDistance_map_le_sqrt_klDiv](CKSD/Bayes/TestingBounds.lean#L23) (proved; scope in docstring).
- **104.75 Convergence of diffusion sampling under a second-moment assumption.**
  [CKSD.klDiv_ddpmLaw_le](CKSD/Bayes/DiffusionModels.lean#L98) (admitted; scope in docstring).
  [CKSD.ddpm_geometric_schedule](CKSD/Bayes/DiffusionModels.lean#L117) (proved; scope in docstring).
  [CKSD.ddpm_parameter_choice](CKSD/Bayes/DiffusionModels.lean#L183) (proved; scope in docstring).
- **104.76 A family of diffusions with prescribed marginals.**
  [CKSD.isFokkerPlanckSolution_add_score_of_continuityEquation](CKSD/Bayes/DiffusionModels.lean#L306) (proved; scope in docstring).
  [CKSD.map_marginalPreservingDiffusion](CKSD/Bayes/DiffusionModels.lean#L397) (admitted; scope in docstring).
  [CKSD.stochasticInterpolant_score_and_velocity](CKSD/Bayes/DiffusionModels.lean#L423) (admitted; scope in docstring).
- **104.77 Half-bridges and iterative proportional fitting.**
  [CKSD.map_half_bridge](CKSD/Bayes/Bridges.lean#L38) (proved; scope in docstring).
  [CKSD.klDiv_half_bridge](CKSD/Bayes/Bridges.lean#L45) (proved; scope in docstring).
  [CKSD.eq_half_bridge_of_minimum_entropy](CKSD/Bayes/Bridges.lean#L52) (proved; scope in docstring).
  [CKSD.klDiv_bridgeIterate_step](CKSD/Bayes/Bridges.lean#L61) (proved; scope in docstring).

### Section 105

- **105.1 Gauss–Markov theorem.**
  [CKSD.variance_projection_le_of_unbiased](CKSD/LinearModels/Regression.lean#L64) (proved; scope in docstring).
- **105.2 Normal sampling theory.**
  [CKSD.gaussian_projection_residual_law_and_indepFun](CKSD/LinearModels/Regression.lean#L90) (admitted; scope in docstring).
- **105.3 Asymptotics of the generalised linear model.**
  [CKSD.tendstoInDistribution_canonicalGLM_root](CKSD/LinearModels/GLMAsymptotics.lean#L61) (admitted; scope in docstring).
  [CKSD.tendstoInDistribution_canonicalGLM_deviance](CKSD/LinearModels/GLMAsymptotics.lean#L92) (admitted; scope in docstring).
- **105.5 Quantile regression.**
  [CKSD.minimizes_expectedQuantileCheckLoss_iff](CKSD/LinearModels/RegressionLimits.lean#L77) (proved; scope in docstring).
  [CKSD.tendstoInDistribution_quantile_regression](CKSD/LinearModels/RegressionLimits.lean#L230) (admitted; scope in docstring).
- **105.6 Finite normal mixtures.**
  [CKSD.gaussianMixtureModel_identifiable](CKSD/LinearModels/Mixtures.lean#L79) (admitted; scope in docstring).
  [CKSD.gaussianMixtureModel_logLikelihood_unbounded](CKSD/LinearModels/Mixtures.lean#L88) (proved; scope in docstring).
- **105.10 Exact tests of nested linear models.**
  [CKSD.nested_gaussian_projection_fisher_law](CKSD/LinearModels/Regression.lean#L102) (admitted; scope in docstring).
- **105.15 Distribution of quadratic forms.**
  [CKSD.indepFun_matrixQuadraticForm_iff](CKSD/LinearModels/Regression.lean#L120) (admitted; scope in docstring).
- **105.16 Optimality of the $F$ test.**
  [CKSD.map_nestedFStatistic_eq_noncentralF](CKSD/LinearModels/FTest.lean#L51) (admitted; scope in docstring).
  [CKSD.strictMono_noncentralF_upper_tail](CKSD/LinearModels/FTest.lean#L72) (admitted; scope in docstring).
  [CKSD.fTest_isUniformlyMostPowerful_invariant](CKSD/LinearModels/FTest.lean#L82) (admitted; scope in docstring).
- **105.22 Wishart distribution and Hotelling's $T^2$.**
  [CKSD.gaussian_sampleMean_scatterMatrix_wishart_and_hotelling](CKSD/LinearModels/Multivariate.lean#L35) (admitted; scope in docstring).
- **105.23 Wilks's lambda.**
  [CKSD.map_wilksLambda_wishart_eq_beta_product](CKSD/LinearModels/MultivariateTests.lean#L79) (admitted; scope in docstring).
- **105.24 Principal component eigenvalues.**
  [CKSD.tendstoInDistribution_gaussian_sample_covariance_eigenvalue](CKSD/LinearModels/MultivariateTests.lean#L91) (admitted; scope in docstring).
- **105.26 Undirected graphical models.**
  [CKSD.gaussian_condIndepFun_iff_precision_eq_zero](CKSD/LinearModels/GaussianGraphical.lean#L52) (admitted; scope in docstring).
- **105.28 Gaussian covariance likelihood.**
  [CKSD.gaussianNegLogLikelihood_minimum_unique](CKSD/LinearModels/Multivariate.lean#L50) (admitted; scope in docstring).
- **105.29 Canonical correlations.**
  [CKSD.charpoly_canonicalCorrelationMatrix_transform](CKSD/LinearModels/CanonicalCorrelation.lean#L75) (proved; scope in docstring).
  [CKSD.norm_canonicalCorrelationMatrix_le_one](CKSD/LinearModels/CanonicalCorrelation.lean#L289) (proved; scope in docstring).
  [CKSD.isGreatest_linearCombinationCorrelation](CKSD/LinearModels/CanonicalCorrelation.lean#L317) (proved; scope in docstring).
  [CKSD.indepFun_gaussian_blocks_iff_canonicalCorrelationMatrix_eq_zero](CKSD/LinearModels/CanonicalCorrelation.lean#L389) (proved; scope in docstring).
- **105.31 Structure of the Wishart law.**
  [CKSD.wishart_determinant_law](CKSD/LinearModels/Multivariate.lean#L62) (admitted; scope in docstring).
- **105.32 Sampling theory of correlation coefficients.**
  [CKSD.gaussian_sample_correlation_student_law](CKSD/LinearModels/Multivariate.lean#L70) (admitted; scope in docstring).
- **105.33 Likelihood-ratio tests of sphericity and independence.**
  [CKSD.tendstoInDistribution_sphericity_likelihood_ratio](CKSD/LinearModels/MultivariateTests.lean#L108) (admitted; scope in docstring).
  [CKSD.tendstoInDistribution_block_independence_likelihood_ratio](CKSD/LinearModels/MultivariateTests.lean#L120) (admitted; scope in docstring).
- **105.34 Invariant tests of a multivariate linear hypothesis.**
  [CKSD.multivariateHypothesisRoots_eq_iff_congruent](CKSD/LinearModels/MultivariateTests.lean#L183) (proved; scope in docstring).
  [CKSD.multivariate_test_statistics_eq_roots](CKSD/LinearModels/MultivariateTests.lean#L343) (proved; scope in docstring).
- **105.35 Factor analysis and identification.**
  [CKSD.normalizedFactorLoading_eq_up_to_signs](CKSD/LinearModels/FactorAnalysis.lean#L62) (admitted; scope in docstring).
  [CKSD.tendstoInProbabilityConst_factor_mle_of_compact](CKSD/LinearModels/FactorAnalysis.lean#L72) (admitted; scope in docstring).
- **105.36 Decomposable models.**
  [CKSD.isUndirectedGlobalMarkovMass_iff_clique_factorization](CKSD/LinearModels/Decomposable.lean#L359) (proved; scope in docstring).
  [CKSD.isGreatest_gaussianConcentrationLogLikelihood_decomposable](CKSD/LinearModels/Decomposable.lean#L423) (admitted; scope in docstring).
  [CKSD.existsUnique_gaussianConcentration_mle](CKSD/LinearModels/Decomposable.lean#L440) (admitted; scope in docstring).
- **105.37 Kiefer–Wolfowitz equivalence.**
  [CKSD.kiefer_wolfowitz_equivalence](CKSD/LinearModels/Design.lean#L40) (admitted; scope in docstring).
- **105.38 Randomization test.**
  [CKSD.randomization_p_value_valid](CKSD/LinearModels/Design.lean#L51) (proved; scope in docstring).
- **105.42 Fisher's inequality and optimality of balanced incomplete blocks.**
  [CKSD.fisher_inequality_of_balanced_incomplete_block_design](CKSD/LinearModels/Design.lean#L81) (proved; scope in docstring).
- **105.44 Latin squares and mutually orthogonal sets.**
  [CKSD.card_orthogonal_latin_squares_le](CKSD/LinearModels/Design.lean#L167) (proved; scope in docstring).
  [CKSD.exists_complete_orthogonal_latin_squares_of_isPrimePow](CKSD/LinearModels/Design.lean#L231) (proved; scope in docstring).
- **105.72 Horvitz–Thompson estimation and design variance.**
  [CKSD.horvitz_thompson_mean_and_variance](CKSD/LinearModels/CausalAndSurvey.lean#L334) (proved; scope in docstring).
  [CKSD.horvitz_thompson_variance_estimator_unbiased](CKSD/LinearModels/CausalAndSurvey.lean#L377) (proved; scope in docstring).
  [CKSD.horvitz_thompson_variance_eq_sen_yates_grundy](CKSD/LinearModels/CausalAndSurvey.lean#L400) (proved; scope in docstring).
- **105.73 Simple and stratified random sampling; Neyman allocation.**
  [CKSD.simple_random_sample_mean_and_variance](CKSD/LinearModels/CausalAndSurvey.lean#L659) (proved; scope in docstring).
  [CKSD.neyman_allocation_optimal](CKSD/LinearModels/CausalAndSurvey.lean#L743) (proved; scope in docstring).
- **105.46 Neyman's theorem.**
  [CKSD.randomized_treatment_difference_mean_and_variance](CKSD/LinearModels/CausalAndSurvey.lean#L676) (proved; scope in docstring).
- **105.47 Identification by regression and by weighting.**
  [CKSD.treatment_effect_identification_of_conditional_independence](CKSD/LinearModels/CausalAndSurvey.lean#L82) (proved; scope in docstring).
- **105.48 Propensity score.**
  [CKSD.condIndepFun_propensityScore](CKSD/LinearModels/Causal.lean#L145) (admitted; scope in docstring).
  [CKSD.condIndepFun_of_propensityScore](CKSD/LinearModels/Causal.lean#L154) (admitted; scope in docstring).
- **105.49 Doubly robust estimator of the average treatment effect.**
  [CKSD.doubly_robust_bias_identity](CKSD/LinearModels/CausalAndSurvey.lean#L141) (proved; scope in docstring).
- **105.50 Local average treatment effect.**
  [CKSD.local_average_treatment_effect_eq_wald_ratio](CKSD/LinearModels/CausalAndSurvey.lean#L234) (proved; scope in docstring).
- **105.55 Two-stage least squares.**
  [CKSD.tendstoInProbabilityConst_twoStageLeastSquares](CKSD/LinearModels/RegressionLimits.lean#L288) (admitted; scope in docstring).
  [CKSD.tendstoInDistribution_twoStageLeastSquares](CKSD/LinearModels/RegressionLimits.lean#L305) (admitted; scope in docstring).
- **105.56 Efficient variance for an average treatment effect.**
  [CKSD.finiteStrataTreatmentInfluence_mean_and_variance](CKSD/LinearModels/CausalEfficiency.lean#L146) (proved; scope in docstring).
  [CKSD.hasDerivAt_finiteStrataTreatmentEffect_score_tilt](CKSD/LinearModels/CausalEfficiency.lean#L316) (proved; scope in docstring).
- **105.62 Directed Markov properties.**
  [CKSD.condIndepMass_directedFactorizationMass_of_dSeparated](CKSD/LinearModels/DirectedGraphical.lean#L464) (proved; scope in docstring).
  [CKSD.CausalGraph.recursivelyFactorizes_tfae](CKSD/LinearModels/DirectedGraphical.lean#L1305) (proved; scope in docstring).
- **105.63 Back-door and front-door formulae.**
  [CKSD.doMarginalMass_eq_backdoor](CKSD/LinearModels/DirectedGraphical.lean#L1343) (proved; scope in docstring).
  [CKSD.doMarginalMass_eq_frontdoor](CKSD/LinearModels/DirectedGraphical.lean#L1394) (proved; scope in docstring).
- **105.64 Rules of the do-calculus.**
  [CKSD.condDoMass_rule_one](CKSD/LinearModels/DirectedGraphical.lean#L1507) (proved; scope in docstring).
  [CKSD.condDoMass_rule_two](CKSD/LinearModels/DirectedGraphical.lean#L1529) (proved; scope in docstring).
  [CKSD.condDoMass_rule_three](CKSD/LinearModels/DirectedGraphical.lean#L1960) (proved; scope in docstring).
- **105.65 Longitudinal $g$-formula.**
  [CKSD.integral_potentialOutcome_eq_gFormula](CKSD/LinearModels/GFormula.lean#L229) (proved; scope in docstring).
- **105.67 Markov equivalence of directed graphs.**
  [CKSD.markovEquivalent_iff_skeleton_and_colliders](CKSD/LinearModels/Causal.lean#L120) (admitted; scope in docstring).
  [CKSD.CausalGraph.skeleton_and_colliders_eq_of_isFaithful](CKSD/LinearModels/DirectedGraphical.lean#L2109) (proved; scope in docstring).
- **105.70 Skeleton and colliders from conditional independences.**
  [CKSD.CausalGraph.dSeparated_parents_of_not_adjacent](CKSD/LinearModels/DirectedGraphical.lean#L2036) (proved; scope in docstring).
  [CKSD.CausalGraph.adjacent_iff_forall_not_dSeparated](CKSD/LinearModels/DirectedGraphical.lean#L2047) (proved; scope in docstring).
  [CKSD.CausalGraph.isCollider_iff_not_mem_of_dSeparated](CKSD/LinearModels/DirectedGraphical.lean#L2074) (proved; scope in docstring).
  [CKSD.CausalGraph.skeleton_and_colliders_eq_of_isFaithful](CKSD/LinearModels/DirectedGraphical.lean#L2109) (proved; scope in docstring).
- **105.71 Identifiability of restricted structural equation models.**
  [CKSD.CausalGraph.edge_eq_of_linearSEMLaw_eq_of_nonGaussian](CKSD/LinearModels/StructuralEquations.lean#L93) (admitted; scope in docstring).
  [CKSD.CausalGraph.edge_eq_of_linearSEMLaw_eq_of_equalVariance](CKSD/LinearModels/StructuralEquations.lean#L107) (admitted; scope in docstring).
  [CKSD.CausalGraph.edge_eq_of_additiveNoiseLaw_eq](CKSD/LinearModels/StructuralEquations.lean#L119) (admitted; scope in docstring).
  [CKSD.CausalGraph.exists_linearGaussianSEM_iff_markovEquivalent](CKSD/LinearModels/StructuralEquations.lean#L136) (admitted; scope in docstring).

### Section 106

- **106.1 Martingale central limit theorem.**
  [CKSD.tendstoInDistribution_martingale_array_sum](CKSD/Processes/TimeSeries.lean#L52) (admitted; scope in docstring).
- **106.2 Wold decomposition and causal autoregression.**
  [CKSD.exists_wold_decomposition](CKSD/Processes/TimeSeries.lean#L503) (proved; scope in docstring).
- **106.4 Bartlett's theorem.**
  [CKSD.tendstoInDistribution_sample_autocorrelations](CKSD/Processes/TimeSeries.lean#L518) (admitted; scope in docstring).
- **106.6 Periodogram and lag-window estimation.**
  [CKSD.tendstoInDistribution_periodogram_div_spectralDensity](CKSD/Processes/Spectral.lean#L76) (admitted; scope in docstring).
  [CKSD.tendsto_lagWindowEstimator_moments](CKSD/Processes/Spectral.lean#L94) (admitted; scope in docstring).
- **106.7 Kalman filter.**
  [CKSD.kalmanFilter](CKSD/Processes/Kalman.lean#L1306) (proved; scope in docstring).
- **106.11 Moving-block bootstrap.**
  [CKSD.movingBlockBootstrap_consistent](CKSD/Processes/Dependence.lean#L66) (admitted; scope in docstring).
- **106.12 Long-run variance of a sample mean.**
  [CKSD.tendsto_normalized_variance_eq_tsum_covariance](CKSD/Processes/TimeSeries.lean#L612) (proved; scope in docstring).
- **106.14 Herglotz theorem and rational spectral densities.**
  [CKSD.exists_stationary_gaussian_process_of_posSemidef](CKSD/Processes/TimeSeries.lean#L769) (proved; scope in docstring).
- **106.16 Kolmogorov's formula for the prediction error.**
  [CKSD.infDist_past_sq_eq_kolmogorov](CKSD/Processes/Spectral.lean#L117) (admitted; scope in docstring).
- **106.17 Asymptotic covariance of ARMA estimators.**
  [CKSD.whittleEstimator_asymptotics](CKSD/Processes/Spectral.lean#L182) (admitted; scope in docstring).
- **106.18 Stationarity of GARCH$(1,1)$.**
  [CKSD.garch_series_summable_and_moments](CKSD/Processes/TimeSeries.lean#L985) (proved; scope in docstring).
- **106.21 Stein's prediction theorem.**
  [CKSD.stein_linearPrediction_equivalent_gaussian](CKSD/Processes/Dependence.lean#L101) (admitted; scope in docstring).
- **106.24 Bochner's theorem and the Matérn family.**
  [CKSD.exists_stationary_field_of_spectral_measure](CKSD/Processes/SpectralAndSequential.lean#L125) (proved; scope in docstring).
- **106.28 Nelson–Aalen estimator.**
  [CKSD.tendstoInDistribution_nelsonAalenEstimator](CKSD/Processes/Survival.lean#L27) (admitted; scope in docstring).
- **106.29 Kaplan–Meier estimator.**
  [CKSD.tendstoInDistribution_kaplanMeierEstimator](CKSD/Processes/Survival.lean#L42) (admitted; scope in docstring).
- **106.30 Cox partial likelihood.**
  [CKSD.coxPartialLikelihood_asymptotics](CKSD/Processes/CountingProcesses.lean#L54) (admitted; scope in docstring).
- **106.34 Rebolledo's martingale central limit theorem.**
  [CKSD.tendstoInDistribution_countingMartingaleTransform](CKSD/Processes/CountingProcesses.lean#L119) (admitted; scope in docstring).
- **106.37 Sequential probability ratio test.**
  [CKSD.integrable_stopped_sum_and_integral_eq](CKSD/Processes/Sequential.lean#L40) (proved; scope in docstring).
- **106.38 Ville's inequality and e-values.**
  [CKSD.measure_iSup_supermartingale_ge_le](CKSD/Processes/Sequential.lean#L154) (proved; scope in docstring).
- **106.39 CUSUM and the Brownian bridge.**
  [CKSD.tendstoInDistribution_cusumBridgeStatistic](CKSD/Processes/BridgeLimits.lean#L33) (admitted; scope in docstring).
- **106.41 Wald's fundamental identity and the operating characteristic.**
  [CKSD.integral_stopped_exponential_eq_one](CKSD/Processes/SpectralAndSequential.lean#L205) (proved; scope in docstring).
- **106.42 Anscombe's theorem.**
  [CKSD.tendstoInDistribution_random_sampleAverage](CKSD/Processes/Sequential.lean#L582) (proved; scope in docstring).
- **106.44 Optimality of CUSUM.**
  [CKSD.cusumStatistic_le_shiryaevRobertsStatistic](CKSD/Processes/Models.lean#L88) (proved; scope in docstring).
- **106.46 Fisher–Tippett–Gnedenko theorem.**
  [CKSD.tendsto_maximum_of_regularly_varying_tail](CKSD/Processes/Extremes.lean#L154) (proved; scope in docstring).
- **106.47 Excesses over high thresholds.**
  [CKSD.hasExtremeValueDomainOfAttraction_iff_pareto_excesses](CKSD/Processes/ExtremeValueLimits.lean#L50) (admitted; scope in docstring).
- **106.48 Extremal index.**
  [CKSD.tendsto_maximum_and_exceedance_count_of_tail_limit](CKSD/Processes/Extremes.lean#L238) (proved; scope in docstring).
- **106.49 Hill estimator.**
  [CKSD.tendstoInDistribution_hillEstimator](CKSD/Processes/ExtremeValueLimits.lean#L83) (admitted; scope in docstring).
- **106.50 Poisson approximation for exceedances.**
  [CKSD.tendsto_maximum_and_exceedance_count_of_tail_limit](CKSD/Processes/Extremes.lean#L238) (proved; scope in docstring).

### Section 107

- **107.1 Fundamental theorem of statistical learning.**
  [CKSD.measure_uniform_empirical_risk_deviation_le](CKSD/Learning/Generalization.lean#L31) (proved; scope in docstring).
- **107.2 Rademacher bound.**
  [CKSD.integral_sSup_sub_le_two_mul_rademacher](CKSD/Learning/Generalization.lean#L244) (proved; scope in docstring).
  [CKSD.rademacher_symmetrization_and_risk_bound](CKSD/Learning/Generalization.lean#L425) (proved; scope in docstring).
- **107.5 Hedge.**
  [CKSD.hedge_regret_le](CKSD/Learning/Generalization.lean#L532) (proved; scope in docstring).
- **107.6 Split conformal prediction.**
  [CKSD.conformal_coverage_ge](CKSD/Learning/Generalization.lean#L677) (proved; scope in docstring).
- **107.7 No free lunch.**
  [CKSD.no_free_lunch_lower_bound](CKSD/Learning/Generalization.lean#L783) (proved; scope in docstring).
- **107.8 Bayes classification risk.**
  [CKSD.classificationRisk_sub_bayes_risk_eq](CKSD/Learning/Generalization.lean#L871) (proved; scope in docstring).
  [CKSD.classificationRisk_plugin_sub_bayes_risk_le](CKSD/Learning/Generalization.lean#L899) (proved; scope in docstring).
- **107.10 Margin bound.**
  [CKSD.measure_margin_generalization_error_le](CKSD/Learning/MarginsAndBandits.lean#L187) (proved; scope in docstring).
- **107.11 Comparison inequality for convex surrogates.**
  [CKSD.surrogate_minimizer_sign_of_convex](CKSD/Learning/Generalization.lean#L935) (proved; scope in docstring).
- **107.12 Generalization of stable algorithms.**
  [CKSD.generalization_bound_of_uniform_stability](CKSD/Learning/Generalization.lean#L1102) (proved; scope in docstring).
- **107.13 Rate of kernel ridge regression.**
  [CKSD.ridgePrediction_oracle_bounds](CKSD/Learning/KernelAndClustering.lean#L43) (admitted; scope in docstring).
- **107.14 Asymptotics of nearest-neighbour rules.**
  [CKSD.tendsto_oneNN_expectedError](CKSD/Learning/LocalAveraging.lean#L65) (admitted; scope in docstring).
  [CKSD.bayesRisk_le_nnRisk_le](CKSD/Learning/LocalAveraging.lean#L73) (proved; scope in docstring).
  [CKSD.exists_tendsto_knn_expectedError](CKSD/Learning/LocalAveraging.lean#L117) (admitted; scope in docstring).
  [CKSD.tendsto_knn_expectedError_bayesRisk](CKSD/Learning/LocalAveraging.lean#L128) (admitted; scope in docstring).
- **107.16 Consistency of $k$-means.**
  [CKSD.ae_tendsto_kmeans_centers_of_compact](CKSD/Learning/KernelAndClustering.lean#L71) (admitted; scope in docstring).
- **107.19 Belief propagation and the Bethe free energy.**
  [CKSD.isBetheStationary_iff_exists_beliefPropagationFixedPoint](CKSD/Learning/GraphicalModels.lean#L139) (admitted; scope in docstring).
- **107.20 Consistency of response-independent forests.**
  [CKSD.tendsto_localAveraging_sq_error](CKSD/Learning/LocalAveraging.lean#L142) (admitted; scope in docstring).
- **107.23 Exact belief propagation on a tree.**
  [CKSD.exists_beliefPropagation_exact_on_tree](CKSD/Learning/GraphicalModels.lean#L150) (admitted; scope in docstring).
  [CKSD.beliefPropagation_tree_unique_up_to_scale](CKSD/Learning/GraphicalModels.lean#L161) (admitted; scope in docstring).
- **107.24 AdaBoost: training error and margins.**
  [CKSD.training_error_le_exponential_loss](CKSD/Learning/Algorithms.lean#L123) (proved; scope in docstring).
- **107.26 Variational representation of the cumulant function.**
  [CKSD.log_sum_exp_entropy_variational_formula](CKSD/Learning/Models.lean#L27) (proved; scope in docstring).
  [CKSD.tendsto_log_sum_exp_div_atTop](CKSD/Learning/Models.lean#L65) (proved; scope in docstring).
- **107.27 Junction-tree exactness.**
  [CKSD.hasJunctionTree_iff_isTriangulated](CKSD/Learning/JunctionTree.lean#L56) (admitted; scope in docstring).
  [CKSD.exists_joint_with_clique_marginals_iff](CKSD/Learning/JunctionTree.lean#L82) (admitted; scope in docstring).
- **107.28 Barron's rate.**
  [CKSD.exists_logisticNetwork_sq_error_le_barron_moment](CKSD/Learning/Approximation.lean#L42) (admitted; scope in docstring).
  [CKSD.exists_feature_average_sq_error_le](CKSD/Learning/Approximation.lean#L82) (proved; scope in docstring).
- **107.29 Deep networks and compositional classes.**
  [CKSD.compositionalHolder_minimax_lower_bound](CKSD/Learning/Networks.lean#L186) (admitted; scope in docstring).
- **107.30 Neural tangent kernel.**
  [CKSD.hasDerivAt_predictions_of_gradient_flow](CKSD/Learning/Models.lean#L104) (proved; scope in docstring).
- **107.31 Ridgeless least squares.**
  [CKSD.ridgeless_gaussian_risk_eq](CKSD/Learning/Models.lean#L114) (admitted; scope in docstring).
- **107.35 Capacity of network classes.**
  [CKSD.card_le_of_shatters_denseSignClass](CKSD/Learning/Networks.lean#L79) (admitted; scope in docstring).
  [CKSD.empiricalRademacherComplexity_biasFree_le](CKSD/Learning/Networks.lean#L102) (admitted; scope in docstring).
- **107.36 Approximation rates of deep ReLU networks.**
  [CKSD.abs_reluLinearInterpolant_sub_le](CKSD/Learning/Approximation.lean#L260) (proved; scope in docstring).
- **107.37 Depth separation.**
  [CKSD.relu_depth_lower_bound](CKSD/Learning/Networks.lean#L119) (admitted; scope in docstring).
  [CKSD.relu_eldan_shamir_separation](CKSD/Learning/Networks.lean#L134) (admitted; scope in docstring).
- **107.39 Gaussian-process limit at initialization.**
  [CKSD.tendstoInDistribution_wide_network_gaussian](CKSD/Learning/Networks.lean#L220) (admitted; scope in docstring).
- **107.40 Implicit bias of gradient descent.**
  [CKSD.tendsto_least_squares_gradient_descent](CKSD/Learning/Models.lean#L127) (proved; scope in docstring).
- **107.41 Exact recovery.**
  [CKSD.exists_exactRecovery_iff](CKSD/Learning/RandomGraphs.lean#L79) (admitted; scope in docstring).
  [CKSD.exists_exactRecovery_iff_of_zero](CKSD/Learning/RandomGraphs.lean#L86) (admitted; scope in docstring).
- **107.42 Kesten–Stigum threshold.**
  [CKSD.exists_weakRecovery_iff](CKSD/Learning/RandomGraphs.lean#L94) (admitted; scope in docstring).
  [CKSD.blockModel_binomialRandom_mutually_contiguous](CKSD/Learning/RandomGraphs.lean#L103) (admitted; scope in docstring).
- **107.43 Aldous–Hoover theorem for graphs.**
  [CKSD.existsUnique_graphonMixture_of_finitePerm_invariant](CKSD/Learning/RandomGraphs.lean#L223) (proved; scope in docstring).
  [CKSD.infiniteSampleLaw_eq_iff_exists_measurePreserving](CKSD/Learning/RandomGraphs.lean#L235) (admitted; scope in docstring).
- **107.47 Phase transitions of the Erdős–Rényi graph.**
  [CKSD.exists_tendsto_binomialRandom_components_le_log](CKSD/Learning/RandomGraphs.lean#L121) (admitted; scope in docstring).
  [CKSD.binomialRandom_giant_component](CKSD/Learning/RandomGraphs.lean#L131) (admitted; scope in docstring).
  [CKSD.binomialRandom_connectivity_threshold](CKSD/Learning/RandomGraphs.lean#L145) (admitted; scope in docstring).
- **107.49 Lai–Robbins lower bound.**
  [CKSD.lai_robbins_lower_bound](CKSD/Learning/Bandits.lean#L104) (admitted; scope in docstring).
- **107.50 Upper confidence bounds.**
  [CKSD.ucb_regret_le](CKSD/Learning/Sequential.lean#L29) (proved; scope in docstring).
- **107.51 Thompson sampling and the Gittins index.**
  [CKSD.tendsto_thompson_regret_div_log](CKSD/Learning/Bandits.lean#L148) (admitted; scope in docstring).
  [CKSD.banditPolicyValue_le_of_gittins](CKSD/Learning/Policies.lean#L563) (admitted; scope in docstring).
- **107.52 Adversarial bandits.**
  [CKSD.exp3_expected_regret_le](CKSD/Learning/MarginsAndBandits.lean#L434) (proved; scope in docstring).
- **107.54 Convergence of $Q$-learning.**
  [CKSD.ae_tendsto_asynchronous_stochastic_approximation](CKSD/Learning/Sequential.lean#L76) (admitted; scope in docstring).
- **107.58 Stationary optimal policies and linear programming.**
  [CKSD.banditPolicyValue_le_of_gittins](CKSD/Learning/Policies.lean#L563) (admitted; scope in docstring).
  [CKSD.exists_bellman_fixed_point_and_greedy_policy](CKSD/Learning/Sequential.lean#L118) (proved; scope in docstring).
- **107.59 Sample complexity with a generative model.**
  [CKSD.policy_value_resolvent_identity_and_error_bound](CKSD/Learning/Sequential.lean#L237) (proved; scope in docstring).
- **107.60 Temporal differences with linear features.**
  [CKSD.norm_projected_fixed_point_sub_le](CKSD/Learning/Sequential.lean#L271) (proved; scope in docstring).
- **107.61 Convergence of natural policy gradient.**
  [CKSD.optimalObjective_sub_npg_le](CKSD/Learning/Policies.lean#L485) (proved; scope in docstring).
- **107.62 Minimax regret of finite-armed bandits.**
  [CKSD.exists_bernoulli_banditRegret_ge](CKSD/Learning/Bandits.lean#L164) (admitted; scope in docstring).
  [CKSD.exists_ucb1_banditRegret_le](CKSD/Learning/Bandits.lean#L657) (proved; scope in docstring).
- **107.63 Self-normalized confidence and LinUCB.**
  [CKSD.measure_exists_selfNormalized_gt_le](CKSD/Learning/Bandits.lean#L743) (admitted; scope in docstring).
  [CKSD.exists_linUCB_regret_le](CKSD/Learning/Bandits.lean#L766) (admitted; scope in docstring).
- **107.65 Composition.**
  [CKSD.isDifferentiallyPrivate_compProd](CKSD/Learning/Privacy.lean#L34) (proved; scope in docstring).
- **107.66 Private mean estimation.**
  [CKSD.isDifferentiallyPrivate_laplaceMeanMechanism](CKSD/Learning/PrivateEstimation.lean#L121) (proved; scope in docstring).
  [CKSD.centralMeanRisk_laplaceMeanMechanism_le](CKSD/Learning/PrivateEstimation.lean#L238) (proved; scope in docstring).
  [CKSD.exists_centralMeanRisk_le](CKSD/Learning/PrivateEstimation.lean#L304) (proved; scope in docstring).
  [CKSD.exists_centralMeanRisk_ge](CKSD/Learning/PrivateEstimation.lean#L723) (proved; scope in docstring).
  [CKSD.isDifferentiallyPrivate_localLaplaceKernel](CKSD/Learning/PrivateEstimation.lean#L933) (proved; scope in docstring).
  [CKSD.localMeanRisk_localLaplace_mean_le](CKSD/Learning/PrivateEstimation.lean#L1010) (proved; scope in docstring).
  [CKSD.localMeanRisk_minimax_order](CKSD/Learning/PrivateEstimation.lean#L1087) (proved; scope in docstring).
- **107.74 Sparse vector technique.**
  [CKSD.aboveThreshold_comparison](CKSD/Learning/Algorithms.lean#L138) (proved; scope in docstring).
- **107.75 Contraction under local privacy.**
  [CKSD.klDiv_comp_le_of_local_differential_privacy](CKSD/Learning/Privacy.lean#L283) (proved; scope in docstring).
  [CKSD.exists_bernoulli_localMeanRisk_ge](CKSD/Learning/PrivateEstimation.lean#L804) (proved; scope in docstring).

### Section 108

- **108.1 Cheeger inequality for the normalized Laplacian.**
  [CKSD.cheeger_inequalities](CKSD/Geometry/GeometricStatistics.lean#L27) (admitted; scope in docstring).
- **108.4 Geodesic approximation.**
  [CKSD.eventually_sampleGraphEDist_intrinsicEDist_le](CKSD/Geometry/ManifoldLearning.lean#L57) (admitted; scope in docstring).
  [CKSD.intrinsicEDist_eq_edist_of_lengthPreserving](CKSD/Geometry/ManifoldLearning.lean#L75) (proved; scope in docstring).
- **108.5 Fréchet means.**
  [CKSD.existsUnique_frechet_mean_of_midpoint_inequality](CKSD/Geometry/GeometricStatistics.lean#L49) (proved; scope in docstring).
- **108.7 Hausdorff estimation of a submanifold.**
  [CKSD.isBoundedInProbability_hausdorff_sampling_error](CKSD/Geometry/GeometricStatistics.lean#L157) (admitted; scope in docstring).
- **108.8 Classical multidimensional scaling.**
  [CKSD.posSemidef_double_centering_iff_sq_euclidean_distances](CKSD/Geometry/GeometricStatistics.lean#L221) (proved; scope in docstring).
- **108.10 Extrinsic projection mean.**
  [CKSD.extrinsic_mean_iff_nearest_expectation](CKSD/Geometry/GeometricStatistics.lean#L282) (proved; scope in docstring).
  [CKSD.tendstoInDistribution_projected_sampleAverage](CKSD/Geometry/GeometricStatistics.lean#L300) (admitted; scope in docstring).
- **108.13 Uniqueness of Fréchet means in small balls.** — theorem formulation pending.
- **108.15 Barycentric equation.** — theorem formulation pending.
- **108.18 Interval decomposition.**
  [CKSD.exists_intervalBasis_of_isPointwiseFiniteDimensional](CKSD/Geometry/PersistenceModules.lean#L53) (admitted; scope in docstring).
  [CKSD.IntervalBasis.exists_equiv_support_eq](CKSD/Geometry/PersistenceModules.lean#L61) (admitted; scope in docstring).
  [CKSD.exists_isSublevelDiagram](CKSD/Geometry/SimplicialPersistence.lean#L485) (proved; scope in docstring).
- **108.19 Bottleneck stability.**
  [CKSD.fullBottleneckEDist_le_of_isSublevelDiagram](CKSD/Geometry/SimplicialPersistence.lean#L1427) (proved; scope in docstring).
- **108.20 Isometry theorem.**
  [CKSD.interleavingEDist_le_fullBottleneckEDist](CKSD/Geometry/PersistenceModules.lean#L210) (proved; scope in docstring).
  [CKSD.interleavingEDist_eq_fullBottleneckEDist](CKSD/Geometry/PersistenceModules.lean#L306) (admitted; scope in docstring).
- **108.21 Čech, Rips, and the nerve.**
  [CKSD.IsCechSimplex.isRipsSimplex](CKSD/Geometry/Persistence.lean#L119) (proved; scope in docstring).
  [CKSD.cech_rips_inclusions](CKSD/Geometry/Topology.lean#L137) (proved; scope in docstring).
- **108.22 Homology from a sample.**
  [CKSD.exists_deformationRetraction_offset_of_hausdorffDist_lt](CKSD/Geometry/TopologicalInference.lean#L93) (admitted; scope in docstring).
  [CKSD.exists_sample_size_hausdorffDist_le](CKSD/Geometry/TopologicalInference.lean#L113) (admitted; scope in docstring).
- **108.23 Central limit theorem for landscapes.**
  [CKSD.ae_tendsto_landscape_sampleAverage](CKSD/Geometry/Landscapes.lean#L40) (proved; scope in docstring).
- **108.24 Stability of the distance to a measure.**
  [CKSD.abs_distanceToMeasure_sub_le_wasserstein](CKSD/Geometry/Topology.lean#L148) (admitted; scope in docstring).
- **108.32 Persistence pairing by matrix reduction.**
  [CKSD.isColumnLow_iff_pairingRankCombination_eq_one](CKSD/Geometry/MatrixReduction.lean#L303) (proved; scope in docstring).
  [CKSD.isColumnLow_iff_of_isMatrixReduction](CKSD/Geometry/MatrixReduction.lean#L310) (proved; scope in docstring).
  [CKSD.persistentBettiOfMatrix_eq_card](CKSD/Geometry/MatrixReduction.lean#L890) (proved; scope in docstring).
  [CKSD.persistentBettiOfMatrix_eq_card_bars](CKSD/Geometry/MatrixReduction.lean#L1003) (proved; scope in docstring).
- **108.34 Sublevel persistence of a Morse function.**
  [CKSD.sublevelHomologyModule_bars_of_isMorse](CKSD/Geometry/TopologicalInference.lean#L185) (admitted; scope in docstring).
- **108.35 Wasserstein stability.**
  [CKSD.diagramWassersteinEDist_le_of_isSublevelDiagram](CKSD/Geometry/SimplicialPersistence.lean#L1941) (proved; scope in docstring).
- **108.36 Gromov–Hausdorff stability of Rips persistence.**
  [CKSD.fullBottleneckEDist_rips_le_ghDist](CKSD/Geometry/RipsStability.lean#L649) (proved; scope in docstring).
- **108.37 Homology inference with positive weak feature size.**
  [CKSD.nonempty_range_offsetHomology_equiv_of_weakFeatureSize](CKSD/Geometry/TopologicalInference.lean#L131) (admitted; scope in docstring).
  [CKSD.nonempty_ripsPersistentHomology_equiv_of_weakFeatureSize](CKSD/Geometry/TopologicalInference.lean#L148) (admitted; scope in docstring).
- **108.40 Empirical Wasserstein bounds.**
  [CKSD.integral_empirical_wasserstein_rpow_le](CKSD/Geometry/Transport.lean#L29) (admitted; scope in docstring).
- **108.42 Consistency of Brenier maps.**
  [CKSD.tendsto_integral_sq_optimal_map_sub](CKSD/Geometry/Transport.lean#L41) (admitted; scope in docstring).
- **108.43 Gromov–Wasserstein distance.**
  [CKSD.exists_measure_preserving_isometryEquiv_of_zero_distortion](CKSD/Geometry/Transport.lean#L57) (admitted; scope in docstring).
- **108.44 Debiased Sinkhorn divergence.**
  [CKSD.realSinkhornDivergence_independent_lower_bound](CKSD/Geometry/Entropic.lean#L72) (proved; scope in docstring).
  [CKSD.realSinkhornDivergence_nonneg](CKSD/Geometry/Entropic.lean#L98) (proved; scope in docstring).
- **108.46 Gaussian transport and barycenters.**
  [CKSD.wasserstein_multivariateGaussian_sq_eq](CKSD/Geometry/Transport.lean#L71) (admitted; scope in docstring).
  [CKSD.exists_unique_gaussian_wasserstein_barycenter](CKSD/Geometry/Transport.lean#L78) (admitted; scope in docstring).
- **108.47 One-dimensional empirical transport limit.**
  [CKSD.tendstoInDistribution_mul_wasserstein_sq_empiricalMeasure](CKSD/Geometry/TransportRates.lean#L37) (admitted; scope in docstring).
- **108.50 Minimax lower bounds for transport estimation.**
  [CKSD.wasserstein_uniform_cube_lower_bound](CKSD/Geometry/Transport.lean#L93) (admitted; scope in docstring).
- **108.51 Smooth laws and smoothed distances.**
  [CKSD.integral_wasserstein_gaussianSmoothing_empiricalMeasure_le](CKSD/Geometry/Transport.lean#L102) (admitted; scope in docstring).
- **108.53 Rates for transport-map estimation.**
  [CKSD.lintegral_transportMapRisk_semidualEstimator_le](CKSD/Geometry/TransportRates.lean#L104) (admitted; scope in docstring).
  [CKSD.lintegral_transportMapRisk_semidualEstimator_le_of_poincare](CKSD/Geometry/TransportRates.lean#L119) (admitted; scope in docstring).
- **108.55 Dimension-free sample complexity of entropic transport.**
  [CKSD.quadraticEntropicTransport_empirical_bounds](CKSD/Geometry/StatisticalTransport.lean#L43) (admitted; scope in docstring).
- **108.56 Semidiscrete dual.**
  [CKSD.semidiscreteTransportDual_concave_differentiable_and_attains_max](CKSD/Geometry/Transport.lean#L112) (admitted; scope in docstring).
- **108.57 Tangent-space linearization.**
  [CKSD.gaussian_optimal_maps_compatible_iff_covariances_commute](CKSD/Geometry/Transport.lean#L136) (proved; scope in docstring).
- **108.58 First-order conditions for barycenters.**
  [CKSD.hasDerivAt_wassersteinBarycenterEnergy_displacement](CKSD/Geometry/StatisticalTransport.lean#L82) (admitted; scope in docstring).
  [CKSD.satisfiesWassersteinKarcherEquation_of_minimizer](CKSD/Geometry/StatisticalTransport.lean#L99) (admitted; scope in docstring).
- **108.59 Procrustes iteration for barycenters.**
  [CKSD.wasserstein_energy_descent_of_averaged_transport](CKSD/Geometry/Transport.lean#L243) (proved; scope in docstring).
- **108.61 Limits of the empirical discrepancy.**
  [CKSD.tendstoInDistribution_squaredMMD_null_finite_features](CKSD/Geometry/Kernels.lean#L28) (admitted; scope in docstring).
  [CKSD.tendstoInDistribution_squaredMMD_alternative_finite_features](CKSD/Geometry/Kernels.lean#L48) (admitted; scope in docstring).
- **108.62 Energy distance and independence.**
  [CKSD.energy_distance_nonneg_eq_zero_iff_and_eq_squaredMMD](CKSD/Geometry/Kernels.lean#L66) (admitted; scope in docstring).
  [CKSD.distance_covariance_nonneg_eq_zero_iff_and_eq_squaredMMD](CKSD/Geometry/Kernels.lean#L76) (admitted; scope in docstring).
- **108.63 Hilbert–Schmidt independence criterion.**
  [CKSD.squaredMMD_joint_prod_eq_zero_iff_indepFun](CKSD/Geometry/Kernels.lean#L88) (proved; scope in docstring).
- **108.68 Criteria for characteristic kernels.**
  [CKSD.isCharacteristicKernel_iff_spectral_measure_full_support](CKSD/Geometry/Kernels.lean#L100) (admitted; scope in docstring).
  [CKSD.squaredMMD_quadratic_polynomial_eq](CKSD/Geometry/Kernels.lean#L178) (proved; scope in docstring).
- **108.70 Metrization of weak convergence.**
  [CKSD.tendstoWeakly_iff_tendsto_squaredMMD_of_tight](CKSD/Geometry/Kernels.lean#L202) (admitted; scope in docstring).
- **108.71 Kernel Stein discrepancy.**
  [CKSD.integral_langevin_stein_operator_eq_zero](CKSD/Geometry/Kernels.lean#L214) (proved; scope in docstring).
- **108.72 Convergence control by kernel Stein discrepancies.**
  [CKSD.tendstoWeakly_of_kernelSteinDiscrepancySq_inverseMultiquadric_tendsto_zero](CKSD/Geometry/SteinDiscrepancy.lean#L57) (admitted; scope in docstring).
  [CKSD.exists_not_tendstoWeakly_of_kernelSteinDiscrepancySq_tendsto_zero](CKSD/Geometry/SteinDiscrepancy.lean#L77) (admitted; scope in docstring).
- **108.74 Random Fourier features.**
  [CKSD.randomFourierFeatureKernel_unbiased_and_concentration](CKSD/Geometry/Kernels.lean#L384) (proved; scope in docstring).
  [CKSD.measure_uniform_randomFourierFeatureKernel_error_le](CKSD/Geometry/Kernels.lean#L458) (admitted; scope in docstring).
  [CKSD.abs_squaredMMD_sub_le_of_uniform_kernel_error](CKSD/Geometry/Kernels.lean#L500) (proved; scope in docstring).
