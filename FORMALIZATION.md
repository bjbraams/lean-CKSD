# CKSD formalization

The public entry point is [CKSD.lean](CKSD.lean). Every project declaration is in
`namespace CKSD` or one of its subnamespaces. The module names follow topics, while
the stable identifiers of [GAPS.md](GAPS.md) connect code to the mathematical catalogue.

There are **841 definitions, abbreviations, structures, and inductive types**
and **2510 theorem statements**: **2421 proved**,
**0 conditional** (the proof is complete but uses an admitted result), and
**89 admitted**. Definitions contain no admissions. A compiled axiom audit
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
  [CKSD.isSufficientStatistic_iff_exists_factorization](CKSD/Inference/ExponentialFamily.lean#L54) (proved; scope in docstring).
  [CKSD.exists_factorization_of_isSufficientStatistic](CKSD/Inference/Factorization.lean#L205) (proved; scope in docstring).
  [CKSD.isSufficientStatistic_of_factorization](CKSD/Inference/Factorization.lean#L241) (proved; scope in docstring).
- **101.2 Minimal sufficiency.**
  [CKSD.isSufficientStatistic_likelihoodRatio_and_ae_eq_comp](CKSD/Inference/ExponentialFamily.lean#L229) (proved; scope in docstring).
- **101.4 Structure of a full-rank exponential family.**
  [CKSD.convex_naturalParameterSpace](CKSD/Inference/ExponentialFamily.lean#L69) (proved; scope in docstring).
  [CKSD.analyticOnNhd_logPartition_and_fderiv_eq_moments](CKSD/Inference/ExponentialFamily.lean#L278) (proved; scope in docstring).
- **101.5 Completeness in a full-rank exponential family.**
  [CKSD.isCompleteStatistic_withDensity_exp_inner](CKSD/Inference/ExponentialFamily.lean#L86) (proved; scope in docstring).
- **101.6 Pitman–Koopman–Darmois theorem, monotone form.**
  [CKSD.exists_exponential_family_of_monotone_sufficient_statistics](CKSD/Inference/ExponentialFamily.lean#L261) (admitted; scope in docstring).
- **101.7 Rao–Blackwell theorem.**
  [CKSD.exists_rao_blackwell_estimator](CKSD/Inference/Estimation.lean#L43) (proved; scope in docstring).
- **101.8 Lehmann–Scheffé theorem.**
  [CKSD.ae_eq_of_isCompleteStatistic_of_isUnbiasedEstimator](CKSD/Inference/Estimation.lean#L106) (proved; scope in docstring).
- **101.9 Basu's theorem.**
  [CKSD.indepFun_of_isSufficientStatistic_of_isBoundedlyCompleteStatistic](CKSD/Inference/Estimation.lean#L123) (proved; scope in docstring).
- **101.10 Information inequality.**
  [CKSD.sq_div_information_le_variance](CKSD/Inference/Estimation.lean#L162) (proved; scope in docstring).
- **101.12 Characterization of UMVU estimators.**
  [CKSD.isMinimumVarianceUnbiasedEstimator_iff_covariance_eq_zero](CKSD/Inference/Estimation.lean#L201) (proved; scope in docstring).
- **101.13 Completeness of the order statistic.**
  [CKSD.isSymmetricallyComplete_of_complete_convex_family](CKSD/Inference/Families.lean#L69) (proved; scope in docstring).
- **101.14 Neyman–Pearson lemma.**
  [CKSD.exists_neyman_pearson_test](CKSD/Inference/NeymanPearson.lean#L106) (proved; scope in docstring).
- **101.15 Karlin–Rubin theorem.**
  [CKSD.isUniformlyMostPowerfulTest_of_monotone_likelihood_ratio](CKSD/Inference/Testing.lean#L65) (proved; scope in docstring).
- **101.17 Gaussian sampling distributions.**
  [CKSD.gaussian_sample_mean_residual_laws](CKSD/Inference/Testing.lean#L132) (proved; scope in docstring).
- **101.21 Distribution of order statistics.**
  [CKSD.map_orderStatistics_eq_withDensity](CKSD/Inference/Families.lean#L84) (proved; scope in docstring).
  [CKSD.map_orderStatistic_eq_withDensity](CKSD/Inference/Families.lean#L143) (proved; scope in docstring).
  [CKSD.map_sort_eq_and_indepFun_orderStatistics](CKSD/Inference/Families.lean#L252) (proved; scope in docstring).
- **101.32 Value of a finite statistical game.**
  [CKSD.exists_statistical_game_saddle_point](CKSD/Inference/Decision.lean#L60) (proved; scope in docstring).
- **101.37 Complete classes.**
  [CKSD.exists_admissible_bayes_risk_le_of_closed_convex](CKSD/Inference/Decision.lean#L108) (proved; scope in docstring).
- **101.39 Hunt–Stein theorem, compact form.**
  [CKSD.exists_equivariant_rule_risk_eq_average](CKSD/Inference/Decision.lean#L202) (proved; scope in docstring).
- **101.40 Pitman estimator of location.**
  [CKSD.pitmanEstimator_minimum_equivariant_risk_of_nonneg](CKSD/Inference/Families.lean#L552) (proved; scope in docstring).
  [CKSD.pitmanEstimator_minimum_equivariant_risk](CKSD/Inference/Families.lean#L641) (proved; scope in docstring).
- **101.42 Mean parameterization.**
  [CKSD.exists_analytic_inverse_exponential_family_mean](CKSD/Inference/Decision.lean#L281) (proved; scope in docstring).
- **101.43 Conditional exponential families.**
  [CKSD.exists_kernel_conditional_exponential_family](CKSD/Inference/ConditionalExponentialFamily.lean#L258) (proved; scope in docstring).
- **101.45 Two-sided tests in a one-parameter exponential family.**
  [CKSD.isUniformlyMostPowerfulUnbiasedTest_of_two_tail_moment_constraints](CKSD/Inference/InvariantTesting.lean#L176) (proved; scope in docstring).
- **101.46 Conditional tests with a nuisance parameter.**
  [CKSD.isUniformlyMostPowerfulUnbiasedTest_conditional_two_sided](CKSD/Inference/ConditionalExponentialFamily.lean#L320) (admitted; scope in docstring).
  [CKSD.isUniformlyMostPowerfulUnbiasedTest_conditional_one_sided](CKSD/Inference/ConditionalExponentialFamily.lean#L340) (admitted; scope in docstring).
- **101.47 Generalized Neyman–Pearson lemma.**
  [CKSD.integral_le_of_generalized_neyman_pearson](CKSD/Inference/NeymanPearson.lean#L47) (proved; scope in docstring).
- **101.49 Neyman structure.**
  [CKSD.condExp_eq_const_of_isSimilarTest](CKSD/Inference/InvariantTesting.lean#L360) (proved; scope in docstring).
- **101.50 Uniformly most powerful tests of a two-sided hypothesis.**
  [CKSD.exists_ump_interval_test](CKSD/Inference/Testing.lean#L491) (proved; scope in docstring).
- **101.53 Karlin–Rubin complete class theorem.**
  [CKSD.exists_one_sided_test_risk_le](CKSD/Inference/Testing.lean#L590) (proved; scope in docstring).
- **101.54 Least favorable distributions.**
  [CKSD.most_powerful_of_mixture_null](CKSD/Inference/Testing.lean#L681) (proved; scope in docstring).
- **101.55 Reduction by a maximal invariant.**
  [CKSD.invariant_iff_factors_through_maximal_invariant](CKSD/Inference/InvariantTesting.lean#L385) (proved; scope in docstring).
- **101.56 Normal tests as uniformly most powerful invariant tests.**
  [CKSD.mean_scale_ratio_eq_iff](CKSD/Inference/InvariantTesting.lean#L401) (proved; scope in docstring).
- **101.57 Estimation of a normal mean.**
  [CKSD.james_stein_risk_eq_and_lt](CKSD/Inference/Gaussian.lean#L377) (proved; scope in docstring).
- **101.58 Blyth's method.**
  [CKSD.isAdmissibleRisk_of_blyth](CKSD/Inference/Decision.lean#L348) (proved; scope in docstring).
- **101.60 Scheffé's method.**
  [CKSD.scheffe_contrast_supremum](CKSD/Inference/Gaussian.lean#L515) (proved; scope in docstring).
- **101.62 Blackwell's theorem.**
  [CKSD.isMoreInformative_iff_isGarbling](CKSD/Inference/Decision.lean#L437) (proved; scope in docstring).
- **101.64 Stein's identity and unbiased risk estimation.**
  [CKSD.gaussian_integration_by_parts](CKSD/Inference/Gaussian.lean#L72) (proved; scope in docstring).
- **101.69 Existence of an exponential-family maximum.**
  [CKSD.exists_isMaxOn_logLikelihood_iff_mem_interior_convexHull_support](CKSD/Inference/ExponentialFamilyMLE.lean#L348) (proved; scope in docstring).
  [CKSD.hasFDerivAt_logPartition_and_eq_of_isMaxOn](CKSD/Inference/ExponentialFamilyMLE.lean#L555) (proved; scope in docstring).

### Section 102

- **102.1 Delta method.**
  [CKSD.tendstoInDistribution_delta_method](CKSD/Asymptotics/Basic.lean#L313) (proved; scope in docstring).
- **102.2 Consistency of maximum likelihood.**
  [CKSD.tendstoInMeasure_mle_of_compact](CKSD/Asymptotics/MEstimators.lean#L188) (proved; scope in docstring).
- **102.3 Asymptotic normality of maximum likelihood.**
  [CKSD.mle_asymptotic_linearization_and_normality](CKSD/Asymptotics/MaximumLikelihood.lean#L29) (proved; scope in docstring).
- **102.4 Z-estimators.**
  [CKSD.zEstimator_asymptotic_linearization_and_normality](CKSD/Asymptotics/ZEstimators.lean#L468) (proved; scope in docstring).
- **102.6 Sample quantiles.**
  [CKSD.tendstoInDistribution_sampleQuantile](CKSD/Asymptotics/Quantiles.lean#L429) (proved; scope in docstring).
- **102.7 Bahadur representation of sample quantiles.**
  [CKSD.tendstoInMeasure_bahadur_remainder](CKSD/Asymptotics/Quantiles.lean#L352) (proved; scope in docstring).
- **102.8 Nondegenerate $U$-statistics.**
  [CKSD.tendstoInDistribution_uStatistic_of_nondegenerate](CKSD/Asymptotics/UStatistics.lean#L44) (proved; scope in docstring).
- **102.11 Likelihood-ratio, Wald, and score tests.**
  [CKSD.tendstoInDistribution_likelihoodRatio_wald_score_chiSquared](CKSD/Asymptotics/LikelihoodTests.lean#L681) (proved; scope in docstring).
  [CKSD.tendstoInDistribution_likelihoodRatio_wald_score_noncentralChiSquared](CKSD/Asymptotics/LikelihoodTests.lean#L767) (proved; scope in docstring).
- **102.12 Contiguity.**
  [CKSD.isContiguous_of_integral_likelihood_ratio_limit_eq_one](CKSD/Asymptotics/Experiments.lean#L49) (proved; scope in docstring).
- **102.13 Local asymptotic normality of smooth models.**
  [CKSD.tendstoInMeasure_log_likelihood_ratio_sub_of_dqm](CKSD/Asymptotics/Experiments.lean#L432) (proved; scope in docstring).
  [CKSD.tendstoInDistribution_score_and_log_likelihood_ratio_expansion_of_dqm](CKSD/Asymptotics/Experiments.lean#L697) (proved; scope in docstring).
- **102.14 Le Cam's third lemma.**
  [CKSD.tendstoInDistribution_of_log_likelihood_ratio](CKSD/Asymptotics/Experiments.lean#L141) (proved; scope in docstring).
- **102.15 Asymptotic representation theorem.**
  [CKSD.exists_gaussian_shift_kernel_of_local_limits](CKSD/Asymptotics/Framework.lean#L133) (proved; scope in docstring).
- **102.16 Convolution theorem.**
  [CKSD.exists_convolution_of_isRegularEstimator](CKSD/Asymptotics/Framework.lean#L250) (proved; scope in docstring).
- **102.17 Local asymptotic minimax theorem.**
  [CKSD.gaussian_risk_le_local_asymptotic_minimax](CKSD/Asymptotics/Framework.lean#L280) (admitted; scope in docstring).
- **102.21 Pitman efficiency and Noether's theorem.**
  [CKSD.tendsto_local_normal_power](CKSD/Asymptotics/Experiments.lean#L197) (proved; scope in docstring).
- **102.23 Consistency of $M$-estimators.**
  [CKSD.tendstoInMeasure_mEstimator](CKSD/Asymptotics/AsymptoticTheory.lean#L45) (proved; scope in docstring).
- **102.24 Asymptotic normality of $M$-estimators.**
  [CKSD.mEstimator_asymptotic_linearization_and_normality](CKSD/Asymptotics/MEstimatorNormality.lean#L770) (proved; scope in docstring).
- **102.25 Rate of convergence of $M$-estimators.**
  [CKSD.isBoundedInProbability_rate_mEstimator](CKSD/Asymptotics/RatesOfConvergence.lean#L52) (proved; scope in docstring).
- **102.28 Functional delta method.**
  [CKSD.tendstoInDistribution_of_hasHadamardFDerivAt](CKSD/Asymptotics/Framework.lean#L294) (proved; scope in docstring).
- **102.29 Hoeffding decomposition.**
  [CKSD.uStatistic_hoeffding_decomposition_and_variance](CKSD/Asymptotics/UStatistics.lean#L534) (proved; scope in docstring).
- **102.30 Degenerate quadratic $U$-statistics.**
  [CKSD.tendstoInDistribution_uStatistic_of_finite_rank_degenerate](CKSD/Asymptotics/UStatistics.lean#L757) (proved; scope in docstring).
- **102.31 Pearson's multinomial tests.**
  [CKSD.tendstoInDistribution_pearson_statistic](CKSD/Asymptotics/AsymptoticTheory.lean#L163) (proved; scope in docstring).
- **102.33 Argmax theorem.**
  [CKSD.tendstoInMeasure_argmax_of_compact](CKSD/Asymptotics/AsymptoticTheory.lean#L266) (proved; scope in docstring).
- **102.34 Semiparametric convolution bound.**
  [CKSD.exists_convolution_of_isRegularAlongPaths](CKSD/Asymptotics/Semiparametric.lean#L82) (admitted; scope in docstring).
  [CKSD.isRegularAlongPaths_gaussian_iff_asymptotically_linear](CKSD/Asymptotics/Semiparametric.lean#L104) (admitted; scope in docstring).
- **102.39 Cross-fitted estimation of a missing mean.**
  [CKSD.crossFittedAverage_missingMean_asymptotically_linear](CKSD/Asymptotics/CrossFitting.lean#L918) (proved; scope in docstring).
- **102.41 Adaptive estimation of a center of symmetry.**
  [CKSD.efficientScore_locationScore_eq](CKSD/Asymptotics/Semiparametric.lean#L198) (proved; scope in docstring).
  [CKSD.exists_adaptive_estimator_center_of_symmetry](CKSD/Asymptotics/Semiparametric.lean#L260) (admitted; scope in docstring).
- **102.44 $M$-estimators and the Huber minimax property.**
  [CKSD.integral_huberScore_sq_le](CKSD/Asymptotics/HigherOrder.lean#L186) (proved; scope in docstring).
- **102.48 Asymptotics of regression $M$-estimators.**
  [CKSD.regression_mEstimator_asymptotic_linearization_and_normality](CKSD/Asymptotics/RegressionMEstimators.lean#L116) (proved; scope in docstring).
- **102.49 One-term Edgeworth expansion.**
  [CKSD.exists_uniform_edgeworth_expansion](CKSD/Asymptotics/HigherOrder.lean#L285) (admitted; scope in docstring).
- **102.50 Edgeworth expansion for smooth functions of means.**
  [CKSD.exists_edgeworth_expansion_smooth_function_of_means](CKSD/Asymptotics/Expansions.lean#L40) (admitted; scope in docstring).
- **102.51 Bootstrap of the mean.**
  [CKSD.tendstoInMeasure_bootstrap_mean_kolmogorovDistance](CKSD/Asymptotics/HigherOrder.lean#L807) (proved; scope in docstring).
- **102.52 Bootstrap of the empirical distribution function.**
  [CKSD.tendstoInProbability_bootstrapBoundedLipschitzDistance](CKSD/Asymptotics/Bootstrap.lean#L66) (admitted; scope in docstring).
- **102.55 Saddlepoint approximation.**
  [CKSD.saddlepoint_approximation_sampleAverage_density](CKSD/Asymptotics/Expansions.lean#L66) (admitted; scope in docstring).
- **102.58 Čencov's theorem.**
  [CKSD.fisherRaoMetric_congruent_embedding](CKSD/Asymptotics/Framework.lean#L438) (proved; scope in docstring).
- **102.60 Second-order accuracy of the studentized bootstrap.**
  [CKSD.studentized_bootstrap_mean_second_order_accuracy](CKSD/Asymptotics/Bootstrap.lean#L85) (admitted; scope in docstring).

### Section 103

- **103.1 Kolmogorov–Smirnov statistic.**
  [CKSD.measure_kolmogorovSmirnovStatistic_gt_le](CKSD/Nonparametric/Estimation.lean#L67) (admitted; scope in docstring).
- **103.4 Kernel density asymptotics.**
  [CKSD.tendstoInDistribution_kernelDensityEstimator](CKSD/Nonparametric/Estimation.lean#L255) (proved; scope in docstring).
- **103.5 Universal $L^1$ consistency.**
  [CKSD.ae_tendsto_integral_abs_kernelDensityEstimator_sub](CKSD/Nonparametric/Estimation.lean#L437) (proved; scope in docstring).
- **103.7 Stone's theorem.**
  [CKSD.tendsto_nadarayaWatson_prediction_error_probability](CKSD/Nonparametric/SmoothingRates.lean#L59) (admitted; scope in docstring).
- **103.8 Representer theorem.**
  [CKSD.minimizer_mem_span_of_feature_vectors](CKSD/Nonparametric/Estimation.lean#L543) (proved; scope in docstring).
- **103.9 Pinsker's theorem and the Sobolev rate.**
  [CKSD.tendsto_gaussianSequenceMinimaxRisk_div_linear](CKSD/Nonparametric/Models.lean#L93) (admitted; scope in docstring).
- **103.11 Grenander estimator.**
  [CKSD.grenanderEstimator_isMaximumLikelihood](CKSD/Nonparametric/Grenander.lean#L452) (proved; scope in docstring).
  [CKSD.tendstoInDistribution_grenanderEstimator](CKSD/Nonparametric/Grenander.lean#L825) (admitted; scope in docstring).
- **103.14 Score-generating functions and locally most powerful rank tests.**
  [CKSD.integral_linearRankStatistic](CKSD/Nonparametric/Estimation.lean#L743) (proved; scope in docstring).
  [CKSD.variance_linearRankStatistic](CKSD/Nonparametric/Estimation.lean#L750) (proved; scope in docstring).
- **103.17 Cramér–von Mises and two-sample Kolmogorov–Smirnov limits.**
  [CKSD.map_cramerVonMisesStatistic_eq_uniform](CKSD/Nonparametric/GoodnessOfFit.lean#L129) (proved; scope in docstring).
  [CKSD.map_twoSampleKolmogorovSmirnovStatistic_eq_uniform](CKSD/Nonparametric/GoodnessOfFit.lean#L269) (proved; scope in docstring).
- **103.22 Hölder regression rates.**
  [CKSD.holderRegressionMinimaxRisk_le](CKSD/Nonparametric/HolderRegressionMinimax.lean#L64) (proved; scope in docstring).
  [CKSD.holderRegressionMinimaxRisk_ge](CKSD/Nonparametric/HolderRegressionMinimax.lean#L531) (proved; scope in docstring).
  [CKSD.holderRegressionMinimaxRisk_bounds](CKSD/Nonparametric/HolderRegressionMinimax.lean#L630) (proved; scope in docstring).
  [CKSD.fixedDesignLocalConstant_risk_le](CKSD/Nonparametric/SmoothingRates.lean#L259) (proved; scope in docstring).
- **103.26 Minimax rates of density estimation.**
  [CKSD.finiteKernelDensityEstimator_risk_le](CKSD/Nonparametric/HolderDensityMinimax.lean#L194) (proved; scope in docstring).
  [CKSD.holderDensityPointwiseMinimaxRisk_lower_bound](CKSD/Nonparametric/HolderDensityMinimax.lean#L739) (proved; scope in docstring).
- **103.27 Risk of isotonic regression.**
  [CKSD.existsUnique_isIsotonicRegressionEstimator](CKSD/Nonparametric/ShapeAndSelection.lean#L95) (proved; scope in docstring).
  [CKSD.isIsotonicRegressionEstimator_isotonicLeastSquares](CKSD/Nonparametric/ShapeAndSelection.lean#L226) (proved; scope in docstring).
  [CKSD.isotonicGaussianRisk_le](CKSD/Nonparametric/ShapeAndSelection.lean#L344) (admitted; scope in docstring).
  [CKSD.isotonicGaussianMinimaxRisk_lower_bound](CKSD/Nonparametric/ShapeAndSelection.lean#L669) (proved; scope in docstring).
- **103.28 Log-concave maximum likelihood.**
  [CKSD.existsUnique_isLogConcaveProjection](CKSD/Nonparametric/LogConcave.lean#L81) (admitted; scope in docstring).
  [CKSD.existsUnique_logConcaveMLE_tent](CKSD/Nonparametric/LogConcave.lean#L95) (admitted; scope in docstring).
  [CKSD.logConcaveMLE_hellingerRisk_le](CKSD/Nonparametric/LogConcave.lean#L106) (admitted; scope in docstring).
  [CKSD.logConcave_minimax_hellingerRisk_lower_bound](CKSD/Nonparametric/LogConcave.lean#L118) (admitted; scope in docstring).
- **103.29 Karhunen–Loève expansion and the Hilbertian central limit theorem.**
  [CKSD.tendstoInDistribution_hilbert_sampleAverage](CKSD/Nonparametric/HighDimensional.lean#L287) (proved; scope in docstring).
- **103.30 Principal components of the empirical covariance.**
  [CKSD.leading_empirical_covariance_eigenvalue_asymptotics](CKSD/Nonparametric/EmpiricalCovariance.lean#L349) (proved; scope in docstring).
  [CKSD.isBoundedInProbability_leading_empirical_eigenvector_error](CKSD/Nonparametric/EmpiricalCovariance.lean#L432) (proved; scope in docstring).
- **103.31 Optimality of functional principal components.**
  [CKSD.sum_ite_le_integral_norm_sub_sum_inner_smul_sq](CKSD/Nonparametric/HighDimensional.lean#L418) (proved; scope in docstring).
- **103.33 Sparse minimax rate.**
  [CKSD.sparseGaussianMinimaxRisk_bounds](CKSD/Nonparametric/Models.lean#L816) (proved; scope in docstring).
- **103.34 Lasso under compatibility.**
  [CKSD.IsLassoEstimator.restrictedL1Norm_compl_sub_le](CKSD/Nonparametric/HighDimensional.lean#L641) (proved; scope in docstring).
  [CKSD.IsLassoEstimator.norm_apply_sub_sq_div_le_of_hasCompatibility](CKSD/Nonparametric/HighDimensional.lean#L685) (proved; scope in docstring).
  [CKSD.IsLassoEstimator.restrictedL1Norm_sub_le](CKSD/Nonparametric/HighDimensional.lean#L703) (proved; scope in docstring).
- **103.35 Penalized model selection.**
  [CKSD.selectedProjectionRisk_oracle_bound](CKSD/Nonparametric/ShapeAndSelection.lean#L832) (proved; scope in docstring).
- **103.37 Benjamini–Hochberg procedure.**
  [CKSD.integral_benjaminiHochbergFalseDiscoveryProportion_le](CKSD/Nonparametric/HighDimensional.lean#L871) (proved; scope in docstring).
- **103.38 Tracy–Widom law and spiked covariance.**
  [CKSD.tendsto_largestSampleCovarianceEigenvalue_tracyWidom](CKSD/Nonparametric/TracyWidom.lean#L71) (admitted; scope in docstring).
  [CKSD.ae_tendsto_largestEigenvalue_spiked_subcritical](CKSD/Nonparametric/TracyWidom.lean#L93) (admitted; scope in docstring).
  [CKSD.ae_tendsto_largestEigenvalue_spiked_supercritical](CKSD/Nonparametric/TracyWidom.lean#L106) (admitted; scope in docstring).
- **103.39 Le Cam's two-point method.**
  [CKSD.one_sub_totalVariationDistance_div_two_le_max_measureReal](CKSD/Nonparametric/LowerBounds/Testing.lean#L50) (proved; scope in docstring).
- **103.40 Fano's method.**
  [CKSD.one_sub_div_log_le_sSup_measureReal](CKSD/Nonparametric/LowerBounds/Testing.lean#L128) (proved; scope in docstring).
- **103.45 Varshamov–Gilbert bound.**
  [CKSD.exists_hamming_packing](CKSD/Nonparametric/LowerBounds/Testing.lean#L233) (proved; scope in docstring).
- **103.46 Assouad's lemma.**
  [CKSD.mul_one_sub_div_two_le_sSup_integral_hammingDist](CKSD/Nonparametric/LowerBounds/Testing.lean#L354) (proved; scope in docstring).
- **103.48 Restricted nullspace and exact recovery.**
  [CKSD.hasNullspaceProperty_iff](CKSD/Nonparametric/SparseRecovery/Basic.lean#L80) (proved; scope in docstring).
  [CKSD.hasNullspaceProperty_of_hasRestrictedIsometry](CKSD/Nonparametric/SparseRecovery/Nullspace.lean#L231) (proved; scope in docstring).
- **103.49 Stable recovery under restricted isometry.**
  [CKSD.hasRobustNullspaceProperty_of_hasRestrictedIsometry](CKSD/Nonparametric/SparseRecovery/Robust.lean#L299) (proved; scope in docstring).
  [CKSD.exists_basisPursuit_error_bound](CKSD/Nonparametric/SparseRecovery/Robust.lean#L343) (proved; scope in docstring).
- **103.52 Thresholded covariance estimation.**
  [CKSD.norm_thresholded_covariance_sub_le](CKSD/Nonparametric/CovarianceThresholding.lean#L69) (proved; scope in docstring).
- **103.53 Gaussian graphical model selection.**
  [CKSD.neighbourhoodSelection_graph_recovery](CKSD/Nonparametric/GraphicalModels.lean#L97) (admitted; scope in docstring).
  [CKSD.graphicalLasso_frobenius_error_bound](CKSD/Nonparametric/GraphicalModels.lean#L138) (admitted; scope in docstring).
- **103.54 Perturbation of the leading eigenvector.**
  [CKSD.exists_eigenvector_norm_sub_le_of_rayleigh_gap](CKSD/Nonparametric/GoodnessOfFit.lean#L410) (proved; scope in docstring).

### Section 104

- **104.1 Bernstein–von Mises theorem.**
  [CKSD.tendstoInMeasure_totalVariationDistance_normalPosterior](CKSD/Bayes/Posterior.lean#L536) (proved; scope in docstring).
- **104.5 Laplace approximation and the BIC.**
  [CKSD.tendsto_laplace_approximation](CKSD/Bayes/Posterior.lean#L751) (proved; scope in docstring).
- **104.10 Highest posterior density regions.**
  [CKSD.volume_highest_density_region_le](CKSD/Bayes/Posterior.lean#L55) (proved; scope in docstring).
- **104.14 Tweedie's formula and Robbins' estimator.**
  [CKSD.integral_mul_gaussianPDFReal_div_eq_add_mul_deriv_log](CKSD/Bayes/Posterior.lean#L86) (proved; scope in docstring).
  [CKSD.integral_mul_poissonMass_div_eq](CKSD/Bayes/Posterior.lean#L176) (proved; scope in docstring).
  [CKSD.ae_tendsto_robbins_estimator](CKSD/Bayes/Posterior.lean#L193) (proved; scope in docstring).
- **104.15 Dirichlet process.**
  [CKSD.isDirichletProcess_stickBreaking](CKSD/Bayes/DirichletProcess.lean#L119) (proved; scope in docstring).
  [CKSD.ae_isDirichletProcessLaw_posterior](CKSD/Bayes/DirichletProcess.lean#L269) (proved; scope in docstring).
  [CKSD.ae_integral_posterior_eq_polyaPredictiveLaw](CKSD/Bayes/DirichletProcess.lean#L288) (proved; scope in docstring).
- **104.16 Pólya urn scheme and distinct values.**
  [CKSD.integral_distinctObservationCount_polya](CKSD/Bayes/PolyaUrn.lean#L137) (proved; scope in docstring).
  [CKSD.ae_tendsto_distinctObservationCount_div_log_polya](CKSD/Bayes/PolyaUrn.lean#L445) (proved; scope in docstring).
- **104.17 Doob's consistency theorem.**
  [CKSD.ae_isPosteriorConsistent_of_identifiable](CKSD/Bayes/Nonparametric.lean#L317) (proved; scope in docstring).
- **104.18 Schwartz's theorem.**
  [CKSD.tendstoInMeasure_posterior_compl_of_kl_support](CKSD/Bayes/PosteriorContraction.lean#L350) (proved; scope in docstring).
- **104.19 Contraction rate of Ghosal, Ghosh, and van der Vaart.**
  [CKSD.exists_posterior_hellinger_contraction](CKSD/Bayes/PosteriorContraction.lean#L639) (proved; scope in docstring).
- **104.20 Linear inverse problems.**
  [CKSD.tendsto_gaussianSeqPosterior_contraction](CKSD/Bayes/InverseProblems.lean#L412) (proved; scope in docstring).
  [CKSD.exists_minimax_rate_inverseProblem](CKSD/Bayes/InverseProblems.lean#L767) (proved; scope in docstring).
- **104.22 Metropolis–Hastings.**
  [CKSD.metropolisTransition_mem_rowStochastic](CKSD/Bayes/MonteCarlo.lean#L81) (proved; scope in docstring).
  [CKSD.metropolisTransition_detailedBalance](CKSD/Bayes/MonteCarlo.lean#L97) (proved; scope in docstring).
  [CKSD.sum_mul_metropolisTransition](CKSD/Bayes/MonteCarlo.lean#L115) (proved; scope in docstring).
- **104.24 Central limit theorem for Markov chain Monte Carlo.**
  [CKSD.tendstoInDistribution_finite_markov_chain_sum](CKSD/Bayes/MarkovChainCLT.lean#L403) (proved; scope in docstring).
- **104.31 Convergence of Metropolis–Hastings.**
  [CKSD.eventually_abs_metropolisTransition_pow_sub_le](CKSD/Bayes/MonteCarlo.lean#L318) (proved; scope in docstring).
  [CKSD.ae_tendsto_sampleAverage_metropolis](CKSD/Bayes/MonteCarlo.lean#L829) (proved; scope in docstring).
- **104.32 Independence and random-walk samplers.**
  [CKSD.abs_sum_independenceSampler_pow_sub_le](CKSD/Bayes/MonteCarlo.lean#L182) (proved; scope in docstring).
- **104.35 Hamiltonian Monte Carlo.**
  [CKSD.measurePreserving_leapfrogStep_iterate](CKSD/Bayes/MonteCarlo.lean#L272) (proved; scope in docstring).
  [CKSD.leapfrogStep_iterate_reversible](CKSD/Bayes/MonteCarlo.lean#L298) (proved; scope in docstring).
- **104.37 Invariant measure and gradient-flow structure.**
  [CKSD.integral_langevin_generator_eq_zero](CKSD/Bayes/Dynamics.lean#L53) (proved; scope in docstring).
- **104.38 Contraction under strong convexity.**
  [CKSD.dist_synchronous_langevin_le_exp](CKSD/Bayes/Dynamics.lean#L79) (proved; scope in docstring).
- **104.39 Iteration complexity of Langevin Monte Carlo.**
  [CKSD.exists_ula_iteration_complexity](CKSD/Bayes/LangevinSampling.lean#L106) (admitted; scope in docstring).
- **104.40 Robbins–Monro convergence and averaging.**
  [CKSD.ae_tendsto_robbins_monro](CKSD/Bayes/StochasticApproximation.lean#L469) (proved; scope in docstring).
- **104.41 Entropy dissipation of Langevin flow.**
  [CKSD.le_exp_neg_mul_of_hasDerivAt_neg_of_two_mul_le](CKSD/Bayes/Dynamics.lean#L147) (proved; scope in docstring).
- **104.43 Jordan–Kinderlehrer–Otto theorem.**
  [CKSD.jko_scheme_tendsto_fokkerPlanck](CKSD/Bayes/FunctionalInequalities.lean#L528) (admitted; scope in docstring).
- **104.44 Convergence of the Langevin diffusion under functional inequalities.**
  [CKSD.poincareInequality_iff_chiSqDiv_langevin_le](CKSD/Bayes/FunctionalInequalities.lean#L70) (admitted; scope in docstring).
  [CKSD.logSobolevInequality_iff_klDiv_langevin_le](CKSD/Bayes/FunctionalInequalities.lean#L82) (admitted; scope in docstring).
  [CKSD.wasserstein_sq_langevin_le_of_logSobolev](CKSD/Bayes/FunctionalInequalities.lean#L94) (admitted; scope in docstring).
  [CKSD.poincareInequality_of_logSobolevInequality](CKSD/Bayes/FunctionalInequalities.lean#L341) (proved; scope in docstring).
  [CKSD.logSobolevInequality_gibbsMeasure_of_bounded_perturbation](CKSD/Bayes/FunctionalInequalities.lean#L478) (proved; scope in docstring).
  [CKSD.poincareInequality_gibbsMeasure_of_bounded_perturbation](CKSD/Bayes/FunctionalInequalities.lean#L495) (proved; scope in docstring).
- **104.45 Langevin Monte Carlo under a logarithmic Sobolev inequality.**
  [CKSD.exists_klDiv_ula_le_of_logSobolev](CKSD/Bayes/LangevinSampling.lean#L126) (admitted; scope in docstring).
  [CKSD.exists_wasserstein_ula_le_of_stronglyConvex](CKSD/Bayes/LangevinSampling.lean#L142) (proved; scope in docstring).
- **104.47 Mixing of Metropolis-adjusted Langevin.**
  [CKSD.exists_mala_mixing_time_le](CKSD/Bayes/LangevinSampling.lean#L195) (admitted; scope in docstring).
  [CKSD.exists_mala_mixing_time_ge](CKSD/Bayes/LangevinSampling.lean#L240) (proved; scope in docstring).
- **104.48 Invariance, contraction, and hypocoercivity.**
  [CKSD.integral_kineticGenerator_eq_zero](CKSD/Bayes/KineticLangevin.lean#L276) (proved; scope in docstring).
  [CKSD.exists_kineticGenerator_not_symmetric](CKSD/Bayes/KineticLangevin.lean#L505) (proved; scope in docstring).
  [CKSD.kineticCouplingNorm_synchronous_le](CKSD/Bayes/KineticLangevin.lean#L818) (proved; scope in docstring).
  [CKSD.exists_kinetic_hypocoercive_decay_of_poincare](CKSD/Bayes/KineticLangevin.lean#L877) (admitted; scope in docstring).
  [CKSD.exists_kinetic_entropic_hypocoercive_decay](CKSD/Bayes/KineticLangevin.lean#L898) (admitted; scope in docstring).
- **104.49 Benaïm's limit-set theorem.**
  [CKSD.ae_isInternallyChainTransitive_limitSet](CKSD/Bayes/StochasticApproximation.lean#L597) (proved; scope in docstring).
  [CKSD.ae_tendsto_equilibrium_of_chainTransitive](CKSD/Bayes/StochasticApproximation.lean#L623) (proved; scope in docstring).
  [CKSD.ae_asymptotic_pseudotrajectory](CKSD/Bayes/StochasticApproximation.lean#L638) (proved; scope in docstring).
- **104.51 Propagation of chaos.**
  [CKSD.exists_unique_mcKeanVlasov_and_particleSystem](CKSD/Bayes/MeanField.lean#L98) (proved; scope in docstring).
  [CKSD.tendsto_particle_paths](CKSD/Bayes/MeanField.lean#L128) (proved; scope in docstring).
- **104.53 Mean-field training.**
  [CKSD.meanFieldRisk_eq](CKSD/Bayes/MeanField.lean#L575) (proved; scope in docstring).
  [CKSD.exists_meanField_limit](CKSD/Bayes/MeanField.lean#L656) (proved; scope in docstring).
- **104.55 Consistency of the particle filter.**
  [CKSD.tendstoInMeasure_particle_average](CKSD/Bayes/ParticleFilter.lean#L737) (proved; scope in docstring).
- **104.56 A quantitative interaction model.**
  [CKSD.exists_lintegral_sup_particle_sub_le](CKSD/Bayes/MeanField.lean#L506) (proved; scope in docstring).
- **104.58 Unbiased particle likelihood.**
  [CKSD.integral_particleLikelihood_eq](CKSD/Bayes/ParticleFilter.lean#L252) (proved; scope in docstring).
- **104.59 Central limit theorem for Feynman–Kac particle models.**
  [CKSD.tendstoInDistribution_particle_average](CKSD/Bayes/ParticleLimitCore.lean#L256) (proved; scope in docstring).
  [CKSD.tendstoInDistribution_particle_likelihood](CKSD/Bayes/ParticleLimitCore.lean#L340) (proved; scope in docstring).
- **104.60 Uniform-in-time particle approximation.**
  [CKSD.exists_uniform_particle_moment_bound](CKSD/Bayes/ParticleLimits.lean#L26) (proved; scope in docstring).
- **104.63 Anderson's time reversal and the probability-flow equation.**
  [CKSD.probabilityFlow_isContinuityEquation_and_map](CKSD/Bayes/DiffusionModels.lean#L76) (admitted; scope in docstring).
- **104.64 Score matching.**
  [CKSD.integral_sq_sub_score_div_two_eq](CKSD/Bayes/Dynamics.lean#L182) (proved; scope in docstring).
- **104.68 Score error and total variation.**
  [CKSD.totalVariationDistance_map_le_sqrt_klDiv](CKSD/Bayes/TestingBounds.lean#L28) (proved; scope in docstring).
- **104.75 Convergence of diffusion sampling under a second-moment assumption.**
  [CKSD.klDiv_ddpmLaw_le](CKSD/Bayes/DiffusionModels.lean#L127) (admitted; scope in docstring).
  [CKSD.exists_ddpm_geometric_schedule](CKSD/Bayes/DiffusionModels.lean#L146) (proved; scope in docstring).
  [CKSD.ddpmStepRatio_pos](CKSD/Bayes/DiffusionModels.lean#L214) (proved; scope in docstring).
  [CKSD.ddpmStepRatio_le_half](CKSD/Bayes/DiffusionModels.lean#L223) (proved; scope in docstring).
  [CKSD.div_two_mul_add_two_mul_ddpmStepRatio_eq](CKSD/Bayes/DiffusionModels.lean#L233) (proved; scope in docstring).
  [CKSD.one_add_inv_ddpmStepRatio_mul_log](CKSD/Bayes/DiffusionModels.lean#L256) (proved; scope in docstring).
- **104.76 A family of diffusions with prescribed marginals.**
  [CKSD.isFokkerPlanckSolution_add_score_of_continuityEquation](CKSD/Bayes/DiffusionModels.lean#L352) (proved; scope in docstring).
  [CKSD.map_marginalPreservingDiffusion](CKSD/Bayes/DiffusionModels.lean#L444) (admitted; scope in docstring).
  [CKSD.stochasticInterpolant_score](CKSD/Bayes/DiffusionModels.lean#L473) (proved; scope in docstring).
  [CKSD.stochasticInterpolant_integral_sub_eq_integral_velocity](CKSD/Bayes/DiffusionModels.lean#L545) (proved; scope in docstring).
- **104.77 Half-bridges and iterative proportional fitting.**
  [CKSD.klDiv_bridgeIterate_step](CKSD/Bayes/Bridges.lean#L56) (proved; scope in docstring).

### Section 105

- **105.1 Gauss–Markov theorem.**
  [CKSD.integral_inner_map_eq_of_map_integral_eq](CKSD/LinearModels/Regression.lean#L105) (proved; scope in docstring).
  [CKSD.variance_inner_map_le](CKSD/LinearModels/Regression.lean#L117) (proved; scope in docstring).
- **105.2 Normal sampling theory.**
  [CKSD.map_norm_sq_sub_div_eq_chiSquared](CKSD/LinearModels/Regression.lean#L163) (proved; scope in docstring).
  [CKSD.indepFun_map_norm_sq_sub](CKSD/LinearModels/Regression.lean#L190) (proved; scope in docstring).
- **105.3 Asymptotics of the generalised linear model.**
  [CKSD.tendstoInDistribution_canonicalGLM_root](CKSD/LinearModels/GLMAsymptotics.lean#L761) (proved; scope in docstring).
  [CKSD.tendstoInDistribution_canonicalGLM_deviance](CKSD/LinearModels/GLMAsymptotics.lean#L897) (proved; scope in docstring).
- **105.5 Quantile regression.**
  [CKSD.minimizes_expectedQuantileCheckLoss_iff](CKSD/LinearModels/RegressionLimits.lean#L150) (proved; scope in docstring).
  [CKSD.tendstoInDistribution_quantile_regression](CKSD/LinearModels/RegressionLimits.lean#L482) (proved; scope in docstring).
- **105.6 Finite normal mixtures.**
  [CKSD.GaussianMixtureModel.exists_equiv_of_law_eq](CKSD/LinearModels/Mixtures.lean#L103) (proved; scope in docstring).
  [CKSD.GaussianMixtureModel.not_bddAbove_logLikelihood](CKSD/LinearModels/Mixtures.lean#L179) (proved; scope in docstring).
- **105.10 Exact tests of nested linear models.**
  [CKSD.map_nestedFStatistic_eq_fisherSnedecor](CKSD/LinearModels/FTest.lean#L206) (proved; scope in docstring).
- **105.15 Distribution of quadratic forms.**
  [CKSD.indepFun_matrixQuadraticForm_iff](CKSD/LinearModels/Regression.lean#L507) (proved; scope in docstring).
- **105.16 Optimality of the $F$ test.**
  [CKSD.map_nestedFStatistic_eq_noncentralF](CKSD/LinearModels/FTest.lean#L97) (proved; scope in docstring).
  [CKSD.strictMono_noncentralF_upper_tail](CKSD/LinearModels/FTest.lean#L231) (proved; scope in docstring).
  [CKSD.fTest_isUniformlyMostPowerful_invariant](CKSD/LinearModels/FTest.lean#L336) (admitted; scope in docstring).
- **105.22 Wishart distribution and Hotelling's $T^2$.**
  [CKSD.gaussian_sampleMean_scatterMatrix_wishart_and_hotelling](CKSD/LinearModels/Multivariate.lean#L83) (proved; scope in docstring).
- **105.23 Wilks's lambda.**
  [CKSD.map_wilksLambda_wishart_eq_beta_product](CKSD/LinearModels/MultivariateTests.lean#L103) (proved; scope in docstring).
- **105.24 Principal component eigenvalues.**
  [CKSD.tendstoInDistribution_gaussian_sample_covariance_eigenvalue](CKSD/LinearModels/MultivariateTests.lean#L175) (proved; scope in docstring).
- **105.26 Undirected graphical models.**
  [CKSD.condIndepFun_multivariateGaussian_iff_inv_apply_eq_zero](CKSD/LinearModels/GaussianGraphical.lean#L251) (proved; scope in docstring).
  [CKSD.hasGaussianPairwiseMarkovProperty_iff_inv_mem_concentrationModel](CKSD/LinearModels/GaussianGraphical.lean#L347) (proved; scope in docstring).
- **105.28 Gaussian covariance likelihood.**
  [CKSD.gaussianNegLogLikelihood_sampleMean_le](CKSD/LinearModels/Multivariate.lean#L396) (proved; scope in docstring).
  [CKSD.gaussianNegLogLikelihood_eq_iff](CKSD/LinearModels/Multivariate.lean#L406) (proved; scope in docstring).
- **105.29 Canonical correlations.**
  [CKSD.charpoly_canonicalCorrelationMatrix_transform](CKSD/LinearModels/CanonicalCorrelation.lean#L128) (proved; scope in docstring).
  [CKSD.norm_canonicalCorrelationMatrix_le_one](CKSD/LinearModels/CanonicalCorrelation.lean#L306) (proved; scope in docstring).
  [CKSD.isGreatest_linearCombinationCorrelation](CKSD/LinearModels/CanonicalCorrelation.lean#L334) (proved; scope in docstring).
  [CKSD.indepFun_gaussian_blocks_iff_canonicalCorrelationMatrix_eq_zero](CKSD/LinearModels/CanonicalCorrelation.lean#L407) (proved; scope in docstring).
- **105.31 Structure of the Wishart law.**
  [CKSD.wishart_determinant_law](CKSD/LinearModels/Multivariate.lean#L417) (proved; scope in docstring).
- **105.32 Sampling theory of correlation coefficients.**
  [CKSD.gaussian_sample_correlation_student_law](CKSD/LinearModels/Multivariate.lean#L695) (proved; scope in docstring).
- **105.33 Likelihood-ratio tests of sphericity and independence.**
  [CKSD.tendstoInDistribution_sphericity_likelihood_ratio](CKSD/LinearModels/MultivariateTests.lean#L232) (proved; scope in docstring).
  [CKSD.tendstoInDistribution_block_independence_likelihood_ratio](CKSD/LinearModels/MultivariateTests.lean#L304) (proved; scope in docstring).
- **105.34 Invariant tests of a multivariate linear hypothesis.**
  [CKSD.multivariateHypothesisRoots_eq_iff_congruent](CKSD/LinearModels/MultivariateTests.lean#L390) (proved; scope in docstring).
  [CKSD.multivariate_test_statistics_eq_roots](CKSD/LinearModels/MultivariateTests.lean#L567) (proved; scope in docstring).
- **105.35 Factor analysis and identification.**
  [CKSD.IsNormalizedFactorLoading.exists_eq_mul_factorColumnSigns](CKSD/LinearModels/FactorAnalysis.lean#L101) (proved; scope in docstring).
  [CKSD.tendstoInMeasure_factor_mle_of_compact](CKSD/LinearModels/FactorAnalysis.lean#L326) (proved; scope in docstring).
- **105.36 Decomposable models.**
  [CKSD.isUndirectedGlobalMarkovMass_iff_clique_factorization](CKSD/LinearModels/Decomposable.lean#L377) (proved; scope in docstring).
  [CKSD.existsUnique_isConcentrationMLE_inv](CKSD/LinearModels/DecomposableGaussian.lean#L343) (proved; scope in docstring).
  [CKSD.isConcentrationMLE_decomposableConcentrationMLE](CKSD/LinearModels/DecomposableGaussian.lean#L785) (proved; scope in docstring).
- **105.37 Kiefer–Wolfowitz equivalence.**
  [CKSD.kiefer_wolfowitz_equivalence](CKSD/LinearModels/Design.lean#L218) (proved; scope in docstring).
- **105.38 Randomization test.**
  [CKSD.sum_ite_randomizationPValue_le](CKSD/LinearModels/Design.lean#L252) (proved; scope in docstring).
- **105.42 Fisher's inequality and optimality of balanced incomplete blocks.**
  [CKSD.fisher_inequality](CKSD/LinearModels/Design.lean#L281) (proved; scope in docstring).
- **105.44 Latin squares and mutually orthogonal sets.**
  [CKSD.card_le_sub_one_of_orthogonalLatinSquares](CKSD/LinearModels/Design.lean#L368) (proved; scope in docstring).
  [CKSD.exists_orthogonalLatinSquares_of_isPrimePow](CKSD/LinearModels/Design.lean#L433) (proved; scope in docstring).
- **105.72 Horvitz–Thompson estimation and design variance.**
  [CKSD.integral_horvitzThompson](CKSD/LinearModels/SurveySampling.lean#L618) (proved; scope in docstring).
  [CKSD.variance_horvitzThompson](CKSD/LinearModels/SurveySampling.lean#L625) (proved; scope in docstring).
  [CKSD.integral_horvitzThompsonVarianceEstimator](CKSD/LinearModels/SurveySampling.lean#L635) (proved; scope in docstring).
  [CKSD.variance_horvitzThompson_eq_sen_yates_grundy](CKSD/LinearModels/SurveySampling.lean#L643) (proved; scope in docstring).
- **105.73 Simple and stratified random sampling; Neyman allocation.**
  [CKSD.integral_sum_div_simpleRandomSampleDesign](CKSD/LinearModels/SurveySampling.lean#L670) (proved; scope in docstring).
  [CKSD.variance_sum_div_simpleRandomSampleDesign](CKSD/LinearModels/SurveySampling.lean#L677) (proved; scope in docstring).
  [CKSD.sq_sum_div_le_sum_sq_div_of_sum_eq](CKSD/LinearModels/SurveySampling.lean#L688) (proved; scope in docstring).
  [CKSD.sq_sum_div_eq_sum_sq_div_iff](CKSD/LinearModels/SurveySampling.lean#L697) (proved; scope in docstring).
- **105.46 Neyman's theorem.**
  [CKSD.integral_differenceInMeans](CKSD/LinearModels/SurveySampling.lean#L715) (proved; scope in docstring).
  [CKSD.variance_differenceInMeans](CKSD/LinearModels/SurveySampling.lean#L724) (proved; scope in docstring).
- **105.47 Identification by regression and by weighting.**
  [CKSD.integral_potentialOutcome_eq_sum_stratumOutcomeMean](CKSD/LinearModels/CausalAndSurvey.lean#L304) (proved; scope in docstring).
  [CKSD.integral_potentialOutcome_eq_integral_div_propensity](CKSD/LinearModels/CausalAndSurvey.lean#L328) (proved; scope in docstring).
- **105.48 Propensity score.**
  [CKSD.condIndepFun_propensityScore](CKSD/LinearModels/CausalEfficiency.lean#L139) (proved; scope in docstring).
  [CKSD.condIndepFun_of_propensityScore](CKSD/LinearModels/CausalEfficiency.lean#L169) (proved; scope in docstring).
- **105.49 Doubly robust estimator of the average treatment effect.**
  [CKSD.integral_treatmentEffectInfluence_sub_eq_sum_mul](CKSD/LinearModels/CausalAndSurvey.lean#L352) (proved; scope in docstring).
- **105.50 Local average treatment effect.**
  [CKSD.wald_ratio_eq_complier_average_effect](CKSD/LinearModels/CausalAndSurvey.lean#L381) (proved; scope in docstring).
- **105.55 Two-stage least squares.**
  [CKSD.tendstoInMeasure_twoStageLeastSquares](CKSD/LinearModels/InstrumentalVariables.lean#L337) (proved; scope in docstring).
  [CKSD.tendstoInDistribution_twoStageLeastSquares](CKSD/LinearModels/InstrumentalVariables.lean#L538) (proved; scope in docstring).
- **105.56 Efficient variance for an average treatment effect.**
  [CKSD.integral_finiteStrataTreatmentInfluence](CKSD/LinearModels/CausalEfficiency.lean#L455) (proved; scope in docstring).
  [CKSD.variance_finiteStrataTreatmentInfluence](CKSD/LinearModels/CausalEfficiency.lean#L469) (proved; scope in docstring).
  [CKSD.hasDerivAt_finiteStrataTreatmentEffect_score_tilt](CKSD/LinearModels/CausalEfficiency.lean#L524) (proved; scope in docstring).
- **105.62 Directed Markov properties.**
  [CKSD.condIndepMass_directedFactorizationMass_of_dSeparated](CKSD/LinearModels/DirectedGraphical/Basic.lean#L491) (proved; scope in docstring).
  [CKSD.CausalGraph.recursivelyFactorizes_tfae](CKSD/LinearModels/DirectedGraphical/Markov.lean#L296) (proved; scope in docstring).
- **105.63 Back-door and front-door formulae.**
  [CKSD.doMarginalMass_eq_backdoor](CKSD/LinearModels/DirectedGraphical/Markov.lean#L336) (proved; scope in docstring).
  [CKSD.doMarginalMass_eq_frontdoor](CKSD/LinearModels/DirectedGraphical/Markov.lean#L387) (proved; scope in docstring).
- **105.64 Rules of the do-calculus.**
  [CKSD.condDoMass_rule_three](CKSD/LinearModels/DirectedGraphical/DoCalculus.lean#L463) (proved; scope in docstring).
  [CKSD.condDoMass_rule_one](CKSD/LinearModels/DirectedGraphical/Interventions.lean#L414) (proved; scope in docstring).
  [CKSD.condDoMass_rule_two](CKSD/LinearModels/DirectedGraphical/Interventions.lean#L439) (proved; scope in docstring).
- **105.65 Longitudinal $g$-formula.**
  [CKSD.integral_potentialOutcome_eq_gFormula](CKSD/LinearModels/GFormula.lean#L248) (proved; scope in docstring).
- **105.67 Markov equivalence of directed graphs.**
  [CKSD.markovEquivalent_iff_skeleton_and_colliders](CKSD/LinearModels/DirectedGraphical/Basic/CausalGraph.lean#L134) (admitted; scope in docstring).
  [CKSD.CausalGraph.isUnshieldedCollider_iff_of_isFaithful](CKSD/LinearModels/DirectedGraphical/Discovery.lean#L159) (proved; scope in docstring).
- **105.70 Skeleton and colliders from conditional independences.**
  [CKSD.CausalGraph.dSeparated_parents_of_not_adjacent](CKSD/LinearModels/DirectedGraphical/Discovery.lean#L40) (proved; scope in docstring).
  [CKSD.CausalGraph.adjacent_iff_forall_not_dSeparated](CKSD/LinearModels/DirectedGraphical/Discovery.lean#L51) (proved; scope in docstring).
  [CKSD.CausalGraph.isCollider_iff_notMem_of_dSeparated](CKSD/LinearModels/DirectedGraphical/Discovery.lean#L78) (proved; scope in docstring).
  [CKSD.CausalGraph.adjacent_iff_of_isFaithful](CKSD/LinearModels/DirectedGraphical/Discovery.lean#L124) (proved; scope in docstring).
  [CKSD.CausalGraph.isUnshieldedCollider_iff_of_isFaithful](CKSD/LinearModels/DirectedGraphical/Discovery.lean#L159) (proved; scope in docstring).
- **105.71 Identifiability of restricted structural equation models.**
  [CKSD.CausalGraph.edge_eq_of_linearSEMLaw_eq_of_nonGaussian](CKSD/LinearModels/StructuralEquations.lean#L107) (admitted; scope in docstring).
  [CKSD.CausalGraph.edge_eq_of_linearSEMLaw_eq_of_equalVariance](CKSD/LinearModels/StructuralEquations.lean#L295) (proved; scope in docstring).
  [CKSD.CausalGraph.edge_eq_of_additiveNoiseLaw_eq](CKSD/LinearModels/StructuralEquations.lean#L348) (admitted; scope in docstring).
  [CKSD.CausalGraph.exists_linearGaussianSEM_iff_markovEquivalent](CKSD/LinearModels/StructuralEquations.lean#L365) (admitted; scope in docstring).

### Section 106

- **106.1 Martingale central limit theorem.**
  [CKSD.tendstoInDistribution_martingale_array_sum](CKSD/Processes/TimeSeries/CentralLimit.lean#L78) (proved; scope in docstring).
- **106.2 Wold decomposition and causal autoregression.**
  [CKSD.exists_wold_decomposition](CKSD/Processes/TimeSeries/Wold.lean#L489) (proved; scope in docstring).
- **106.4 Bartlett's theorem.**
  [CKSD.tendstoInDistribution_sample_autocorrelations](CKSD/Processes/TimeSeries/SampleAutocorrelation.lean#L800) (proved; scope in docstring).
- **106.6 Periodogram and lag-window estimation.**
  [CKSD.tendstoInDistribution_periodogram_div_spectralDensity](CKSD/Processes/Spectral.lean#L102) (proved; scope in docstring).
  [CKSD.tendsto_lagWindowEstimator_moments](CKSD/Processes/Spectral.lean#L125) (admitted; scope in docstring).
- **106.7 Kalman filter.**
  [CKSD.KalmanModel.kalman_filter](CKSD/Processes/Kalman/Filter.lean#L425) (proved; scope in docstring).
- **106.11 Moving-block bootstrap.**
  [CKSD.tendstoInMeasure_kolmogorovDistance_movingBlockBootstrapLaw](CKSD/Processes/Dependence.lean#L105) (admitted; scope in docstring).
- **106.12 Long-run variance of a sample mean.**
  [CKSD.tendsto_mul_variance_sampleAverage](CKSD/Processes/TimeSeries/LongRunVariance.lean#L123) (proved; scope in docstring).
- **106.14 Herglotz theorem and rational spectral densities.**
  [CKSD.IsPositiveSemidefiniteSequence.exists_stationary_gaussian](CKSD/Processes/TimeSeries/StationaryGaussian.lean#L169) (proved; scope in docstring).
- **106.16 Kolmogorov's formula for the prediction error.**
  [CKSD.infDist_past_sq_eq_kolmogorov](CKSD/Processes/Spectral.lean#L146) (admitted; scope in docstring).
- **106.17 Asymptotic covariance of ARMA estimators.**
  [CKSD.tendsto_whittleEstimator](CKSD/Processes/Spectral.lean#L210) (admitted; scope in docstring).
- **106.18 Stationarity of GARCH$(1,1)$.**
  [CKSD.ae_summable_garchTerm](CKSD/Processes/TimeSeries/Garch.lean#L173) (proved; scope in docstring).
  [CKSD.integral_garchVariance](CKSD/Processes/TimeSeries/Garch.lean#L231) (proved; scope in docstring).
  [CKSD.garchVariance_ae_eq](CKSD/Processes/TimeSeries/Garch.lean#L245) (proved; scope in docstring).
  [CKSD.covariance_garchProcess](CKSD/Processes/TimeSeries/Garch.lean#L293) (proved; scope in docstring).
- **106.21 Stein's prediction theorem.**
  [CKSD.eventually_abs_linearPredictionError_div_sub_one_le](CKSD/Processes/Dependence.lean#L144) (admitted; scope in docstring).
- **106.24 Bochner's theorem and the Matérn family.**
  [CKSD.exists_stationary_field_of_spectral_measure](CKSD/Processes/Spectral.lean#L342) (proved; scope in docstring).
- **106.28 Nelson–Aalen estimator.**
  [CKSD.tendstoInDistribution_nelsonAalenEstimator](CKSD/Processes/Survival.lean#L537) (proved; scope in docstring).
- **106.29 Kaplan–Meier estimator.**
  [CKSD.tendstoInDistribution_kaplanMeierEstimator](CKSD/Processes/Survival.lean#L806) (proved; scope in docstring).
- **106.30 Cox partial likelihood.**
  [CKSD.tendsto_coxPartialLikelihoodMaximizer](CKSD/Processes/CountingProcesses.lean#L86) (admitted; scope in docstring).
- **106.34 Rebolledo's martingale central limit theorem.**
  [CKSD.tendstoInDistribution_countingMartingaleTransform](CKSD/Processes/CountingProcesses.lean#L151) (admitted; scope in docstring).
- **106.37 Sequential probability ratio test.**
  [CKSD.integrable_stopped_sum](CKSD/Processes/Sequential.lean#L118) (proved; scope in docstring).
  [CKSD.integral_stopped_sum_eq](CKSD/Processes/Sequential.lean#L128) (proved; scope in docstring).
- **106.38 Ville's inequality and e-values.**
  [CKSD.measure_iSup_supermartingale_ge_le](CKSD/Processes/Sequential.lean#L181) (proved; scope in docstring).
- **106.39 CUSUM and the Brownian bridge.**
  [CKSD.tendstoInDistribution_cusumBridgeStatistic](CKSD/Processes/BridgeLimits.lean#L35) (admitted; scope in docstring).
- **106.41 Wald's fundamental identity and the operating characteristic.**
  [CKSD.integral_stopped_exponential_eq_one](CKSD/Processes/WaldIdentity.lean#L68) (proved; scope in docstring).
- **106.42 Anscombe's theorem.**
  [CKSD.tendstoInDistribution_random_sampleAverage](CKSD/Processes/Sequential.lean#L583) (proved; scope in docstring).
- **106.44 Optimality of CUSUM.**
  [CKSD.cusumStatistic_le_shiryaevRobertsStatistic](CKSD/Processes/Models.lean#L75) (proved; scope in docstring).
- **106.46 Fisher–Tippett–Gnedenko theorem.**
  [CKSD.tendsto_maximum_of_hasRegularlyVaryingTail](CKSD/Processes/Extremes.lean#L251) (proved; scope in docstring).
- **106.47 Excesses over high thresholds.**
  [CKSD.hasExtremeValueDomainOfAttraction_iff_pareto_excesses](CKSD/Processes/ExtremeValueLimits.lean#L76) (admitted; scope in docstring).
- **106.48 Extremal index.**
  [CKSD.tendstoInDistribution_card_exceedances](CKSD/Processes/Extremes.lean#L269) (proved; scope in docstring).
- **106.49 Hill estimator.**
  [CKSD.tendstoInDistribution_hillEstimator](CKSD/Processes/ExtremeValueLimits.lean#L106) (admitted; scope in docstring).
- **106.50 Poisson approximation for exceedances.**
  [CKSD.tendstoInDistribution_card_exceedances](CKSD/Processes/Extremes.lean#L269) (proved; scope in docstring).

### Section 107

- **107.1 Fundamental theorem of statistical learning.**
  [CKSD.measure_uniform_empirical_risk_deviation_le](CKSD/Learning/Generalization/Concentration.lean#L44) (proved; scope in docstring).
- **107.2 Rademacher bound.**
  [CKSD.integral_sSup_sub_le_two_mul_rademacher](CKSD/Learning/Generalization/Concentration.lean#L257) (proved; scope in docstring).
  [CKSD.measureReal_two_mul_rademacher_add_lt_sSup_le](CKSD/Learning/Generalization/Concentration.lean#L442) (proved; scope in docstring).
- **107.5 Hedge.**
  [CKSD.hedge_regret_le](CKSD/Learning/Generalization/ExponentialWeights.lean#L71) (proved; scope in docstring).
- **107.6 Split conformal prediction.**
  [CKSD.div_le_measureReal_conformalEvent](CKSD/Learning/Generalization/Conformal.lean#L211) (proved; scope in docstring).
  [CKSD.measureReal_conformalEvent_eq_div](CKSD/Learning/Generalization/Conformal.lean#L232) (proved; scope in docstring).
- **107.7 No free lunch.**
  [CKSD.exists_labelling_le_average_error](CKSD/Learning/Generalization/Classification.lean#L60) (proved; scope in docstring).
- **107.8 Bayes classification risk.**
  [CKSD.classificationRisk_sub_bayes_risk_eq](CKSD/Learning/Generalization/Classification.lean#L157) (proved; scope in docstring).
  [CKSD.classificationRisk_plugin_sub_bayes_risk_le](CKSD/Learning/Generalization/Classification.lean#L184) (proved; scope in docstring).
- **107.10 Margin bound.**
  [CKSD.measure_margin_generalization_error_le](CKSD/Learning/MarginsAndBandits.lean#L68) (proved; scope in docstring).
- **107.11 Comparison inequality for convex surrogates.**
  [CKSD.surrogate_minimizer_sign_of_convex](CKSD/Learning/Generalization/Classification.lean#L216) (proved; scope in docstring).
- **107.12 Generalization of stable algorithms.**
  [CKSD.measureReal_sum_div_add_lt_integral_le_of_stable](CKSD/Learning/Generalization/Stability.lean#L193) (proved; scope in docstring).
- **107.13 Rate of kernel ridge regression.**
  [CKSD.ridgePrediction_oracle_bounds](CKSD/Learning/KernelAndClustering.lean#L310) (proved; scope in docstring).
- **107.14 Asymptotics of nearest-neighbour rules.**
  [CKSD.tendsto_oneNN_expectedError](CKSD/Learning/LocalAveraging.lean#L79) (admitted; scope in docstring).
  [CKSD.bayesRisk_le_nnRisk_le](CKSD/Learning/LocalAveraging.lean#L87) (proved; scope in docstring).
  [CKSD.exists_tendsto_knn_expectedError](CKSD/Learning/LocalAveraging.lean#L131) (admitted; scope in docstring).
  [CKSD.tendsto_knn_expectedError_bayesRisk](CKSD/Learning/LocalAveraging.lean#L142) (admitted; scope in docstring).
- **107.16 Consistency of $k$-means.**
  [CKSD.ae_tendsto_kmeans_centers_of_compact](CKSD/Learning/KernelAndClustering.lean#L534) (proved; scope in docstring).
- **107.19 Belief propagation and the Bethe free energy.**
  [CKSD.isBetheStationary_iff_exists_beliefPropagationFixedPoint](CKSD/Learning/GraphicalModels.lean#L673) (proved; scope in docstring).
- **107.20 Consistency of response-independent forests.**
  [CKSD.tendsto_localAveraging_sq_error](CKSD/Learning/LocalAveraging.lean#L156) (admitted; scope in docstring).
- **107.23 Exact belief propagation on a tree.**
  [CKSD.exists_beliefPropagation_exact_on_tree](CKSD/Learning/BeliefPropagationTree.lean#L557) (proved; scope in docstring).
  [CKSD.beliefPropagation_tree_unique_up_to_scale](CKSD/Learning/BeliefPropagationTree.lean#L625) (proved; scope in docstring).
- **107.24 AdaBoost: training error and margins.**
  [CKSD.training_error_le_exponential_loss](CKSD/Learning/Algorithms.lean#L98) (proved; scope in docstring).
- **107.26 Variational representation of the cumulant function.**
  [CKSD.sum_mul_sub_mul_log_le_log_sum_exp](CKSD/Learning/Models.lean#L52) (proved; scope in docstring).
  [CKSD.sum_softmax_mul_sub_mul_log_eq_log_sum_exp](CKSD/Learning/Models.lean#L80) (proved; scope in docstring).
  [CKSD.tendsto_log_sum_exp_div_atTop](CKSD/Learning/Models.lean#L97) (proved; scope in docstring).
- **107.27 Junction-tree exactness.**
  [CKSD.hasJunctionTree_iff_isTriangulated](CKSD/Learning/JunctionTree.lean#L69) (proved; scope in docstring).
  [CKSD.sum_eq_one_and_tableMarginal_eq_of_jointMarginal](CKSD/Learning/JunctionTree.lean#L427) (proved; scope in docstring).
  [CKSD.junctionTreeProduct_isJointLaw](CKSD/Learning/JunctionTree.lean#L440) (proved; scope in docstring).
  [CKSD.exists_joint_with_clique_marginals_iff](CKSD/Learning/JunctionTree.lean#L546) (proved; scope in docstring).
- **107.28 Barron's rate.**
  [CKSD.exists_logisticNetwork_sq_error_le_barron_moment](CKSD/Learning/Approximation.lean#L58) (admitted; scope in docstring).
  [CKSD.exists_feature_average_sq_error_le](CKSD/Learning/Approximation.lean#L98) (proved; scope in docstring).
- **107.29 Deep networks and compositional classes.**
  [CKSD.compositionalHolder_minimax_lower_bound](CKSD/Learning/Networks.lean#L652) (admitted; scope in docstring).
- **107.30 Neural tangent kernel.**
  [CKSD.hasDerivAt_predictions_of_gradient_flow](CKSD/Learning/Models.lean#L140) (proved; scope in docstring).
- **107.31 Ridgeless least squares.**
  [CKSD.ridgeless_gaussian_risk_eq](CKSD/Learning/Models.lean#L319) (proved; scope in docstring).
- **107.35 Capacity of network classes.**
  [CKSD.card_le_of_shatters_denseSignClass](CKSD/Learning/Networks.lean#L98) (admitted; scope in docstring).
  [CKSD.empiricalRademacherComplexity_biasFree_le](CKSD/Learning/Networks.lean#L523) (proved; scope in docstring).
- **107.36 Approximation rates of deep ReLU networks.**
  [CKSD.abs_reluLinearInterpolant_sub_le](CKSD/Learning/Approximation.lean#L272) (proved; scope in docstring).
- **107.37 Depth separation.**
  [CKSD.relu_depth_lower_bound](CKSD/Learning/Networks.lean#L581) (admitted; scope in docstring).
  [CKSD.relu_eldan_shamir_separation](CKSD/Learning/Networks.lean#L597) (admitted; scope in docstring).
- **107.39 Gaussian-process limit at initialization.**
  [CKSD.tendstoInDistribution_wide_network_gaussian](CKSD/Learning/Networks.lean#L688) (proved; scope in docstring).
- **107.40 Implicit bias of gradient descent.**
  [CKSD.tendsto_least_squares_gradient_descent](CKSD/Learning/Models.lean#L362) (proved; scope in docstring).
- **107.41 Exact recovery.**
  [CKSD.exists_exactRecovery_iff](CKSD/Learning/RandomGraphs.lean#L82) (admitted; scope in docstring).
  [CKSD.exists_exactRecovery_iff_of_zero](CKSD/Learning/RandomGraphs.lean#L89) (admitted; scope in docstring).
- **107.42 Kesten–Stigum threshold.**
  [CKSD.exists_weakRecovery_iff](CKSD/Learning/RandomGraphs.lean#L97) (admitted; scope in docstring).
  [CKSD.blockModel_binomialRandom_mutually_contiguous](CKSD/Learning/RandomGraphs.lean#L106) (admitted; scope in docstring).
- **107.43 Aldous–Hoover theorem for graphs.**
  [CKSD.existsUnique_graphonMixture_of_finitePerm_invariant](CKSD/Learning/RandomGraphs.lean#L228) (proved; scope in docstring).
  [CKSD.infiniteSampleLaw_eq_iff_exists_measurePreserving](CKSD/Learning/RandomGraphs.lean#L241) (admitted; scope in docstring).
- **107.47 Phase transitions of the Erdős–Rényi graph.**
  [CKSD.tendsto_binomialRandom_connected_threshold](CKSD/Learning/RandomGraphs/ConnectivityThreshold.lean#L239) (proved; scope in docstring).
  [CKSD.tendsto_binomialRandom_connected_of_tendsto_atTop](CKSD/Learning/RandomGraphs/ConnectivityThreshold.lean#L327) (proved; scope in docstring).
  [CKSD.tendsto_binomialRandom_exists_isolated_of_tendsto_atBot](CKSD/Learning/RandomGraphs/ConnectivityThreshold.lean#L354) (proved; scope in docstring).
  [CKSD.exists_tendsto_binomialRandom_components_le_log'](CKSD/Learning/RandomGraphs/Subcritical.lean#L510) (proved; scope in docstring).
  [CKSD.exists_tendsto_binomialRandom_components_le_log](CKSD/Learning/RandomGraphs.lean#L124) (proved; scope in docstring).
  [CKSD.binomialRandom_giant_component](CKSD/Learning/RandomGraphs.lean#L134) (admitted; scope in docstring).
  [CKSD.binomialRandom_connectivity_threshold](CKSD/Learning/RandomGraphs.lean#L148) (proved; scope in docstring).
- **107.49 Lai–Robbins lower bound.**
  [CKSD.lai_robbins_lower_bound](CKSD/Learning/Bandits.lean#L106) (admitted; scope in docstring).
- **107.50 Upper confidence bounds.**
  [CKSD.integral_regret_le_of_ucb](CKSD/Learning/UCBAnalysis.lean#L529) (proved; scope in docstring).
- **107.51 Thompson sampling and the Gittins index.**
  [CKSD.tendsto_thompson_regret_div_log](CKSD/Learning/Bandits.lean#L142) (admitted; scope in docstring).
  [CKSD.banditPolicyValue_le_of_gittins](CKSD/Learning/Policies.lean#L520) (admitted; scope in docstring).
- **107.52 Adversarial bandits.**
  [CKSD.integral_regret_le_of_exp3](CKSD/Learning/MarginsAndBandits.lean#L262) (proved; scope in docstring).
- **107.54 Convergence of $Q$-learning.**
  [CKSD.ae_tendsto_asynchronous_stochastic_approximation](CKSD/Learning/MarkovDecision.lean#L379) (admitted; scope in docstring).
- **107.58 Stationary optimal policies and linear programming.**
  [CKSD.bellmanOperator_optimalStateValue](CKSD/Learning/MarkovDecision.lean#L134) (proved; scope in docstring).
  [CKSD.exists_greedy_optimalStateValue](CKSD/Learning/MarkovDecision.lean#L140) (proved; scope in docstring).
  [CKSD.optimalStateValue_le_of_forall_le](CKSD/Learning/MarkovDecision.lean#L151) (proved; scope in docstring).
  [CKSD.sum_mul_optimalStateValue_le](CKSD/Learning/MarkovDecision.lean#L172) (proved; scope in docstring).
  [CKSD.sum_mul_optimalStateValue_eq_iff](CKSD/Learning/MarkovDecision.lean#L180) (proved; scope in docstring).
  [CKSD.banditPolicyValue_le_of_gittins](CKSD/Learning/Policies.lean#L520) (admitted; scope in docstring).
- **107.59 Sample complexity with a generative model.**
  [CKSD.inv_one_sub_smul_mulVec_sub_eq](CKSD/Learning/MarkovDecision.lean#L310) (proved; scope in docstring).
  [CKSD.norm_inv_one_sub_smul_mulVec_sub_le](CKSD/Learning/MarkovDecision.lean#L327) (proved; scope in docstring).
- **107.60 Temporal differences with linear features.**
  [CKSD.norm_projected_fixed_point_sub_le](CKSD/Learning/MarkovDecision.lean#L346) (proved; scope in docstring).
- **107.61 Convergence of natural policy gradient.**
  [CKSD.optimalObjective_sub_npg_le](CKSD/Learning/Policies.lean#L439) (proved; scope in docstring).
- **107.62 Minimax regret of finite-armed bandits.**
  [CKSD.exists_bernoulli_banditRegret_ge](CKSD/Learning/Bandits.lean#L159) (admitted; scope in docstring).
  [CKSD.exists_ucb1_banditRegret_le](CKSD/Learning/Bandits.lean#L652) (proved; scope in docstring).
- **107.63 Self-normalized confidence and LinUCB.**
  [CKSD.measure_exists_selfNormalized_gt_le](CKSD/Learning/Bandits.lean#L737) (admitted; scope in docstring).
  [CKSD.exists_linUCB_regret_le](CKSD/Learning/Bandits.lean#L761) (admitted; scope in docstring).
- **107.65 Composition.**
  [CKSD.isDifferentiallyPrivate_compProd](CKSD/Learning/Privacy.lean#L47) (proved; scope in docstring).
- **107.66 Private mean estimation.**
  [CKSD.exists_centralMeanRisk_ge](CKSD/Learning/PrivateEstimation/CentralLowerBounds.lean#L418) (proved; scope in docstring).
  [CKSD.isDifferentiallyPrivate_localLaplaceKernel](CKSD/Learning/PrivateEstimation/Local.lean#L185) (proved; scope in docstring).
  [CKSD.localMeanRisk_localLaplace_mean_le](CKSD/Learning/PrivateEstimation/Local.lean#L246) (proved; scope in docstring).
  [CKSD.localMeanRisk_minimax_order](CKSD/Learning/PrivateEstimation/Local.lean#L323) (proved; scope in docstring).
  [CKSD.isDifferentiallyPrivate_laplaceMeanMechanism](CKSD/Learning/PrivateEstimation/Mechanisms.lean#L161) (proved; scope in docstring).
  [CKSD.centralMeanRisk_laplaceMeanMechanism_le](CKSD/Learning/PrivateEstimation/Mechanisms.lean#L265) (proved; scope in docstring).
  [CKSD.exists_centralMeanRisk_le](CKSD/Learning/PrivateEstimation/Mechanisms.lean#L329) (proved; scope in docstring).
- **107.74 Sparse vector technique.**
  [CKSD.sub_le_of_threshold_add_le_add](CKSD/Learning/Algorithms.lean#L115) (proved; scope in docstring).
  [CKSD.le_add_of_add_lt_threshold_add](CKSD/Learning/Algorithms.lean#L123) (proved; scope in docstring).
- **107.75 Contraction under local privacy.**
  [CKSD.klDiv_comp_le_of_local_differential_privacy](CKSD/Learning/Privacy.lean#L289) (proved; scope in docstring).
  [CKSD.exists_bernoulli_localMeanRisk_ge](CKSD/Learning/PrivateEstimation/Local.lean#L63) (proved; scope in docstring).

### Section 108

- **108.1 Cheeger inequality for the normalized Laplacian.**
  [CKSD.spectralGap_cheegerConstant_bounds](CKSD/Geometry/Cheeger.lean#L439) (proved; scope in docstring).
- **108.4 Geodesic approximation.**
  [CKSD.eventually_sampleGraphEDist_intrinsicEDist_le](CKSD/Geometry/ManifoldLearning.lean#L68) (admitted; scope in docstring).
  [CKSD.intrinsicEDist_eq_edist_of_lengthPreserving](CKSD/Geometry/ManifoldLearning.lean#L90) (proved; scope in docstring).
- **108.5 Fréchet means.**
  [CKSD.existsUnique_frechet_mean_of_midpoint_inequality](CKSD/Geometry/GeometricStatistics.lean#L60) (proved; scope in docstring).
- **108.7 Hausdorff estimation of a submanifold.**
  [CKSD.isBoundedInProbability_hausdorff_sampling_error](CKSD/Geometry/GeometricStatistics.lean#L189) (proved; scope in docstring).
- **108.8 Classical multidimensional scaling.**
  [CKSD.posSemidef_double_centering_iff_sq_euclidean_distances](CKSD/Geometry/GeometricStatistics.lean#L374) (proved; scope in docstring).
- **108.10 Extrinsic projection mean.**
  [CKSD.extrinsic_mean_iff_nearest_expectation](CKSD/Geometry/GeometricStatistics.lean#L441) (proved; scope in docstring).
  [CKSD.tendstoInDistribution_projected_sampleAverage](CKSD/Geometry/GeometricStatistics.lean#L454) (proved; scope in docstring).
- **108.13 Uniqueness of Fréchet means in small balls.** — theorem formulation pending.
- **108.15 Barycentric equation.** — theorem formulation pending.
- **108.18 Interval decomposition.**
  [CKSD.exists_intervalBasis_of_isPointwiseFiniteDimensional](CKSD/Geometry/PersistenceModules.lean#L61) (admitted; scope in docstring).
  [CKSD.IntervalBasis.exists_equiv_support_eq](CKSD/Geometry/PersistenceModules.lean#L290) (proved; scope in docstring).
  [CKSD.exists_isSublevelDiagram](CKSD/Geometry/SimplicialPersistence/Chains.lean#L470) (proved; scope in docstring).
- **108.19 Bottleneck stability.**
  [CKSD.fullBottleneckEDist_le_of_isSublevelDiagram](CKSD/Geometry/SimplicialPersistence/Stability.lean#L315) (proved; scope in docstring).
- **108.20 Isometry theorem.**
  [CKSD.interleavingEDist_le_fullBottleneckEDist](CKSD/Geometry/PersistenceModules.lean#L451) (proved; scope in docstring).
  [CKSD.interleavingEDist_eq_fullBottleneckEDist](CKSD/Geometry/PersistenceModules.lean#L547) (admitted; scope in docstring).
- **108.21 Čech, Rips, and the nerve.**
  [CKSD.IsCechSimplex.isRipsSimplex](CKSD/Geometry/Persistence.lean#L133) (proved; scope in docstring).
  [CKSD.cech_rips_inclusions](CKSD/Geometry/Topology.lean#L161) (proved; scope in docstring).
- **108.22 Homology from a sample.**
  [CKSD.exists_deformationRetraction_offset_of_hausdorffDist_lt](CKSD/Geometry/TopologicalInference.lean#L95) (admitted; scope in docstring).
  [CKSD.exists_sample_size_hausdorffDist_le](CKSD/Geometry/TopologicalInference.lean#L115) (proved; scope in docstring).
- **108.23 Central limit theorem for landscapes.**
  [CKSD.LandscapeLp.ae_tendsto_sampleAverage](CKSD/Geometry/Landscapes.lean#L52) (proved; scope in docstring).
- **108.24 Stability of the distance to a measure.**
  [CKSD.abs_distanceToMeasure_sub_le_wasserstein](CKSD/Geometry/Topology.lean#L212) (proved; scope in docstring).
- **108.32 Persistence pairing by matrix reduction.**
  [CKSD.isColumnLow_iff_pairingRankCombination_eq_one](CKSD/Geometry/MatrixReduction/Basic.lean#L300) (proved; scope in docstring).
  [CKSD.isColumnLow_iff_of_isMatrixReduction](CKSD/Geometry/MatrixReduction/Basic.lean#L308) (proved; scope in docstring).
  [CKSD.persistentBettiOfMatrix_eq_card](CKSD/Geometry/MatrixReduction/Homology.lean#L169) (proved; scope in docstring).
  [CKSD.IsColumnLow.dim_eq_and_persistentBettiOfMatrix_eq](CKSD/Geometry/MatrixReduction/Homology.lean#L281) (proved; scope in docstring).
- **108.34 Sublevel persistence of a Morse function.**
  [CKSD.sublevelHomologyModule_bars_of_isMorse](CKSD/Geometry/TopologicalInference.lean#L262) (admitted; scope in docstring).
- **108.35 Wasserstein stability.**
  [CKSD.diagramWassersteinEDist_le_of_isSublevelDiagram](CKSD/Geometry/SimplicialPersistence/Stability.lean#L829) (proved; scope in docstring).
- **108.36 Gromov–Hausdorff stability of Rips persistence.**
  [CKSD.fullBottleneckEDist_rips_le_ghDist](CKSD/Geometry/RipsStability.lean#L559) (proved; scope in docstring).
- **108.37 Homology inference with positive weak feature size.**
  [CKSD.nonempty_range_offsetHomology_equiv_of_weakFeatureSize](CKSD/Geometry/TopologicalInference.lean#L205) (admitted; scope in docstring).
  [CKSD.nonempty_ripsPersistentHomology_equiv_of_weakFeatureSize](CKSD/Geometry/TopologicalInference.lean#L225) (admitted; scope in docstring).
- **108.40 Empirical Wasserstein bounds.**
  [CKSD.integral_empirical_wasserstein_rpow_le](CKSD/Geometry/Transport.lean#L66) (admitted; scope in docstring).
- **108.42 Consistency of Brenier maps.**
  [CKSD.tendsto_integral_sq_optimal_map_sub](CKSD/Geometry/OptimalMapStability.lean#L239) (proved; scope in docstring).
- **108.43 Gromov–Wasserstein distance.**
  [CKSD.exists_measure_preserving_isometryEquiv_of_zero_distortion](CKSD/Geometry/Transport.lean#L105) (proved; scope in docstring).
- **108.44 Debiased Sinkhorn divergence.**
  [CKSD.realSinkhornDivergence_independent_lower_bound](CKSD/Geometry/Entropic.lean#L84) (proved; scope in docstring).
  [CKSD.realSinkhornDivergence_nonneg](CKSD/Geometry/Entropic.lean#L112) (proved; scope in docstring).
- **108.46 Gaussian transport and barycenters.**
  [CKSD.wasserstein_multivariateGaussian_sq_eq](CKSD/Geometry/GaussianTransport.lean#L103) (proved; scope in docstring).
  [CKSD.exists_unique_gaussian_wasserstein_barycenter](CKSD/Geometry/Transport.lean#L154) (proved; scope in docstring).
- **108.47 One-dimensional empirical transport limit.**
  [CKSD.tendstoInDistribution_mul_wasserstein_sq_empiricalMeasure](CKSD/Geometry/TransportRates.lean#L50) (admitted; scope in docstring).
- **108.50 Minimax lower bounds for transport estimation.**
  [CKSD.rpow_div_le_wassersteinEDist_volume_cube](CKSD/Geometry/Transport.lean#L278) (proved; scope in docstring).
- **108.51 Smooth laws and smoothed distances.**
  [CKSD.integral_wasserstein_gaussianSmoothing_empiricalMeasure_le](CKSD/Geometry/Transport.lean#L394) (proved; scope in docstring).
- **108.53 Rates for transport-map estimation.**
  [CKSD.lintegral_transportMapRisk_semidualEstimator_le](CKSD/Geometry/TransportRates.lean#L119) (admitted; scope in docstring).
  [CKSD.lintegral_transportMapRisk_semidualEstimator_le_of_poincare](CKSD/Geometry/TransportRates.lean#L136) (admitted; scope in docstring).
- **108.55 Dimension-free sample complexity of entropic transport.**
  [CKSD.quadraticEntropicTransport_empirical_bounds](CKSD/Geometry/StatisticalTransport.lean#L67) (admitted; scope in docstring).
- **108.56 Semidiscrete dual.**
  [CKSD.hasFDerivAt_integral_semidiscretePotential](CKSD/Geometry/SemidiscreteTransport.lean#L286) (proved; scope in docstring).
  [CKSD.hasFDerivAt_semidiscreteTransportDual](CKSD/Geometry/SemidiscreteTransport.lean#L354) (proved; scope in docstring).
  [CKSD.contDiff_semidiscreteTransportDual](CKSD/Geometry/SemidiscreteTransport.lean#L384) (proved; scope in docstring).
  [CKSD.concaveOn_semidiscreteTransportDual](CKSD/Geometry/SemidiscreteTransport.lean#L395) (proved; scope in docstring).
  [CKSD.semidiscreteTransportDual_isMax_iff](CKSD/Geometry/SemidiscreteTransport.lean#L511) (proved; scope in docstring).
  [CKSD.exists_isMax_semidiscreteTransportDual](CKSD/Geometry/SemidiscreteTransport.lean#L537) (proved; scope in docstring).
  [CKSD.map_semidiscreteTransportMap](CKSD/Geometry/SemidiscreteTransport.lean#L655) (proved; scope in docstring).
  [CKSD.integral_norm_sub_semidiscreteTransportMap_sq](CKSD/Geometry/SemidiscreteTransport.lean#L683) (proved; scope in docstring).
  [CKSD.ofReal_semidiscreteTransportDual_le_lintegral](CKSD/Geometry/SemidiscreteTransport.lean#L711) (proved; scope in docstring).
  [CKSD.semidiscreteTransportDual_eq_wassersteinEDist_sq](CKSD/Geometry/SemidiscreteTransport.lean#L779) (proved; scope in docstring).
  [CKSD.semidiscreteTransportDual_concave_differentiable_and_attains_max](CKSD/Geometry/Transport.lean#L411) (proved; scope in docstring).
- **108.57 Tangent-space linearization.**
  [CKSD.optimalMap_eq_cfcSqrt_mul_inv_iff_commute](CKSD/Geometry/Transport.lean#L445) (proved; scope in docstring).
- **108.58 First-order conditions for barycenters.**
  [CKSD.hasDerivAt_wassersteinBarycenterEnergy_displacement](CKSD/Geometry/StatisticalTransport.lean#L137) (proved; scope in docstring).
  [CKSD.satisfiesWassersteinKarcherEquation_of_minimizer](CKSD/Geometry/StatisticalTransport.lean#L171) (proved; scope in docstring).
- **108.59 Procrustes iteration for barycenters.**
  [CKSD.wassersteinBarycenterEnergy_map_sub_le](CKSD/Geometry/Transport.lean#L570) (proved; scope in docstring).
- **108.61 Limits of the empirical discrepancy.**
  [CKSD.tendstoInDistribution_unbiasedSquaredMMD_null](CKSD/Geometry/Kernels.lean#L276) (proved; scope in docstring).
  [CKSD.tendstoInDistribution_unbiasedSquaredMMD_alternative](CKSD/Geometry/Kernels.lean#L549) (proved; scope in docstring).
- **108.62 Energy distance and independence.**
  [CKSD.energy_distance_nonneg_eq_zero_iff_and_eq_squaredMMD](CKSD/Geometry/Kernels.lean#L696) (proved; scope in docstring).
  [CKSD.distance_covariance_nonneg_eq_zero_iff_and_eq_squaredMMD](CKSD/Geometry/Kernels.lean#L710) (proved; scope in docstring).
- **108.63 Hilbert–Schmidt independence criterion.**
  [CKSD.squaredMMD_joint_prod_eq_zero_iff_indepFun](CKSD/Geometry/Kernels.lean#L738) (proved; scope in docstring).
- **108.68 Criteria for characteristic kernels.**
  [CKSD.isCharacteristicKernel_iff_spectral_measure_full_support](CKSD/Geometry/Kernels.lean#L754) (proved; scope in docstring).
  [CKSD.squaredMMD_quadratic_polynomial_eq](CKSD/Geometry/Kernels.lean#L835) (proved; scope in docstring).
- **108.70 Metrization of weak convergence.**
  [CKSD.tendsto_probabilityMeasure_iff_tendsto_squaredMMD_of_tight](CKSD/Geometry/Kernels.lean#L879) (proved; scope in docstring).
- **108.71 Kernel Stein discrepancy.**
  [CKSD.integral_langevin_stein_operator_eq_zero](CKSD/Geometry/Kernels.lean#L930) (proved; scope in docstring).
- **108.72 Convergence control by kernel Stein discrepancies.**
  [CKSD.tendsto_of_kernelSteinDiscrepancySq_inverseMultiquadric_tendsto_zero](CKSD/Geometry/SteinDiscrepancy.lean#L70) (admitted; scope in docstring).
  [CKSD.exists_not_tendsto_of_kernelSteinDiscrepancySq_tendsto_zero](CKSD/Geometry/SteinDiscrepancy.lean#L90) (admitted; scope in docstring).
- **108.74 Random Fourier features.**
  [CKSD.integral_randomFourierFeatureKernel](CKSD/Geometry/RandomFeatures.lean#L151) (proved; scope in docstring).
  [CKSD.measureReal_abs_randomFourierFeatureKernel_sub_ge_le](CKSD/Geometry/RandomFeatures.lean#L181) (proved; scope in docstring).
  [CKSD.measure_uniform_randomFourierFeatureKernel_error_le](CKSD/Geometry/RandomFeatures.lean#L535) (proved; scope in docstring).
  [CKSD.abs_squaredMMD_sub_le_of_uniform_kernel_error](CKSD/Geometry/RandomFeatures.lean#L678) (proved; scope in docstring).
