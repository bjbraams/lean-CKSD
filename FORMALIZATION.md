# CKSD formalization

The public entry point is [CKSD.lean](CKSD.lean). Every project declaration is in
`namespace CKSD` or one of its subnamespaces. The module names follow topics, while
the stable identifiers of [GAPS.md](GAPS.md) connect code to the mathematical catalogue.

There are **846 definitions, abbreviations, structures, and inductive types**
and **2864 theorem statements**: **2775 proved**,
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
  [CKSD.isSufficientStatistic_iff_exists_factorization](CKSD/Inference/ExponentialFamily.lean#L58) (proved; scope in docstring).
  [CKSD.exists_factorization_of_isSufficientStatistic](CKSD/Inference/Factorization.lean#L205) (proved; scope in docstring).
  [CKSD.isSufficientStatistic_of_factorization](CKSD/Inference/Factorization.lean#L241) (proved; scope in docstring).
- **101.2 Minimal sufficiency.**
  [CKSD.isSufficientStatistic_likelihoodRatio_and_ae_eq_comp](CKSD/Inference/ExponentialFamily.lean#L236) (proved; scope in docstring).
- **101.4 Structure of a full-rank exponential family.**
  [CKSD.convex_naturalParameterSpace](CKSD/Inference/ExponentialFamily.lean#L74) (proved; scope in docstring).
  [CKSD.analyticOnNhd_logPartition_and_fderiv_eq_moments](CKSD/Inference/ExponentialFamily.lean#L288) (proved; scope in docstring).
- **101.5 Completeness in a full-rank exponential family.**
  [CKSD.isCompleteStatistic_withDensity_exp_inner](CKSD/Inference/ExponentialFamily.lean#L93) (proved; scope in docstring).
- **101.6 Pitman–Koopman–Darmois theorem, monotone form.**
  [CKSD.exists_exponential_family_of_monotone_sufficient_statistics](CKSD/Inference/ExponentialFamily.lean#L271) (admitted; scope in docstring).
- **101.7 Rao–Blackwell theorem.**
  [CKSD.exists_rao_blackwell_estimator](CKSD/Inference/Estimation.lean#L44) (proved; scope in docstring).
- **101.8 Lehmann–Scheffé theorem.**
  [CKSD.ae_eq_of_isCompleteStatistic_of_isUnbiasedEstimator](CKSD/Inference/Estimation.lean#L107) (proved; scope in docstring).
- **101.9 Basu's theorem.**
  [CKSD.indepFun_of_isSufficientStatistic_of_isBoundedlyCompleteStatistic](CKSD/Inference/Estimation.lean#L124) (proved; scope in docstring).
- **101.10 Information inequality.**
  [CKSD.sq_div_information_le_variance](CKSD/Inference/Estimation.lean#L163) (proved; scope in docstring).
- **101.12 Characterization of UMVU estimators.**
  [CKSD.isMinimumVarianceUnbiasedEstimator_iff_covariance_eq_zero](CKSD/Inference/Estimation.lean#L202) (proved; scope in docstring).
- **101.13 Completeness of the order statistic.**
  [CKSD.isSymmetricallyComplete_of_complete_convex_family](CKSD/Inference/Families.lean#L68) (proved; scope in docstring).
- **101.14 Neyman–Pearson lemma.**
  [CKSD.exists_neyman_pearson_test](CKSD/Inference/NeymanPearson.lean#L224) (proved; scope in docstring).
- **101.15 Karlin–Rubin theorem.**
  [CKSD.isUniformlyMostPowerfulTest_of_monotone_likelihood_ratio](CKSD/Inference/Testing.lean#L67) (proved; scope in docstring).
- **101.17 Gaussian sampling distributions.**
  [CKSD.gaussian_sample_mean_residual_laws](CKSD/Inference/Testing.lean#L134) (proved; scope in docstring).
- **101.21 Distribution of order statistics.**
  [CKSD.map_orderStatistics_eq_withDensity](CKSD/Inference/Families.lean#L83) (proved; scope in docstring).
  [CKSD.map_orderStatistic_eq_withDensity](CKSD/Inference/Families.lean#L142) (proved; scope in docstring).
  [CKSD.map_sort_eq_and_indepFun_orderStatistics](CKSD/Inference/Families.lean#L253) (proved; scope in docstring).
- **101.32 Value of a finite statistical game.**
  [CKSD.exists_statistical_game_saddle_point](CKSD/Inference/Decision.lean#L59) (proved; scope in docstring).
- **101.37 Complete classes.**
  [CKSD.exists_admissible_bayes_risk_le_of_closed_convex](CKSD/Inference/Decision.lean#L106) (proved; scope in docstring).
- **101.39 Hunt–Stein theorem, compact form.**
  [CKSD.exists_equivariant_rule_risk_eq_average](CKSD/Inference/Decision.lean#L199) (proved; scope in docstring).
- **101.40 Pitman estimator of location.**
  [CKSD.pitmanEstimator_minimum_equivariant_risk](CKSD/Inference/Families.lean#L638) (proved; scope in docstring).
- **101.42 Mean parameterization.**
  [CKSD.exists_analytic_inverse_exponential_family_mean](CKSD/Inference/Decision.lean#L283) (proved; scope in docstring).
- **101.43 Conditional exponential families.**
  [CKSD.exists_kernel_conditional_exponential_family](CKSD/Inference/ConditionalExponentialFamily.lean#L282) (proved; scope in docstring).
- **101.45 Two-sided tests in a one-parameter exponential family.**
  [CKSD.integral_le_integral_of_two_tail_of_moment_eq](CKSD/Inference/InvariantTesting.lean#L176) (proved; scope in docstring).
  [CKSD.isUniformlyMostPowerfulUnbiasedTest_of_two_tail_moment_constraints](CKSD/Inference/InvariantTesting.lean#L261) (proved; scope in docstring).
- **101.46 Conditional tests with a nuisance parameter.**
  [CKSD.isUniformlyMostPowerfulUnbiasedTest_conditional_two_sided](CKSD/Inference/ConditionalExponentialFamily.lean#L343) (admitted; scope in docstring).
  [CKSD.isUniformlyMostPowerfulUnbiasedTest_conditional_one_sided](CKSD/Inference/ConditionalExponentialFamily.lean#L368) (admitted; scope in docstring).
- **101.47 Generalized Neyman–Pearson lemma.**
  [CKSD.integral_le_of_generalized_neyman_pearson](CKSD/Inference/NeymanPearson.lean#L47) (proved; scope in docstring).
- **101.49 Neyman structure.**
  [CKSD.condExp_eq_const_of_isSimilarTest](CKSD/Inference/InvariantTesting.lean#L383) (proved; scope in docstring).
- **101.50 Uniformly most powerful tests of a two-sided hypothesis.**
  [CKSD.exists_ump_interval_test](CKSD/Inference/Testing.lean#L502) (proved; scope in docstring).
- **101.53 Karlin–Rubin complete class theorem.**
  [CKSD.exists_one_sided_test_risk_le](CKSD/Inference/Testing.lean#L602) (proved; scope in docstring).
- **101.54 Least favorable distributions.**
  [CKSD.most_powerful_of_mixture_null](CKSD/Inference/Testing.lean#L693) (proved; scope in docstring).
- **101.55 Reduction by a maximal invariant.**
  [CKSD.invariant_iff_factors_through_maximal_invariant](CKSD/Inference/InvariantTesting.lean#L409) (proved; scope in docstring).
- **101.56 Normal tests as uniformly most powerful invariant tests.**
  [CKSD.mean_scale_ratio_eq_iff](CKSD/Inference/InvariantTesting.lean#L425) (proved; scope in docstring).
- **101.57 Estimation of a normal mean.**
  [CKSD.james_stein_risk_eq_and_lt](CKSD/Inference/Gaussian.lean#L377) (proved; scope in docstring).
- **101.58 Blyth's method.**
  [CKSD.isAdmissibleRisk_of_blyth](CKSD/Inference/Decision.lean#L350) (proved; scope in docstring).
- **101.60 Scheffé's method.**
  [CKSD.scheffe_contrast_supremum](CKSD/Inference/Gaussian.lean#L517) (proved; scope in docstring).
- **101.62 Blackwell's theorem.**
  [CKSD.isMoreInformative_iff_isGarbling](CKSD/Inference/Decision.lean#L439) (proved; scope in docstring).
- **101.64 Stein's identity and unbiased risk estimation.**
  [CKSD.gaussian_integration_by_parts](CKSD/Inference/Gaussian.lean#L71) (proved; scope in docstring).
- **101.69 Existence of an exponential-family maximum.**
  [CKSD.exists_isMaxOn_logLikelihood_iff_mem_interior_convexHull_support](CKSD/Inference/ExponentialFamilyMLE.lean#L338) (proved; scope in docstring).
  [CKSD.hasFDerivAt_logPartition_and_eq_of_isMaxOn](CKSD/Inference/ExponentialFamilyMLE.lean#L546) (proved; scope in docstring).

### Section 102

- **102.1 Delta method.**
  [CKSD.tendstoInDistribution_delta_method](CKSD/Asymptotics/Basic.lean#L391) (proved; scope in docstring).
- **102.2 Consistency of maximum likelihood.**
  [CKSD.tendstoInMeasure_mle_of_compact](CKSD/Asymptotics/MEstimation/Consistency.lean#L216) (proved; scope in docstring).
- **102.3 Asymptotic normality of maximum likelihood.**
  [CKSD.mle_asymptotic_linearization_and_normality](CKSD/Asymptotics/MEstimation/MaximumLikelihood.lean#L222) (proved; scope in docstring).
- **102.4 Z-estimators.**
  [CKSD.zEstimator_asymptotic_linearization_and_normality](CKSD/Asymptotics/MEstimation/ZEstimators.lean#L217) (proved; scope in docstring).
- **102.6 Sample quantiles.**
  [CKSD.tendstoInDistribution_sampleQuantile](CKSD/Asymptotics/Quantiles.lean#L431) (proved; scope in docstring).
- **102.7 Bahadur representation of sample quantiles.**
  [CKSD.tendstoInMeasure_bahadur_remainder](CKSD/Asymptotics/Quantiles.lean#L354) (proved; scope in docstring).
- **102.8 Nondegenerate $U$-statistics.**
  [CKSD.tendstoInDistribution_uStatistic](CKSD/Asymptotics/UStatistics/Limits.lean#L44) (proved; scope in docstring).
- **102.11 Likelihood-ratio, Wald, and score tests.**
  [CKSD.tendstoInDistribution_likelihoodRatio_wald_score_chiSquared](CKSD/Asymptotics/LikelihoodTests.lean#L698) (proved; scope in docstring).
  [CKSD.tendstoInDistribution_likelihoodRatio_wald_score_noncentralChiSquared](CKSD/Asymptotics/LikelihoodTests.lean#L775) (proved; scope in docstring).
- **102.12 Contiguity.**
  [CKSD.isContiguous_of_integral_likelihood_ratio_limit_eq_one](CKSD/Asymptotics/LAN/LeCam.lean#L48) (proved; scope in docstring).
- **102.13 Local asymptotic normality of smooth models.**
  [CKSD.tendstoInMeasure_log_likelihood_ratio_sub_of_dqm](CKSD/Asymptotics/LAN/LeCam.lean#L694) (proved; scope in docstring).
  [CKSD.tendstoInDistribution_score_and_log_likelihood_ratio_expansion_of_dqm](CKSD/Asymptotics/LAN/LeCam.lean#L796) (proved; scope in docstring).
- **102.14 Le Cam's third lemma.**
  [CKSD.tendstoInDistribution_of_log_likelihood_ratio](CKSD/Asymptotics/LAN/LeCam.lean#L148) (proved; scope in docstring).
- **102.15 Asymptotic representation theorem.**
  [CKSD.exists_gaussian_shift_kernel_of_local_limits](CKSD/Asymptotics/LAN/Representation.lean#L53) (proved; scope in docstring).
- **102.16 Convolution theorem.**
  [CKSD.exists_convolution_of_isRegularEstimator](CKSD/Asymptotics/LAN/Representation.lean#L167) (proved; scope in docstring).
- **102.17 Local asymptotic minimax theorem.**
  [CKSD.gaussian_risk_le_local_asymptotic_minimax](CKSD/Asymptotics/LAN/Representation.lean#L197) (admitted; scope in docstring).
- **102.21 Pitman efficiency and Noether's theorem.**
  [CKSD.tendsto_local_normal_power](CKSD/Asymptotics/LAN/LeCam.lean#L204) (proved; scope in docstring).
- **102.23 Consistency of $M$-estimators.**
  [CKSD.tendstoInMeasure_mEstimator](CKSD/Asymptotics/AsymptoticTheory.lean#L41) (proved; scope in docstring).
- **102.24 Asymptotic normality of $M$-estimators.**
  [CKSD.mEstimator_asymptotic_linearization_and_normality](CKSD/Asymptotics/MEstimation/Normality.lean#L829) (proved; scope in docstring).
- **102.25 Rate of convergence of $M$-estimators.**
  [CKSD.isBoundedInProbability_rate_mEstimator](CKSD/Asymptotics/RatesOfConvergence.lean#L150) (proved; scope in docstring).
- **102.28 Functional delta method.**
  [CKSD.tendstoInDistribution_of_hasHadamardFDerivAt](CKSD/Asymptotics/FunctionalDeltaMethod.lean#L44) (proved; scope in docstring).
- **102.29 Hoeffding decomposition.**
  [CKSD.uStatistic_hoeffding_decomposition_and_variance](CKSD/Asymptotics/UStatistics/Limits.lean#L534) (proved; scope in docstring).
- **102.30 Degenerate quadratic $U$-statistics.**
  [CKSD.tendstoInDistribution_uStatistic_of_finite_rank_degenerate](CKSD/Asymptotics/UStatistics/Limits.lean#L756) (proved; scope in docstring).
- **102.31 Pearson's multinomial tests.**
  [CKSD.tendstoInDistribution_pearson_statistic](CKSD/Asymptotics/AsymptoticTheory.lean#L160) (proved; scope in docstring).
- **102.33 Argmax theorem.**
  [CKSD.tendstoInMeasure_argmax_of_compact](CKSD/Asymptotics/AsymptoticTheory.lean#L267) (proved; scope in docstring).
- **102.34 Semiparametric convolution bound.**
  [CKSD.exists_convolution_of_isRegularAlongPaths](CKSD/Asymptotics/Semiparametric.lean#L83) (admitted; scope in docstring).
  [CKSD.isRegularAlongPaths_gaussian_iff_asymptotically_linear](CKSD/Asymptotics/Semiparametric.lean#L105) (admitted; scope in docstring).
- **102.39 Cross-fitted estimation of a missing mean.**
  [CKSD.crossFittedAverage_missingMean_asymptotically_linear](CKSD/Asymptotics/CrossFitting.lean#L383) (proved; scope in docstring).
- **102.41 Adaptive estimation of a center of symmetry.**
  [CKSD.efficientScore_locationScore_eq](CKSD/Asymptotics/Semiparametric.lean#L209) (proved; scope in docstring).
  [CKSD.exists_adaptive_estimator_center_of_symmetry](CKSD/Asymptotics/Semiparametric.lean#L271) (admitted; scope in docstring).
- **102.44 $M$-estimators and the Huber minimax property.**
  [CKSD.integral_huberScore_sq_le](CKSD/Asymptotics/Robustness.lean#L165) (proved; scope in docstring).
- **102.48 Asymptotics of regression $M$-estimators.**
  [CKSD.regression_mEstimator_asymptotic_linearization_and_normality](CKSD/Asymptotics/MEstimation/Regression.lean#L114) (proved; scope in docstring).
- **102.49 One-term Edgeworth expansion.**
  [CKSD.exists_uniform_edgeworth_expansion](CKSD/Asymptotics/Expansions.lean#L39) (admitted; scope in docstring).
- **102.50 Edgeworth expansion for smooth functions of means.**
  [CKSD.exists_edgeworth_expansion_smooth_function_of_means](CKSD/Asymptotics/Expansions.lean#L60) (admitted; scope in docstring).
- **102.51 Bootstrap of the mean.**
  [CKSD.tendstoInMeasure_bootstrap_mean_kolmogorovDistance](CKSD/Asymptotics/Bootstrap.lean#L565) (proved; scope in docstring).
- **102.52 Bootstrap of the empirical distribution function.**
  [CKSD.tendstoInProbability_bootstrapBoundedLipschitzDistance](CKSD/Asymptotics/Bootstrap.lean#L118) (admitted; scope in docstring).
- **102.55 Saddlepoint approximation.**
  [CKSD.saddlepoint_approximation_sampleAverage_density](CKSD/Asymptotics/Expansions.lean#L86) (admitted; scope in docstring).
- **102.58 Čencov's theorem.**
  [CKSD.fisherRaoMetric_congruent_embedding](CKSD/Asymptotics/InformationGeometry.lean#L92) (proved; scope in docstring).
- **102.60 Second-order accuracy of the studentized bootstrap.**
  [CKSD.studentized_bootstrap_mean_second_order_accuracy](CKSD/Asymptotics/Bootstrap.lean#L137) (admitted; scope in docstring).

### Section 103

- **103.1 Kolmogorov–Smirnov statistic.**
  [CKSD.measure_kolmogorovSmirnovStatistic_gt_le](CKSD/Nonparametric/Estimation.lean#L79) (admitted; scope in docstring).
- **103.4 Kernel density asymptotics.**
  [CKSD.tendstoInDistribution_kernelDensityEstimator](CKSD/Nonparametric/Estimation.lean#L404) (proved; scope in docstring).
- **103.5 Universal $L^1$ consistency.**
  [CKSD.ae_tendsto_integral_abs_kernelDensityEstimator_sub](CKSD/Nonparametric/Estimation.lean#L474) (proved; scope in docstring).
- **103.7 Stone's theorem.**
  [CKSD.tendsto_nadarayaWatson_prediction_error_probability](CKSD/Nonparametric/SmoothingRates.lean#L66) (admitted; scope in docstring).
- **103.8 Representer theorem.**
  [CKSD.minimizer_mem_span_of_feature_vectors](CKSD/Nonparametric/Estimation.lean#L580) (proved; scope in docstring).
- **103.9 Pinsker's theorem and the Sobolev rate.**
  [CKSD.tendsto_gaussianSequenceMinimaxRisk_div_linear](CKSD/Nonparametric/Models.lean#L83) (admitted; scope in docstring).
- **103.11 Grenander estimator.**
  [CKSD.grenanderEstimator_isMaximumLikelihood](CKSD/Nonparametric/Density/Grenander.lean#L759) (proved; scope in docstring).
  [CKSD.tendstoInDistribution_grenanderEstimator](CKSD/Nonparametric/Density/Grenander.lean#L877) (admitted; scope in docstring).
- **103.14 Score-generating functions and locally most powerful rank tests.**
  [CKSD.integral_linearRankStatistic](CKSD/Nonparametric/Estimation.lean#L781) (proved; scope in docstring).
  [CKSD.variance_linearRankStatistic](CKSD/Nonparametric/Estimation.lean#L788) (proved; scope in docstring).
- **103.17 Cramér–von Mises and two-sample Kolmogorov–Smirnov limits.**
  [CKSD.map_cramerVonMisesStatistic_eq_uniform](CKSD/Nonparametric/GoodnessOfFit.lean#L122) (proved; scope in docstring).
  [CKSD.map_twoSampleKolmogorovSmirnovStatistic_eq_uniform](CKSD/Nonparametric/GoodnessOfFit.lean#L261) (proved; scope in docstring).
- **103.22 Hölder regression rates.**
  [CKSD.holderRegressionMinimaxRisk_le](CKSD/Nonparametric/HolderRegressionMinimax.lean#L70) (proved; scope in docstring).
  [CKSD.holderRegressionMinimaxRisk_ge](CKSD/Nonparametric/HolderRegressionMinimax.lean#L537) (proved; scope in docstring).
  [CKSD.holderRegressionMinimaxRisk_bounds](CKSD/Nonparametric/HolderRegressionMinimax.lean#L636) (proved; scope in docstring).
  [CKSD.fixedDesignLocalConstant_risk_le](CKSD/Nonparametric/SmoothingRates.lean#L325) (proved; scope in docstring).
- **103.26 Minimax rates of density estimation.**
  [CKSD.finiteKernelDensityEstimator_risk_le](CKSD/Nonparametric/Density/HolderMinimax.lean#L254) (proved; scope in docstring).
  [CKSD.holderDensityPointwiseMinimaxRisk_lower_bound](CKSD/Nonparametric/Density/HolderMinimax.lean#L755) (proved; scope in docstring).
- **103.27 Risk of isotonic regression.**
  [CKSD.existsUnique_isIsotonicRegressionEstimator](CKSD/Nonparametric/IsotonicRegression.lean#L88) (proved; scope in docstring).
  [CKSD.isIsotonicRegressionEstimator_isotonicLeastSquares](CKSD/Nonparametric/IsotonicRegression.lean#L219) (proved; scope in docstring).
  [CKSD.isotonicGaussianRisk_le](CKSD/Nonparametric/IsotonicRegression.lean#L337) (admitted; scope in docstring).
  [CKSD.isotonicGaussianMinimaxRisk_lower_bound](CKSD/Nonparametric/IsotonicRegression.lean#L661) (proved; scope in docstring).
- **103.28 Log-concave maximum likelihood.**
  [CKSD.existsUnique_isLogConcaveProjection](CKSD/Nonparametric/Density/LogConcave.lean#L92) (admitted; scope in docstring).
  [CKSD.existsUnique_logConcaveMLE_tent](CKSD/Nonparametric/Density/LogConcave.lean#L106) (admitted; scope in docstring).
  [CKSD.logConcaveMLE_hellingerRisk_le](CKSD/Nonparametric/Density/LogConcave.lean#L117) (admitted; scope in docstring).
  [CKSD.logConcave_minimax_hellingerRisk_lower_bound](CKSD/Nonparametric/Density/LogConcave.lean#L129) (admitted; scope in docstring).
- **103.29 Karhunen–Loève expansion and the Hilbertian central limit theorem.**
  [CKSD.tendstoInDistribution_hilbert_sampleAverage](CKSD/Nonparametric/HighDimensional/HilbertCLT.lean#L273) (proved; scope in docstring).
- **103.30 Principal components of the empirical covariance.**
  [CKSD.leading_empirical_covariance_eigenvalue_asymptotics](CKSD/Nonparametric/EmpiricalCovariance.lean#L357) (proved; scope in docstring).
  [CKSD.isBoundedInProbability_leading_empirical_eigenvector_error](CKSD/Nonparametric/EmpiricalCovariance.lean#L443) (proved; scope in docstring).
- **103.31 Optimality of functional principal components.**
  [CKSD.sum_ite_le_integral_norm_sub_sum_inner_smul_sq](CKSD/Nonparametric/HighDimensional/PrincipalComponents.lean#L58) (proved; scope in docstring).
- **103.33 Sparse minimax rate.**
  [CKSD.sparseGaussianMinimaxRisk_bounds](CKSD/Nonparametric/HighDimensional/SparseMinimax.lean#L629) (proved; scope in docstring).
- **103.34 Lasso under compatibility.**
  [CKSD.IsLassoEstimator.restrictedL1Norm_compl_sub_le](CKSD/Nonparametric/HighDimensional/Lasso.lean#L161) (proved; scope in docstring).
  [CKSD.IsLassoEstimator.norm_apply_sub_sq_div_le_of_hasCompatibility](CKSD/Nonparametric/HighDimensional/Lasso.lean#L205) (proved; scope in docstring).
  [CKSD.IsLassoEstimator.restrictedL1Norm_sub_le](CKSD/Nonparametric/HighDimensional/Lasso.lean#L223) (proved; scope in docstring).
- **103.35 Penalized model selection.**
  [CKSD.selectedProjectionRisk_oracle_bound](CKSD/Nonparametric/ModelSelection.lean#L193) (proved; scope in docstring).
- **103.37 Benjamini–Hochberg procedure.**
  [CKSD.integral_benjaminiHochbergFalseDiscoveryProportion_le](CKSD/Nonparametric/HighDimensional/FalseDiscoveryRate.lean#L194) (proved; scope in docstring).
- **103.38 Tracy–Widom law and spiked covariance.**
  [CKSD.tendsto_largestSampleCovarianceEigenvalue_tracyWidom](CKSD/Nonparametric/TracyWidom.lean#L78) (admitted; scope in docstring).
  [CKSD.ae_tendsto_largestEigenvalue_spiked_subcritical](CKSD/Nonparametric/TracyWidom.lean#L102) (admitted; scope in docstring).
  [CKSD.ae_tendsto_largestEigenvalue_spiked_supercritical](CKSD/Nonparametric/TracyWidom.lean#L115) (admitted; scope in docstring).
- **103.39 Le Cam's two-point method.**
  [CKSD.one_sub_totalVariationDistance_div_two_le_max_measureReal](CKSD/Nonparametric/LowerBounds/Testing.lean#L60) (proved; scope in docstring).
- **103.40 Fano's method.**
  [CKSD.one_sub_div_log_le_sSup_measureReal](CKSD/Nonparametric/LowerBounds/Testing.lean#L137) (proved; scope in docstring).
- **103.45 Varshamov–Gilbert bound.**
  [CKSD.exists_hamming_packing](CKSD/Nonparametric/LowerBounds/Testing.lean#L242) (proved; scope in docstring).
- **103.46 Assouad's lemma.**
  [CKSD.mul_one_sub_div_two_le_sSup_integral_hammingDist](CKSD/Nonparametric/LowerBounds/Testing.lean#L363) (proved; scope in docstring).
- **103.48 Restricted nullspace and exact recovery.**
  [CKSD.hasNullspaceProperty_iff](CKSD/Nonparametric/SparseRecovery/Basic.lean#L85) (proved; scope in docstring).
  [CKSD.hasNullspaceProperty_of_hasRestrictedIsometry](CKSD/Nonparametric/SparseRecovery/Nullspace.lean#L241) (proved; scope in docstring).
- **103.49 Stable recovery under restricted isometry.**
  [CKSD.hasRobustNullspaceProperty_of_hasRestrictedIsometry](CKSD/Nonparametric/SparseRecovery/Robust.lean#L308) (proved; scope in docstring).
  [CKSD.exists_basisPursuit_error_bound](CKSD/Nonparametric/SparseRecovery/Robust.lean#L487) (proved; scope in docstring).
- **103.52 Thresholded covariance estimation.**
  [CKSD.norm_thresholded_covariance_sub_le](CKSD/Nonparametric/HighDimensional/CovarianceThresholding.lean#L75) (proved; scope in docstring).
- **103.53 Gaussian graphical model selection.**
  [CKSD.neighbourhoodSelection_graph_recovery](CKSD/Nonparametric/HighDimensional/GraphicalModels.lean#L102) (admitted; scope in docstring).
  [CKSD.graphicalLasso_frobenius_error_bound](CKSD/Nonparametric/HighDimensional/GraphicalModels.lean#L143) (admitted; scope in docstring).
- **103.54 Perturbation of the leading eigenvector.**
  [CKSD.exists_eigenvector_norm_sub_le_of_rayleigh_gap](CKSD/Nonparametric/HighDimensional/EigenvectorPerturbation.lean#L121) (proved; scope in docstring).

### Section 104

- **104.1 Bernstein–von Mises theorem.**
  [CKSD.tendstoInMeasure_totalVariationDistance_normalPosterior](CKSD/Bayes/Posterior/BernsteinVonMises.lean#L344) (proved; scope in docstring).
- **104.5 Laplace approximation and the BIC.**
  [CKSD.tendsto_laplace_approximation](CKSD/Bayes/Posterior/Laplace.lean#L264) (proved; scope in docstring).
- **104.10 Highest posterior density regions.**
  [CKSD.volume_highest_density_region_le](CKSD/Bayes/Posterior/Basic.lean#L44) (proved; scope in docstring).
- **104.14 Tweedie's formula and Robbins' estimator.**
  [CKSD.integral_mul_gaussianPDFReal_div_eq_add_mul_deriv_log](CKSD/Bayes/Posterior/Basic.lean#L76) (proved; scope in docstring).
  [CKSD.integral_mul_poissonMass_div_eq](CKSD/Bayes/Posterior/Basic.lean#L166) (proved; scope in docstring).
  [CKSD.ae_tendsto_robbins_estimator](CKSD/Bayes/Posterior/Basic.lean#L183) (proved; scope in docstring).
- **104.15 Dirichlet process.**
  [CKSD.isDirichletProcess_stickBreaking](CKSD/Bayes/Dirichlet/Process.lean#L122) (proved; scope in docstring).
  [CKSD.ae_isDirichletProcessLaw_posterior](CKSD/Bayes/Dirichlet/Process.lean#L273) (proved; scope in docstring).
  [CKSD.ae_integral_posterior_eq_polyaPredictiveLaw](CKSD/Bayes/Dirichlet/Process.lean#L286) (proved; scope in docstring).
- **104.16 Pólya urn scheme and distinct values.**
  [CKSD.integral_distinctObservationCount_polya](CKSD/Bayes/PolyaUrn.lean#L138) (proved; scope in docstring).
  [CKSD.ae_tendsto_distinctObservationCount_div_log_polya](CKSD/Bayes/PolyaUrn.lean#L610) (proved; scope in docstring).
- **104.17 Doob's consistency theorem.**
  [CKSD.ae_isPosteriorConsistent_of_identifiable](CKSD/Bayes/Nonparametric.lean#L343) (proved; scope in docstring).
- **104.18 Schwartz's theorem.**
  [CKSD.tendstoInMeasure_posterior_compl_of_kl_support](CKSD/Bayes/PosteriorContraction.lean#L361) (proved; scope in docstring).
- **104.19 Contraction rate of Ghosal, Ghosh, and van der Vaart.**
  [CKSD.hasPosteriorContractionRate_statisticalHellingerDistance](CKSD/Bayes/PosteriorContraction.lean#L658) (proved; scope in docstring).
- **104.20 Linear inverse problems.**
  [CKSD.tendsto_gaussianSeqPosterior_contraction](CKSD/Bayes/InverseProblems.lean#L420) (proved; scope in docstring).
  [CKSD.exists_minimax_rate_inverseProblem](CKSD/Bayes/InverseProblems.lean#L770) (proved; scope in docstring).
- **104.22 Metropolis–Hastings.**
  [CKSD.metropolisTransition_mem_rowStochastic](CKSD/Bayes/MonteCarlo/MetropolisHastings.lean#L73) (proved; scope in docstring).
  [CKSD.metropolisTransition_detailedBalance](CKSD/Bayes/MonteCarlo/MetropolisHastings.lean#L90) (proved; scope in docstring).
  [CKSD.sum_mul_metropolisTransition](CKSD/Bayes/MonteCarlo/MetropolisHastings.lean#L108) (proved; scope in docstring).
- **104.24 Central limit theorem for Markov chain Monte Carlo.**
  [CKSD.tendstoInDistribution_finite_markov_chain_sum](CKSD/Bayes/MonteCarlo/MarkovChainCLT.lean#L444) (proved; scope in docstring).
- **104.31 Convergence of Metropolis–Hastings.**
  [CKSD.eventually_abs_metropolisTransition_pow_sub_le](CKSD/Bayes/MonteCarlo/MetropolisHastings.lean#L171) (proved; scope in docstring).
  [CKSD.ae_tendsto_sampleAverage_metropolis](CKSD/Bayes/MonteCarlo/MetropolisHastings.lean#L294) (proved; scope in docstring).
- **104.32 Independence and random-walk samplers.**
  [CKSD.abs_sum_independenceSampler_pow_sub_le](CKSD/Bayes/MonteCarlo/MetropolisHastings.lean#L118) (proved; scope in docstring).
- **104.35 Hamiltonian Monte Carlo.**
  [CKSD.measurePreserving_leapfrogStep_iterate](CKSD/Bayes/Langevin/Hamiltonian/Leapfrog.lean#L67) (proved; scope in docstring).
  [CKSD.leapfrogStep_iterate_reversible](CKSD/Bayes/Langevin/Hamiltonian/Leapfrog.lean#L93) (proved; scope in docstring).
- **104.37 Invariant measure and gradient-flow structure.**
  [CKSD.integral_langevin_generator_eq_zero](CKSD/Bayes/Dynamics.lean#L49) (proved; scope in docstring).
- **104.38 Contraction under strong convexity.**
  [CKSD.dist_synchronous_langevin_le_exp](CKSD/Bayes/Dynamics.lean#L75) (proved; scope in docstring).
- **104.39 Iteration complexity of Langevin Monte Carlo.**
  [CKSD.exists_ula_iteration_complexity](CKSD/Bayes/Langevin/Sampling.lean#L102) (admitted; scope in docstring).
- **104.40 Robbins–Monro convergence and averaging.**
  [CKSD.ae_tendsto_robbins_monro](CKSD/Bayes/StochasticApproximation.lean#L488) (proved; scope in docstring).
- **104.41 Entropy dissipation of Langevin flow.**
  [CKSD.le_exp_neg_mul_of_hasDerivAt_neg_of_two_mul_le](CKSD/Bayes/Dynamics.lean#L143) (proved; scope in docstring).
- **104.43 Jordan–Kinderlehrer–Otto theorem.**
  [CKSD.jko_scheme_tendsto_fokkerPlanck](CKSD/Bayes/FunctionalInequalities.lean#L521) (admitted; scope in docstring).
- **104.44 Convergence of the Langevin diffusion under functional inequalities.**
  [CKSD.poincareInequality_iff_chiSqDiv_langevin_le](CKSD/Bayes/FunctionalInequalities.lean#L67) (admitted; scope in docstring).
  [CKSD.logSobolevInequality_iff_klDiv_langevin_le](CKSD/Bayes/FunctionalInequalities.lean#L79) (admitted; scope in docstring).
  [CKSD.wasserstein_sq_langevin_le_of_logSobolev](CKSD/Bayes/FunctionalInequalities.lean#L91) (admitted; scope in docstring).
  [CKSD.poincareInequality_of_logSobolevInequality](CKSD/Bayes/FunctionalInequalities.lean#L368) (proved; scope in docstring).
  [CKSD.logSobolevInequality_gibbsMeasure_of_bounded_perturbation](CKSD/Bayes/FunctionalInequalities.lean#L467) (proved; scope in docstring).
  [CKSD.poincareInequality_gibbsMeasure_of_bounded_perturbation](CKSD/Bayes/FunctionalInequalities.lean#L486) (proved; scope in docstring).
- **104.45 Langevin Monte Carlo under a logarithmic Sobolev inequality.**
  [CKSD.exists_klDiv_ula_le_of_logSobolev](CKSD/Bayes/Langevin/Sampling.lean#L122) (admitted; scope in docstring).
  [CKSD.exists_wasserstein_ula_le_of_stronglyConvex](CKSD/Bayes/Langevin/Sampling.lean#L138) (proved; scope in docstring).
- **104.47 Mixing of Metropolis-adjusted Langevin.**
  [CKSD.exists_mala_mixing_time_le](CKSD/Bayes/Langevin/Sampling.lean#L186) (admitted; scope in docstring).
  [CKSD.exists_mala_mixing_time_ge](CKSD/Bayes/Langevin/Sampling.lean#L237) (proved; scope in docstring).
- **104.48 Invariance, contraction, and hypocoercivity.**
  [CKSD.integral_kineticGenerator_eq_zero](CKSD/Bayes/Langevin/Kinetic.lean#L280) (proved; scope in docstring).
  [CKSD.exists_kineticGenerator_not_symmetric](CKSD/Bayes/Langevin/Kinetic.lean#L510) (proved; scope in docstring).
  [CKSD.kineticCouplingNorm_synchronous_le](CKSD/Bayes/Langevin/Kinetic.lean#L823) (proved; scope in docstring).
  [CKSD.exists_kinetic_hypocoercive_decay_of_poincare](CKSD/Bayes/Langevin/Kinetic.lean#L883) (admitted; scope in docstring).
  [CKSD.exists_kinetic_entropic_hypocoercive_decay](CKSD/Bayes/Langevin/Kinetic.lean#L904) (admitted; scope in docstring).
- **104.49 Benaïm's limit-set theorem.**
  [CKSD.ae_isInternallyChainTransitive_limitSet](CKSD/Bayes/StochasticApproximation.lean#L606) (proved; scope in docstring).
  [CKSD.ae_tendsto_equilibrium_of_chainTransitive](CKSD/Bayes/StochasticApproximation.lean#L636) (proved; scope in docstring).
  [CKSD.ae_asymptotic_pseudotrajectory](CKSD/Bayes/StochasticApproximation.lean#L652) (proved; scope in docstring).
- **104.51 Propagation of chaos.**
  [CKSD.exists_unique_mcKeanVlasov_and_particleSystem](CKSD/Bayes/MeanField/PropagationOfChaos.lean#L72) (proved; scope in docstring).
  [CKSD.tendsto_particle_paths](CKSD/Bayes/MeanField/PropagationOfChaos.lean#L104) (proved; scope in docstring).
- **104.53 Mean-field training.**
  [CKSD.meanFieldRisk_eq](CKSD/Bayes/MeanField/Training/Limit.lean#L75) (proved; scope in docstring).
  [CKSD.hasGradientAt_meanFieldPotential_empiricalMeasure](CKSD/Bayes/MeanField/Training/Limit.lean#L163) (proved; scope in docstring).
  [CKSD.exists_meanField_limit](CKSD/Bayes/MeanField/Training/Limit.lean#L192) (proved; scope in docstring).
- **104.55 Consistency of the particle filter.**
  [CKSD.tendstoInMeasure_particle_average](CKSD/Bayes/Particle/Filter.lean#L820) (proved; scope in docstring).
- **104.56 A quantitative interaction model.**
  [CKSD.exists_lintegral_sup_particle_sub_le](CKSD/Bayes/MeanField/PropagationOfChaos.lean#L493) (proved; scope in docstring).
- **104.58 Unbiased particle likelihood.**
  [CKSD.integral_particleLikelihood_eq](CKSD/Bayes/Particle/Filter.lean#L262) (proved; scope in docstring).
- **104.59 Central limit theorem for Feynman–Kac particle models.**
  [CKSD.tendstoInDistribution_particle_average](CKSD/Bayes/Particle/LimitCore.lean#L268) (proved; scope in docstring).
  [CKSD.tendstoInDistribution_particle_likelihood](CKSD/Bayes/Particle/LimitCore.lean#L355) (proved; scope in docstring).
- **104.60 Uniform-in-time particle approximation.**
  [CKSD.exists_uniform_particle_moment_bound](CKSD/Bayes/Particle/Limits.lean#L29) (proved; scope in docstring).
- **104.63 Anderson's time reversal and the probability-flow equation.**
  [CKSD.probabilityFlow_isContinuityEquation_and_map](CKSD/Bayes/Diffusion/Models.lean#L77) (admitted; scope in docstring).
- **104.64 Score matching.**
  [CKSD.integral_sq_sub_score_div_two_eq](CKSD/Bayes/Dynamics.lean#L178) (proved; scope in docstring).
- **104.68 Score error and total variation.**
  [CKSD.totalVariationDistance_map_le_sqrt_klDiv](CKSD/Bayes/Diffusion/TotalVariation.lean#L30) (proved; scope in docstring).
- **104.75 Convergence of diffusion sampling under a second-moment assumption.**
  [CKSD.klDiv_ddpmLaw_le](CKSD/Bayes/Diffusion/Models.lean#L128) (admitted; scope in docstring).
  [CKSD.exists_ddpm_geometric_schedule](CKSD/Bayes/Diffusion/Models.lean#L147) (proved; scope in docstring).
  [CKSD.ddpmStepRatio_pos](CKSD/Bayes/Diffusion/Models.lean#L215) (proved; scope in docstring).
  [CKSD.ddpmStepRatio_le_half](CKSD/Bayes/Diffusion/Models.lean#L223) (proved; scope in docstring).
  [CKSD.div_two_mul_add_two_mul_ddpmStepRatio_eq](CKSD/Bayes/Diffusion/Models.lean#L233) (proved; scope in docstring).
  [CKSD.one_add_inv_ddpmStepRatio_mul_log](CKSD/Bayes/Diffusion/Models.lean#L256) (proved; scope in docstring).
- **104.76 A family of diffusions with prescribed marginals.**
  [CKSD.isFokkerPlanckSolution_add_score_of_continuityEquation](CKSD/Bayes/Diffusion/Models.lean#L355) (proved; scope in docstring).
  [CKSD.map_marginalPreservingDiffusion](CKSD/Bayes/Diffusion/Models.lean#L446) (admitted; scope in docstring).
  [CKSD.stochasticInterpolant_score](CKSD/Bayes/Diffusion/Models.lean#L475) (proved; scope in docstring).
  [CKSD.stochasticInterpolant_integral_sub_eq_integral_velocity](CKSD/Bayes/Diffusion/Models.lean#L571) (proved; scope in docstring).
- **104.77 Half-bridges and iterative proportional fitting.**
  [CKSD.klDiv_bridgeIterate_step](CKSD/Bayes/Bridges.lean#L58) (proved; scope in docstring).

### Section 105

- **105.1 Gauss–Markov theorem.**
  [CKSD.integral_inner_map_eq_of_map_integral_eq](CKSD/LinearModels/Regression.lean#L102) (proved; scope in docstring).
  [CKSD.variance_inner_map_le](CKSD/LinearModels/Regression.lean#L114) (proved; scope in docstring).
- **105.2 Normal sampling theory.**
  [CKSD.map_norm_sq_sub_div_eq_chiSquared](CKSD/LinearModels/Regression.lean#L171) (proved; scope in docstring).
  [CKSD.indepFun_map_norm_sq_sub](CKSD/LinearModels/Regression.lean#L200) (proved; scope in docstring).
- **105.3 Asymptotics of the generalised linear model.**
  [CKSD.tendstoInDistribution_canonicalGLM_root](CKSD/LinearModels/GLM/Asymptotics.lean#L594) (proved; scope in docstring).
  [CKSD.tendstoInDistribution_canonicalGLM_deviance](CKSD/LinearModels/GLM/Asymptotics.lean#L784) (proved; scope in docstring).
- **105.5 Quantile regression.**
  [CKSD.minimizes_expectedQuantileCheckLoss_iff](CKSD/LinearModels/RegressionLimits.lean#L159) (proved; scope in docstring).
  [CKSD.tendstoInDistribution_quantile_regression](CKSD/LinearModels/RegressionLimits.lean#L559) (proved; scope in docstring).
- **105.6 Finite normal mixtures.**
  [CKSD.GaussianMixtureModel.exists_equiv_of_law_eq](CKSD/LinearModels/Mixtures.lean#L104) (proved; scope in docstring).
  [CKSD.GaussianMixtureModel.not_bddAbove_logLikelihood](CKSD/LinearModels/Mixtures.lean#L177) (proved; scope in docstring).
- **105.10 Exact tests of nested linear models.**
  [CKSD.map_nestedFStatistic_eq_fisherSnedecor](CKSD/LinearModels/FTest.lean#L203) (proved; scope in docstring).
- **105.15 Distribution of quadratic forms.**
  [CKSD.indepFun_matrixQuadraticForm_iff](CKSD/LinearModels/Regression.lean#L518) (proved; scope in docstring).
- **105.16 Optimality of the $F$ test.**
  [CKSD.map_nestedFStatistic_eq_noncentralF](CKSD/LinearModels/FTest.lean#L98) (proved; scope in docstring).
  [CKSD.strictMono_noncentralF_upper_tail](CKSD/LinearModels/FTest.lean#L228) (proved; scope in docstring).
  [CKSD.fTest_isUniformlyMostPowerful_invariant](CKSD/LinearModels/FTest.lean#L336) (admitted; scope in docstring).
- **105.22 Wishart distribution and Hotelling's $T^2$.**
  [CKSD.gaussian_sampleMean_scatterMatrix_wishart_and_hotelling](CKSD/LinearModels/Multivariate/NormalSample.lean#L83) (proved; scope in docstring).
- **105.23 Wilks's lambda.**
  [CKSD.map_wilksLambda_wishart_eq_beta_product](CKSD/LinearModels/Multivariate/Tests.lean#L102) (proved; scope in docstring).
- **105.24 Principal component eigenvalues.**
  [CKSD.tendstoInDistribution_gaussian_sample_covariance_eigenvalue](CKSD/LinearModels/Multivariate/Tests.lean#L169) (proved; scope in docstring).
- **105.26 Undirected graphical models.**
  [CKSD.condIndepFun_multivariateGaussian_iff_inv_apply_eq_zero](CKSD/LinearModels/Graphical/Gaussian.lean#L251) (proved; scope in docstring).
  [CKSD.hasGaussianPairwiseMarkovProperty_iff_inv_mem_concentrationModel](CKSD/LinearModels/Graphical/Gaussian.lean#L347) (proved; scope in docstring).
- **105.28 Gaussian covariance likelihood.**
  [CKSD.gaussianNegLogLikelihood_sampleMean_le](CKSD/LinearModels/Multivariate/NormalSample.lean#L394) (proved; scope in docstring).
  [CKSD.gaussianNegLogLikelihood_eq_iff](CKSD/LinearModels/Multivariate/NormalSample.lean#L404) (proved; scope in docstring).
- **105.29 Canonical correlations.**
  [CKSD.charpoly_canonicalCorrelationMatrix_transform](CKSD/LinearModels/Multivariate/CanonicalCorrelation.lean#L127) (proved; scope in docstring).
  [CKSD.norm_canonicalCorrelationMatrix_le_one](CKSD/LinearModels/Multivariate/CanonicalCorrelation.lean#L305) (proved; scope in docstring).
  [CKSD.isGreatest_linearCombinationCorrelation](CKSD/LinearModels/Multivariate/CanonicalCorrelation.lean#L333) (proved; scope in docstring).
  [CKSD.indepFun_gaussian_blocks_iff_canonicalCorrelationMatrix_eq_zero](CKSD/LinearModels/Multivariate/CanonicalCorrelation.lean#L406) (proved; scope in docstring).
- **105.31 Structure of the Wishart law.**
  [CKSD.wishart_determinant_law](CKSD/LinearModels/Multivariate/NormalSample.lean#L415) (proved; scope in docstring).
- **105.32 Sampling theory of correlation coefficients.**
  [CKSD.gaussian_sample_correlation_student_law](CKSD/LinearModels/Multivariate/NormalSample.lean#L667) (proved; scope in docstring).
- **105.33 Likelihood-ratio tests of sphericity and independence.**
  [CKSD.tendstoInDistribution_sphericity_likelihood_ratio](CKSD/LinearModels/Multivariate/Tests.lean#L226) (proved; scope in docstring).
  [CKSD.tendstoInDistribution_block_independence_likelihood_ratio](CKSD/LinearModels/Multivariate/Tests.lean#L301) (proved; scope in docstring).
- **105.34 Invariant tests of a multivariate linear hypothesis.**
  [CKSD.multivariateHypothesisRoots_eq_iff_congruent](CKSD/LinearModels/Multivariate/Tests.lean#L389) (proved; scope in docstring).
  [CKSD.multivariate_test_statistics_eq_roots](CKSD/LinearModels/Multivariate/Tests.lean#L567) (proved; scope in docstring).
- **105.35 Factor analysis and identification.**
  [CKSD.IsNormalizedFactorLoading.exists_eq_mul_factorColumnSigns](CKSD/LinearModels/FactorAnalysis.lean#L101) (proved; scope in docstring).
  [CKSD.tendstoInMeasure_factor_mle_of_compact](CKSD/LinearModels/FactorAnalysis.lean#L328) (proved; scope in docstring).
- **105.36 Decomposable models.**
  [CKSD.isUndirectedGlobalMarkovMass_iff_clique_factorization](CKSD/LinearModels/Graphical/Decomposable.lean#L385) (proved; scope in docstring).
  [CKSD.existsUnique_isConcentrationMLE_inv](CKSD/LinearModels/Graphical/DecomposableGaussian.lean#L318) (proved; scope in docstring).
  [CKSD.isConcentrationMLE_decomposableConcentrationMLE](CKSD/LinearModels/Graphical/DecomposableGaussian.lean#L761) (proved; scope in docstring).
- **105.37 Kiefer–Wolfowitz equivalence.**
  [CKSD.kiefer_wolfowitz_equivalence](CKSD/LinearModels/Design.lean#L216) (proved; scope in docstring).
- **105.38 Randomization test.**
  [CKSD.sum_ite_randomizationPValue_le](CKSD/LinearModels/Design.lean#L250) (proved; scope in docstring).
- **105.42 Fisher's inequality and optimality of balanced incomplete blocks.**
  [CKSD.points_le_blocks_of_balancedIncompleteBlockDesign](CKSD/LinearModels/Design.lean#L279) (proved; scope in docstring).
- **105.44 Latin squares and mutually orthogonal sets.**
  [CKSD.card_le_sub_one_of_orthogonalLatinSquares](CKSD/LinearModels/Design.lean#L366) (proved; scope in docstring).
  [CKSD.exists_orthogonalLatinSquares_of_isPrimePow](CKSD/LinearModels/Design.lean#L431) (proved; scope in docstring).
- **105.72 Horvitz–Thompson estimation and design variance.**
  [CKSD.integral_horvitzThompson](CKSD/LinearModels/SurveySampling.lean#L632) (proved; scope in docstring).
  [CKSD.variance_horvitzThompson](CKSD/LinearModels/SurveySampling.lean#L639) (proved; scope in docstring).
  [CKSD.integral_horvitzThompsonVarianceEstimator](CKSD/LinearModels/SurveySampling.lean#L649) (proved; scope in docstring).
  [CKSD.variance_horvitzThompson_eq_sen_yates_grundy](CKSD/LinearModels/SurveySampling.lean#L657) (proved; scope in docstring).
- **105.73 Simple and stratified random sampling; Neyman allocation.**
  [CKSD.integral_sum_div_simpleRandomSampleDesign](CKSD/LinearModels/SurveySampling.lean#L682) (proved; scope in docstring).
  [CKSD.variance_sum_div_simpleRandomSampleDesign](CKSD/LinearModels/SurveySampling.lean#L689) (proved; scope in docstring).
  [CKSD.sq_sum_div_le_sum_sq_div_of_sum_eq](CKSD/LinearModels/SurveySampling.lean#L700) (proved; scope in docstring).
  [CKSD.sq_sum_div_eq_sum_sq_div_iff](CKSD/LinearModels/SurveySampling.lean#L709) (proved; scope in docstring).
- **105.46 Neyman's theorem.**
  [CKSD.integral_differenceInMeans](CKSD/LinearModels/SurveySampling.lean#L727) (proved; scope in docstring).
  [CKSD.variance_differenceInMeans](CKSD/LinearModels/SurveySampling.lean#L736) (proved; scope in docstring).
- **105.47 Identification by regression and by weighting.**
  [CKSD.integral_potentialOutcome_eq_sum_stratumOutcomeMean](CKSD/LinearModels/Causal/Identification.lean#L304) (proved; scope in docstring).
  [CKSD.integral_potentialOutcome_eq_integral_div_propensity](CKSD/LinearModels/Causal/Identification.lean#L329) (proved; scope in docstring).
- **105.48 Propensity score.**
  [CKSD.condIndepFun_propensityScore](CKSD/LinearModels/Causal/Efficiency.lean#L148) (proved; scope in docstring).
  [CKSD.condIndepFun_of_propensityScore](CKSD/LinearModels/Causal/Efficiency.lean#L177) (proved; scope in docstring).
- **105.49 Doubly robust estimator of the average treatment effect.**
  [CKSD.integral_treatmentEffectInfluence_sub_eq_sum_mul](CKSD/LinearModels/Causal/Identification.lean#L354) (proved; scope in docstring).
- **105.50 Local average treatment effect.**
  [CKSD.wald_ratio_eq_complier_average_effect](CKSD/LinearModels/Causal/Identification.lean#L385) (proved; scope in docstring).
- **105.55 Two-stage least squares.**
  [CKSD.tendstoInMeasure_twoStageLeastSquares](CKSD/LinearModels/Causal/InstrumentalVariables.lean#L341) (proved; scope in docstring).
  [CKSD.tendstoInDistribution_twoStageLeastSquares](CKSD/LinearModels/Causal/InstrumentalVariables.lean#L542) (proved; scope in docstring).
- **105.56 Efficient variance for an average treatment effect.**
  [CKSD.integral_finiteStrataTreatmentInfluence](CKSD/LinearModels/Causal/Efficiency.lean#L479) (proved; scope in docstring).
  [CKSD.variance_finiteStrataTreatmentInfluence](CKSD/LinearModels/Causal/Efficiency.lean#L493) (proved; scope in docstring).
  [CKSD.hasDerivAt_finiteStrataTreatmentEffect_score_tilt](CKSD/LinearModels/Causal/Efficiency.lean#L548) (proved; scope in docstring).
- **105.62 Directed Markov properties.**
  [CKSD.condIndepMass_directedFactorizationMass_of_dSeparated](CKSD/LinearModels/DirectedGraphical/Basic.lean#L539) (proved; scope in docstring).
  [CKSD.CausalGraph.recursivelyFactorizes_tfae](CKSD/LinearModels/DirectedGraphical/Markov.lean#L298) (proved; scope in docstring).
- **105.63 Back-door and front-door formulae.**
  [CKSD.doMarginalMass_eq_backdoor](CKSD/LinearModels/DirectedGraphical/Markov.lean#L338) (proved; scope in docstring).
  [CKSD.doMarginalMass_eq_frontdoor](CKSD/LinearModels/DirectedGraphical/Markov.lean#L384) (proved; scope in docstring).
- **105.64 Rules of the do-calculus.**
  [CKSD.condDoMass_rule_three](CKSD/LinearModels/DirectedGraphical/DoCalculus.lean#L508) (proved; scope in docstring).
  [CKSD.condDoMass_rule_one](CKSD/LinearModels/DirectedGraphical/Interventions.lean#L427) (proved; scope in docstring).
  [CKSD.condDoMass_rule_two](CKSD/LinearModels/DirectedGraphical/Interventions.lean#L454) (proved; scope in docstring).
- **105.65 Longitudinal $g$-formula.**
  [CKSD.integral_potentialOutcome_eq_gFormula](CKSD/LinearModels/Causal/GFormula.lean#L248) (proved; scope in docstring).
- **105.67 Markov equivalence of directed graphs.**
  [CKSD.markovEquivalent_iff_skeleton_and_colliders](CKSD/LinearModels/DirectedGraphical/Basic/CausalGraph.lean#L159) (admitted; scope in docstring).
  [CKSD.CausalGraph.isUnshieldedCollider_iff_of_isFaithful](CKSD/LinearModels/DirectedGraphical/Discovery.lean#L159) (proved; scope in docstring).
- **105.70 Skeleton and colliders from conditional independences.**
  [CKSD.CausalGraph.dSeparated_parents_of_not_adjacent](CKSD/LinearModels/DirectedGraphical/Discovery.lean#L40) (proved; scope in docstring).
  [CKSD.CausalGraph.adjacent_iff_forall_not_dSeparated](CKSD/LinearModels/DirectedGraphical/Discovery.lean#L51) (proved; scope in docstring).
  [CKSD.CausalGraph.isCollider_iff_notMem_of_dSeparated](CKSD/LinearModels/DirectedGraphical/Discovery.lean#L78) (proved; scope in docstring).
  [CKSD.CausalGraph.adjacent_iff_of_isFaithful](CKSD/LinearModels/DirectedGraphical/Discovery.lean#L124) (proved; scope in docstring).
  [CKSD.CausalGraph.isUnshieldedCollider_iff_of_isFaithful](CKSD/LinearModels/DirectedGraphical/Discovery.lean#L159) (proved; scope in docstring).
- **105.71 Identifiability of restricted structural equation models.**
  [CKSD.CausalGraph.edge_eq_of_linearSEMLaw_eq_of_nonGaussian](CKSD/LinearModels/Causal/StructuralEquations.lean#L110) (admitted; scope in docstring).
  [CKSD.CausalGraph.edge_eq_of_linearSEMLaw_eq_of_equalVariance](CKSD/LinearModels/Causal/StructuralEquations.lean#L294) (proved; scope in docstring).
  [CKSD.CausalGraph.edge_eq_of_additiveNoiseLaw_eq](CKSD/LinearModels/Causal/StructuralEquations.lean#L347) (admitted; scope in docstring).
  [CKSD.CausalGraph.exists_linearGaussianSEM_iff_markovEquivalent](CKSD/LinearModels/Causal/StructuralEquations.lean#L364) (admitted; scope in docstring).

### Section 106

- **106.1 Martingale central limit theorem.**
  [CKSD.tendstoInDistribution_martingale_array_sum](CKSD/Processes/TimeSeries/CentralLimit.lean#L78) (proved; scope in docstring).
- **106.2 Wold decomposition and causal autoregression.**
  [CKSD.exists_wold_decomposition](CKSD/Processes/TimeSeries/Wold.lean#L494) (proved; scope in docstring).
- **106.4 Bartlett's theorem.**
  [CKSD.tendstoInDistribution_sample_autocorrelations](CKSD/Processes/TimeSeries/SampleAutocorrelation.lean#L802) (proved; scope in docstring).
- **106.6 Periodogram and lag-window estimation.**
  [CKSD.tendstoInDistribution_periodogram_div_spectralDensity](CKSD/Processes/Spectral.lean#L102) (proved; scope in docstring).
  [CKSD.tendsto_lagWindowEstimator_moments](CKSD/Processes/Spectral.lean#L125) (admitted; scope in docstring).
- **106.7 Kalman filter.**
  [CKSD.KalmanModel.condDistrib_state_eq_multivariateGaussian](CKSD/Processes/Kalman/Filter.lean#L428) (proved; scope in docstring).
- **106.11 Moving-block bootstrap.**
  [CKSD.tendstoInMeasure_kolmogorovDistance_movingBlockBootstrapLaw](CKSD/Processes/Dependence.lean#L108) (admitted; scope in docstring).
- **106.12 Long-run variance of a sample mean.**
  [CKSD.tendsto_mul_variance_sampleAverage](CKSD/Processes/TimeSeries/LongRunVariance.lean#L121) (proved; scope in docstring).
- **106.14 Herglotz theorem and rational spectral densities.**
  [CKSD.IsPositiveSemidefiniteSequence.exists_stationary_gaussian](CKSD/Processes/TimeSeries/StationaryGaussian.lean#L169) (proved; scope in docstring).
- **106.16 Kolmogorov's formula for the prediction error.**
  [CKSD.infDist_past_sq_eq_kolmogorov](CKSD/Processes/Spectral.lean#L146) (admitted; scope in docstring).
- **106.17 Asymptotic covariance of ARMA estimators.**
  [CKSD.tendsto_whittleEstimator](CKSD/Processes/Spectral.lean#L210) (admitted; scope in docstring).
- **106.18 Stationarity of GARCH$(1,1)$.**
  [CKSD.ae_summable_garchTerm](CKSD/Processes/TimeSeries/Garch.lean#L175) (proved; scope in docstring).
  [CKSD.integral_garchVariance](CKSD/Processes/TimeSeries/Garch.lean#L233) (proved; scope in docstring).
  [CKSD.garchVariance_ae_eq](CKSD/Processes/TimeSeries/Garch.lean#L247) (proved; scope in docstring).
  [CKSD.covariance_garchProcess](CKSD/Processes/TimeSeries/Garch.lean#L295) (proved; scope in docstring).
- **106.21 Stein's prediction theorem.**
  [CKSD.eventually_abs_linearPredictionError_div_sub_one_le](CKSD/Processes/Dependence.lean#L147) (admitted; scope in docstring).
- **106.24 Bochner's theorem and the Matérn family.**
  [CKSD.exists_stationary_field_of_spectral_measure](CKSD/Processes/Spectral.lean#L342) (proved; scope in docstring).
- **106.28 Nelson–Aalen estimator.**
  [CKSD.tendstoInDistribution_nelsonAalenEstimator](CKSD/Processes/Survival.lean#L549) (proved; scope in docstring).
- **106.29 Kaplan–Meier estimator.**
  [CKSD.tendstoInDistribution_kaplanMeierEstimator](CKSD/Processes/Survival.lean#L817) (proved; scope in docstring).
- **106.30 Cox partial likelihood.**
  [CKSD.tendsto_coxPartialLikelihoodMaximizer](CKSD/Processes/CountingProcesses.lean#L87) (admitted; scope in docstring).
- **106.34 Rebolledo's martingale central limit theorem.**
  [CKSD.tendstoInDistribution_countingMartingaleTransform](CKSD/Processes/CountingProcesses.lean#L152) (admitted; scope in docstring).
- **106.37 Sequential probability ratio test.**
  [CKSD.integrable_stopped_sum](CKSD/Processes/Sequential.lean#L121) (proved; scope in docstring).
  [CKSD.integral_stopped_sum_eq](CKSD/Processes/Sequential.lean#L131) (proved; scope in docstring).
- **106.38 Ville's inequality and e-values.**
  [CKSD.measure_iSup_supermartingale_ge_le](CKSD/Processes/Sequential.lean#L184) (proved; scope in docstring).
- **106.39 CUSUM and the Brownian bridge.**
  [CKSD.tendstoInDistribution_cusumBridgeStatistic](CKSD/Processes/BridgeLimits.lean#L37) (admitted; scope in docstring).
- **106.41 Wald's fundamental identity and the operating characteristic.**
  [CKSD.integral_stopped_exponential_eq_one](CKSD/Processes/WaldIdentity.lean#L239) (proved; scope in docstring).
- **106.42 Anscombe's theorem.**
  [CKSD.tendstoInDistribution_random_sampleAverage](CKSD/Processes/Sequential.lean#L608) (proved; scope in docstring).
- **106.44 Optimality of CUSUM.**
  [CKSD.cusumStatistic_le_shiryaevRobertsStatistic](CKSD/Processes/Models.lean#L84) (proved; scope in docstring).
- **106.46 Fisher–Tippett–Gnedenko theorem.**
  [CKSD.tendsto_maximum_of_hasRegularlyVaryingTail](CKSD/Processes/Extremes.lean#L250) (proved; scope in docstring).
- **106.47 Excesses over high thresholds.**
  [CKSD.hasExtremeValueDomainOfAttraction_iff_pareto_excesses](CKSD/Processes/ExtremeValueLimits.lean#L78) (admitted; scope in docstring).
- **106.48 Extremal index.**
  [CKSD.tendstoInDistribution_card_exceedances](CKSD/Processes/Extremes.lean#L268) (proved; scope in docstring).
- **106.49 Hill estimator.**
  [CKSD.tendstoInDistribution_hillEstimator](CKSD/Processes/ExtremeValueLimits.lean#L108) (admitted; scope in docstring).
- **106.50 Poisson approximation for exceedances.**
  [CKSD.tendstoInDistribution_card_exceedances](CKSD/Processes/Extremes.lean#L268) (proved; scope in docstring).

### Section 107

- **107.1 Fundamental theorem of statistical learning.**
  [CKSD.measure_uniform_empirical_risk_deviation_le](CKSD/Learning/Generalization/Concentration.lean#L44) (proved; scope in docstring).
- **107.2 Rademacher bound.**
  [CKSD.integral_sSup_sub_le_two_mul_rademacher](CKSD/Learning/Generalization/Concentration.lean#L249) (proved; scope in docstring).
  [CKSD.measureReal_two_mul_rademacher_add_lt_sSup_le](CKSD/Learning/Generalization/Concentration.lean#L420) (proved; scope in docstring).
- **107.5 Hedge.**
  [CKSD.hedge_regret_le](CKSD/Learning/Generalization/ExponentialWeights.lean#L73) (proved; scope in docstring).
- **107.6 Split conformal prediction.**
  [CKSD.div_le_measureReal_conformalEvent](CKSD/Learning/Generalization/Conformal.lean#L213) (proved; scope in docstring).
  [CKSD.measureReal_conformalEvent_eq_div](CKSD/Learning/Generalization/Conformal.lean#L234) (proved; scope in docstring).
- **107.7 No free lunch.**
  [CKSD.exists_labelling_le_average_error](CKSD/Learning/Generalization/Classification.lean#L63) (proved; scope in docstring).
- **107.8 Bayes classification risk.**
  [CKSD.classificationRisk_sub_bayes_risk_eq](CKSD/Learning/Generalization/Classification.lean#L160) (proved; scope in docstring).
  [CKSD.classificationRisk_plugin_sub_bayes_risk_le](CKSD/Learning/Generalization/Classification.lean#L185) (proved; scope in docstring).
- **107.10 Margin bound.**
  [CKSD.measure_margin_generalization_error_le](CKSD/Learning/Generalization/Margin.lean#L68) (proved; scope in docstring).
- **107.11 Comparison inequality for convex surrogates.**
  [CKSD.surrogate_minimizer_sign_of_convex](CKSD/Learning/Generalization/Classification.lean#L216) (proved; scope in docstring).
- **107.12 Generalization of stable algorithms.**
  [CKSD.measureReal_sum_div_add_lt_integral_le_of_stable](CKSD/Learning/Generalization/Stability.lean#L196) (proved; scope in docstring).
- **107.13 Rate of kernel ridge regression.**
  [CKSD.ridgePrediction_oracle_bounds](CKSD/Learning/KernelAndClustering.lean#L314) (proved; scope in docstring).
- **107.14 Asymptotics of nearest-neighbour rules.**
  [CKSD.tendsto_oneNN_expectedError](CKSD/Learning/LocalAveraging.lean#L81) (admitted; scope in docstring).
  [CKSD.bayesRisk_le_nnRisk_le](CKSD/Learning/LocalAveraging.lean#L89) (proved; scope in docstring).
  [CKSD.exists_tendsto_knn_expectedError](CKSD/Learning/LocalAveraging.lean#L133) (admitted; scope in docstring).
  [CKSD.tendsto_knn_expectedError_bayesRisk](CKSD/Learning/LocalAveraging.lean#L144) (admitted; scope in docstring).
- **107.16 Consistency of $k$-means.**
  [CKSD.ae_tendsto_kmeans_centers_of_compact](CKSD/Learning/KernelAndClustering.lean#L539) (proved; scope in docstring).
- **107.19 Belief propagation and the Bethe free energy.**
  [CKSD.PairwiseGraphicalModel.isBetheStationary_iff_exists_beliefPropagationFixedPoint](CKSD/Learning/GraphicalModels/Basic.lean#L758) (proved; scope in docstring).
- **107.20 Consistency of response-independent forests.**
  [CKSD.tendsto_localAveraging_sq_error](CKSD/Learning/LocalAveraging.lean#L158) (admitted; scope in docstring).
- **107.23 Exact belief propagation on a tree.**
  [CKSD.PairwiseGraphicalModel.exists_beliefPropagation_exact_on_tree](CKSD/Learning/GraphicalModels/BeliefPropagationTree.lean#L563) (proved; scope in docstring).
  [CKSD.PairwiseGraphicalModel.beliefPropagation_tree_unique_up_to_scale](CKSD/Learning/GraphicalModels/BeliefPropagationTree.lean#L629) (proved; scope in docstring).
- **107.24 AdaBoost: training error and margins.**
  [CKSD.training_error_le_exponential_loss](CKSD/Learning/Algorithms.lean#L176) (proved; scope in docstring).
  [CKSD.boosting_training_error_le](CKSD/Learning/Algorithms.lean#L386) (proved; scope in docstring).
- **107.26 Variational representation of the cumulant function.**
  [CKSD.sum_mul_sub_mul_log_le_log_sum_exp](CKSD/Learning/Models.lean#L50) (proved; scope in docstring).
  [CKSD.sum_softmax_mul_sub_mul_log_eq_log_sum_exp](CKSD/Learning/Models.lean#L66) (proved; scope in docstring).
  [CKSD.tendsto_log_sum_exp_div_atTop](CKSD/Learning/Models.lean#L83) (proved; scope in docstring).
- **107.27 Junction-tree exactness.**
  [CKSD.hasJunctionTree_iff_isTriangulated](CKSD/Learning/GraphicalModels/JunctionTree.lean#L72) (proved; scope in docstring).
  [CKSD.sum_eq_one_and_tableMarginal_eq_of_jointMarginal](CKSD/Learning/GraphicalModels/JunctionTree.lean#L451) (proved; scope in docstring).
  [CKSD.junctionTreeProduct_isJointLaw](CKSD/Learning/GraphicalModels/JunctionTree.lean#L565) (proved; scope in docstring).
  [CKSD.exists_joint_with_clique_marginals_iff](CKSD/Learning/GraphicalModels/JunctionTree.lean#L585) (proved; scope in docstring).
- **107.28 Barron's rate.**
  [CKSD.exists_logisticNetwork_sq_error_le_barron_moment](CKSD/Learning/Approximation.lean#L60) (admitted; scope in docstring).
  [CKSD.exists_feature_average_sq_error_le](CKSD/Learning/Approximation.lean#L99) (proved; scope in docstring).
- **107.29 Deep networks and compositional classes.**
  [CKSD.compositionalHolder_minimax_lower_bound](CKSD/Learning/Networks.lean#L651) (admitted; scope in docstring).
- **107.30 Neural tangent kernel.**
  [CKSD.hasDerivAt_predictions_of_gradient_flow](CKSD/Learning/Models.lean#L127) (proved; scope in docstring).
- **107.31 Ridgeless least squares.**
  [CKSD.ridgeless_gaussian_risk_eq](CKSD/Learning/Models.lean#L306) (proved; scope in docstring).
- **107.35 Capacity of network classes.**
  [CKSD.card_le_of_shatters_denseSignClass](CKSD/Learning/Networks.lean#L98) (admitted; scope in docstring).
  [CKSD.empiricalRademacherComplexity_biasFree_le](CKSD/Learning/Networks.lean#L524) (proved; scope in docstring).
- **107.36 Approximation rates of deep ReLU networks.**
  [CKSD.abs_reluLinearInterpolant_sub_le](CKSD/Learning/Approximation.lean#L273) (proved; scope in docstring).
- **107.37 Depth separation.**
  [CKSD.relu_depth_lower_bound](CKSD/Learning/Networks.lean#L580) (admitted; scope in docstring).
  [CKSD.relu_eldan_shamir_separation](CKSD/Learning/Networks.lean#L596) (admitted; scope in docstring).
- **107.39 Gaussian-process limit at initialization.**
  [CKSD.tendstoInDistribution_wide_network_gaussian](CKSD/Learning/Networks.lean#L689) (proved; scope in docstring).
- **107.40 Implicit bias of gradient descent.**
  [CKSD.tendsto_least_squares_gradient_descent](CKSD/Learning/Models.lean#L349) (proved; scope in docstring).
- **107.41 Exact recovery.**
  [CKSD.exists_exactRecovery_iff](CKSD/Learning/RandomGraphs.lean#L77) (admitted; scope in docstring).
  [CKSD.exists_exactRecovery_iff_of_zero](CKSD/Learning/RandomGraphs.lean#L88) (admitted; scope in docstring).
- **107.42 Kesten–Stigum threshold.**
  [CKSD.exists_weakRecovery_iff](CKSD/Learning/RandomGraphs.lean#L96) (admitted; scope in docstring).
  [CKSD.blockModel_binomialRandom_mutually_contiguous](CKSD/Learning/RandomGraphs.lean#L105) (admitted; scope in docstring).
- **107.43 Aldous–Hoover theorem for graphs.**
  [CKSD.existsUnique_graphonMixture_of_finitePerm_invariant](CKSD/Learning/RandomGraphs.lean#L197) (proved; scope in docstring).
  [CKSD.infiniteSampleLaw_eq_iff_exists_measurePreserving](CKSD/Learning/RandomGraphs.lean#L210) (admitted; scope in docstring).
- **107.47 Phase transitions of the Erdős–Rényi graph.**
  [CKSD.tendsto_binomialRandom_connected_threshold](CKSD/Learning/RandomGraphs/ConnectivityThreshold.lean#L234) (proved; scope in docstring).
  [CKSD.tendsto_binomialRandom_connected_of_tendsto_atTop](CKSD/Learning/RandomGraphs/ConnectivityThreshold.lean#L323) (proved; scope in docstring).
  [CKSD.tendsto_binomialRandom_exists_isolated_of_tendsto_atBot](CKSD/Learning/RandomGraphs/ConnectivityThreshold.lean#L350) (proved; scope in docstring).
  [CKSD.binomialRandom_connectivity_threshold](CKSD/Learning/RandomGraphs/ConnectivityThreshold.lean#L476) (proved; scope in docstring).
  [CKSD.exists_tendsto_binomialRandom_components_le_log](CKSD/Learning/RandomGraphs/Subcritical.lean#L520) (proved; scope in docstring).
  [CKSD.binomialRandom_giant_component](CKSD/Learning/RandomGraphs.lean#L121) (admitted; scope in docstring).
- **107.49 Lai–Robbins lower bound.**
  [CKSD.lai_robbins_lower_bound](CKSD/Learning/Bandits/Stochastic.lean#L104) (admitted; scope in docstring).
- **107.50 Upper confidence bounds.**
  [CKSD.integral_regret_le_of_ucb](CKSD/Learning/Bandits/UCB.lean#L530) (proved; scope in docstring).
- **107.51 Thompson sampling and the Gittins index.**
  [CKSD.FiniteMarkovBandit.banditPolicyValue_le_of_gittins](CKSD/Learning/Bandits/Gittins.lean#L88) (admitted; scope in docstring).
  [CKSD.tendsto_thompson_regret_div_log](CKSD/Learning/Bandits/Stochastic.lean#L140) (admitted; scope in docstring).
- **107.52 Adversarial bandits.**
  [CKSD.integral_regret_le_of_exp3](CKSD/Learning/Bandits/Exp3.lean#L246) (proved; scope in docstring).
- **107.54 Convergence of $Q$-learning.**
  [CKSD.ae_tendsto_asynchronous_stochastic_approximation](CKSD/Learning/Reinforcement/MarkovDecision.lean#L389) (admitted; scope in docstring).
- **107.58 Stationary optimal policies and linear programming.**
  [CKSD.FiniteMarkovBandit.banditPolicyValue_le_of_gittins](CKSD/Learning/Bandits/Gittins.lean#L88) (admitted; scope in docstring).
  [CKSD.FiniteMarkovDecisionProcess.bellmanOperator_optimalStateValue](CKSD/Learning/Reinforcement/MarkovDecision.lean#L142) (proved; scope in docstring).
  [CKSD.FiniteMarkovDecisionProcess.exists_greedy_optimalStateValue](CKSD/Learning/Reinforcement/MarkovDecision.lean#L148) (proved; scope in docstring).
  [CKSD.FiniteMarkovDecisionProcess.optimalStateValue_le_of_forall_le](CKSD/Learning/Reinforcement/MarkovDecision.lean#L159) (proved; scope in docstring).
  [CKSD.FiniteMarkovDecisionProcess.sum_mul_optimalStateValue_le](CKSD/Learning/Reinforcement/MarkovDecision.lean#L180) (proved; scope in docstring).
  [CKSD.FiniteMarkovDecisionProcess.sum_mul_optimalStateValue_eq_iff](CKSD/Learning/Reinforcement/MarkovDecision.lean#L188) (proved; scope in docstring).
- **107.59 Sample complexity with a generative model.**
  [CKSD.inv_one_sub_smul_mulVec_sub_eq](CKSD/Learning/Reinforcement/MarkovDecision.lean#L320) (proved; scope in docstring).
  [CKSD.norm_inv_one_sub_smul_mulVec_sub_le](CKSD/Learning/Reinforcement/MarkovDecision.lean#L337) (proved; scope in docstring).
- **107.60 Temporal differences with linear features.**
  [CKSD.norm_projected_fixed_point_sub_le](CKSD/Learning/Reinforcement/MarkovDecision.lean#L356) (proved; scope in docstring).
- **107.61 Convergence of natural policy gradient.**
  [CKSD.FiniteMarkovDecisionProcess.optimalObjective_sub_npg_le](CKSD/Learning/Reinforcement/PolicyOptimization.lean#L423) (proved; scope in docstring).
- **107.62 Minimax regret of finite-armed bandits.**
  [CKSD.exists_bernoulli_banditRegret_ge](CKSD/Learning/Bandits/Stochastic.lean#L157) (admitted; scope in docstring).
  [CKSD.exists_ucb1_banditRegret_le](CKSD/Learning/Bandits/Stochastic.lean#L650) (proved; scope in docstring).
- **107.63 Self-normalized confidence and LinUCB.**
  [CKSD.measure_exists_selfNormalized_gt_le](CKSD/Learning/Bandits/Stochastic.lean#L735) (admitted; scope in docstring).
  [CKSD.exists_linUCB_regret_le](CKSD/Learning/Bandits/Stochastic.lean#L759) (admitted; scope in docstring).
- **107.65 Composition.**
  [CKSD.isDifferentiallyPrivate_compProd](CKSD/Learning/Privacy/Basic.lean#L41) (proved; scope in docstring).
- **107.66 Private mean estimation.**
  [CKSD.exists_centralMeanRisk_ge](CKSD/Learning/Privacy/CentralLowerBounds.lean#L353) (proved; scope in docstring).
  [CKSD.isDifferentiallyPrivate_localLaplaceKernel](CKSD/Learning/Privacy/LocalEstimation.lean#L189) (proved; scope in docstring).
  [CKSD.localMeanRisk_localLaplace_mean_le](CKSD/Learning/Privacy/LocalEstimation.lean#L250) (proved; scope in docstring).
  [CKSD.localMeanRisk_minimax_order](CKSD/Learning/Privacy/LocalEstimation.lean#L327) (proved; scope in docstring).
  [CKSD.isDifferentiallyPrivate_laplaceMeanMechanism](CKSD/Learning/Privacy/Mechanisms.lean#L183) (proved; scope in docstring).
  [CKSD.centralMeanRisk_laplaceMeanMechanism_le](CKSD/Learning/Privacy/Mechanisms.lean#L287) (proved; scope in docstring).
  [CKSD.exists_centralMeanRisk_le](CKSD/Learning/Privacy/Mechanisms.lean#L351) (proved; scope in docstring).
- **107.74 Sparse vector technique.**
  [CKSD.sub_le_of_threshold_add_le_add](CKSD/Learning/Algorithms.lean#L193) (proved; scope in docstring).
  [CKSD.le_add_of_add_lt_threshold_add](CKSD/Learning/Algorithms.lean#L201) (proved; scope in docstring).
  [CKSD.one_sub_le_measureReal_aboveThreshold_accurate](CKSD/Learning/Algorithms.lean#L236) (proved; scope in docstring).
- **107.75 Contraction under local privacy.**
  [CKSD.klDiv_comp_le_of_local_differential_privacy](CKSD/Learning/Privacy/Basic.lean#L234) (proved; scope in docstring).
  [CKSD.exists_bernoulli_localMeanRisk_ge](CKSD/Learning/Privacy/LocalEstimation.lean#L67) (proved; scope in docstring).

### Section 108

- **108.1 Cheeger inequality for the normalized Laplacian.**
  [CKSD.spectralGap_cheegerConstant_bounds](CKSD/Geometry/Cheeger.lean#L442) (proved; scope in docstring).
- **108.4 Geodesic approximation.**
  [CKSD.eventually_sampleGraphEDist_intrinsicEDist_le](CKSD/Geometry/ManifoldLearning.lean#L69) (admitted; scope in docstring).
  [CKSD.intrinsicEDist_eq_edist_of_lengthPreserving](CKSD/Geometry/ManifoldLearning.lean#L91) (proved; scope in docstring).
- **108.5 Fréchet means.**
  [CKSD.existsUnique_frechet_mean_of_midpoint_inequality](CKSD/Geometry/GeometricStatistics.lean#L61) (proved; scope in docstring).
- **108.7 Hausdorff estimation of a submanifold.**
  [CKSD.isBoundedInProbability_hausdorff_sampling_error](CKSD/Geometry/GeometricStatistics.lean#L234) (proved; scope in docstring).
- **108.8 Classical multidimensional scaling.**
  [CKSD.posSemidef_double_centering_iff_sq_euclidean_distances](CKSD/Geometry/GeometricStatistics.lean#L396) (proved; scope in docstring).
- **108.10 Extrinsic projection mean.**
  [CKSD.extrinsic_mean_iff_nearest_expectation](CKSD/Geometry/GeometricStatistics.lean#L460) (proved; scope in docstring).
  [CKSD.tendstoInDistribution_projected_sampleAverage](CKSD/Geometry/GeometricStatistics.lean#L473) (proved; scope in docstring).
- **108.13 Uniqueness of Fréchet means in small balls.** — theorem formulation pending.
- **108.15 Barycentric equation.** — theorem formulation pending.
- **108.18 Interval decomposition.**
  [CKSD.exists_intervalBasis_of_isPointwiseFiniteDimensional](CKSD/Geometry/Persistence/Modules.lean#L65) (admitted; scope in docstring).
  [CKSD.IntervalBasis.exists_equiv_support_eq](CKSD/Geometry/Persistence/Modules.lean#L296) (proved; scope in docstring).
  [CKSD.exists_isSublevelDiagram](CKSD/Geometry/SimplicialPersistence/Chains.lean#L521) (proved; scope in docstring).
- **108.19 Bottleneck stability.**
  [CKSD.fullBottleneckEDist_le_of_isSublevelDiagram](CKSD/Geometry/SimplicialPersistence/Stability.lean#L326) (proved; scope in docstring).
- **108.20 Isometry theorem.**
  [CKSD.interleavingEDist_le_fullBottleneckEDist](CKSD/Geometry/Persistence/Modules.lean#L457) (proved; scope in docstring).
  [CKSD.interleavingEDist_eq_fullBottleneckEDist](CKSD/Geometry/Persistence/Modules.lean#L538) (admitted; scope in docstring).
- **108.21 Čech, Rips, and the nerve.**
  [CKSD.IsCechSimplex.isRipsSimplex](CKSD/Geometry/Persistence/Basic.lean#L172) (proved; scope in docstring).
  [CKSD.cech_rips_inclusions](CKSD/Geometry/Persistence/CechRips.lean#L159) (proved; scope in docstring).
- **108.22 Homology from a sample.**
  [CKSD.exists_deformationRetraction_offset_of_hausdorffDist_lt](CKSD/Geometry/Persistence/TopologicalInference.lean#L82) (admitted; scope in docstring).
  [CKSD.exists_sample_size_hausdorffDist_le](CKSD/Geometry/Persistence/TopologicalInference.lean#L103) (proved; scope in docstring).
- **108.23 Central limit theorem for landscapes.**
  [CKSD.LandscapeLp.ae_tendsto_sampleAverage](CKSD/Geometry/Persistence/Landscapes.lean#L45) (proved; scope in docstring).
- **108.24 Stability of the distance to a measure.**
  [CKSD.abs_distanceToMeasure_sub_le_wasserstein](CKSD/Geometry/Persistence/CechRips.lean#L207) (proved; scope in docstring).
- **108.32 Persistence pairing by matrix reduction.**
  [CKSD.isColumnLow_iff_pairingRankCombination_eq_one](CKSD/Geometry/MatrixReduction/Basic.lean#L315) (proved; scope in docstring).
  [CKSD.isColumnLow_iff_of_isMatrixReduction](CKSD/Geometry/MatrixReduction/Basic.lean#L323) (proved; scope in docstring).
  [CKSD.persistentBettiOfMatrix_eq_card](CKSD/Geometry/MatrixReduction/Homology.lean#L169) (proved; scope in docstring).
  [CKSD.IsColumnLow.dim_eq_and_persistentBettiOfMatrix_eq](CKSD/Geometry/MatrixReduction/Homology.lean#L395) (proved; scope in docstring).
- **108.34 Sublevel persistence of a Morse function.**
  [CKSD.sublevelHomologyModule_bars_of_isMorse](CKSD/Geometry/Persistence/TopologicalInference.lean#L251) (admitted; scope in docstring).
- **108.35 Wasserstein stability.**
  [CKSD.diagramWassersteinEDist_le_of_isSublevelDiagram](CKSD/Geometry/SimplicialPersistence/Stability.lean#L794) (proved; scope in docstring).
- **108.36 Gromov–Hausdorff stability of Rips persistence.**
  [CKSD.fullBottleneckEDist_rips_le_ghDist](CKSD/Geometry/Persistence/RipsStability.lean#L566) (proved; scope in docstring).
- **108.37 Homology inference with positive weak feature size.**
  [CKSD.nonempty_range_offsetHomology_equiv_of_weakFeatureSize](CKSD/Geometry/Persistence/TopologicalInference.lean#L194) (admitted; scope in docstring).
  [CKSD.nonempty_ripsPersistentHomology_equiv_of_weakFeatureSize](CKSD/Geometry/Persistence/TopologicalInference.lean#L214) (admitted; scope in docstring).
- **108.40 Empirical Wasserstein bounds.**
  [CKSD.integral_empirical_wasserstein_rpow_le](CKSD/Geometry/Transport/Statistical.lean#L63) (admitted; scope in docstring).
- **108.42 Consistency of Brenier maps.**
  [CKSD.tendsto_integral_sq_optimal_map_sub](CKSD/Geometry/Transport/OptimalMapStability.lean#L258) (proved; scope in docstring).
- **108.43 Gromov–Wasserstein distance.**
  [CKSD.exists_measure_preserving_isometryEquiv_of_zero_distortion](CKSD/Geometry/Transport/Statistical.lean#L102) (proved; scope in docstring).
- **108.44 Debiased Sinkhorn divergence.**
  [CKSD.realSinkhornDivergence_independent_lower_bound](CKSD/Geometry/Transport/Entropic.lean#L100) (proved; scope in docstring).
  [CKSD.realSinkhornDivergence_nonneg](CKSD/Geometry/Transport/Entropic.lean#L129) (proved; scope in docstring).
- **108.46 Gaussian transport and barycenters.**
  [CKSD.wasserstein_multivariateGaussian_sq_eq](CKSD/Geometry/Transport/Gaussian.lean#L103) (proved; scope in docstring).
  [CKSD.exists_unique_gaussian_wasserstein_barycenter](CKSD/Geometry/Transport/Statistical.lean#L152) (proved; scope in docstring).
- **108.47 One-dimensional empirical transport limit.**
  [CKSD.tendstoInDistribution_mul_wasserstein_sq_empiricalMeasure](CKSD/Geometry/Transport/Rates.lean#L58) (admitted; scope in docstring).
- **108.50 Minimax lower bounds for transport estimation.**
  [CKSD.rpow_div_le_wassersteinEDist_volume_cube](CKSD/Geometry/Transport/Statistical.lean#L277) (proved; scope in docstring).
- **108.51 Smooth laws and smoothed distances.**
  [CKSD.integral_wasserstein_gaussianSmoothing_empiricalMeasure_le](CKSD/Geometry/Transport/Statistical.lean#L389) (proved; scope in docstring).
- **108.53 Rates for transport-map estimation.**
  [CKSD.lintegral_transportMapRisk_semidualEstimator_le](CKSD/Geometry/Transport/Rates.lean#L127) (admitted; scope in docstring).
  [CKSD.lintegral_transportMapRisk_semidualEstimator_le_of_poincare](CKSD/Geometry/Transport/Rates.lean#L144) (admitted; scope in docstring).
- **108.55 Dimension-free sample complexity of entropic transport.**
  [CKSD.quadraticEntropicTransport_empirical_bounds](CKSD/Geometry/Transport/Entropic.lean#L162) (admitted; scope in docstring).
- **108.56 Semidiscrete dual.**
  [CKSD.hasFDerivAt_integral_semidiscretePotential](CKSD/Geometry/Transport/Semidiscrete.lean#L287) (proved; scope in docstring).
  [CKSD.hasFDerivAt_semidiscreteTransportDual](CKSD/Geometry/Transport/Semidiscrete.lean#L355) (proved; scope in docstring).
  [CKSD.contDiff_semidiscreteTransportDual](CKSD/Geometry/Transport/Semidiscrete.lean#L385) (proved; scope in docstring).
  [CKSD.concaveOn_semidiscreteTransportDual](CKSD/Geometry/Transport/Semidiscrete.lean#L396) (proved; scope in docstring).
  [CKSD.semidiscreteTransportDual_isMax_iff](CKSD/Geometry/Transport/Semidiscrete.lean#L513) (proved; scope in docstring).
  [CKSD.exists_isMax_semidiscreteTransportDual](CKSD/Geometry/Transport/Semidiscrete.lean#L539) (proved; scope in docstring).
  [CKSD.map_semidiscreteTransportMap](CKSD/Geometry/Transport/Semidiscrete.lean#L658) (proved; scope in docstring).
  [CKSD.integral_norm_sub_semidiscreteTransportMap_sq](CKSD/Geometry/Transport/Semidiscrete.lean#L686) (proved; scope in docstring).
  [CKSD.ofReal_semidiscreteTransportDual_le_lintegral](CKSD/Geometry/Transport/Semidiscrete.lean#L714) (proved; scope in docstring).
  [CKSD.semidiscreteTransportDual_eq_wassersteinEDist_sq](CKSD/Geometry/Transport/Semidiscrete.lean#L782) (proved; scope in docstring).
  [CKSD.semidiscreteTransportDual_concave_differentiable_and_attains_max](CKSD/Geometry/Transport/Statistical.lean#L406) (proved; scope in docstring).
- **108.57 Tangent-space linearization.**
  [CKSD.optimalMap_eq_cfcSqrt_mul_inv_iff_commute](CKSD/Geometry/Transport/Statistical.lean#L441) (proved; scope in docstring).
- **108.58 First-order conditions for barycenters.**
  [CKSD.hasDerivAt_wassersteinBarycenterEnergy_displacement](CKSD/Geometry/Transport/Barycenter.lean#L233) (proved; scope in docstring).
  [CKSD.satisfiesWassersteinKarcherEquation_of_minimizer](CKSD/Geometry/Transport/Barycenter.lean#L267) (proved; scope in docstring).
- **108.59 Procrustes iteration for barycenters.**
  [CKSD.wassersteinBarycenterEnergy_map_sub_le](CKSD/Geometry/Transport/Barycenter.lean#L127) (proved; scope in docstring).
- **108.61 Limits of the empirical discrepancy.**
  [CKSD.tendstoInDistribution_unbiasedSquaredMMD_null](CKSD/Geometry/Kernels/UnbiasedMMD.lean#L272) (proved; scope in docstring).
  [CKSD.tendstoInDistribution_unbiasedSquaredMMD_alternative](CKSD/Geometry/Kernels/UnbiasedMMD.lean#L529) (proved; scope in docstring).
- **108.62 Energy distance and independence.**
  [CKSD.energy_distance_nonneg_eq_zero_iff_and_eq_squaredMMD](CKSD/Geometry/Kernels/Characteristic.lean#L69) (proved; scope in docstring).
  [CKSD.distance_covariance_nonneg_eq_zero_iff_and_eq_squaredMMD](CKSD/Geometry/Kernels/Characteristic.lean#L82) (proved; scope in docstring).
- **108.63 Hilbert–Schmidt independence criterion.**
  [CKSD.squaredMMD_joint_prod_eq_zero_iff_indepFun](CKSD/Geometry/Kernels/Characteristic.lean#L108) (proved; scope in docstring).
- **108.68 Criteria for characteristic kernels.**
  [CKSD.isCharacteristicKernel_iff_spectral_measure_full_support](CKSD/Geometry/Kernels/Characteristic.lean#L124) (proved; scope in docstring).
  [CKSD.squaredMMD_quadratic_polynomial_eq](CKSD/Geometry/Kernels/Characteristic.lean#L194) (proved; scope in docstring).
- **108.70 Metrization of weak convergence.**
  [CKSD.tendsto_probabilityMeasure_iff_tendsto_squaredMMD_of_tight](CKSD/Geometry/Kernels/Characteristic.lean#L242) (proved; scope in docstring).
- **108.71 Kernel Stein discrepancy.**
  [CKSD.integral_langevin_stein_operator_eq_zero](CKSD/Geometry/Kernels/Characteristic.lean#L291) (proved; scope in docstring).
- **108.72 Convergence control by kernel Stein discrepancies.**
  [CKSD.tendsto_of_kernelSteinDiscrepancySq_inverseMultiquadric_tendsto_zero](CKSD/Geometry/Kernels/SteinDiscrepancy.lean#L70) (admitted; scope in docstring).
  [CKSD.exists_not_tendsto_of_kernelSteinDiscrepancySq_tendsto_zero](CKSD/Geometry/Kernels/SteinDiscrepancy.lean#L93) (admitted; scope in docstring).
- **108.74 Random Fourier features.**
  [CKSD.integral_randomFourierFeatureKernel](CKSD/Geometry/Kernels/RandomFeatures.lean#L160) (proved; scope in docstring).
  [CKSD.measureReal_abs_randomFourierFeatureKernel_sub_ge_le](CKSD/Geometry/Kernels/RandomFeatures.lean#L189) (proved; scope in docstring).
  [CKSD.measure_uniform_randomFourierFeatureKernel_error_le](CKSD/Geometry/Kernels/RandomFeatures.lean#L530) (proved; scope in docstring).
  [CKSD.abs_squaredMMD_sub_le_of_uniform_kernel_error](CKSD/Geometry/Kernels/RandomFeatures.lean#L669) (proved; scope in docstring).
