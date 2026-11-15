# Mathlib-style assessment of CKSD

The project contains 387 Lean modules under `CKSD/` and 3715 inventoried declarations:
847 definitions, abbreviations, structures and inductive types, and 2868 theorem statements
(2779 proved, no conditional results, and 89 admitted). The largest module is
[Learning/GraphicalModels/ChordalGraphs.lean](CKSD/Learning/GraphicalModels/ChordalGraphs.lean)
at 982 lines, below the 1500-line hard limit; modules near 1000 lines are candidates for
splitting at a natural mathematical seam. All modules use the module system without a blanket
`@[expose]`: definitions whose bodies are part of their interface carry `@[expose]`
individually, the others have defining lemmas, and proof-only dependencies are plain imports.
All modules have Mathlib-style module documentation with the mathematical scope, main
definitions and main results. All authored definitions, abbreviations, structures, inductive
types and theorem statements have formal docstrings, as do all structure fields. Theorem
docstrings state the mathematics together with the `GAPS ddd.k` tag of the catalogue entry
they formalize.

The dependency baseline is Lean `v4.36.0-rc2`, Mathlib
`6135ffb78e8bcd3fcc8ec02f3f82ea0b0737358b`, TauCeti
`afa08a3ed16fb167e35de371afb1eb03fbc5913a`, and Statlib
`eeaac0283690efaa60c31115400cf561836baeb9`. Namespace and build conventions are in
[AGENTS.md](AGENTS.md). Declaration statuses and source locations are in
[FORMALIZATION.md](FORMALIZATION.md); this assessment does not certify the truth of admissions.

## Proved statistical foundations

The following scoped catalogue statements have complete proofs with no admitted dependencies:

- [Blackwell comparison theorem for finite parameter sets](CKSD/Inference/Decision.lean#L439) (GAPS 101.62).
- [MALA lower bound with curvature chosen after the step size](CKSD/Bayes/Langevin/Sampling.lean#L237) (GAPS 104.47).
- [Wasserstein barycenter directional first variation](CKSD/Geometry/Transport/Barycenter.lean#L233) (GAPS 108.58).
- [LAN representation of local limit laws by a Gaussian-shift kernel](CKSD/Asymptotics/LAN/Representation.lean#L53) (GAPS 102.15).
- [Hájek convolution theorem for regular estimators](CKSD/Asymptotics/LAN/Representation.lean#L167) (GAPS 102.16).
- [Existence and uniqueness of every discrete JKO step](CKSD/Bayes/FunctionalInequalities.lean#L508) (the discrete part of GAPS 104.43).
- [Strongly convex ULA Wasserstein convergence bound](CKSD/Bayes/Langevin/Sampling.lean#L138) (GAPS 104.45).
- [Uniform-in-time particle-filter moment bound](CKSD/Bayes/Particle/Limits.lean#L29) (GAPS 104.60).
- [Mean-field training limit with almost-sure uniform empirical convergence](CKSD/Bayes/MeanField/Training/Limit.lean#L192) (GAPS 104.53).
- [Gaussian block-independence likelihood-ratio chi-squared limit](CKSD/LinearModels/Multivariate/Tests.lean#L301) (GAPS 105.33).
- [Benaïm stochastic-approximation limit-set theorem](CKSD/Bayes/StochasticApproximation.lean#L606) (GAPS 104.49).
- [Bounded-perturbation logarithmic Sobolev inequality](CKSD/Bayes/FunctionalInequalities.lean#L467) (GAPS 104.44).
- [McKean–Vlasov and finite-particle well-posedness](CKSD/Bayes/MeanField/PropagationOfChaos.lean#L72) (GAPS 104.51).
- [General propagation of chaos on continuous path spaces](CKSD/Bayes/MeanField/PropagationOfChaos.lean#L104) (GAPS 104.51).
- [Exact Wilks determinant-ratio Beta-product law](CKSD/LinearModels/Multivariate/Tests.lean#L102) (GAPS 105.23).
- [Gaussian sphericity likelihood-ratio chi-squared limit](CKSD/LinearModels/Multivariate/Tests.lean#L226) (GAPS 105.33).
- [Stochastic-approximation asymptotic pseudotrajectory](CKSD/Bayes/StochasticApproximation.lean#L652) (GAPS 104.49).
- [Quantitative synchronous propagation of chaos](CKSD/Bayes/MeanField/PropagationOfChaos.lean#L493) (GAPS 104.56).
- [Gaussian simple covariance-eigenvalue central limit theorem](CKSD/LinearModels/Multivariate/Tests.lean#L169) (GAPS 105.24).
- [Energy-distance positivity and separation](CKSD/Geometry/Kernels/Characteristic.lean#L69) (GAPS 108.62).
- [Distance-covariance positivity and independence criterion](CKSD/Geometry/Kernels/Characteristic.lean#L82) (GAPS 108.62).
- [Finite statistical minimax and a least-favourable prior](CKSD/Inference/Decision.lean#L59) (GAPS 101.32).
- [Hellinger posterior contraction under entropy and KL prior-mass bounds](CKSD/Bayes/PosteriorContraction.lean#L658) (GAPS 104.19).
- [Stochastic-interpolant score identity](CKSD/Bayes/Diffusion/Models.lean#L475) (GAPS 104.76).
- [Finite Gaussian-mixture identifiability up to relabeling](CKSD/LinearModels/Mixtures.lean#L104) (GAPS 105.6).
- [Canonical GLM chi-squared deviance limit](CKSD/LinearModels/GLM/Asymptotics.lean#L784) (GAPS 105.3).
- [Characteristic translation-invariant kernels and full spectral support](CKSD/Geometry/Kernels/Characteristic.lean#L124) (GAPS 108.68).
- [Gaussian likelihood minimum](CKSD/LinearModels/Multivariate/NormalSample.lean#L394) and [uniqueness](CKSD/LinearModels/Multivariate/NormalSample.lean#L404) (GAPS 105.28).
- [Invariance of the kinetic Gibbs law against smooth compactly supported tests](CKSD/Bayes/Langevin/Kinetic.lean#L280) (GAPS 104.48).
- [Exact noncentral F law for nested Gaussian projections](CKSD/LinearModels/FTest.lean#L98) and its [central case](CKSD/LinearModels/FTest.lean#L203) (GAPS 105.16).
- [Normalized factor-loading uniqueness up to column signs](CKSD/LinearModels/FactorAnalysis.lean#L101) (GAPS 105.35).
- [Projected empirical-mean central limit theorem](CKSD/Geometry/GeometricStatistics.lean#L473) (GAPS 108.10).
- [Finite-rank degenerate U-statistic Gaussian-chaos limit](CKSD/Asymptotics/UStatistics/Limits.lean#L756) (GAPS 102.30).
- [Mean-square stability of optimal transport maps](CKSD/Geometry/Transport/OptimalMapStability.lean#L258) (GAPS 108.42).
- [Order-two Hoeffding decomposition and exact variance](CKSD/Asymptotics/UStatistics/Limits.lean#L534) (GAPS 102.29).
- [Gaussian Bures formula with singular covariances](CKSD/Geometry/Transport/Gaussian.lean#L103) (GAPS 108.46).

The general [Euclidean central limit theorem](CKSD/Asymptotics/MultivariateCLT.lean) permits
singular covariance matrices and almost-everywhere measurable IID observations. Convergence in distribution, convergence in probability and weak convergence of laws are
Mathlib's `TendstoInDistribution`, `TendstoInMeasure` and convergence in the topology of
`ProbabilityMeasure`; variances, covariances and distribution functions are Mathlib's `Var[·]`,
`cov[·, ·]` and `ProbabilityTheory.cdf`. The [asymptotic foundations](CKSD/Asymptotics/Basic.lean)
supply Slutsky's lemma, tightness, the delta method and the IID central-limit adapter, and
[boundedness in probability](CKSD/Inference/Basic.lean#L145) is equivalent to Mathlib's
`IsTightMeasureSet` for the laws.

The [Poincaré inequality under bounded perturbation](CKSD/Bayes/FunctionalInequalities.lean#L486)
and the [stochastic-approximation equilibrium corollary](CKSD/Bayes/StochasticApproximation.lean#L636)
have complete proofs with no admitted dependencies.

## Mathematical domains and conventions

- Test functions in weak formulations of Fokker–Planck and kinetic equations, and smoothness hypotheses on potentials and densities, are `ContDiff ℝ ∞` (infinitely differentiable). In Mathlib `ContDiff ℝ ⊤` means analytic, and an analytic function with compact support on a Euclidean space of positive dimension vanishes.
- [Particle likelihood asymptotic variance](CKSD/Bayes/Particle/LimitCore.lean#L74) sums the centred second-moment ratios, with the subtraction of one inside each summand. The time-zero identity and the zero-variance identity for unit potentials are proved. The particle central limit theorems and the uniform-in-time particle error bound are proved. Their catalogue source is [SYNOPSIS104](SYNOPSIS104.md), items 59–60.
- [Threshold-excess discrepancy](CKSD/Processes/ExtremeValueLimits.lean#L69) takes its supremum over every nonnegative excess, including points at and beyond a terminal atom. The generalized Pareto distribution function is extended across its endpoint. The domain-of-attraction equivalence remains admitted; see [SYNOPSIS106](SYNOPSIS106.md), item 47.
- [Offset deformation retraction](CKSD/Geometry/Persistence/TopologicalInference.lean#L82) requires a finite nonempty sample on the manifold. This excludes the empty/nonempty real-Hausdorff-distance degeneracy. The retraction theorem remains admitted; see [SYNOPSIS108](SYNOPSIS108.md), item 22.
- [Offset homology inference](CKSD/Geometry/Persistence/TopologicalInference.lean#L194) uses closed offsets (`cthickening`). With `d_H(K, P) = ε` for a compact `K` and a finite `P`, the closed interleavings `K^a ⊆ P^{a+ε}` and `P^a ⊆ K^{a+ε}` hold, so the boundary case `j = i + 2ε` of [SYNOPSIS108](SYNOPSIS108.md), item 37, is included. The theorem remains admitted.
- [Regular transport potentials](CKSD/Geometry/Transport/Rates.lean#L98) have ambient twice continuous differentiability at every point of the closed conjugacy ball and Hessian bounds there. Both statistical map-rate statements require the source to be supported in a smaller concentric closed ball of radius `r < 1`; constants may depend on the interior margin. This controls gradients where risk is evaluated and prevents constrained-conjugacy boundary ties. Both rate statements remain admitted; see [SYNOPSIS108](SYNOPSIS108.md), item 53.
- [Gaussian SEM equivalence](CKSD/LinearModels/Causal/StructuralEquations.lean#L364) compares representations faithful to their respective graphs. Nonzero edge coefficients alone do not supply faithfulness. The theorem remains admitted; see [SYNOPSIS105](SYNOPSIS105.md), item 71.
- [Active paths](CKSD/LinearModels/DirectedGraphical/Basic/CausalGraph.lean#L94) constrain only interior vertices, and [d-separation](CKSD/LinearModels/DirectedGraphical/Basic/CausalGraph.lean#L109) does not require disjoint vertex sets. For an endpoint `a ∈ Z`, the paths active given `Z` are those active given `(Z \ {a}) ∪ {a'}` after adding a leaf `a → a'`. Such leaves preserve skeletons and unshielded colliders, so Markov equivalence over all triples agrees with the classical notion over disjoint triples (SYNOPSIS105, item 67).
- [Bayes rules](CKSD/Inference/Model.lean#L113) have integrable risk and are compared with rules of integrable risk; [minimax rules](CKSD/Inference/Model.lean#L120) have risk bounded above and are compared with rules of bounded risk. Totalized integrals and real suprema therefore cannot assign the value `0` to a non-integrable or unbounded risk.
- [Characteristic kernels](CKSD/Geometry/Basic.lean#L133) quantify over probability laws against which the kernel is integrable, so the Bochner convention cannot make the squared MMD vanish for the wrong reason. The [squared MMD](CKSD/Geometry/Kernels/Distance.lean#L278) equals the squared distance of TauCeti kernel mean embeddings.
- [Compositional-class minimax risk](CKSD/Learning/Networks.lean#L651) and the [Eldan–Shamir depth separation](CKSD/Learning/Networks.lean#L596) use extended nonnegative integrals. Infinite squared loss is allowed and cannot become zero through the nonintegrable Bochner-integral convention. Both lower bounds remain admitted; see [SYNOPSIS107](SYNOPSIS107.md), items 29 and 37.
- [LinUCB regret](CKSD/Learning/Bandits/Stochastic.lean#L759) uses the scale `max σ (B * W)` with the stated positive parameters and ridge regularization. It accounts for initial exploration even with arbitrarily small noise. The statistical confidence and regret theorems remain admitted; see [SYNOPSIS107](SYNOPSIS107.md), item 63.
- [Stochastic little-o](CKSD/Asymptotics/Basic.lean#L148) and [stochastic big-O](CKSD/Asymptotics/Basic.lean#L154) require an eventually positive deterministic scale. In particular, an identically zero scale cannot satisfy either predicate.
- The [ULA bound under a logarithmic Sobolev inequality](CKSD/Bayes/Langevin/Sampling.lean#L122) uses Vempala and Wibisono's step-size range `h ≤ α/(4β²)` (SYNOPSIS104, item 45).
- The [Grenander limit law](CKSD/Nonparametric/Density/Grenander.lean#L877) assumes a density vanishing on the negative half-line and nonincreasing on `[0, ∞)`; positivity at `x₀` follows from `f'(x₀) < 0` (SYNOPSIS103, item 11).

The corresponding SYNOPSIS statements are the mathematical source for GAPS and STRUCTURE.
Their domains and risk conventions agree across these files. The pinned-library coverage rule
is unchanged: 537 synopsis entries comprise 5 covered, 55 partly covered, and 477 not covered;
296 selected gap families and 110 easy entries, with 53 Scope paragraphs, retain their meanings.
Local CKSD results do not change the coverage classifications of the pinned dependencies.

## Cross-fitting

The [cross-fitted missing-mean statement](CKSD/Asymptotics/CrossFitting.lean#L383)
uses a fixed finite number of folds and requires a common positive lower bound on fold
proportions only for sufficiently large sample sizes:

```lean
∀ᶠ n in atTop, ∀ k,
  c * n ≤ (Finset.univ.filter fun i ↦ (split n).fold i = k).card
```

A condition imposed at every sample size would, at `n = 1`, require every fold to contain at
least one observation. A partition of a singleton has at most one nonempty fold, so that
condition permits only one fold. The eventual condition permits ordinary cross-fitting.
Training excludes the evaluation fold, and the stated nuisance-error and score conditions
remain essential. The asymptotic linearity theorem itself remains admitted.

## Hypotheses and generality

Hypotheses implied by the others are omitted, both in proved theorems and in admitted ones,
where the implication is checked mathematically. Typical omitted hypotheses are integrability
forced by a normalization `∫ f = 1` or `∫ ε² = 1`, positivity facts implied by the existence
of an index or by an eigen-equation, a standard Borel structure implied by Polish and Borel
instances, and probability of a limit law implied by weak convergence. Repeated hypothesis
blocks are bundled as structures, for example `IsRobbinsMonroScheme`, `IsIIDNoise`,
`IsRandomCensoringModel` and `IsPositiveSemidefiniteSequence`, and weak stationarity is the single
predicate `IsWeaklyStationary`.

Finite index sets are arbitrary `Fintype` types and Euclidean spaces are general real inner
product spaces wherever the arguments allow; examples include exponential families, PCA,
covariance thresholding, Metropolis–Hastings chains, Kalman models, Cox models, graphical
models, Markov decision processes, Wasserstein barycenters and manifold-learning maps. Statements
that remain on `ℝ^d` or `Fin n` follow their sources or depend on interfaces, such as
`multivariateGaussian`, that are stated for `EuclideanSpace`.

## Module organization

Each section has an entry module (`CKSD/Inference.lean`, …, `CKSD/Geometry.lean`) whose
docstring lists its components. The dependency order is Inference → Asymptotics →
Nonparametric → Bayes, LinearModels, Processes → Learning, Geometry; Inference does not import
Asymptotics. Among the statistics sections 101–106, a module may import any module of
Inference, but from Asymptotics, Nonparametric, Bayes, LinearModels or Processes only a
`Basic` module; `scripts/check_imports.py` checks this rule. Focused components include:

- [Nonparametric/EmpiricalCovariance/Basic.lean](CKSD/Nonparametric/EmpiricalCovariance/Basic.lean): shared covariance moments, fluctuations, and centered quadratic statistics; [LinearModels/Multivariate/CovarianceEigenvalues.lean](CKSD/LinearModels/Multivariate/CovarianceEigenvalues.lean) combines them with population-gap perturbation estimates at any simple ordered eigenvalue.
- [Bayes/StochasticApproximation/Path.lean](CKSD/Bayes/StochasticApproximation/Path.lean) and [Bayes/MartingaleSeries.lean](CKSD/Bayes/MartingaleSeries.lean): deterministic interpolation estimates and almost-sure convergence of localized martingale noise; [Bayes/MeanField/Coupling.lean](CKSD/Bayes/MeanField/Coupling.lean), [Bayes/MeanField/Path/Map.lean](CKSD/Bayes/MeanField/Path/Map.lean), and the mean-field fluctuation modules supply synchronous coupling and independent nonlinear comparison processes.
- [Geometry/Kernels/EnergyDistance.lean](CKSD/Geometry/Kernels/EnergyDistance.lean), [Geometry/Kernels/Distance.lean](CKSD/Geometry/Kernels/Distance.lean), [Geometry/Kernels/DistanceProductSeparation.lean](CKSD/Geometry/Kernels/DistanceProductSeparation.lean), and [Geometry/Kernels/DistanceCovarianceCentering.lean](CKSD/Geometry/Kernels/DistanceCovarianceCentering.lean): CDF and projection formulas, distance-kernel positivity, fixed-marginal separation, and double-centering identities.
- [Inference/NeymanPearson.lean](CKSD/Inference/NeymanPearson.lean): the generalized Neyman–Pearson lemma, threshold tests and monotone likelihood ratios, used by the testing modules.
- [Inference/Density.lean](CKSD/Inference/Density.lean): the common density API, including `CKSD.map_withDensity_comp` and `HasDensity.integral_eq_one`.
- [Asymptotics/Basic.lean](CKSD/Asymptotics/Basic.lean): Slutsky's lemma, tightness, the delta method, stochastic algebra and the IID central-limit adapter; [Asymptotics/LAN/Basic.lean](CKSD/Asymptotics/LAN/Basic.lean): local experiments, local asymptotic normality and regular estimators, with the representation and convolution theorems in [Asymptotics/LAN/Representation.lean](CKSD/Asymptotics/LAN/Representation.lean); M-, Z- and maximum-likelihood estimation is in `CKSD/Asymptotics/MEstimation/`, U-statistics in `CKSD/Asymptotics/UStatistics/`.
- [LinearModels/DirectedGraphical.lean](CKSD/LinearModels/DirectedGraphical.lean): finite graphical-law foundations, interventions, Markov theory, do-calculus and discovery, with the causal-graph core (directed acyclic graphs, active trails, d-separation) in [LinearModels/DirectedGraphical/Basic.lean](CKSD/LinearModels/DirectedGraphical/Basic.lean); [LinearModels/SurveySampling.lean](CKSD/LinearModels/SurveySampling.lean) holds design-based survey sampling.
- [Bayes/Diffusion/Basic.lean](CKSD/Bayes/Diffusion/Basic.lean) and [Bayes/Particle/Filter.lean](CKSD/Bayes/Particle/Filter.lean): diffusion generators and discretizations, and Feynman–Kac particle approximations.
- [Learning/Generalization.lean](CKSD/Learning/Generalization.lean): concentration/Rademacher estimates, contraction, exponential weights, conformal ranks, classification and stability; [Learning/Reinforcement/MarkovDecision.lean](CKSD/Learning/Reinforcement/MarkovDecision.lean) holds Bellman operators and temporal-difference learning.
- [Learning/Privacy.lean](CKSD/Learning/Privacy.lean): differential-privacy basics, mechanisms, central lower bounds and local privacy.
- [Geometry/MatrixReduction.lean](CKSD/Geometry/MatrixReduction.lean): reduction foundations, homology and barcode rank formulas.
- [Geometry/SimplicialPersistence.lean](CKSD/Geometry/SimplicialPersistence.lean): chains, sublevel diagrams, bottleneck stability and Wasserstein stability, using shared diagram metrics and finite combinatorics.
- [Nonparametric/LowerBounds.lean](CKSD/Nonparametric/LowerBounds.lean): testing, packing and Gaussian lower bounds; sparse recovery is in `CKSD/Nonparametric/SparseRecovery/` and covariance thresholding in `CKSD/Nonparametric/HighDimensional/`.
- [Processes/Kalman.lean](CKSD/Processes/Kalman.lean): model, covariance/error recursions and Gaussian filter laws. Generic block-independence and random-index tools are in [Processes/Independence.lean](CKSD/Processes/Independence.lean), and Wald's fundamental identity is in [Processes/WaldIdentity.lean](CKSD/Processes/WaldIdentity.lean).
- [Processes/TimeSeries.lean](CKSD/Processes/TimeSeries.lean): Wold decomposition, martingale and Bartlett central limit theorems, long-run variance, stationary Gaussian construction and GARCH series.

Upstream definitions are used directly where they agree with the statistical object, with
small bridge lemmas where CKSD keeps a statistical adapter: Mathlib `Measure.conv`,
`TendstoInMeasure`, `tvDist`, `Matrix.rowStochastic`, `bernoulliMeasure`, `poissonMeasure`,
`HolderWith`, `hammingDist`, `Maximal` and `Set.projIcc`; TauCeti `uniformMeasure`, `quantile`,
`covMatrix` and kernel mean embeddings; and Statlib `klBerReal`. Conventions and source
provenance are in [CREDITS.md](CREDITS.md). Broader convergence interoperability must preserve
the project's outer/nonseparable scope; an indiscriminate replacement by a separability-restricted
theorem would lose generality.

## Remaining Mathlib-review concerns

The principal remaining requirement is full proofs of the admitted results. Substantive
statistical hypotheses and constants still need proof-level validation; compilation of an
admission is not evidence of mathematical correctness.

The 89 direct admissions comprise 22 in Learning, 14 in Geometry, 14 in Nonparametric,
12 in Bayes, 10 in Processes, 9 in Asymptotics, 5 in LinearModels, and
3 in Inference. Sections 101–106 contain 53 admissions. There are no theorem
proofs conditional on admitted dependencies.

The Bayesian admissions concern diffusion identities and marginal laws, entropy bounds for
Langevin discretizations, Metropolis-adjusted Langevin mixing, hypocoercivity, and transport
and gradient-flow inequalities. Other recurring themes are nonregular
and resampling asymptotics, nonparametric shape constraints and random-matrix limits, statistical
learning rates, and geometric regularity and topological inference.

- The two semiparametric efficiency statements require a common sigma-finite dominating
  measure. With uncountable counting measure, atomless path laws can have chosen
  Radon–Nikodym derivative zero, making the bare QMD remainder vacuous. Generic
  reference-measure obstruction lemmas are proved; both efficiency statements remain admitted.
- The probability-flow statement in `CKSD/Bayes/Diffusion/Models.lean` uses continuous
  trajectories in addition to right derivatives. A fixed-time jump can have zero right
  derivative everywhere. The prescribed-marginal diffusion statement uses joint drift
  measurability on the time interval and pathwise interval integrability. These guards
  give the intended ODE/SDE meaning; the marginal identification proofs remain admitted.
- Several long proofs have natural factoring opportunities: the Grenander maximum-likelihood characterization, Wald's fundamental identity, Exp3 regret, the Kalman filter laws, rule three of the do-calculus, the sublevel-diagram construction and the ordered Wasserstein stability step, and the Laplace approximation. Some repeated proof steps remain in the persistence modules (discordant pairs, `U`/`V`-symmetric interleaving blocks) and in the private-estimation variance computations.
- Some admitted statements remain conjunctions or carry `let` bindings in their statements, because a split would multiply admissions; these should be split as they are proved. A few helper names (`hedge_regret_le`, `surrogate_minimizer_sign_of_convex`, `bayesRisk_le_nnRisk_le`) and ASCII Greek identifiers (`mu`, `theta`, …) in Inference and Asymptotics do not yet follow Mathlib conventions.
- Parallel constructions without bridge lemmas remain for sublevel chains versus filtered boundary matrices, and for the Bayes classification risk versus the risk of the plug-in rule. `CausalGraph` is a local directed-acyclic-graph structure, not Mathlib's `Digraph`.
- General lemmas used by one application (concave chord inequalities in the Grenander module, Kolmogorov's maximal inequality for independent sums) would belong in a shared helper module or upstream.
- `DenseNetParams` still indexes hidden weights by all natural-number layers. A finite parameter type or an explicit restriction/quotient would support future parameter-space measurability and derivatives.
- Real Hellinger and density adapters document their valid finite-divergence/absolute-continuity domain. Use those guards when deriving distance/density interpretations; the definitions themselves remain totalized.
- Copyright, authorship and licensing need a deliberate project decision before upstream submission. No authors or license are inferred.

The [Mathlib naming](https://leanprover-community.github.io/contribute/naming.html),
[style](https://leanprover-community.github.io/contribute/style.html), and
[documentation](https://mathlib.org/contribute/doc.html) guides provide the upstream conventions.
Project-specific namespace and module requirements remain authoritative.

## Proof-source support

[proof_sources.json](proof_sources.json) identifies local PDF proof passages by filename,
checksum, printed page and physical PDF page. Each target records a paraphrased argument,
comparison with the Lean hypotheses, and the remaining formal prerequisites. A source proof
outline, a deferred exercise, and a completed Lean proof have distinct roles in this index.

The Gaussian block-independence likelihood-ratio proof uses Muirhead's determinant tilt and
Beta-product law, together with local Gamma cancellation and the logarithmic Beta-product limit.
The ULA Wasserstein proof combines the sampling reference's coupling argument with an
invariant Hamiltonian comparison trajectory, retaining arbitrary initial probability laws.
The uniform particle moment proof uses Del Moral's normalized telescoping and mixing argument,
conditional empirical moments, and geometric summation for every real moment order at least one.
The mean-field training limit uses bounded Lipschitz characteristic representation proved by
backward transport tests. Comparison-curve moments are derived from continuity-equation action,
and the empirical limit does not require measurability of the supplied particle paths.
The LAN representation theorem combines joint-limit extraction, likelihood transfer and a
common conditional-kernel construction for tilted joint laws. The proof allows varying sample
spaces and arbitrary nonempty Polish Borel outputs, and controls singular alternatives without
assuming finite-sample absolute continuity. Gaussian tilting also gives completeness of the
Gaussian location family.
Hájek's convolution theorem identifies a regular estimator's limit law as a Gaussian
convolved with an independent residual law. Gaussian completeness identifies the kernel
almost everywhere; translation invariance makes its residual law constant almost everywhere.
Gaussian Anderson concentration and the associated risk comparisons for measurable symmetric
bowl-shaped losses allow singular covariance and infinite loss. The separate local asymptotic
minimax theorem for arbitrary estimator sequences remains admitted.
Every positive discrete JKO step has a unique minimizer for a continuous nonnegative potential.
Gaussian entropy compensation supplies the Euclidean direct method, and strict convexity along
ordinary mixtures gives uniqueness without convexity of the potential. The continuous-time
convergence and strong space-time L1 conclusion remain admitted.

Blackwell comparison for finite parameter sets is proved by exact finite-action simulation,
compact likelihood-vector approximation and standard-Borel disintegration. The source space
remains arbitrary measurable. The MALA lower-bound declaration permits the curvature scale
to depend on the step size and accuracy; its Gaussian construction does not establish the
normalized-curvature minimax lower bound from the reference. The Wasserstein barycenter
first variation permits arbitrary measurable square-integrable displacement fields.

The proof-source index covers every remaining admitted statement across Sections 101–108.
Its 49 local PDFs have exact page locators and checksums; worked proofs, outlines, statements,
source-hypothesis mismatches and unavailable primary papers are distinguished explicitly.

## Validation

The ordinary full build completes successfully with 11927 jobs. The remaining admitted
declarations generate expected warnings. All 365 individual Lean files pass strict checks (364 in the broad check and the later
transport module checked separately). The inventory
checker `scripts/check_formalization.py` audits compiled axiom dependencies, docstring adjacency and source hashes. Individual module checks
(`scripts/check_lean_files.py`) use both `autoImplicit=false` and `relaxedAutoImplicit=false`
after building their imports. These checks do not turn the remaining statistical admissions
into proofs.
