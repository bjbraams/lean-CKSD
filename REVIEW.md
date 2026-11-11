# Mathlib-style assessment of CKSD

The project contains 301 Lean modules under `CKSD/` and 3085 inventoried declarations:
824 definitions, abbreviations, structures and inductive types, and 2261 theorem statements
(2164 proved, no conditional results, and 97 admitted). The largest module is
[GLMAsymptotics.lean](CKSD/LinearModels/GLMAsymptotics.lean) at 1070 lines, below the
1500-line hard limit. Modules near 1000 lines are candidates for splitting at a natural mathematical seam. All modules use
the module system and have Mathlib-style module documentation with the mathematical scope, main definitions and main results. All authored definitions, abbreviations,
structures, inductive types and theorem statements have formal docstrings, as do all 136 structure
fields. Theorem docstrings state the mathematics together with the `GAPS ddd.k` tag of the
catalogue entry they formalize.

The dependency baseline is Lean `v4.36.0-rc2`, Mathlib
`6135ffb78e8bcd3fcc8ec02f3f82ea0b0737358b`, TauCeti
`afa08a3ed16fb167e35de371afb1eb03fbc5913a`, and Statlib
`eeaac0283690efaa60c31115400cf561836baeb9`. Namespace and build conventions are in
[AGENTS.md](AGENTS.md). Declaration statuses and source locations are in
[FORMALIZATION.md](FORMALIZATION.md); this assessment does not certify the truth of admissions.

## Proved statistical foundations

The following scoped catalogue statements have complete proofs with no admitted dependencies:

- [Gaussian block-independence likelihood-ratio chi-squared limit](CKSD/LinearModels/MultivariateTests.lean#L304) (GAPS 105.33).
- [Benaïm stochastic-approximation limit-set theorem](CKSD/Bayes/StochasticApproximation.lean#L597) (GAPS 104.49).
- [Bounded-perturbation logarithmic Sobolev inequality](CKSD/Bayes/FunctionalInequalities.lean#L475) (GAPS 104.44).
- [McKean–Vlasov and finite-particle well-posedness](CKSD/Bayes/MeanField.lean#L88) (GAPS 104.51).
- [General propagation of chaos on continuous path spaces](CKSD/Bayes/MeanField.lean#L118) (GAPS 104.51).
- [Exact Wilks determinant-ratio Beta-product law](CKSD/LinearModels/MultivariateTests.lean#L103) (GAPS 105.23).
- [Gaussian sphericity likelihood-ratio chi-squared limit](CKSD/LinearModels/MultivariateTests.lean#L232) (GAPS 105.33).
- [Stochastic-approximation asymptotic pseudotrajectory](CKSD/Bayes/StochasticApproximation.lean#L638) (GAPS 104.49).
- [Quantitative synchronous propagation of chaos](CKSD/Bayes/MeanField.lean#L506) (GAPS 104.56).
- [Gaussian simple covariance-eigenvalue central limit theorem](CKSD/LinearModels/MultivariateTests.lean#L175) (GAPS 105.24).
- [Energy-distance positivity and separation](CKSD/Geometry/Kernels.lean#L696) (GAPS 108.62).
- [Distance-covariance positivity and independence criterion](CKSD/Geometry/Kernels.lean#L710) (GAPS 108.62).
- [Finite statistical minimax and a least-favourable prior](CKSD/Inference/Decision.lean#L54) (GAPS 101.32).
- [Hellinger posterior contraction under entropy and KL prior-mass bounds](CKSD/Bayes/PosteriorContraction.lean#L639) (GAPS 104.19).
- [Stochastic-interpolant score identity](CKSD/Bayes/DiffusionModels.lean#L464) (GAPS 104.76).
- [Finite Gaussian-mixture identifiability up to relabeling](CKSD/LinearModels/Mixtures.lean#L103) (GAPS 105.6).
- [Canonical GLM chi-squared deviance limit](CKSD/LinearModels/GLMAsymptotics.lean#L897) (GAPS 105.3).
- [Characteristic translation-invariant kernels and full spectral support](CKSD/Geometry/Kernels.lean#L754) (GAPS 108.68).
- [Gaussian likelihood minimum](CKSD/LinearModels/Multivariate.lean#L396) and [uniqueness](CKSD/LinearModels/Multivariate.lean#L406) (GAPS 105.28).
- [Invariance of the kinetic Gibbs law against smooth compactly supported tests](CKSD/Bayes/KineticLangevin.lean#L276) (GAPS 104.48).
- [Exact noncentral F law for nested Gaussian projections](CKSD/LinearModels/FTest.lean#L97) and its [central case](CKSD/LinearModels/FTest.lean#L206) (GAPS 105.16).
- [Normalized factor-loading uniqueness up to column signs](CKSD/LinearModels/FactorAnalysis.lean#L101) (GAPS 105.35).
- [Projected empirical-mean central limit theorem](CKSD/Geometry/GeometricStatistics.lean#L454) (GAPS 108.10).
- [Finite-rank degenerate U-statistic Gaussian-chaos limit](CKSD/Asymptotics/UStatistics.lean#L757) (GAPS 102.30).
- [Mean-square stability of optimal transport maps](CKSD/Geometry/OptimalMapStability.lean#L239) (GAPS 108.42).
- [Order-two Hoeffding decomposition and exact variance](CKSD/Asymptotics/UStatistics.lean#L534) (GAPS 102.29).
- [Gaussian Bures formula with singular covariances](CKSD/Geometry/GaussianTransport.lean#L103) (GAPS 108.46).

The general [Euclidean central limit theorem](CKSD/Asymptotics/MultivariateCLT.lean) permits
singular covariance matrices and almost-everywhere measurable IID observations. Convergence in distribution, convergence in probability and weak convergence of laws are
Mathlib's `TendstoInDistribution`, `TendstoInMeasure` and convergence in the topology of
`ProbabilityMeasure`; variances, covariances and distribution functions are Mathlib's `Var[·]`,
`cov[·, ·]` and `ProbabilityTheory.cdf`. The [asymptotic foundations](CKSD/Asymptotics/Basic.lean)
supply Slutsky's lemma, tightness, the delta method and the IID central-limit adapter, and
[boundedness in probability](CKSD/Inference/Basic.lean#L138) is equivalent to Mathlib's
`IsTightMeasureSet` for the laws.

The [Poincaré inequality under bounded perturbation](CKSD/Bayes/FunctionalInequalities.lean#L492)
and the [stochastic-approximation equilibrium corollary](CKSD/Bayes/StochasticApproximation.lean#L623)
have complete proofs with no admitted dependencies.

## Mathematical domains and conventions

- Test functions in weak formulations of Fokker–Planck and kinetic equations, and smoothness hypotheses on potentials and densities, are `ContDiff ℝ ∞` (infinitely differentiable). In Mathlib `ContDiff ℝ ⊤` means analytic, and an analytic function with compact support on a Euclidean space of positive dimension vanishes.
- [Particle likelihood asymptotic variance](CKSD/Bayes/ParticleLimits.lean#L64) sums the centred second-moment ratios, with the subtraction of one inside each summand. The time-zero identity and the zero-variance identity for unit potentials are proved. The particle central limit theorems are proved; the uniform-in-time particle error bound remains admitted. Their catalogue source is [SYNOPSIS104](SYNOPSIS104.md), item 59.
- [Threshold-excess discrepancy](CKSD/Processes/ExtremeValueLimits.lean#L67) takes its supremum over every nonnegative excess, including points at and beyond a terminal atom. The generalized Pareto distribution function is extended across its endpoint. The domain-of-attraction equivalence remains admitted; see [SYNOPSIS106](SYNOPSIS106.md), item 47.
- [Offset deformation retraction](CKSD/Geometry/TopologicalInference.lean#L95) requires a finite nonempty sample on the manifold. This excludes the empty/nonempty real-Hausdorff-distance degeneracy. The retraction theorem remains admitted; see [SYNOPSIS108](SYNOPSIS108.md), item 22.
- [Offset homology inference](CKSD/Geometry/TopologicalInference.lean#L205) uses closed offsets (`cthickening`). With `d_H(K, P) = ε` for a compact `K` and a finite `P`, the closed interleavings `K^a ⊆ P^{a+ε}` and `P^a ⊆ K^{a+ε}` hold, so the boundary case `j = i + 2ε` of [SYNOPSIS108](SYNOPSIS108.md), item 37, is included. The theorem remains admitted.
- [Regular transport potentials](CKSD/Geometry/TransportRates.lean#L90) have ambient twice continuous differentiability at every point of the closed conjugacy ball and Hessian bounds there. Both statistical map-rate statements require the source to be supported in a smaller concentric closed ball of radius `r < 1`; constants may depend on the interior margin. This controls gradients where risk is evaluated and prevents constrained-conjugacy boundary ties. Both rate statements remain admitted; see [SYNOPSIS108](SYNOPSIS108.md), item 53.
- [Gaussian SEM equivalence](CKSD/LinearModels/StructuralEquations.lean#L365) compares representations faithful to their respective graphs. Nonzero edge coefficients alone do not supply faithfulness. The theorem remains admitted; see [SYNOPSIS105](SYNOPSIS105.md), item 71.
- [Active paths](CKSD/LinearModels/DirectedGraphical/Basic/CausalGraph.lean#L82) constrain only interior vertices, and [d-separation](CKSD/LinearModels/DirectedGraphical/Basic/CausalGraph.lean#L97) does not require disjoint vertex sets. For an endpoint `a ∈ Z`, the paths active given `Z` are those active given `(Z \ {a}) ∪ {a'}` after adding a leaf `a → a'`. Such leaves preserve skeletons and unshielded colliders, so Markov equivalence over all triples agrees with the classical notion over disjoint triples (SYNOPSIS105, item 67).
- [Bayes rules](CKSD/Inference/Model.lean#L101) have integrable risk and are compared with rules of integrable risk; [minimax rules](CKSD/Inference/Model.lean#L108) have risk bounded above and are compared with rules of bounded risk. Totalized integrals and real suprema therefore cannot assign the value `0` to a non-integrable or unbounded risk.
- [Characteristic kernels](CKSD/Geometry/Basic.lean#L103) quantify over probability laws against which the kernel is integrable, so the Bochner convention cannot make the squared MMD vanish for the wrong reason. The [squared MMD](CKSD/Geometry/DistanceKernel.lean#L256) equals the squared distance of TauCeti kernel mean embeddings.
- [Compositional-class minimax risk](CKSD/Learning/Networks.lean#L652) and the [Eldan–Shamir depth separation](CKSD/Learning/Networks.lean#L597) use extended nonnegative integrals. Infinite squared loss is allowed and cannot become zero through the nonintegrable Bochner-integral convention. Both lower bounds remain admitted; see [SYNOPSIS107](SYNOPSIS107.md), items 29 and 37.
- [LinUCB regret](CKSD/Learning/Bandits.lean#L761) uses the scale `max σ (B * W)` with the stated positive parameters and ridge regularization. It accounts for initial exploration even with arbitrarily small noise. The statistical confidence and regret theorems remain admitted; see [SYNOPSIS107](SYNOPSIS107.md), item 63.
- [Stochastic little-o](CKSD/Asymptotics/Framework.lean#L79) and [stochastic big-O](CKSD/Asymptotics/Framework.lean#L85) require an eventually positive deterministic scale. In particular, an identically zero scale cannot satisfy either predicate.
- The [ULA bound under a logarithmic Sobolev inequality](CKSD/Bayes/LangevinSampling.lean#L125) uses Vempala and Wibisono's step-size range `h ≤ α/(4β²)` (SYNOPSIS104, item 45).
- The [Grenander limit law](CKSD/Nonparametric/Grenander.lean#L825) assumes a density vanishing on the negative half-line and nonincreasing on `[0, ∞)`; positivity at `x₀` follows from `f'(x₀) < 0` (SYNOPSIS103, item 11).

The corresponding SYNOPSIS statements are the mathematical source for GAPS and STRUCTURE.
Their domains and risk conventions agree across these files. The pinned-library coverage rule
is unchanged: 537 synopsis entries comprise 5 covered, 55 partly covered, and 477 not covered;
296 selected gap families and 110 easy entries, with 53 Scope paragraphs, retain their meanings.
Local CKSD results do not change the coverage classifications of the pinned dependencies.

## Cross-fitting

The [cross-fitted missing-mean statement](CKSD/Asymptotics/CrossFitting.lean#L918)
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

- [Nonparametric/EmpiricalCovariance/Basic.lean](CKSD/Nonparametric/EmpiricalCovariance/Basic.lean): shared covariance moments, fluctuations, and centered quadratic statistics; [LinearModels/CovarianceEigenvalues.lean](CKSD/LinearModels/CovarianceEigenvalues.lean) combines them with population-gap perturbation estimates at any simple ordered eigenvalue.
- [Bayes/StochasticApproximationPath.lean](CKSD/Bayes/StochasticApproximationPath.lean) and [MartingaleSeries.lean](CKSD/Bayes/MartingaleSeries.lean): deterministic interpolation estimates and almost-sure convergence of localized martingale noise; [MeanFieldCoupling.lean](CKSD/Bayes/MeanFieldCoupling.lean), [MeanFieldPathMap.lean](CKSD/Bayes/MeanFieldPathMap.lean), and the mean-field fluctuation modules supply synchronous coupling and independent nonlinear comparison processes.
- [Geometry/EnergyDistance.lean](CKSD/Geometry/EnergyDistance.lean), [DistanceKernel.lean](CKSD/Geometry/DistanceKernel.lean), [DistanceProductSeparation.lean](CKSD/Geometry/DistanceProductSeparation.lean), and [DistanceCovarianceCentering.lean](CKSD/Geometry/DistanceCovarianceCentering.lean): CDF and projection formulas, distance-kernel positivity, fixed-marginal separation, and double-centering identities.
- [Inference/NeymanPearson.lean](CKSD/Inference/NeymanPearson.lean): the generalized Neyman–Pearson lemma, threshold tests and monotone likelihood ratios, used by the testing modules.
- [Inference/Density.lean](CKSD/Inference/Density.lean): the common density API, including `CKSD.map_withDensity_comp` and `HasDensity.integral_eq_one`.
- [Asymptotics/Basic.lean](CKSD/Asymptotics/Basic.lean): Slutsky's lemma, tightness, the delta method, stochastic algebra and the IID central-limit adapter; [Asymptotics/Estimators.lean](CKSD/Asymptotics/Estimators.lean): likelihood support, maximum likelihood, quantiles, Z-estimators and U-statistics.
- [LinearModels/DirectedGraphical.lean](CKSD/LinearModels/DirectedGraphical.lean): finite graphical-law foundations, interventions, Markov theory, do-calculus and discovery, with the causal-graph core (directed acyclic graphs, active trails, d-separation) in [DirectedGraphical/Basic.lean](CKSD/LinearModels/DirectedGraphical/Basic.lean); [SurveySampling.lean](CKSD/LinearModels/SurveySampling.lean) holds design-based survey sampling.
- [Bayes/Diffusion.lean](CKSD/Bayes/Diffusion.lean) and [Bayes/ParticleFilter.lean](CKSD/Bayes/ParticleFilter.lean): diffusion generators and discretizations, and Feynman–Kac particle approximations.
- [Learning/Generalization.lean](CKSD/Learning/Generalization.lean): concentration/Rademacher estimates, contraction, exponential weights, conformal ranks, classification and stability; [Learning/MarkovDecision.lean](CKSD/Learning/MarkovDecision.lean) holds Bellman operators and temporal-difference learning.
- [Learning/PrivateEstimation.lean](CKSD/Learning/PrivateEstimation.lean): mechanisms, central lower bounds and local privacy.
- [Geometry/MatrixReduction.lean](CKSD/Geometry/MatrixReduction.lean): reduction foundations, homology and barcode rank formulas.
- [Geometry/SimplicialPersistence.lean](CKSD/Geometry/SimplicialPersistence.lean): chains, sublevel diagrams, bottleneck stability and Wasserstein stability, using shared diagram metrics and finite combinatorics.
- [Nonparametric/LowerBounds.lean](CKSD/Nonparametric/LowerBounds.lean): testing/packing lower bounds, restricted-isometry sparse recovery and covariance thresholding.
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

The 97 direct admissions comprise 22 in Learning, 16 in Bayes, 15 in Geometry,
14 in Nonparametric, 11 in Asymptotics, 10 in Processes, 5 in LinearModels, and
4 in Inference. Sections 101–106 contain 60 admissions. There are no theorem
proofs conditional on admitted dependencies.

The Bayesian admissions concern diffusion identities and marginal laws, Langevin discretization
and hypocoercivity, transport and gradient-flow inequalities, uniform-in-time particle-filter
error bounds, and the mean-field neural-network limit. Other recurring themes are nonregular
and resampling asymptotics, nonparametric shape constraints and random-matrix limits, statistical
learning rates, and geometric regularity and topological inference.

- `IsContiguous` is not yet reconciled with Statlib's contiguity predicates.
- The admitted marginal-preserving diffusion statement in `CKSD/Bayes/DiffusionModels.lean`
  requires a time-measurability review. Its weak Fokker–Planck predicate controls the
  time integrals of spatially averaged generators, while its path equation does not
  explicitly require interval integrability of the drift along paths. Uniform spatial
  Lipschitz continuity and finite integrated action alone do not provide that missing
  measurability. The totalized Bochner integral in the path equation therefore needs
  an additional guard before this statement can certify the intended diffusion law.
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
The LAN representation theorem has a proved common conditional-kernel construction for tilted
joint laws; joint-limit extraction and likelihood transfer remain necessary for the full theorem.

## Validation

The ordinary full build completes successfully with 11685 jobs and no warnings from CKSD files
other than admitted declarations. All 310 individual Lean file checks pass. The inventory
checker `scripts/check_formalization.py` audits compiled axiom dependencies, docstring adjacency and source hashes. Individual module checks
(`scripts/check_lean_files.py`) use both `autoImplicit=false` and `relaxedAutoImplicit=false`
after building their imports. These checks do not turn the remaining statistical admissions
into proofs.
