# Mathlib-style assessment of CKSD

The project contains 201 Lean modules under `CKSD/` and 2363 inventoried declarations:
762 definitions, abbreviations, structures and inductive types, and 1601 theorem statements
(1455 proved, two conditional on admitted results, and 144 admitted). Every file is below the
1000-line splitting threshold (1500 lines is the hard limit); the largest is
[RegressionLimits.lean](CKSD/LinearModels/RegressionLimits.lean) at 997 lines. All modules use
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

- [Gaussian likelihood minimum](CKSD/LinearModels/Multivariate.lean#L299) and [uniqueness](CKSD/LinearModels/Multivariate.lean#L309) (GAPS 105.28).
- [Invariance of the kinetic Gibbs law against smooth compactly supported tests](CKSD/Bayes/KineticLangevin.lean#L274) (GAPS 104.48).
- [Exact noncentral F law for nested Gaussian projections](CKSD/LinearModels/FTest.lean#L93) and its [central case](CKSD/LinearModels/FTest.lean#L200) (GAPS 105.16).
- [Normalized factor-loading uniqueness up to column signs](CKSD/LinearModels/FactorAnalysis.lean#L98) (GAPS 105.35).
- [Projected empirical-mean central limit theorem](CKSD/Geometry/GeometricStatistics.lean#L505) (GAPS 108.10).
- [Finite-rank degenerate U-statistic Gaussian-chaos limit](CKSD/Asymptotics/UStatistics.lean#L756) (GAPS 102.30).
- [Mean-square stability of optimal transport maps](CKSD/Geometry/OptimalMapStability.lean#L235) (GAPS 108.42).
- [Order-two Hoeffding decomposition and exact variance](CKSD/Asymptotics/UStatistics.lean#L533) (GAPS 102.29).
- [Gaussian Bures formula with singular covariances](CKSD/Geometry/GaussianTransport.lean#L100) (GAPS 108.46).

The general [Euclidean central limit theorem](CKSD/Asymptotics/MultivariateCLT.lean) permits
singular covariance matrices and almost-everywhere measurable IID observations. Convergence in distribution, convergence in probability and weak convergence of laws are
Mathlib's `TendstoInDistribution`, `TendstoInMeasure` and convergence in the topology of
`ProbabilityMeasure`; variances, covariances and distribution functions are Mathlib's `Var[·]`,
`cov[·, ·]` and `ProbabilityTheory.cdf`. The [asymptotic foundations](CKSD/Asymptotics/Basic.lean)
supply Slutsky's lemma, tightness, the delta method and the IID central-limit adapter, and
[boundedness in probability](CKSD/Inference/Basic.lean#L130) is equivalent to Mathlib's
`IsTightMeasureSet` for the laws.

The two conditional theorems have complete proofs from admitted results:
[Poincaré inequality under bounded perturbation](CKSD/Bayes/FunctionalInequalities.lean#L512)
(from the admitted logarithmic Sobolev half) and the
[stochastic-approximation equilibrium corollary](CKSD/Bayes/StochasticApproximation.lean#L542).

## Mathematical domains and conventions

- Test functions in weak formulations of Fokker–Planck and kinetic equations, and smoothness hypotheses on potentials and densities, are `ContDiff ℝ ∞` (infinitely differentiable). In Mathlib `ContDiff ℝ ⊤` means analytic, and an analytic function with compact support on a Euclidean space of positive dimension vanishes.
- [Particle likelihood asymptotic variance](CKSD/Bayes/ParticleLimits.lean#L55) sums the centred second-moment ratios, with the subtraction of one inside each summand. The time-zero identity and the zero-variance identity for unit potentials are proved. The particle central limit theorems remain admitted; their catalogue source is [SYNOPSIS104](SYNOPSIS104.md), item 59.
- [Threshold-excess discrepancy](CKSD/Processes/ExtremeValueLimits.lean#L65) takes its supremum over every nonnegative excess, including points at and beyond a terminal atom. The generalized Pareto distribution function is extended across its endpoint. The domain-of-attraction equivalence remains admitted; see [SYNOPSIS106](SYNOPSIS106.md), item 47.
- [Offset deformation retraction](CKSD/Geometry/TopologicalInference.lean#L89) requires a finite nonempty sample on the manifold. This excludes the empty/nonempty real-Hausdorff-distance degeneracy. The retraction theorem remains admitted; see [SYNOPSIS108](SYNOPSIS108.md), item 22.
- [Offset homology inference](CKSD/Geometry/TopologicalInference.lean#L126) uses closed offsets (`cthickening`). With `d_H(K, P) = ε` for a compact `K` and a finite `P`, the closed interleavings `K^a ⊆ P^{a+ε}` and `P^a ⊆ K^{a+ε}` hold, so the boundary case `j = i + 2ε` of [SYNOPSIS108](SYNOPSIS108.md), item 37, is included. The theorem remains admitted.
- [Regular transport potentials](CKSD/Geometry/TransportRates.lean#L86) have ambient twice continuous differentiability at every point of the closed conjugacy ball and Hessian bounds there. Both statistical map-rate statements require the source to be supported in a smaller concentric closed ball of radius `r < 1`; constants may depend on the interior margin. This controls gradients where risk is evaluated and prevents constrained-conjugacy boundary ties. Both rate statements remain admitted; see [SYNOPSIS108](SYNOPSIS108.md), item 53.
- [Gaussian SEM equivalence](CKSD/LinearModels/StructuralEquations.lean#L131) compares representations faithful to their respective graphs. Nonzero edge coefficients alone do not supply faithfulness. The theorem remains admitted; see [SYNOPSIS105](SYNOPSIS105.md), item 71.
- [Active paths](CKSD/LinearModels/DirectedGraphical/Basic/CausalGraph.lean#L79) constrain only interior vertices, and [d-separation](CKSD/LinearModels/DirectedGraphical/Basic/CausalGraph.lean#L94) does not require disjoint vertex sets. For an endpoint `a ∈ Z`, the paths active given `Z` are those active given `(Z \ {a}) ∪ {a'}` after adding a leaf `a → a'`. Such leaves preserve skeletons and unshielded colliders, so Markov equivalence over all triples agrees with the classical notion over disjoint triples (SYNOPSIS105, item 67).
- [Bayes rules](CKSD/Inference/Model.lean#L98) have integrable risk and are compared with rules of integrable risk; [minimax rules](CKSD/Inference/Model.lean#L105) have risk bounded above and are compared with rules of bounded risk. Totalized integrals and real suprema therefore cannot assign the value `0` to a non-integrable or unbounded risk.
- [Characteristic kernels](CKSD/Geometry/Basic.lean#L98) quantify over probability laws against which the kernel is integrable, so the Bochner convention cannot make the squared MMD vanish for the wrong reason. The [squared MMD](CKSD/Geometry/Kernels.lean#L73) equals the squared distance of TauCeti kernel mean embeddings.
- [Compositional-class minimax risk](CKSD/Learning/Networks.lean#L643) and the [Eldan–Shamir depth separation](CKSD/Learning/Networks.lean#L589) use extended nonnegative integrals. Infinite squared loss is allowed and cannot become zero through the nonintegrable Bochner-integral convention. Both lower bounds remain admitted; see [SYNOPSIS107](SYNOPSIS107.md), items 29 and 37.
- [LinUCB regret](CKSD/Learning/Bandits.lean#L753) uses the scale `max σ (B * W)` with the stated positive parameters and ridge regularization. It accounts for initial exploration even with arbitrarily small noise. The statistical confidence and regret theorems remain admitted; see [SYNOPSIS107](SYNOPSIS107.md), item 63.
- [Stochastic little-o](CKSD/Asymptotics/Framework.lean#L77) and [stochastic big-O](CKSD/Asymptotics/Framework.lean#L83) require an eventually positive deterministic scale. In particular, an identically zero scale cannot satisfy either predicate.
- The [ULA bound under a logarithmic Sobolev inequality](CKSD/Bayes/LangevinSampling.lean#L121) uses Vempala and Wibisono's step-size range `h ≤ α/(4β²)` (SYNOPSIS104, item 45).
- The [Grenander limit law](CKSD/Nonparametric/Grenander.lean#L819) assumes a density vanishing on the negative half-line and nonincreasing on `[0, ∞)`; positivity at `x₀` follows from `f'(x₀) < 0` (SYNOPSIS103, item 11).

The corresponding SYNOPSIS statements are the mathematical source for GAPS and STRUCTURE.
Their domains and risk conventions agree across these files. The pinned-library coverage rule
is unchanged: 537 synopsis entries comprise 5 covered, 55 partly covered, and 477 not covered;
296 selected gap families and 110 easy entries, with 53 Scope paragraphs, retain their meanings.
Local CKSD results do not change the coverage classifications of the pinned dependencies.

## Cross-fitting

The [cross-fitted missing-mean statement](CKSD/Asymptotics/CrossFitting.lean#L910)
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

- `IsContiguous` is not yet reconciled with Statlib's contiguity predicates.
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

## Validation

The ordinary full build completes successfully with 10805 jobs and no warnings from CKSD files
other than admitted declarations. The inventory checker `scripts/check_formalization.py` audits
compiled axiom dependencies, docstring adjacency and source hashes. Individual module checks
(`scripts/check_lean_files.py`) use both `autoImplicit=false` and `relaxedAutoImplicit=false`
after building their imports. These checks do not turn the remaining statistical admissions
into proofs.
