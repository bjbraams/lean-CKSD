# Mathlib-style assessment of CKSD

The project contains 187 Lean modules and 2095 inventoried declarations: 756 definitions,
abbreviations, structures and inductive types, and 1339 theorem statements (1144 proved,
one conditional on an admitted result, and 194 admitted). Every file is below 1000 physical lines; the largest is
`CKSD/Inference/Families.lean` at 956 lines. All modules use the module system and have module
documentation. All authored definitions, abbreviations, structures, inductive types and theorem
statements have formal docstrings, as do all 118 structure fields. The two network constructors
have their own docstrings.

The dependency baseline is Lean `v4.36.0-rc2`, Mathlib
`6135ffb78e8bcd3fcc8ec02f3f82ea0b0737358b`, TauCeti
`afa08a3ed16fb167e35de371afb1eb03fbc5913a`, and Statlib
`eeaac0283690efaa60c31115400cf561836baeb9`. Namespace and build conventions are in
[AGENTS.md](AGENTS.md). Declaration statuses and source locations are in
[FORMALIZATION.md](FORMALIZATION.md); this assessment does not certify the truth of admissions.

## Proved statistical foundations

The following scoped catalogue statements have complete proofs with no admitted dependencies:

- [Gaussian likelihood minimum and uniqueness](CKSD/LinearModels/Multivariate.lean#L175) (GAPS 105.28).
- [Invariance of the kinetic Gibbs law against smooth compactly supported tests](CKSD/Bayes/KineticLangevin.lean#L255) (GAPS 104.48).
- [Exact noncentral F law for nested Gaussian projections](CKSD/LinearModels/FTest.lean#L79) (GAPS 105.16).
- [Normalized factor-loading uniqueness up to column signs](CKSD/LinearModels/FactorAnalysis.lean#L66) (GAPS 105.35).
- [Projected empirical-mean central limit theorem](CKSD/Geometry/GeometricStatistics.lean#L302) (GAPS 108.10).
- [Finite-rank degenerate U-statistic Gaussian-chaos limit](CKSD/Asymptotics/UStatistics.lean#L674) (GAPS 102.30).
- [Mean-square stability of optimal transport maps](CKSD/Geometry/OptimalMapStability.lean#L234) (GAPS 108.42).
- [Order-two Hoeffding decomposition and exact variance](CKSD/Asymptotics/UStatistics.lean#L440) (GAPS 102.29).
- [Gaussian Bures formula with singular covariances](CKSD/Geometry/GaussianTransport.lean#L96) (GAPS 108.46).

The general [Euclidean central limit theorem](CKSD/Asymptotics/MultivariateCLT.lean) permits
singular covariance matrices and almost-everywhere measurable IID observations. The
[CKSD–Mathlib convergence adapter](CKSD/Asymptotics/Convergence.lean) connects the two probability-law
interfaces. The finite-rank U-statistic and projected-mean limits use these foundations.
The factor-loading theorem requires no separate positivity assumption on the unique variances:
its supplied normalization conditions suffice.

## Mathematical domains and conventions

- [Particle likelihood asymptotic variance](CKSD/Bayes/ParticleLimits.lean#L38) sums the centred second-moment ratios, with the subtraction of one inside each summand. The time-zero identity and the zero-variance identity for unit potentials are proved. The particle central limit theorems remain admitted; their catalogue source is [SYNOPSIS104](SYNOPSIS104.md), item 59.
- [Threshold-excess discrepancy](CKSD/Processes/ExtremeValueLimits.lean#L45) takes its supremum over every nonnegative excess, including points at and beyond a terminal atom. The generalized Pareto distribution function is extended across its endpoint. The domain-of-attraction equivalence remains admitted; see [SYNOPSIS106](SYNOPSIS106.md), item 47.
- [Offset deformation retraction](CKSD/Geometry/TopologicalInference.lean#L94) requires a finite nonempty sample on the manifold. This excludes the empty/nonempty real-Hausdorff-distance degeneracy. The retraction theorem remains admitted; see [SYNOPSIS108](SYNOPSIS108.md), item 22.
- [Regular transport potentials](CKSD/Geometry/TransportRates.lean#L76) have ambient twice continuous differentiability at every point of the closed conjugacy ball and Hessian bounds there. Both statistical map-rate statements require the source to be supported in a smaller concentric closed ball of radius `r < 1`; constants may depend on the interior margin. This controls gradients where risk is evaluated and prevents constrained-conjugacy boundary ties. Both rate statements remain admitted; see [SYNOPSIS108](SYNOPSIS108.md), item 53.
- [Gaussian SEM equivalence](CKSD/LinearModels/StructuralEquations.lean#L136) compares representations faithful to their respective graphs. Nonzero edge coefficients alone do not supply faithfulness. The theorem remains admitted; see [SYNOPSIS105](SYNOPSIS105.md), item 71.
- [Compositional-class minimax risk](CKSD/Learning/Networks.lean#L187) uses an extended nonnegative integral. Infinite squared loss is allowed and cannot become zero through the nonintegrable Bochner-integral convention. The lower bound remains admitted; see [SYNOPSIS107](SYNOPSIS107.md), item 29.
- [LinUCB regret](CKSD/Learning/Bandits.lean#L767) uses the scale `max σ (B * W)` with the stated positive parameters and ridge regularization. It accounts for initial exploration even with arbitrarily small noise. The statistical confidence and regret theorems remain admitted; see [SYNOPSIS107](SYNOPSIS107.md), item 63.
- [Weak convergence](CKSD/Inference/Basic.lean#L44) records finiteness of every source measure and the limit, together with convergence of bounded continuous integrals. Its constructor and test-function coercion support the finite-measure API without identifying an infinite-mass law with zero.
- [Stochastic little-o](CKSD/Asymptotics/Framework.lean#L49) and [stochastic big-O](CKSD/Asymptotics/Framework.lean#L55) require an eventually positive deterministic scale. In particular, an identically zero scale cannot satisfy either predicate.

The corresponding SYNOPSIS statements are the mathematical source for GAPS and STRUCTURE.
Their domains and risk conventions agree across these files. The pinned-library coverage rule
is unchanged: 537 synopsis entries comprise 5 covered, 55 partly covered, and 477 not covered;
296 selected gap families and 110 easy entries, with 53 Scope paragraphs, retain their meanings.
Local CKSD results do not change the coverage classifications of the pinned dependencies.

## Cross-fitting

The [cross-fitted missing-mean statement](CKSD/Asymptotics/Semiparametric.lean#L140)
uses a fixed finite number of folds and requires a common positive lower bound on fold
proportions only for sufficiently large sample sizes:

```lean
∀ᶠ n in atTop, ∀ k,
  c * n ≤ (Finset.univ.filter fun i ↦ (split n).fold i = k).card
```

A condition imposed at every sample size would, at `n = 1`, require every fold to contain at
least one observation. A partition of a singleton has at most one nonempty fold, so that
condition permits only one fold. The eventual condition permits ordinary cross-fitting;
a strict Lean probe verifies it for the balanced two-fold split with `c = 1/4` once `n ≥ 2`.
Training excludes the evaluation fold, and the stated nuisance-error and score conditions
remain essential. The asymptotic linearity theorem itself remains admitted.

## Hypotheses and unused arguments

The compiled Batteries unused-argument test examines actual types and completed proof or
definition terms. A hypothesis absent from both can be omitted while retaining the existing
proof. Such a finding concerns current completed code, not an argument expected to become
necessary when an admission is proved. The test deliberately skips direct admissions and
underscore-prefixed arguments. Those require mathematical inspection; an admission's failure
to mention a hypothesis is not evidence that the hypothesis can be deleted.

The compiled unused-argument test reports no remaining unused declaration arguments
among its eligible declarations. The core APIs use the smaller justified hypotheses. Examples include M-estimator consistency
without estimator measurability in the outer-event argument, MMD tightness convergence without
ambient completeness, representer theory using only completeness of the finite-dimensional
feature span, factorization without extra statistic-space assumptions, and finite-dimensional
matrix/graph adapters without irrelevant finite-index instances. Statistical wrappers retain
positivity, integrability, model, independence and normalization hypotheses actually required.
Underscore-prefixed conventional assumptions are omitted where the proof already follows from
more direct supplied identities or stopping-time hypotheses.

Further possible moment reductions in the admitted multivariate/2SLS limits require implication
lemmas and full proofs. They are not justified merely by the current admission. Likewise,
source absolute continuity is unnecessary for the Karcher implication with supplied optimal
maps, but may be necessary for separate first-variation/existence statements.

## Module organization

Original import paths re-export mathematical components, preserving public declaration names
apart from the single duplicate density-pushforward lemma. The common density result is
`CKSD.map_withDensity_comp` in [Inference/Density.lean](CKSD/Inference/Density.lean); reverse
orientations use its symmetric equality.

The following subject modules have focused components:

- [Asymptotics/Estimators.lean](CKSD/Asymptotics/Estimators.lean): convergence/Slutsky, likelihood support, maximum likelihood, quantiles, Z-estimators and U-statistics.
- [LinearModels/DirectedGraphical.lean](CKSD/LinearModels/DirectedGraphical.lean): finite graphical-law foundations, interventions, Markov theory, do-calculus and discovery.
- [Learning/Generalization.lean](CKSD/Learning/Generalization.lean): concentration/Rademacher estimates, exponential weights, conformal ranks, classification and stability.
- [Learning/PrivateEstimation.lean](CKSD/Learning/PrivateEstimation.lean): mechanisms, central lower bounds and local privacy.
- [Geometry/MatrixReduction.lean](CKSD/Geometry/MatrixReduction.lean): reduction foundations, homology and barcode rank formulas.
- [Geometry/SimplicialPersistence.lean](CKSD/Geometry/SimplicialPersistence.lean): chains, sublevel diagrams, bottleneck stability and Wasserstein stability, using shared diagram metrics and finite combinatorics.
- [Nonparametric/LowerBounds.lean](CKSD/Nonparametric/LowerBounds.lean): testing/packing lower bounds, restricted-isometry sparse recovery and covariance thresholding.
- [Processes/Kalman.lean](CKSD/Processes/Kalman.lean): model, covariance/error recursions and Gaussian filter laws. Generic conditioning and independence tools are in [GaussianConditioning.lean](CKSD/Processes/GaussianConditioning.lean).
- [Processes/TimeSeries.lean](CKSD/Processes/TimeSeries.lean): Wold decomposition, long-run variance, stationary Gaussian construction and GARCH series.

The population covariance matrix is a thin adapter to pinned TauCeti's `covMatrix`; the
square-root inequality uses Mathlib's `Real.rpow_add_le_add_rpow`; maximal-invariant factorization
uses Mathlib's `Function.factorsThrough_iff`. Conventions and source provenance are in
[CREDITS.md](CREDITS.md). Broader convergence interoperability must preserve the project's
outer/nonseparable scope; an indiscriminate replacement by a separability-restricted theorem
would lose generality.

## Remaining Mathlib-review concerns

The principal remaining requirement is full proofs of the admitted results. Substantive
statistical hypotheses and constants still need proof-level validation; compilation of an
admission is not evidence of mathematical correctness.

- Many module headers outside the focused components remain generic catalogue summaries or refer to section drafts. They should describe mathematical scope, notation, conventions and named main results.
- Most declarations remain directly under `CKSD`. Give generic implementation helpers descriptive object namespaces or private visibility where appropriate; preserve the required CKSD root namespace and external callers.
- Public helper names such as `centered_identity`, `mem_of_subset_of_mem`, and `sum_le_sum_of_dominates` are hard to discover. Large conjunction theorems should expose separately named conclusion lemmas. Conclusion-based names and consistent American spelling remain appropriate targets.
- Long individual proofs still have useful factoring opportunities: LAN remainder estimates, Grenander grid slopes, RIP support/tail bounds, Gaussian projection standardization, and Exp3 inverse-probability integrability.
- Finite-update, finite-supremum, clipping, Hamming-distance and entropy atoms have Mathlib APIs worth connecting explicitly. Common chordality/maximal-clique foundations should bridge Decomposable and JunctionTree.
- `DenseNetParams` still indexes hidden weights by all natural-number layers. A finite parameter type or an explicit restriction/quotient would support future parameter-space measurability and derivatives.
- Real Hellinger and density adapters document their valid finite-divergence/absolute-continuity domain. Use those guards when deriving distance/density interpretations; the definitions themselves remain totalized.
- Copyright, authorship and licensing need a deliberate project decision before upstream submission. No authors or license are inferred.

The [Mathlib naming](https://leanprover-community.github.io/contribute/naming.html),
[style](https://leanprover-community.github.io/contribute/style.html), and
[documentation](https://mathlib.org/contribute/doc.html) guides provide the upstream conventions.
Project-specific namespace and module requirements remain authoritative.

## Validation

The ordinary full build completes successfully with 10673 jobs. The inventory checker audits
compiled axiom dependencies and source hashes. Formal docstring inspection uses
`Lean.findDocString?` and `Lean.getStructureInfo?`, including every structure field. Unused
argument checks use the pinned Batteries environment test on all authored declarations.
Strict checks of the proof modules and public entry points pass. Individual module checks use both `autoImplicit=false` and `relaxedAutoImplicit=false` after
building their imports. Semantic probes check the finite-measure convergence domain,
eventually positive stochastic scales, balanced two-fold partitions, and constant-potential
particle variances. They do not turn the remaining statistical admissions into proofs.
