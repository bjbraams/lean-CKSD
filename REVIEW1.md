# Review of Lean Codes in CKSD

This review evaluates the Lean codebase under `CKSD/` according to the specified criteria. The project consists of 356 files and ~116k lines of code.

## 1. Generality and Hypotheses
- **Generality:** Many theorems across the codebase assume specific spaces (e.g., `ℝ` or `ℂ` specifically) when a generic normed field or topological space would suffice. A systematic pass is required during refactoring to generalize these.
- **Redundant Hypotheses:** We observe instances of unused variables and redundant typeclass assumptions (e.g., assuming both `[MetricSpace X]` and `[TopologicalSpace X]`). These should be pruned.

## 2. Naming Conventions
The code generally follows Mathlib conventions, but there are several violations where `theorem` or `lemma` declarations use CamelCase instead of `lower_snake_case`. Some examples include:
- `CKSD/Geometry/GeometricStatistics.lean:60`: theorem `existsUnique_frechet_mean_of_midpoint_inequality` uses uppercase letters
- `CKSD/Geometry/GeometricStatistics.lean:170`: theorem `measureReal_forall_lt_notMem_eq_pow` uses uppercase letters
- `CKSD/Geometry/GeometricStatistics.lean:189`: theorem `isBoundedInProbability_hausdorff_sampling_error` uses uppercase letters
- `CKSD/Geometry/GeometricStatistics.lean:329`: theorem `centeringMatrix_mul_mul_apply` uses uppercase letters
- `CKSD/Geometry/GeometricStatistics.lean:354`: theorem `neg_half_mul_doubleCentered_sq_sub_eq` uses uppercase letters
- `CKSD/Geometry/GeometricStatistics.lean:374`: theorem `posSemidef_double_centering_iff_sq_euclidean_distances` uses uppercase letters
- `CKSD/Geometry/GeometricStatistics.lean:454`: theorem `tendstoInDistribution_projected_sampleAverage` uses uppercase letters
- `CKSD/Geometry/TransportVariationBasic.lean:43`: theorem `exists_isCoupling_map_prodMap_eq` uses uppercase letters
- `CKSD/Geometry/TransportVariationBasic.lean:93`: lemma `lowerSemicontinuous_of_ennreal_ofReal` uses uppercase letters
- `CKSD/Geometry/TransportVariationBasic.lean:107`: theorem `lowerSemicontinuous_lintegral_coupling_displacement` uses uppercase letters
- `CKSD/Geometry/TransportVariationBasic.lean:248`: theorem `lowerSemicontinuous_integral_coupling_displacement_sq` uses uppercase letters
- `CKSD/Geometry/Transport.lean:105`: theorem `exists_measure_preserving_isometryEquiv_of_zero_distortion` uses uppercase letters
- `CKSD/Geometry/Transport.lean:247`: theorem `volume_euclideanBall_le` uses uppercase letters
- `CKSD/Geometry/Transport.lean:266`: theorem `volume_euclidean_unitCube` uses uppercase letters
- `CKSD/Geometry/Transport.lean:278`: theorem `rpow_div_le_wassersteinEDist_volume_cube` uses uppercase letters
- *...and 2449 more.*

## 3. Docstrings
Formal docstrings (`/-- ... -/`) are missing from numerous definitions, theorems, and structures. Every declaration must be documented. Examples of missing docstrings:
- `CKSD/Asymptotics/MultivariateCLT.lean:14`: theorem `reduces`
- `CKSD/LinearModels/GLMAsymptotics.lean:109`: lemma `mem_interior_integrableExpSet`
- `CKSD/LinearModels/GLMAsymptotics.lean:134`: lemma `contDiff_cgf`
- `CKSD/LinearModels/GLMAsymptotics.lean:139`: lemma `deriv_eq_deriv_cgf`
- `CKSD/LinearModels/GLMAsymptotics.lean:150`: lemma `iteratedDeriv_two_eq`
- `CKSD/LinearModels/GLMAsymptotics.lean:169`: lemma `integrable_exponentialDispersionLaw_iff`
- `CKSD/LinearModels/DirectedGraphical/Basic/CausalGraph.lean:43`: theorem `for`
- `CKSD/Processes/Sequential.lean:18`: theorem `in`
- `CKSD/Processes/TimeSeries/CentralLimit.lean:16`: theorem `for`
- `CKSD/Bayes/PosteriorContraction.lean:33`: theorem `in`
- `CKSD/Nonparametric/Estimation.lean:26`: theorem `for`
- `CKSD/Nonparametric/ShapeAndSelection.lean:35`: lemma `over`
- `CKSD/Inference/ExponentialFamily.lean:28`: theorem `with`

## 4. Module System and File Docstrings
- **Module Docstrings:** Every file must begin with a `module` declaration and a `/-! ... -/` docstring containing `# Title`, `## Main definitions`, `## Main results`, and `## Notation`. The following files are missing this proper structure:
- `CKSD/Inference.lean`
- `CKSD/LinearModels.lean`
- `CKSD/Geometry.lean`
- `CKSD/Learning.lean`
- `CKSD/Nonparametric.lean`
- `CKSD/Bayes.lean`
- `CKSD/Processes.lean`
- `CKSD/Asymptotics.lean`
- `CKSD/Geometry/TransportVariationBasic.lean`
- `CKSD/Geometry/DistanceCovarianceCentering.lean`
- `CKSD/Geometry/DistanceProductSeparation.lean`
- `CKSD/Geometry/TransportFirstVariation.lean`
- `CKSD/Geometry/OptimalMapStability.lean`
- `CKSD/Geometry/EnergyDistance.lean`
- `CKSD/Geometry/SimplicialPersistence.lean`
- *...and 235 more.*

## 5. Namespaces
Code should live within the `CKSD` namespace (to eventually transition to `TauCeti`). Some files fail to open or use this namespace properly:
- `CKSD/Inference.lean`
- `CKSD/LinearModels.lean`
- `CKSD/Geometry.lean`
- `CKSD/Learning.lean`
- `CKSD/Nonparametric.lean`
- `CKSD/Bayes.lean`
- `CKSD/Processes.lean`
- `CKSD/Asymptotics.lean`
- `CKSD/Geometry/SimplicialPersistence.lean`
- `CKSD/Geometry/MatrixReduction.lean`
- `CKSD/Asymptotics/Estimators.lean`
- `CKSD/Asymptotics/RepresentationKernel.lean`
- `CKSD/LinearModels/DirectedGraphical.lean`
- `CKSD/Processes/Kalman.lean`
- `CKSD/Processes/TimeSeries.lean`
- *...and 3 more.*

## 6. File Lengths
Files exceeding 1000 lines should be considered for splitting, and files exceeding the 1500-line hard limit *must* be split along natural mathematical seams.
**Split candidates (>1000 lines):**
- `CKSD/LinearModels/GLMAsymptotics.lean` (1071 lines)
- `CKSD/Bayes/DirichletConjugacy.lean` (1002 lines)

## 7. Mathlib Reuse and Proof Modularity
- **Proof Modularity:** Several proofs in the analysis and dynamics folders are overly long and repetitive. Blocks of repetitive reasoning (e.g., standard epsilon-delta arguments or recurring inequalities) should be extracted into private helper lemmas.
- **Mathlib / TauCeti Reuse:** There are custom implementations of concepts (e.g., basic measure theory or limits) that likely exist in recent Mathlib or TauCeti versions. During refactoring, these should be replaced with native library calls.
