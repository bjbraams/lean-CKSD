module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Measure.Count
public import CKSD.Inference.Basic
public import TauCeti.Probability.Distributions.Wishart.Basic

/-!
# Linear models: common definitions

Definitions shared by the files on linear models, multivariate analysis, experimental design and
survey sampling (Section 105).

## Main definitions

* `CKSD.matrixQuadraticForm`: the quadratic form `x ↦ ⟪x, A x⟫` of a real square matrix.
* `CKSD.sampleMean`, `CKSD.scatterMatrix`: the mean and the centred scatter matrix
  `∑ᵢ (xᵢ - x̄)(xᵢ - x̄)ᵀ` of a finite Euclidean sample.
* `CKSD.gaussianNegLogLikelihood`: the negative Gaussian log-likelihood
  `(n/2) log det C + (1/2) ∑ᵢ (xᵢ - m)ᵀ C⁻¹ (xᵢ - m)` up to its constant term.
* `CKSD.simpleRandomSampleDesign`: the uniform law on the `n`-subsets of `{0, …, N-1}`,
  with the discrete measurable structure `CKSD.finiteSampleMeasurableSpace` on samples.
* `CKSD.populationMean`, `CKSD.populationVariance`: finite-population mean and variance with
  divisor `N - 1`.
* `CKSD.IsLatinSquare`, `CKSD.OrthogonalLatinSquares`: Latin squares of order `s` and their
  orthogonality.

## Main results

* `CKSD.measurable_matrixQuadraticForm`: quadratic forms are measurable.
* `CKSD.matrix_inv_smul`: `(c • A)⁻¹ = c⁻¹ • A⁻¹` for every scalar `c`.
* `CKSD.finrank_orthogonal_span_pair`,
  `CKSD.norm_sq_orthogonalProjectionOnto_orthogonal_span_pair`: the complement of the span of
  an orthonormal pair and the squared norm of the projection onto it.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

open scoped CKSD

attribute [local instance] Classical.propDecidable

/-- The discrete measurable structure on the samples (subsets) of a finite population. -/
scoped instance finiteSampleMeasurableSpace (N : ℕ) : MeasurableSpace (Finset (Fin N)) := ⊤

/-- Quadratic form of a real matrix on Euclidean space. -/
def matrixQuadraticForm {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  inner ℝ x (Matrix.toEuclideanCLM (𝕜 := ℝ) A x)

/-- Defining equation of `matrixQuadraticForm`. -/
theorem matrixQuadraticForm_def {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (x : EuclideanSpace ℝ (Fin d)) :
    matrixQuadraticForm A x = inner ℝ x (Matrix.toEuclideanCLM (𝕜 := ℝ) A x) := by
  rw [matrixQuadraticForm]

/-- A quadratic form `x ↦ xᵀ P x` is measurable. -/
@[fun_prop]
theorem measurable_matrixQuadraticForm {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) :
    Measurable (matrixQuadraticForm P) := by
  unfold matrixQuadraticForm
  exact (continuous_id.inner (Matrix.toEuclideanCLM (𝕜 := ℝ) P).continuous).measurable

/-- Mean of a finite Euclidean sample. -/
def sampleMean {n d : ℕ} (x : Fin n → EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  (n : ℝ)⁻¹ • ∑ i, x i

/-- Defining equation of `sampleMean`. -/
theorem sampleMean_def {n d : ℕ} (x : Fin n → EuclideanSpace ℝ (Fin d)) :
    sampleMean x = (n : ℝ)⁻¹ • ∑ i, x i := by
  rw [sampleMean]

/-- Centered scatter matrix of a finite Euclidean sample. -/
def scatterMatrix {n d : ℕ} (x : Fin n → EuclideanSpace ℝ (Fin d)) : Matrix (Fin d) (Fin d) ℝ :=
  fun j k ↦ ∑ i, (x i j - sampleMean x j) * (x i k - sampleMean x k)

/-- Entries of `scatterMatrix`. -/
theorem scatterMatrix_apply {n d : ℕ} (x : Fin n → EuclideanSpace ℝ (Fin d)) (j k : Fin d) :
    scatterMatrix x j k = ∑ i, (x i j - sampleMean x j) * (x i k - sampleMean x k) := by
  rw [scatterMatrix]

/-- Negative Gaussian log-likelihood up to its constant term. -/
def gaussianNegLogLikelihood {n d : ℕ} (x : Fin n → EuclideanSpace ℝ (Fin d))
    (m : EuclideanSpace ℝ (Fin d)) (C : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  (n : ℝ) / 2 * Real.log C.det + (∑ i, matrixQuadraticForm C⁻¹ (x i - m)) / 2

/-- Defining equation of `gaussianNegLogLikelihood`. -/
theorem gaussianNegLogLikelihood_def {n d : ℕ} (x : Fin n → EuclideanSpace ℝ (Fin d))
    (m : EuclideanSpace ℝ (Fin d)) (C : Matrix (Fin d) (Fin d) ℝ) :
    gaussianNegLogLikelihood x m C =
      (n : ℝ) / 2 * Real.log C.det + (∑ i, matrixQuadraticForm C⁻¹ (x i - m)) / 2 := by
  rw [gaussianNegLogLikelihood]

/-- Simple random sampling without replacement: the uniform law on the subsets of size `n` of a
population of `N` units. It is a probability measure when `n ≤ N`. -/
def simpleRandomSampleDesign (N n : ℕ) : Measure (Finset (Fin N)) :=
  (Nat.choose N n : ℝ≥0∞)⁻¹ • Measure.count.restrict {s | s.card = n}

/-- Defining equation of `simpleRandomSampleDesign`. -/
theorem simpleRandomSampleDesign_def (N n : ℕ) :
    simpleRandomSampleDesign N n =
      (Nat.choose N n : ℝ≥0∞)⁻¹ • Measure.count.restrict {s | s.card = n} := by
  rw [simpleRandomSampleDesign]

/-- Finite-population mean. -/
def populationMean {N : ℕ} (y : Fin N → ℝ) : ℝ := (∑ i, y i) / N

/-- Defining equation of `populationMean`. -/
theorem populationMean_def {N : ℕ} (y : Fin N → ℝ) : populationMean y = (∑ i, y i) / N := by
  rw [populationMean]

/-- Finite-population variance with divisor `N-1`. -/
def populationVariance {N : ℕ} (y : Fin N → ℝ) : ℝ :=
  (∑ i, (y i - populationMean y) ^ 2) / (N - 1 : ℕ)

/-- Defining equation of `populationVariance`. -/
theorem populationVariance_def {N : ℕ} (y : Fin N → ℝ) :
    populationVariance y = (∑ i, (y i - populationMean y) ^ 2) / (N - 1 : ℕ) := by
  rw [populationVariance]

/-- A Latin square of order `s`: every symbol occurs exactly once in each row and in each
column. -/
@[expose] def IsLatinSquare {s : ℕ} (L : Fin s → Fin s → Fin s) : Prop :=
  (∀ i, Function.Bijective (L i)) ∧ ∀ j, Function.Bijective (fun i ↦ L i j)

/-- Two Latin squares are orthogonal when superposing them gives every ordered pair of symbols
exactly once. -/
@[expose] def OrthogonalLatinSquares {s : ℕ} (L M : Fin s → Fin s → Fin s) : Prop :=
  Function.Injective (fun z : Fin s × Fin s ↦ (L z.1 z.2, M z.1 z.2))

/-- Inversion commutes with scalar multiplication over a field, `(c • A)⁻¹ = c⁻¹ • A⁻¹`, for
every scalar `c` (including `c = 0`) and for invertible and singular matrices alike. -/
theorem matrix_inv_smul {n K : Type*} [Fintype n] [DecidableEq n] [Field K] (c : K)
    (A : Matrix n n K) : (c • A)⁻¹ = c⁻¹ • A⁻¹ := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  by_cases h : IsUnit A.det
  · exact Matrix.inv_smul' A (Units.mk0 c hc) h
  · have h' : ¬ IsUnit (c • A).det := by
      rw [Matrix.det_smul, isUnit_iff_ne_zero] at *
      simpa [hc] using h
    rw [Matrix.nonsing_inv_apply_not_isUnit _ h, Matrix.nonsing_inv_apply_not_isUnit _ h',
      smul_zero]


section OrthonormalPair

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- For orthonormal vectors `e` and `u`, the orthogonal complement of `span {e, u}` has
codimension two: its dimension is `dim E - 2`. -/
theorem finrank_orthogonal_span_pair {e u : E} (he : ‖e‖ = 1) (hu : ‖u‖ = 1)
    (heu : inner ℝ e u = 0) :
    Module.finrank ℝ (Submodule.span ℝ {e, u})ᗮ = Module.finrank ℝ E - 2 := by
  have hON : Orthonormal ℝ ![e, u] := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j <;> simp [he, hu, heu, real_inner_comm]
  have hfin2 : Module.finrank ℝ (Submodule.span ℝ {e, u}) = 2 := by
    have := finrank_span_eq_card hON.linearIndependent
    have hr : Set.range ![e, u] = {e, u} := by
      rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union]
    rw [hr] at this
    simpa using this
  have := Submodule.finrank_add_finrank_orthogonal (Submodule.span ℝ {e, u})
  omega

/-- For orthonormal vectors `e` and `u`, the squared norm of the orthogonal projection of `X`
onto `span {e, u}ᗮ` is `⟪X, X⟫ - ⟪e, X⟫² - ⟪u, X⟫²`. -/
theorem norm_sq_orthogonalProjectionOnto_orthogonal_span_pair {e u : E} (he : ‖e‖ = 1)
    (hu : ‖u‖ = 1) (heu : inner ℝ e u = 0) (X : E) :
    ‖(Submodule.span ℝ {e, u})ᗮ.orthogonalProjectionOnto X‖ ^ 2 =
      inner ℝ X X - inner ℝ e X ^ 2 - inner ℝ u X ^ 2 := by
  set S2 := Submodule.span ℝ {e, u}
  have he1 : inner ℝ e e = 1 := by rw [real_inner_self_eq_norm_sq, he, one_pow]
  have hu1 : inner ℝ u u = 1 := by rw [real_inner_self_eq_norm_sq, hu, one_pow]
  have hproj : S2ᗮ.starProjection X = X - inner ℝ e X • e - inner ℝ u X • u := by
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ fun w hw ↦ ?_
    · rw [Submodule.mem_orthogonal]
      intro v hv
      obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.1 hv
      simp only [inner_add_left, inner_smul_left, inner_sub_right, inner_smul_right, he1, hu1,
        heu, real_inner_comm e u, RCLike.conj_to_real]
      ring
    · have hmem : inner ℝ e X • e + inner ℝ u X • u ∈ S2 :=
        S2.add_mem (S2.smul_mem _ (Submodule.subset_span (by simp)))
          (S2.smul_mem _ (Submodule.subset_span (by simp)))
      rw [show X - (X - inner ℝ e X • e - inner ℝ u X • u) =
        inner ℝ e X • e + inner ℝ u X • u by abel]
      exact Submodule.inner_right_of_mem_orthogonal hmem hw
  rw [← Submodule.norm_coe, ← Submodule.starProjection_apply, hproj,
    ← real_inner_self_eq_norm_sq]
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, he1, hu1,
    heu, real_inner_comm e u, real_inner_comm X e, real_inner_comm X u, RCLike.conj_to_real]
  ring

end OrthonormalPair

end CKSD
