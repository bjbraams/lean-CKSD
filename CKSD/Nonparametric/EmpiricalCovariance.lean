module

public import CKSD.Nonparametric.Basic

/-!
# Empirical covariance and simple leading principal components

The covariance uses the empirical mean and divisor `n`. The results concern a simple leading
component in finite-dimensional Euclidean space under a fourth-moment hypothesis; they do not
assert the infinite-dimensional spectral expansion of GAPS 103.30. The spectral gap is specified
by a Rayleigh bound on the orthogonal complement, without choosing an ordering of eigenbases.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators Matrix.Norms.L2Operator

namespace CKSD

/-- Population covariance in Euclidean coordinates, using Mathlib's covariance adapter. -/
def euclideanCovarianceMatrix {d : ℕ} (P : Measure (EuclideanSpace ℝ (Fin d))) :
    Matrix (Fin d) (Fin d) ℝ :=
  fun i j ↦ covariance P (fun x ↦ x i) (fun x ↦ x j)

/-- The sample-centred empirical covariance matrix, with divisor `n`. -/
def empiricalCovarianceMatrix {Ω : Type*} {d : ℕ}
    (X : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (n : ℕ) (ω : Ω) :
    Matrix (Fin d) (Fin d) ℝ :=
  fun i j ↦ (∑ k ∈ Finset.range n,
    (X k ω i - sampleAverage X n ω i) * (X k ω j - sampleAverage X n ω j)) / n

/-- Largest Rayleigh value of a real matrix; the intended spectral interpretation is symmetric.
The empty unit sphere in dimension zero gives the usual real `sSup ∅ = 0` convention. -/
def leadingRayleighValue {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  sSup {r : ℝ | ∃ u : EuclideanSpace ℝ (Fin d), ‖u‖ = 1 ∧
    r = inner ℝ u (Matrix.toEuclideanCLM (𝕜 := ℝ) A u)}

/-- GAPS 103.30: leading empirical covariance eigenvalue expansion and CLT in finite dimension.
The Gaussian variance formula is not needed for this non-Gaussian fourth-moment version. -/
theorem leading_empirical_covariance_eigenvalue_asymptotics
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure P]
    (X : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (hiid : IsIndependentIdenticallyDistributed μ X P) (h4 : MemLp id 4 P)
    (v : EuclideanSpace ℝ (Fin d)) (hv : ‖v‖ = 1) (lambda gap : ℝ)
    (hlambda : 0 < lambda) (hgap : 0 < gap)
    (heig : Matrix.toEuclideanCLM (𝕜 := ℝ) (euclideanCovarianceMatrix P) v = lambda • v)
    (hother : ∀ u : EuclideanSpace ℝ (Fin d), inner ℝ u v = 0 →
      inner ℝ u (Matrix.toEuclideanCLM (𝕜 := ℝ) (euclideanCovarianceMatrix P) u) ≤
        (lambda - gap) * ‖u‖ ^ 2) :
    TendstoInProbabilityConst μ (fun n ω ↦ Real.sqrt n *
      (leadingRayleighValue (empiricalCovarianceMatrix X n ω) - lambda -
        inner ℝ v (Matrix.toEuclideanCLM (𝕜 := ℝ)
          (empiricalCovarianceMatrix X n ω - euclideanCovarianceMatrix P) v))) 0 ∧
    TendstoInDistribution μ (fun n ω ↦ Real.sqrt n *
      (leadingRayleighValue (empiricalCovarianceMatrix X n ω) - lambda))
      (gaussianReal 0 (Real.toNNReal
        (variance P (fun x ↦ inner ℝ (x - ∫ z, z ∂P) v ^ 2)))) := by
  sorry

/-- GAPS 103.30: the root-`n` bound for a measurably chosen leading empirical eigenvector.
Its sign is fixed by nonnegative inner product with the population eigenvector. -/
theorem isBoundedInProbability_leading_empirical_eigenvector_error
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure P]
    (X : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (hiid : IsIndependentIdenticallyDistributed μ X P) (h4 : MemLp id 4 P)
    (v : EuclideanSpace ℝ (Fin d)) (hv : ‖v‖ = 1) (lambda gap : ℝ)
    (hlambda : 0 < lambda) (hgap : 0 < gap)
    (heig : Matrix.toEuclideanCLM (𝕜 := ℝ) (euclideanCovarianceMatrix P) v = lambda • v)
    (hother : ∀ u : EuclideanSpace ℝ (Fin d), inner ℝ u v = 0 →
      inner ℝ u (Matrix.toEuclideanCLM (𝕜 := ℝ) (euclideanCovarianceMatrix P) u) ≤
        (lambda - gap) * ‖u‖ ^ 2)
    (w : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (hw : ∀ n, Measurable (w n))
    (hwunit : ∀ n ω, ‖w n ω‖ = 1) (hsign : ∀ n ω, 0 ≤ inner ℝ (w n ω) v)
    (hwleading : ∀ n ω, Matrix.toEuclideanCLM (𝕜 := ℝ) (empiricalCovarianceMatrix X n ω)
      (w n ω) = leadingRayleighValue (empiricalCovarianceMatrix X n ω) • w n ω) :
    IsBoundedInProbability μ (fun n ω ↦ Real.sqrt n * ‖w n ω - v‖) := by
  sorry

/-- The empirical covariance of the empty sample is the zero matrix. -/
@[simp] theorem empiricalCovarianceMatrix_zero {Ω : Type*} {d : ℕ}
    (X : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (ω : Ω) :
    empiricalCovarianceMatrix X 0 ω = 0 := by
  ext i j
  simp [empiricalCovarianceMatrix]

/-- An empirical covariance matrix is symmetric, for every sample including the empty one. -/
theorem empiricalCovarianceMatrix_isSymm {Ω : Type*} {d : ℕ}
    (X : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (n : ℕ) (ω : Ω) :
    (empiricalCovarianceMatrix X n ω).IsSymm := by
  ext i j
  simp only [Matrix.transpose_apply, empiricalCovarianceMatrix]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  exact mul_comm _ _

end CKSD
