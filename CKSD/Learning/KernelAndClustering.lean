module

public import CKSD.Learning.Algorithms

/-!
# Kernel ridge regression and compact-support clustering

The ridge model is represented by a finite feature matrix, hence a positive semidefinite Gram
matrix. Its normalization matches the objective with squared-error coefficient `1/(2n)`.
The clustering statement uses a compact set containing both observations and centers and asks
for uniqueness only of the center set; different orderings are identified by Hausdorff distance.
Matrices, Gaussian laws, and Hausdorff distance are Mathlib APIs.

## Main definitions

* `CKSD.ridgeSmoother`, `CKSD.ridgePrediction`: fixed-design ridge regression.
* `CKSD.HasKernelCriticalRadius`: the empirical kernel critical-radius inequality.
* `CKSD.kmeansSampleRisk`: the empirical `k`-means distortion.

## Main results

* `CKSD.ridgePrediction_oracle_bounds`: kernel-ridge oracle bounds (GAPS 107.13).
* `CKSD.ae_tendsto_kmeans_centers_of_compact`: consistency of empirical `k`-means
  (GAPS 107.16).
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace CKSD

/-- Fixed-design ridge smoother for the objective `‖y - Aβ‖²/(2n) + λ‖β‖²`. -/
def ridgeSmoother {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℝ) (lambda : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  A * (A.transpose * A + (2 * (n : ℝ) * lambda) • (1 : Matrix (Fin p) (Fin p) ℝ))⁻¹ *
    A.transpose

/-- Predicted values of a fixed-design ridge fit. -/
def ridgePrediction {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℝ) (lambda : ℝ)
    (y : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  Matrix.toEuclideanLin (𝕜 := ℝ) (ridgeSmoother A lambda) y

/-- Empirical kernel critical-radius inequality in terms of normalized Gram eigenvalues. -/
def HasKernelCriticalRadius {n : ℕ} (eigenvalues : Fin n → ℝ) (R sigma delta : ℝ) : Prop :=
  Real.sqrt ((2 / (n : ℝ)) * ∑ j, min (delta ^ 2) (eigenvalues j)) ≤
    R * delta ^ 2 / (4 * sigma)

/-- GAPS 107.13: fixed-design kernel-ridge oracle bounds for a finite feature representation.
The constants are universal. Both the expected bound and the Gaussian tail bound use the same
critical radius. The eigenvalues `mu j` of the normalized Gram matrix `A Aᵀ / n` are
automatically nonnegative. This does not formalize the eigenvalue-decay calculation for infinite
RKHSs. -/
theorem ridgePrediction_oracle_bounds :
    ∃ c₀ > (0 : ℝ), ∃ c₁ > (0 : ℝ), ∃ c₂ > (0 : ℝ), ∃ c₃ > (0 : ℝ),
      ∀ n p : ℕ, 0 < n → ∀ A : Matrix (Fin n) (Fin p) ℝ,
      ∀ e : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)),
      ∀ mu : Fin n → ℝ,
      (∀ j, Matrix.toEuclideanLin (𝕜 := ℝ) (((n : ℝ)⁻¹) • (A * A.transpose)) (e j) =
        mu j • e j) →
      ∀ R sigma delta lambda : ℝ,
      0 < R → 0 < sigma → 0 < delta → HasKernelCriticalRadius mu R sigma delta →
      2 * delta ^ 2 ≤ lambda → ∀ truth : EuclideanSpace ℝ (Fin n),
      ∀ beta : EuclideanSpace ℝ (Fin p), ‖beta‖ ≤ R →
      let bound := c₀ * (‖Matrix.toEuclideanLin (𝕜 := ℝ) A beta - truth‖ ^ 2 / n +
        c₁ * R ^ 2 * (delta ^ 2 + lambda));
      (∫ z, ‖ridgePrediction A lambda (truth + sigma • z) - truth‖ ^ 2 / n
        ∂stdGaussian (EuclideanSpace ℝ (Fin n))) ≤ bound ∧
      (stdGaussian (EuclideanSpace ℝ (Fin n))).real
        {z | bound < ‖ridgePrediction A lambda (truth + sigma • z) - truth‖ ^ 2 / n} ≤
          c₂ * Real.exp (-c₃ * n * R ^ 2 * delta ^ 2 / sigma ^ 2) := by
  sorry

/-- Empirical `k`-means distortion of a finite sample, using an ordered center representation. -/
def kmeansSampleRisk {X : Type*} [PseudoMetricSpace X] {n k : ℕ}
    (x : Fin n → X) (centers : Fin k → X) : ℝ :=
  (∑ i, sInf (range fun j ↦ dist (x i) (centers j) ^ 2)) / n

/-- GAPS 107.16: almost-sure consistency of compactly constrained empirical `k`-means minimizers.
This scope assumes a fixed compact support containing all centers. The unbounded-support theorem
under only a second moment requires an additional localization argument. (For `k = 0` all center
sets are empty and the statement is trivial.) -/
theorem ae_tendsto_kmeans_centers_of_compact
    {Ω : Type*} [MeasurableSpace Ω] {d k : ℕ}
    (P : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure P]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (hiid : IsIndependentIdenticallyDistributed μ X P)
    (K : Set (EuclideanSpace ℝ (Fin d))) (hK : IsCompact K) (hsupp : P K = 1)
    (star : Fin k → K)
    (hmin : ∀ c : Fin k → K, kmeansRisk P (fun i ↦ (star i).val) ≤
      kmeansRisk P (fun i ↦ (c i).val))
    (hunique : ∀ c : Fin k → K, kmeansRisk P (fun i ↦ (c i).val) =
      kmeansRisk P (fun i ↦ (star i).val) →
        range (fun i ↦ (c i).val) = range (fun i ↦ (star i).val))
    (C : ℕ → Ω → Fin k → K) (hC : ∀ n, Measurable (C n))
    (hopt : ∀ n : ℕ, 0 < n → ∀ᵐ ω ∂μ, ∀ c : Fin k → K,
      kmeansSampleRisk (fun i : Fin n ↦ X i.val ω) (fun j ↦ (C n ω j).val) ≤
        kmeansSampleRisk (fun i : Fin n ↦ X i.val ω) (fun j ↦ (c j).val)) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ Metric.hausdorffDist
      (range fun j ↦ (C n ω j).val) (range fun j ↦ (star j).val)) atTop (𝓝 0) := by
  sorry

/-- Permuting center labels leaves the population distortion unchanged. -/
theorem kmeansRisk_comp_perm {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    {k : ℕ} (P : Measure X) (c : Fin k → X) (σ : Equiv.Perm (Fin k)) :
    kmeansRisk P (c ∘ σ) = kmeansRisk P c := by
  unfold kmeansRisk
  congr 1 with x
  exact congrArg sInf (EquivLike.range_comp (fun j ↦ dist x (c j) ^ 2) σ)

/-- A ridge smoother sends zero observations to zero predicted values. -/
@[simp] theorem ridgePrediction_zero {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℝ)
    (lambda : ℝ) : ridgePrediction A lambda 0 = 0 := by simp [ridgePrediction]

end CKSD
