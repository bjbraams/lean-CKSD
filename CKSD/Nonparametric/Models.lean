module

public import CKSD.Nonparametric.Basic
public import Mathlib.Probability.ProductMeasure

/-!
# Nonparametric and sparse estimation models

Gaussian sequence experiments, Sobolev ellipsoids, regression smoothers, isotonic criteria, and
regularized linear estimation. All losses that may be infinite use nonnegative extended reals.
Sources: GAPS 103.7–103.11, 103.22–103.28, 103.33–103.35, 103.48–103.49.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- Gaussian sequence observation law with noise standard deviation `ε`. -/
def gaussianSequenceLaw (θ : ℕ → ℝ) (ε : ℝ) : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun j ↦ gaussianReal (θ j) (Real.toNNReal (ε ^ 2)))

/-- Squared sequence error, taking value infinity when the difference is not square summable. -/
def sequenceSquaredError (a b : ℕ → ℝ) : ℝ≥0∞ :=
  ∑' j, ENNReal.ofReal ((a j - b j) ^ 2)

/-- Weighted ellipsoid; the radius convention is `sum (a_j theta_j)^2 ≤ R`. -/
def sequenceEllipsoid (a : ℕ → ℝ) (R : ℝ≥0∞) : Set (ℕ → ℝ) :=
  {θ | (∑' j, ENNReal.ofReal ((a j * θ j) ^ 2)) ≤ R}

/-- Sobolev ellipsoid indexed from frequency one. -/
def sobolevEllipsoid (β : ℝ) (R : ℝ≥0∞) : Set (ℕ → ℝ) :=
  sequenceEllipsoid (fun j ↦ Real.rpow (j + 1) β) R

/-- Minimax squared risk over measurable Gaussian-sequence estimators. -/
def gaussianSequenceMinimaxRisk (Θ : Set (ℕ → ℝ)) (ε : ℝ) : ℝ≥0∞ :=
  ⨅ T : {T : (ℕ → ℝ) → (ℕ → ℝ) // Measurable T},
    ⨆ θ : Θ, ∫⁻ y, sequenceSquaredError (T.val y) θ.val ∂gaussianSequenceLaw θ.val ε

/-- Linear minimax risk with coordinatewise shrinkage estimators. -/
def gaussianSequenceLinearMinimaxRisk (Θ : Set (ℕ → ℝ)) (ε : ℝ) : ℝ≥0∞ :=
  ⨅ c : ℕ → ℝ, ⨆ θ : Θ,
    ∫⁻ y, sequenceSquaredError (fun j ↦ c j * y j) θ.val ∂gaussianSequenceLaw θ.val ε

/-- Pinsker's positive-part shrinkage weights. -/
def pinskerWeight (a : ℕ → ℝ) (μ : ℝ) (j : ℕ) : ℝ := max 0 (1 - a j / μ)

/-- GAPS 103.9: asymptotic equivalence of arbitrary and linear minimax risks on an ellipsoid. -/
theorem tendsto_gaussianSequenceMinimaxRisk_div_linear (a : ℕ → ℝ)
    (ha : ∀ j, 0 < a j) (hmono : Monotone a) (hlim : Tendsto a atTop atTop)
    (R : ℝ) (hR : 0 < R) :
    Tendsto (fun ε ↦ (gaussianSequenceMinimaxRisk (sequenceEllipsoid a (ENNReal.ofReal R)) ε).toReal /
      (gaussianSequenceLinearMinimaxRisk (sequenceEllipsoid a (ENNReal.ofReal R)) ε).toReal)
      (𝓝[>] 0) (𝓝 1) := by
  sorry

/-- Nadaraya–Watson estimator; the value when all weights vanish is zero. -/
def nadarayaWatson {d n : ℕ} (K : EuclideanSpace ℝ (Fin d) → ℝ) (h : ℝ)
    (x : Fin n → EuclideanSpace ℝ (Fin d)) (y : Fin n → ℝ)
    (t : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (∑ i, K (h⁻¹ • (x i - t)) * y i) / (∑ i, K (h⁻¹ • (x i - t)))

/-- Squared regression prediction error under the feature law. -/
def regressionPredictionError {X : Type*} [MeasurableSpace X]
    (P : Measure X) (m estimate : X → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal ((estimate x - m x) ^ 2) ∂P

/-- An isotonic least-squares estimator is a minimizer over the monotone cone. -/
def IsIsotonicRegressionEstimator {n : ℕ} (y estimate : Fin n → ℝ) : Prop :=
  Monotone estimate ∧ ∀ θ : Fin n → ℝ, Monotone θ →
    (∑ i, (y i - estimate i) ^ 2) ≤ ∑ i, (y i - θ i) ^ 2

/-- The lasso objective, with the `1/(2n)` squared-error normalization. -/
def lassoObjective {n p : ℕ}
    (A : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (y : EuclideanSpace ℝ (Fin n)) (lambda : ℝ) (β : EuclideanSpace ℝ (Fin p)) : ℝ :=
  ‖y - A β‖ ^ 2 / (2 * n) + lambda * restrictedL1Norm Finset.univ β

/-- A lasso estimate minimizes the lasso objective. -/
def IsLassoEstimator {n p : ℕ}
    (A : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (y : EuclideanSpace ℝ (Fin n)) (lambda : ℝ) (β : EuclideanSpace ℝ (Fin p)) : Prop :=
  ∀ b, lassoObjective A y lambda β ≤ lassoObjective A y lambda b

/-- Compatibility lower bound on the specified sparsity cone. -/
def HasCompatibility {n p : ℕ}
    (A : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (S : Finset (Fin p)) (L κ : ℝ) : Prop :=
  ∀ δ, restrictedL1Norm Sᶜ δ ≤ L * restrictedL1Norm S δ →
    κ ^ 2 * (restrictedL1Norm S δ) ^ 2 ≤ (S.card : ℝ) * ‖A δ‖ ^ 2 / n

/-- Basis pursuit with a norm-bounded residual. -/
def IsBasisPursuitEstimator {n p : ℕ}
    (A : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (y : EuclideanSpace ℝ (Fin n)) (η : ℝ) (β : EuclideanSpace ℝ (Fin p)) : Prop :=
  ‖A β - y‖ ≤ η ∧ ∀ b, ‖A b - y‖ ≤ η →
    restrictedL1Norm Finset.univ β ≤ restrictedL1Norm Finset.univ b

/-- Scalar soft thresholding. -/
def softThreshold (τ x : ℝ) : ℝ := max 0 (x - τ) - max 0 (-x - τ)

/-- Gaussian finite-dimensional sparse estimation experiment. -/
def sparseGaussianLaw {p : ℕ} (θ : EuclideanSpace ℝ (Fin p)) (σ : ℝ) :
    Measure (EuclideanSpace ℝ (Fin p)) :=
  multivariateGaussian θ (σ ^ 2 • (1 : Matrix (Fin p) (Fin p) ℝ))

/-- Minimax squared risk over the `s`-sparse vectors. -/
def sparseGaussianMinimaxRisk (p s : ℕ) (σ : ℝ) : ℝ≥0∞ :=
  ⨅ T : {T : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p) // Measurable T},
    ⨆ θ : {θ : EuclideanSpace ℝ (Fin p) // sparsity θ ≤ s},
      ∫⁻ y, ENNReal.ofReal (‖T.val y - θ.val‖ ^ 2) ∂sparseGaussianLaw θ.val σ

/-- GAPS 103.33: minimax sparse Gaussian rate with universal constants. -/
theorem sparseGaussianMinimaxRisk_bounds :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ p s : ℕ, 1 ≤ s → 2 * s ≤ p → ∀ σ : ℝ, 0 < σ →
      ENNReal.ofReal (c * σ ^ 2 * s * Real.log ((p : ℝ) / s)) ≤ sparseGaussianMinimaxRisk p s σ ∧
      sparseGaussianMinimaxRisk p s σ ≤
        ENNReal.ofReal (C * σ ^ 2 * s * Real.log ((p : ℝ) / s)) := by
  sorry

/-- A Hölder ball of order at most one on a specified domain. -/
def IsHolderRegressionFunction {X : Type*} [PseudoMetricSpace X]
    (domain : Set X) (β L : ℝ) (f : X → ℝ) : Prop :=
  (∀ x ∈ domain, |f x| ≤ L) ∧
    ∀ x ∈ domain, ∀ y ∈ domain, |f x - f y| ≤ L * Real.rpow (dist x y) β

/-- Any sequence has zero squared error against itself, including nonsummable sequences. -/
@[simp] theorem sequenceSquaredError_self (θ : ℕ → ℝ) : sequenceSquaredError θ θ = 0 := by
  simp [sequenceSquaredError]

/-- A zero bandwidth gives the unweighted mean when the kernel is nonzero at the origin. -/
theorem nadarayaWatson_zero_bandwidth {d n : ℕ} (K : EuclideanSpace ℝ (Fin d) → ℝ)
    (hK : K 0 ≠ 0) (x : Fin n → EuclideanSpace ℝ (Fin d)) (y : Fin n → ℝ)
    (t : EuclideanSpace ℝ (Fin d)) :
    nadarayaWatson K 0 x y t = (∑ i, y i) / n := by
  simp only [nadarayaWatson, inv_zero, zero_smul, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

end CKSD
