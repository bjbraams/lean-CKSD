module

public import CKSD.Nonparametric.Basic
public import Mathlib.Probability.ProductMeasure

/-!
# Gaussian sequence, regression, and sparse estimation models

The Gaussian sequence model `y_j = θ_j + ε ξ_j` with its ellipsoid parameter sets, the
Nadaraya–Watson smoother, isotonic least squares, the lasso with the compatibility condition, and
the sparse Gaussian location model. Losses that may be infinite take values in `ℝ≥0∞`, and
minimax risks are infima over measurable estimators of suprema of such risks.

## Main definitions

* `CKSD.gaussianSequenceLaw`, `CKSD.sequenceEllipsoid`, `CKSD.sobolevEllipsoid`,
  `CKSD.gaussianSequenceMinimaxRisk`, `CKSD.gaussianSequenceLinearMinimaxRisk`: the Gaussian
  sequence experiment, the ellipsoids `∑ (a_j θ_j)² ≤ R`, and the minimax and linear minimax
  squared risks.
* `CKSD.nadarayaWatson`: the Nadaraya–Watson estimator, with value `0` where all weights vanish.
* `CKSD.IsIsotonicRegressionEstimator`: a least-squares fit over nondecreasing vectors.
* `CKSD.lassoObjective`, `CKSD.IsLassoEstimator`, `CKSD.HasCompatibility`: the lasso criterion
  `‖y - A β‖² / (2n) + λ ‖β‖₁`, its minimizers, and the compatibility condition on a cone.
* `CKSD.sparseGaussianLaw`, `CKSD.sparseGaussianMinimaxRisk`: the Gaussian location model and
  the minimax squared risk over `s`-sparse means.

## Main results

* `CKSD.tendsto_gaussianSequenceMinimaxRisk_div_linear` (Pinsker): on an ellipsoid the minimax
  risk is asymptotically equivalent to the linear minimax risk as `ε → 0`.
* `CKSD.sparseGaussianMinimaxRisk_bounds`: the minimax risk over `s`-sparse means is of order
  `σ² s log(p / s)`.

Sources: GAPS 103.7, 103.9, 103.21, 103.33, and 103.34.
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

/-- GAPS 103.9: Pinsker's theorem. On the ellipsoid `∑ (a_j θ_j)² ≤ R` with positive
nondecreasing `a_j → ∞`, the ratio of the minimax squared risk to the linear minimax squared
risk tends to `1` as the noise level `ε` decreases to `0`. -/
theorem tendsto_gaussianSequenceMinimaxRisk_div_linear (a : ℕ → ℝ)
    (ha : ∀ j, 0 < a j) (hmono : Monotone a) (hlim : Tendsto a atTop atTop)
    (R : ℝ) (hR : 0 < R) :
    Tendsto (fun ε ↦
      (gaussianSequenceMinimaxRisk (sequenceEllipsoid a (ENNReal.ofReal R)) ε).toReal /
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

/-- The compatibility condition with constant `κ` on the cone `‖δ_{Sᶜ}‖₁ ≤ L ‖δ_S‖₁`:
`κ² ‖δ_S‖₁² ≤ |S| ‖A δ‖² / n` for every `δ` in the cone. -/
def HasCompatibility {n p : ℕ}
    (A : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (S : Finset (Fin p)) (L κ : ℝ) : Prop :=
  ∀ δ, restrictedL1Norm Sᶜ δ ≤ L * restrictedL1Norm S δ →
    κ ^ 2 * (restrictedL1Norm S δ) ^ 2 ≤ (S.card : ℝ) * ‖A δ‖ ^ 2 / n

/-- Gaussian finite-dimensional sparse estimation experiment. -/
def sparseGaussianLaw {p : ℕ} (θ : EuclideanSpace ℝ (Fin p)) (σ : ℝ) :
    Measure (EuclideanSpace ℝ (Fin p)) :=
  multivariateGaussian θ (σ ^ 2 • (1 : Matrix (Fin p) (Fin p) ℝ))

/-- Minimax squared risk over the `s`-sparse vectors. -/
def sparseGaussianMinimaxRisk (p s : ℕ) (σ : ℝ) : ℝ≥0∞ :=
  ⨅ T : {T : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p) // Measurable T},
    ⨆ θ : {θ : EuclideanSpace ℝ (Fin p) // sparsity θ ≤ s},
      ∫⁻ y, ENNReal.ofReal (‖T.val y - θ.val‖ ^ 2) ∂sparseGaussianLaw θ.val σ

/-- GAPS 103.33: the sparse minimax rate. There are universal constants `0 < c ≤ C` such that
for `1 ≤ s` and `2 s ≤ p` the minimax squared risk over `s`-sparse means in `N(θ, σ² I_p)` lies
between `c σ² s log(p / s)` and `C σ² s log(p / s)`. -/
theorem sparseGaussianMinimaxRisk_bounds :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ p s : ℕ, 1 ≤ s → 2 * s ≤ p → ∀ σ : ℝ, 0 < σ →
      ENNReal.ofReal (c * σ ^ 2 * s * Real.log ((p : ℝ) / s)) ≤ sparseGaussianMinimaxRisk p s σ ∧
      sparseGaussianMinimaxRisk p s σ ≤
        ENNReal.ofReal (C * σ ^ 2 * s * Real.log ((p : ℝ) / s)) := by
  sorry

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
