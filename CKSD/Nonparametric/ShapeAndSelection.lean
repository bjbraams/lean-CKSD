module

public import CKSD.Nonparametric.Models
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Shape constraints and penalized projection models

The isotonic risk bounds are in the Gaussian-noise scope, with the empirical squared norm
normalization `1/n`. The model-selection statement permits a countable collection of linear
models, specifies the measurable selected index, and uses actual orthogonal projections.
Sources: GAPS 103.27 and 103.35.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace CKSD

/-- Cone of nondecreasing finite real vectors. -/
def isotonicCone (n : ℕ) : Set (Fin n → ℝ) := {θ | Monotone θ}

/-- Variation of a finite real vector, including the empty-vector value zero. -/
def finiteVectorVariation {n : ℕ} (θ : Fin n → ℝ) : ℝ :=
  sSup (range θ) - sInf (range θ)

/-- Gaussian isotonic regression risk, divided by sample size. -/
def isotonicGaussianRisk {n : ℕ} (θ : Fin n → ℝ)
    (T : (Fin n → ℝ) → (Fin n → ℝ)) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal ((∑ i, (T y i - θ i) ^ 2) / n)
    ∂(Measure.pi fun i : Fin n ↦ gaussianReal (θ i) 1)

/-- The bounded monotone class used in the isotonic minimax lower bound. -/
def isotonicUnitBall (n : ℕ) : Set (Fin n → ℝ) :=
  {θ | Monotone θ ∧ ∀ i, |θ i| ≤ 1}

/-- Gaussian isotonic minimax risk on the bounded monotone class. -/
def isotonicGaussianMinimaxRisk (n : ℕ) : ℝ≥0∞ :=
  ⨅ T : {T : (Fin n → ℝ) → (Fin n → ℝ) // Measurable T},
    ⨆ θ : isotonicUnitBall n, isotonicGaussianRisk θ.val T.val

/-- Mean response over a contiguous block of indices. -/
def blockAverage {n : ℕ} (y : Fin n → ℝ) (a b : Fin n) : ℝ :=
  (∑ j ∈ Finset.Icc a b, y j) / (b.val - a.val + 1 : ℕ)

/-- Isotonic least squares in its explicit max–min block-average form. -/
def isotonicLeastSquares {n : ℕ} (y : Fin n → ℝ) (i : Fin n) : ℝ :=
  ⨆ a : {a : Fin n // a ≤ i}, ⨅ b : {b : Fin n // i ≤ b}, blockAverage y a.val b.val

/-- GAPS 103.27: the max–min block-average formula is the isotonic least-squares fit. -/
theorem isIsotonicRegressionEstimator_isotonicLeastSquares {n : ℕ} (y : Fin n → ℝ) :
    IsIsotonicRegressionEstimator y (isotonicLeastSquares y) := by
  sorry

/-- GAPS 103.27: existence and uniqueness of the isotonic least-squares fit. -/
theorem existsUnique_isIsotonicRegressionEstimator {n : ℕ} (y : Fin n → ℝ) :
    ∃! θ : Fin n → ℝ, IsIsotonicRegressionEstimator y θ := by
  let K : Set (EuclideanSpace ℝ (Fin n)) := {x | Monotone (fun i ↦ x i)}
  have hclosed : IsClosed K :=
    isClosed_monotone.preimage (PiLp.continuous_ofLp 2 (fun _ : Fin n ↦ ℝ))
  have hconv : Convex ℝ K := by
    intro x hx z hz a b ha hb _ i j hij
    change a * x i + b * z i ≤ a * x j + b * z j
    have hx' := hx hij
    have hz' := hz hij
    nlinarith [mul_nonneg ha (sub_nonneg.mpr hx'), mul_nonneg hb (sub_nonneg.mpr hz')]
  have hne : K.Nonempty := ⟨0, fun _ _ _ ↦ le_rfl⟩
  letI : Nonempty K := hne.to_subtype
  let u : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 y
  have hsq (a : EuclideanSpace ℝ (Fin n)) :
      ‖u - a‖ ^ 2 = ∑ i, (y i - a i) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp only [u, PiLp.sub_apply, PiLp.toLp_apply, Real.norm_eq_abs, sq_abs]
  obtain ⟨v, hv, hvnorm⟩ :=
    exists_norm_eq_iInf_of_complete_convex hne hclosed.isComplete hconv u
  have hbelow (a : K) : (⨅ w : K, ‖u - w‖) ≤ ‖u - a‖ :=
    ciInf_le ⟨0, fun _ ⟨_, heq⟩ ↦ heq ▸ norm_nonneg _⟩ a
  refine ⟨fun i ↦ v i, ⟨hv, ?_⟩, ?_⟩
  · intro θ hθ
    have hnorm : ‖u - v‖ ≤ ‖u - WithLp.toLp 2 θ‖ :=
      hvnorm.trans_le (hbelow ⟨WithLp.toLp 2 θ, hθ⟩)
    have hnormsq := mul_self_le_mul_self (norm_nonneg (u - v)) hnorm
    rw [← sq, ← sq] at hnormsq
    rw [hsq v, hsq (WithLp.toLp 2 θ)] at hnormsq
    exact hnormsq
  · intro z hz
    let w : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 z
    have hw : w ∈ K := hz.1
    have hwmin (a : K) : ‖u - w‖ ≤ ‖u - a‖ := by
      apply nonneg_le_nonneg_of_sq_le_sq (norm_nonneg _)
      rw [← sq, ← sq]
      rw [hsq w, hsq a]
      exact hz.2 (fun i ↦ a.val i) a.property
    have hwnorm : ‖u - w‖ = ⨅ a : K, ‖u - a‖ :=
      le_antisymm (le_ciInf hwmin) (hbelow ⟨w, hw⟩)
    have hvw := (norm_eq_iInf_iff_real_inner_le_zero hconv hv).mp hvnorm w hw
    have hwv := (norm_eq_iInf_iff_real_inner_le_zero hconv hw).mp hwnorm v hv
    have hid : inner ℝ (u - v) (w - v) + inner ℝ (u - w) (v - w) = ‖w - v‖ ^ 2 := by
      rw [show u - v = (u - w) + (w - v) by abel,
        show v - w = -(w - v) by abel, inner_add_left, inner_neg_right,
        real_inner_self_eq_norm_sq]
      ring
    have hnormzero : ‖w - v‖ = 0 := by nlinarith [sq_nonneg ‖w - v‖]
    have heq : w = v := sub_eq_zero.mp (norm_eq_zero.mp hnormzero)
    funext i
    exact congrArg (fun a : EuclideanSpace ℝ (Fin n) ↦ a i) heq

/-- GAPS 103.27: the adaptive variation risk bound for Gaussian isotonic least squares.
The more general independent finite-variance-error version is not asserted here. -/
theorem isotonicGaussianRisk_le :
    ∃ C > (0 : ℝ), ∀ n : ℕ, 0 < n → ∀ θ : Fin n → ℝ, Monotone θ →
      ∀ T : (Fin n → ℝ) → (Fin n → ℝ), Measurable T →
      (∀ y, IsIsotonicRegressionEstimator y (T y)) →
      isotonicGaussianRisk θ T ≤ ENNReal.ofReal
        (C * (Real.rpow (finiteVectorVariation θ / n) (2 / 3 : ℝ) +
          Real.log (Real.exp 1 * n) / n)) := by
  sorry

/-- GAPS 103.27: no estimator improves the Gaussian bounded-isotonic minimax rate. -/
theorem isotonicGaussianMinimaxRisk_lower_bound :
    ∃ c > (0 : ℝ), ∀ n : ℕ, 0 < n →
      ENNReal.ofReal (c * Real.rpow (n : ℝ) (-2 / 3 : ℝ)) ≤
        isotonicGaussianMinimaxRisk n := by
  sorry

/-- Orthogonal least-squares fit within a selected linear model. -/
def projectionModelFit {M : Type*} {n : ℕ}
    (S : M → Submodule ℝ (EuclideanSpace ℝ (Fin n))) (m : M)
    (y : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  (S m).starProjection y

/-- Penalized empirical residual criterion for linear model selection. -/
def penalizedModelCriterion {M : Type*} {n : ℕ}
    (S : M → Submodule ℝ (EuclideanSpace ℝ (Fin n))) (pen : M → ℝ)
    (y : EuclideanSpace ℝ (Fin n)) (m : M) : ℝ :=
  ‖y - projectionModelFit S m y‖ ^ 2 / n + pen m

/-- Normalized prediction risk of a selected projection fit in Gaussian regression. -/
def selectedProjectionRisk {M : Type*} {n : ℕ}
    (S : M → Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (select : EuclideanSpace ℝ (Fin n) → M)
    (f : EuclideanSpace ℝ (Fin n)) (σ : ℝ) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal (‖projectionModelFit S (select y) y - f‖ ^ 2 / n)
    ∂(multivariateGaussian f (σ ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ)))

/-- GAPS 103.35: the countable-model oracle inequality for penalized least squares.
The prior weights, dimension penalty, and empirical minimizer are explicit. -/
theorem selectedProjectionRisk_oracle_bound :
    ∃ κ₀ > (0 : ℝ), ∀ κ > κ₀, ∃ C > (0 : ℝ),
      ∀ n : ℕ, 0 < n → ∀ (M : Type*) [Countable M] [Nonempty M]
      [MeasurableSpace M] [MeasurableSingletonClass M],
      ∀ S : M → Submodule ℝ (EuclideanSpace ℝ (Fin n)),
      ∀ π : M → ℝ≥0, (∀ m, 0 < π m) → (∑' m, (π m : ℝ≥0∞)) ≤ 1 →
      ∀ σ : ℝ, 0 < σ → ∀ pen : M → ℝ,
      (∀ m, κ * σ ^ 2 / n *
        (Module.finrank ℝ (S m) + Real.log (1 / (π m : ℝ))) ≤ pen m) →
      ∀ select : EuclideanSpace ℝ (Fin n) → M, Measurable select →
      (∀ y m, penalizedModelCriterion S pen y (select y) ≤ penalizedModelCriterion S pen y m) →
      ∀ f : EuclideanSpace ℝ (Fin n),
      selectedProjectionRisk S select f σ ≤ ENNReal.ofReal
        (C * ((⨅ m, ‖f - projectionModelFit S m f‖ ^ 2 / n + pen m) + σ ^ 2 / n)) := by
  sorry

/-- The isotonic cone is convex. -/
theorem convex_isotonicCone (n : ℕ) : Convex ℝ (isotonicCone n) := by
  intro x hx y hy a b ha hb _ i j hij
  change a * x i + b * y i ≤ a * x j + b * y j
  have hx' := hx hij
  have hy' := hy hij
  nlinarith [mul_nonneg ha (sub_nonneg.mpr hx'), mul_nonneg hb (sub_nonneg.mpr hy')]

/-- The fitted value is unchanged when the response already lies in the selected model. -/
theorem projectionModelFit_of_mem {M : Type*} {n : ℕ}
    (S : M → Submodule ℝ (EuclideanSpace ℝ (Fin n))) (m : M)
    (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ S m) : projectionModelFit S m y = y := by
  exact Submodule.starProjection_eq_self_iff.mpr hy

end CKSD
