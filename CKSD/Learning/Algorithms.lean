module

public import CKSD.Learning.Basic
public import CKSD.Processes.Models


/-!
# Learning objectives, boosting, and private threshold queries

Basic objects of empirical risk minimization, margin-based classification and boosting, simple
neural predictors, `k`-means, and the AboveThreshold mechanism.

## Main definitions

* `CKSD.empiricalRisk`, `CKSD.IsEmpiricalRiskMinimizer`: empirical risk on a finite sample.
* `CKSD.marginLoss`, `CKSD.exponentialLoss`: ramp and exponential margin losses.
* `CKSD.boostingScore`, `CKSD.boostingWeight`, `CKSD.boostingWeightedError`: AdaBoost.
* `CKSD.relu`, `CKSD.twoLayerPredictor`: one-hidden-layer predictors.
* `CKSD.kmeansRisk`: the population `k`-means distortion.
* `CKSD.HasQuerySensitivity`, `CKSD.aboveThresholdTime`: the AboveThreshold mechanism.

## Main results

* `CKSD.training_error_le_exponential_loss`: the exponential loss dominates the training error
  (GAPS 107.24).
* `CKSD.sub_le_of_threshold_add_le_add`, `CKSD.le_add_of_add_lt_threshold_add`: accuracy of
  AboveThreshold on the bounded-noise event (GAPS 107.74).

Sources: Sections 107A–107D of `GAPS.md`.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- Empirical risk on a finite sample. -/
def empiricalRisk {H X : Type*} {n : ℕ} (loss : H → X → ℝ) (h : H) (x : Fin n → X) : ℝ :=
  (∑ i, loss h (x i)) / n

/-- An empirical risk minimizer; existence is a separate assertion. -/
def IsEmpiricalRiskMinimizer {H X : Type*} {n : ℕ}
    (loss : H → X → ℝ) (x : Fin n → X) (h : H) : Prop :=
  ∀ g, empiricalRisk loss h x ≤ empiricalRisk loss g x

/-- Ramp margin loss at a positive margin scale. -/
def marginLoss (ρ margin : ℝ) : ℝ := min 1 (max 0 (1 - margin / ρ))

/-- Exponential loss of a signed binary margin. -/
def exponentialLoss (margin : ℝ) : ℝ := Real.exp (-margin)

/-- AdaBoost's accumulated score from a sequence of weak binary predictors. -/
def boostingScore {X : Type*} (h : ℕ → X → ℝ) (α : ℕ → ℝ) (T : ℕ) (x : X) : ℝ :=
  ∑ t ∈ Finset.range T, α t * h t x

/-- AdaBoost's normalized observation weights before round `t`. -/
def boostingWeight {X : Type*} {n : ℕ} (x : Fin n → X) (y : Fin n → ℝ)
    (h : ℕ → X → ℝ) (α : ℕ → ℝ) (t : ℕ) (i : Fin n) : ℝ :=
  Real.exp (-y i * boostingScore h α t (x i)) /
    ∑ j, Real.exp (-y j * boostingScore h α t (x j))

/-- Weighted misclassification error of a weak predictor. -/
def boostingWeightedError {X : Type*} {n : ℕ} (x : Fin n → X) (y : Fin n → ℝ)
    (h : ℕ → X → ℝ) (α : ℕ → ℝ) (t : ℕ) : ℝ :=
  ∑ i, if h t (x i) ≠ y i then boostingWeight x y h α t i else 0

/-- Scalar ReLU activation `x ↦ max 0 x` (the scalar form of TauCeti's vector-valued
`reluActivation`). -/
def relu (x : ℝ) : ℝ := max 0 x

/-- A one-hidden-layer real predictor `x ↦ ∑ⱼ aⱼ σ(⟪wⱼ, x⟫ + bⱼ)` with `N` hidden units on a
real inner product space. -/
def twoLayerPredictor {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {N : ℕ}
    (σ : ℝ → ℝ) (a : Fin N → ℝ) (w : Fin N → E) (b : Fin N → ℝ) (x : E) : ℝ :=
  ∑ j, a j * σ (inner ℝ (w j) x + b j)

/-- Population `k`-means distortion `∫ minⱼ d(x, cⱼ)² dP` for an ordered list of `k` centers.
The minimum is the real `sInf` of a finite set; for `k = 0` it is `sInf ∅ = 0`. -/
def kmeansRisk {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] {k : ℕ}
    (P : Measure X) (centers : Fin k → X) : ℝ :=
  ∫ x, sInf (range fun j ↦ dist x (centers j) ^ 2) ∂P

/-- A query has sensitivity at most `c` for the supplied neighboring-data relation. -/
def HasQuerySensitivity {D : Type*} (R : D → D → Prop) (c : ℝ) (f : D → ℝ) : Prop :=
  ∀ d d', R d d' → |f d - f d'| ≤ c

/-- AboveThreshold's first crossing, for fixed threshold noise and a noise stream. -/
def aboveThresholdTime {D : Type*} (query : ℕ → D → ℝ) (T z : ℝ)
    (noise : ℕ → ℝ) (d : D) : ℕ∞ :=
  thresholdHittingTime (fun n (_ : Unit) ↦ query n d + noise n) (T + z) ()

/-- GAPS 107.24, exponential loss dominates empirical training error, including zero margins. -/
theorem training_error_le_exponential_loss {n : ℕ} (margin : Fin n → ℝ) :
    (((Finset.univ.filter fun i ↦ margin i ≤ 0).card : ℝ) / n) ≤
      (∑ i, exponentialLoss (margin i)) / n := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  calc
    ((Finset.univ.filter fun i ↦ margin i ≤ 0).card : ℝ) =
        ∑ i, if margin i ≤ 0 then (1 : ℝ) else 0 := by simp
    _ ≤ ∑ i, exponentialLoss (margin i) := by
      apply Finset.sum_le_sum
      intro i _
      split_ifs with h
      · exact (Real.one_le_exp_iff).mpr (neg_nonneg.mpr h)
      · exact (Real.exp_pos _).le

/-- GAPS 107.74, deterministic accuracy on the simultaneous bounded-noise event, crossing case:
if the threshold noise `z` and the query noise are at most `α / 2` in absolute value, a noisy
query value at or above the noisy threshold `T + z` has true value at least `T - α`. -/
theorem sub_le_of_threshold_add_le_add {value T z noise α : ℝ}
    (hz : |z| ≤ α / 2) (hnoise : |noise| ≤ α / 2) (h : T + z ≤ value + noise) :
    T - α ≤ value := by
  linarith [abs_le.mp hz, abs_le.mp hnoise]

/-- GAPS 107.74, deterministic accuracy on the simultaneous bounded-noise event, non-crossing
case: if the threshold noise `z` and the query noise are at most `α / 2` in absolute value, a
noisy query value below the noisy threshold `T + z` has true value at most `T + α`. -/
theorem le_add_of_add_lt_threshold_add {value T z noise α : ℝ}
    (hz : |z| ≤ α / 2) (hnoise : |noise| ≤ α / 2) (h : value + noise < T + z) :
    value ≤ T + α := by
  linarith [abs_le.mp hz, abs_le.mp hnoise]

/-- The ReLU activation is nonnegative. -/
theorem relu_nonneg (x : ℝ) : 0 ≤ relu x := le_max_left _ _

/-- ReLU is the identity on the nonnegative half-line. -/
@[simp] theorem relu_of_nonneg {x : ℝ} (hx : 0 ≤ x) : relu x = x := max_eq_right hx

end CKSD
