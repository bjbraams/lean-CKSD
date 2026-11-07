module

public import CKSD.Learning.Basic
public import CKSD.Processes.Models

/-!
# Learning objectives, networks, and sequential algorithms

Definitions for empirical risk minimization, margins, boosting, finite neural networks, bandits,
and private threshold queries. Kernels continue to represent randomized algorithms.
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

/-- Scalar ReLU activation. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- An affine layer of a finite dense neural network. -/
structure DenseLayer (m n : ℕ) where
  /-- Weight matrix. -/
  weight : Matrix (Fin n) (Fin m) ℝ
  /-- Bias vector. -/
  bias : Fin n → ℝ

/-- Affine evaluation of one dense layer. -/
def DenseLayer.affine {m n : ℕ} (L : DenseLayer m n) (x : Fin m → ℝ) : Fin n → ℝ :=
  L.weight.mulVec x + L.bias

/-- A finite feed-forward network, built from compatible affine layers. -/
inductive FeedForwardNetwork (input : ℕ) : ℕ → Type
  | inputLayer : FeedForwardNetwork input input
  | addLayer {m n : ℕ} : FeedForwardNetwork input m → DenseLayer m n → FeedForwardNetwork input n

/-- Evaluation with a fixed activation after every affine layer. -/
def FeedForwardNetwork.eval {d n : ℕ} (σ : ℝ → ℝ) :
    FeedForwardNetwork d n → (Fin d → ℝ) → (Fin n → ℝ)
  | .inputLayer, x => x
  | .addLayer net layer, x => fun i ↦ σ (layer.affine (net.eval σ x) i)

/-- Number of affine layers in a finite network. -/
def FeedForwardNetwork.depth {d n : ℕ} : FeedForwardNetwork d n → ℕ
  | .inputLayer => 0
  | .addLayer net _ => net.depth + 1

/-- Number of scalar parameters of a network, including biases. -/
def FeedForwardNetwork.parameterCount {d n : ℕ} : FeedForwardNetwork d n → ℕ
  | .inputLayer => 0
  | @FeedForwardNetwork.addLayer _ m n net _ => net.parameterCount + m * n + n

/-- A one-hidden-layer real predictor, with an affine output layer. -/
def twoLayerPredictor {d N : ℕ} (σ : ℝ → ℝ) (a : Fin N → ℝ)
    (w : Fin N → EuclideanSpace ℝ (Fin d)) (b : Fin N → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ := ∑ j, a j * σ (inner ℝ (w j) x + b j)

/-- Population `k`-means distortion for an ordered representation of the centers. -/
def kmeansRisk {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] {k : ℕ}
    (P : Measure X) (centers : Fin k → X) : ℝ :=
  ∫ x, sInf (range fun j ↦ dist x (centers j) ^ 2) ∂P

/-- A policy maps the observed past actions and rewards to a distribution on the next arm. -/
abbrev BanditPolicy (K : ℕ) :=
  ∀ t : ℕ, Kernel (Fin t → Fin K × ℝ) (Fin K)

/-- Cumulative pseudo-regret relative to an optimal arm. -/
def banditPseudoRegret {Ω : Type*} {K : ℕ} (μ : Fin K → ℝ) (star : Fin K)
    (A : ℕ → Ω → Fin K) (T : ℕ) (ω : Ω) : ℝ :=
  ∑ t ∈ Finset.range T, (μ star - μ (A t ω))

/-- Exp3's importance-weighted estimated loss for one observed action and loss. -/
def importanceWeightedBanditLoss {K : ℕ} (p : Fin K → ℝ) (chosen : Fin K)
    (loss : ℝ) (i : Fin K) : ℝ := if i = chosen then loss / p i else 0

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

/-- GAPS 107.74, deterministic accuracy on the simultaneous bounded-noise event. -/
theorem aboveThreshold_comparison (value T z noise α : ℝ)
    (hz : |z| ≤ α / 2) (hnoise : |noise| ≤ α / 2) :
    (T + z ≤ value + noise → T - α ≤ value) ∧
      (value + noise < T + z → value ≤ T + α) := by
  constructor <;> intro h <;> obtain ⟨hz₁, hz₂⟩ := abs_le.mp hz <;>
    obtain ⟨hn₁, hn₂⟩ := abs_le.mp hnoise <;> linarith

/-- The ReLU activation is nonnegative. -/
theorem relu_nonneg (x : ℝ) : 0 ≤ relu x := le_max_left _ _

/-- ReLU is the identity on the nonnegative half-line. -/
@[simp] theorem relu_of_nonneg {x : ℝ} (hx : 0 ≤ x) : relu x = x := max_eq_right hx

end CKSD
