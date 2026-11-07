module

public import CKSD.LinearModels.Causal
public import CKSD.Asymptotics.Basic

/-!
# Quantile-regression and instrumental-variable limits

Quantile regression uses independent, nonidentically distributed responses and fixed design.
Instrumental-variable experiments store the regressor, instrument, and structural error, with
outcomes obtained from the structural equation. Sources: GAPS 105.5 and 105.55.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

/-- Expected check loss for a scalar location candidate. -/
def expectedQuantileCheckLoss (P : Measure ℝ) (tau a : ℝ) : ℝ :=
  ∫ y, quantileCheckLoss tau (y - a) ∂P

/-- GAPS 105.5: expected check-loss minimizers are precisely the distributional quantiles.
This characterization allows atoms; finite first moment makes every displayed risk finite. -/
theorem minimizes_expectedQuantileCheckLoss_iff (P : Measure ℝ) [IsProbabilityMeasure P]
    (hint : Integrable id P) (tau : ℝ) (htau : tau ∈ Ioo 0 1) (a : ℝ) :
    (∀ b, expectedQuantileCheckLoss P tau a ≤ expectedQuantileCheckLoss P tau b) ↔
      P.real (Iio a) ≤ tau ∧ tau ≤ P.real (Iic a) := by
  sorry

/-- Normalized weighted design second-moment matrix. -/
def weightedDesignMoment {p : ℕ} (x : ℕ → EuclideanSpace ℝ (Fin p))
    (w : ℕ → ℝ) (n : ℕ) : Matrix (Fin p) (Fin p) ℝ :=
  fun j k ↦ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, w i * x i j * x i k

/-- GAPS 105.5: fixed-design quantile-regression central limit theorem.
The density bounds, uniform local continuity, design limits, and maximal leverage condition
are all explicit. No identical-distribution assumption is imposed on the responses. -/
theorem tendstoInDistribution_quantile_regression
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (Q : ℕ → Measure ℝ)
    (hQ : ∀ i, IsProbabilityMeasure (Q i)) (f : ℕ → ℝ → ℝ)
    (hf : ∀ i, HasDensity (Q i) volume (f i))
    (Y : ℕ → Ω → ℝ) (hY : ∀ i, Measurable (Y i)) (hind : iIndepFun Y P)
    (hlaw : ∀ i, P.map (Y i) = Q i) (x : ℕ → EuclideanSpace ℝ (Fin p))
    (beta : EuclideanSpace ℝ (Fin p)) (tau : ℝ) (htau : tau ∈ Ioo 0 1)
    (hquantile : ∀ i, cdf (Q i) (inner ℝ (x i) beta) = tau)
    (a b : ℝ) (ha : 0 < a)
    (hbound : ∀ i, f i (inner ℝ (x i) beta) ∈ Icc a b)
    (hequi : ∀ eps > 0, ∃ delta > 0, ∀ i t,
      |t - inner ℝ (x i) beta| < delta → |f i t - f i (inner ℝ (x i) beta)| < eps)
    (D₀ D₁ : Matrix (Fin p) (Fin p) ℝ) (hD₀ : D₀.PosDef) (hD₁ : D₁.PosDef)
    (hdesign : Tendsto (weightedDesignMoment x (fun _ ↦ 1)) atTop (𝓝 D₀))
    (hweighted : Tendsto (weightedDesignMoment x (fun i ↦ f i (inner ℝ (x i) beta)))
      atTop (𝓝 D₁))
    (hleverage : Tendsto (fun n : ℕ ↦ sSup (range fun i : Fin n ↦ ‖x i.val‖) /
      Real.sqrt n) atTop (𝓝 0))
    (T : ℕ → Ω → EuclideanSpace ℝ (Fin p)) (hT : ∀ n, Measurable (T n))
    (hmin : ∀ n : ℕ, 0 < n → ∀ᵐ ω ∂P, IsQuantileRegressionEstimator tau
      (fun i : Fin n ↦ x i.val) (fun i : Fin n ↦ Y i.val ω) (T n ω)) :
    TendstoInDistribution P (fun n ω ↦ Real.sqrt n • (T n ω - beta))
      (multivariateGaussian 0 ((tau * (1 - tau)) • (D₁⁻¹ * D₀ * D₁⁻¹))) := by
  sorry

/-- Structural observation in an instrumental-variable model: regressor, instrument, error. -/
abbrev InstrumentalVariableObservation (p k : ℕ) :=
  EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin k) × ℝ

/-- Second moment of the instruments. -/
def instrumentSecondMoment {p k : ℕ} (Q : Measure (InstrumentalVariableObservation p k)) :
    Matrix (Fin k) (Fin k) ℝ := fun i j ↦ ∫ z, z.2.1 i * z.2.1 j ∂Q

/-- Cross second moment between instruments and regressors. -/
def instrumentRegressorMoment {p k : ℕ} (Q : Measure (InstrumentalVariableObservation p k)) :
    Matrix (Fin k) (Fin p) ℝ := fun i j ↦ ∫ z, z.2.1 i * z.1 j ∂Q

/-- Instrument-score covariance in the correctly specified structural model. -/
def instrumentErrorMoment {p k : ℕ} (Q : Measure (InstrumentalVariableObservation p k)) :
    Matrix (Fin k) (Fin k) ℝ := fun i j ↦ ∫ z, z.2.2 ^ 2 * z.2.1 i * z.2.1 j ∂Q

/-- Two-stage least-squares sample estimator under the structural equation. -/
def instrumentalVariableSampleEstimator {p k n : ℕ} (beta : EuclideanSpace ℝ (Fin p))
    (sample : Fin n → InstrumentalVariableObservation p k) : EuclideanSpace ℝ (Fin p) :=
  WithLp.toLp 2 (twoStageLeastSquares
    (fun i j ↦ (sample i).1 j) (fun i j ↦ (sample i).2.1 j)
    (fun i ↦ inner ℝ (sample i).1 beta + (sample i).2.2))

/-- Asymptotic two-stage least-squares covariance from the population instrument moments. -/
def instrumentalVariableCovariance {p k : ℕ}
    (Q : Measure (InstrumentalVariableObservation p k)) : Matrix (Fin p) (Fin p) ℝ :=
  let Z := instrumentSecondMoment Q
  let D := instrumentRegressorMoment Q
  let H := D.transpose * Z⁻¹ * D
  H⁻¹ * D.transpose * Z⁻¹ * instrumentErrorMoment Q * Z⁻¹ * D * H⁻¹

/-- GAPS 105.55: consistency of two-stage least squares under second-moment and rank conditions. -/
theorem tendstoInProbabilityConst_twoStageLeastSquares
    {Ω : Type*} [MeasurableSpace Ω] {p k : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Q : Measure (InstrumentalVariableObservation p k)) [IsProbabilityMeasure Q]
    (h2 : MemLp id 2 Q)
    (horthogonal : ∀ i : Fin k, (∫ z, z.2.1 i * z.2.2 ∂Q) = 0)
    (hZ : (instrumentSecondMoment Q).PosDef)
    (hH : ((instrumentRegressorMoment Q).transpose * (instrumentSecondMoment Q)⁻¹ *
      instrumentRegressorMoment Q).PosDef)
    (X : ℕ → Ω → InstrumentalVariableObservation p k)
    (hiid : IsIndependentIdenticallyDistributed P X Q) (beta : EuclideanSpace ℝ (Fin p)) :
    TendstoInProbabilityConst P
      (fun n ω ↦ instrumentalVariableSampleEstimator beta (fun i : Fin n ↦ X i.val ω)) beta := by
  sorry

/-- GAPS 105.55: heteroscedasticity-robust two-stage least-squares central limit theorem.
Square integrability of the instrument-error product is explicit, as required for its CLT. -/
theorem tendstoInDistribution_twoStageLeastSquares
    {Ω : Type*} [MeasurableSpace Ω] {p k : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Q : Measure (InstrumentalVariableObservation p k)) [IsProbabilityMeasure Q]
    (h2 : MemLp id 2 Q) (hD4 : MemLp Prod.fst 4 Q)
    (hZ4 : MemLp (fun z ↦ z.2.1) 4 Q)
    (hscore : MemLp (fun z ↦ z.2.2 • z.2.1) 2 Q)
    (horthogonal : ∀ i : Fin k, (∫ z, z.2.1 i * z.2.2 ∂Q) = 0)
    (hZ : (instrumentSecondMoment Q).PosDef)
    (hH : ((instrumentRegressorMoment Q).transpose * (instrumentSecondMoment Q)⁻¹ *
      instrumentRegressorMoment Q).PosDef)
    (X : ℕ → Ω → InstrumentalVariableObservation p k)
    (hiid : IsIndependentIdenticallyDistributed P X Q) (beta : EuclideanSpace ℝ (Fin p)) :
    TendstoInDistribution P (fun n ω ↦ Real.sqrt n •
      (instrumentalVariableSampleEstimator beta (fun i : Fin n ↦ X i.val ω) - beta))
      (multivariateGaussian 0 (instrumentalVariableCovariance Q)) := by
  sorry

end CKSD
