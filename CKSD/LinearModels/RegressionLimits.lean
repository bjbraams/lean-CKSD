module

public import CKSD.LinearModels.Causal
public import CKSD.Asymptotics.Basic

/-!
# Quantile-regression and instrumental-variable limits

Quantile regression uses independent, nonidentically distributed responses and fixed design.
Instrumental-variable experiments store the regressor, instrument, and structural error, with
outcomes obtained from the structural equation. The quantile characterization of check-loss
minimizers uses Mathlib's continuity of measure (`Monotone.measure_iUnion`) and the right
continuity of `ProbabilityTheory.cdf`. Sources: GAPS 105.5 and 105.55.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

/-- Expected check loss for a scalar location candidate. -/
def expectedQuantileCheckLoss (P : Measure ℝ) (tau a : ℝ) : ℝ :=
  ∫ y, quantileCheckLoss tau (y - a) ∂P

/-- The check loss as a linear part plus a negative part. -/
theorem quantileCheckLoss_eq_add_max (τ u : ℝ) :
    quantileCheckLoss τ u = τ * u + max (-u) 0 := by
  unfold quantileCheckLoss
  split_ifs with h
  · rw [max_eq_left (by linarith)]; ring
  · rw [max_eq_right (by linarith)]; ring

/-- Measurability of the check loss. -/
theorem measurable_quantileCheckLoss (τ : ℝ) : Measurable (quantileCheckLoss τ) := by
  have : quantileCheckLoss τ = fun u ↦ τ * u + max (-u) 0 :=
    funext (quantileCheckLoss_eq_add_max τ)
  rw [this]
  fun_prop

/-- The check loss at a translated location is integrable when the law has a first moment. -/
theorem integrable_quantileCheckLoss_sub (P : Measure ℝ) [IsProbabilityMeasure P]
    (hint : Integrable id P) (τ a : ℝ) (hτ : τ ∈ Icc (0 : ℝ) 1) :
    Integrable (fun y ↦ quantileCheckLoss τ (y - a)) P := by
  refine Integrable.mono' ((hint.norm.add (integrable_const |a|))) ?_ ?_
  · exact ((measurable_quantileCheckLoss τ).comp (measurable_id.sub_const a)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun y ↦ ?_
    rw [quantileCheckLoss_eq_add_max, Real.norm_eq_abs]
    simp only [Pi.add_apply, id, Real.norm_eq_abs]
    have h1 := abs_sub (y) a
    rcases le_total (y - a) 0 with h | h
    · rw [max_eq_left (by linarith), abs_le]
      constructor <;> nlinarith [abs_nonneg (y - a), abs_of_nonpos h, hτ.1, hτ.2]
    · rw [max_eq_right (by linarith), abs_le]
      constructor <;> nlinarith [abs_nonneg (y - a), abs_of_nonneg h, hτ.1, hτ.2]

/-- A constant multiple of a centred indicator is integrable under a probability measure. -/
theorem integrable_add_mul_sub_indicator (P : Measure ℝ) [IsProbabilityMeasure P]
    {s : Set ℝ} (hs : MeasurableSet s) (c τ : ℝ) :
    Integrable (fun y ↦ c * (τ - s.indicator 1 y)) P :=
  ((integrable_const τ).sub ((integrable_const 1).indicator hs)).const_mul c

/-- Integral of an integrable function plus a constant multiple of a centred indicator. -/
theorem integral_add_mul_sub_indicator (P : Measure ℝ) [IsProbabilityMeasure P]
    {g : ℝ → ℝ} (hg : Integrable g P) {s : Set ℝ} (hs : MeasurableSet s) (c τ : ℝ) :
    (∫ y, (g y + c * (τ - s.indicator 1 y)) ∂P) = (∫ y, g y ∂P) + c * (τ - P.real s) := by
  have h₁ : Integrable (fun y ↦ s.indicator (1 : ℝ → ℝ) y) P := (integrable_const 1).indicator hs
  rw [integral_add hg (integrable_add_mul_sub_indicator P hs c τ), integral_const_mul,
    integral_sub (integrable_const τ) h₁, integral_const, integral_indicator_one hs]
  simp

/-- GAPS 105.5: expected check-loss minimizers are precisely the distributional quantiles.
This characterization allows atoms; finite first moment makes every displayed risk finite. -/
theorem minimizes_expectedQuantileCheckLoss_iff (P : Measure ℝ) [IsProbabilityMeasure P]
    (hint : Integrable id P) (tau : ℝ) (htau : tau ∈ Ioo 0 1) (a : ℝ) :
    (∀ b, expectedQuantileCheckLoss P tau a ≤ expectedQuantileCheckLoss P tau b) ↔
      P.real (Iio a) ≤ tau ∧ tau ≤ P.real (Iic a) := by
  have hτ : tau ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self htau
  have hI := fun c ↦ integrable_quantileCheckLoss_sub P hint tau c hτ
  simp only [quantileCheckLoss_eq_add_max] at hI
  unfold expectedQuantileCheckLoss
  simp only [quantileCheckLoss_eq_add_max]
  constructor
  · intro hmin
    constructor
    · by_contra hlt
      push Not at hlt
      -- some `Iic (a - h)` already has mass above `tau`
      obtain ⟨n, hn⟩ : ∃ n : ℕ, tau < P.real (Iic (a - 1 / (n + 1))) := by
        have hmono : Monotone fun n : ℕ ↦ Iic (a - 1 / ((n : ℝ) + 1)) := by
          intro m n hmn
          apply Iic_subset_Iic.2
          have : (1 : ℝ) / (n + 1) ≤ 1 / (m + 1) := by
            apply one_div_le_one_div_of_le (by positivity)
            exact_mod_cast Nat.add_le_add_right hmn 1
          linarith
        have hU : (⋃ n : ℕ, Iic (a - 1 / ((n : ℝ) + 1))) = Iio a := by
          ext y
          simp only [mem_iUnion, mem_Iic, mem_Iio]
          constructor
          · rintro ⟨n, hn⟩
            have : (0 : ℝ) < 1 / (n + 1) := by positivity
            linarith
          · intro hy
            obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hy)
            exact ⟨n, by linarith⟩
        have h := hmono.measure_iUnion (μ := P)
        rw [hU] at h
        have hlt' : ENNReal.ofReal tau < P (Iio a) := by
          rw [← ofReal_measureReal (measure_ne_top P _)]
          exact (ENNReal.ofReal_lt_ofReal_iff (by linarith [htau.1, hlt])).2 hlt
        rw [h] at hlt'
        obtain ⟨n, hn⟩ := lt_iSup_iff.1 hlt'
        refine ⟨n, ?_⟩
        rw [measureReal_def]
        exact (ENNReal.ofReal_lt_iff_lt_toReal htau.1.le (measure_ne_top P _)).1 hn
      set h : ℝ := 1 / (n + 1) with hh
      have hpos : 0 < h := by positivity
      have hle : ∀ y, tau * (y - (a - h)) + max (-(y - (a - h))) 0 ≤
          tau * (y - a) + max (-(y - a)) 0 + h * (tau - (Iic (a - h)).indicator 1 y) := by
        intro y
        by_cases hy : y ∈ Iic (a - h)
        · rw [indicator_of_mem hy]
          simp only [mem_Iic] at hy
          simp only [Pi.one_apply]
          rw [max_eq_left (by linarith), max_eq_left (by linarith)]
          linarith
        · rw [indicator_of_notMem hy]
          simp only [mem_Iic, not_le] at hy
          rw [max_eq_right (by linarith)]
          have := le_max_right (-(y - a)) 0
          nlinarith
      have hint' := integral_mono (hI (a - h)) ((hI a).add
        (integrable_add_mul_sub_indicator P measurableSet_Iic h tau)) hle
      simp only [Pi.add_apply] at hint'
      rw [integral_add_mul_sub_indicator P (hI a) measurableSet_Iic] at hint'
      have := hmin (a - h)
      nlinarith
    · by_contra hlt
      push Not at hlt
      -- right continuity of the distribution function
      have hcont := (ProbabilityTheory.cdf P).right_continuous a
      rw [Metric.continuousWithinAt_iff] at hcont
      obtain ⟨δ, hδ, hδ'⟩ := hcont (tau - P.real (Iic a)) (by linarith)
      set h := δ / 2 with hh
      have hpos : 0 < h := by positivity
      have hFh : P.real (Iic (a + h)) < tau := by
        have := hδ' (x := a + h) (by simp only [mem_Ici]; linarith)
          (by rw [Real.dist_eq]; rw [abs_of_pos (by linarith)]; linarith)
        rw [ProbabilityTheory.cdf_eq_real, ProbabilityTheory.cdf_eq_real, Real.dist_eq] at this
        have := (abs_lt.1 this).2
        linarith
      have hle : ∀ y, tau * (y - (a + h)) + max (-(y - (a + h))) 0 ≤
          tau * (y - a) + max (-(y - a)) 0 + h * ((Iic (a + h)).indicator 1 y - tau) := by
        intro y
        by_cases hy : y ∈ Iic (a + h)
        · rw [indicator_of_mem hy]
          simp only [Pi.one_apply]
          have := le_max_left (-(y - a)) 0
          have := le_max_right (-(y - a)) 0
          rcases le_total (y - (a + h)) 0 with h1 | h1
          · rw [max_eq_left (by linarith)]; nlinarith
          · rw [max_eq_right (by linarith)]; nlinarith
        · rw [indicator_of_notMem hy]
          simp only [mem_Iic, not_le] at hy
          rw [max_eq_right (by linarith), max_eq_right (by linarith)]
          linarith
      have hle' : ∀ y, tau * (y - (a + h)) + max (-(y - (a + h))) 0 ≤
          tau * (y - a) + max (-(y - a)) 0 + (-h) * (tau - (Iic (a + h)).indicator 1 y) := by
        intro y; have := hle y; linarith
      have hint' := integral_mono (hI (a + h)) ((hI a).add
        (integrable_add_mul_sub_indicator P measurableSet_Iic (-h) tau)) hle'
      simp only [Pi.add_apply] at hint'
      rw [integral_add_mul_sub_indicator P (hI a) measurableSet_Iic] at hint'
      have := hmin (a + h)
      nlinarith
  · rintro ⟨h₁, h₂⟩ b
    rcases le_total a b with hab | hab
    · have hle : ∀ y, tau * (y - a) + max (-(y - a)) 0 + (a - b) * (tau - (Iic a).indicator 1 y) ≤
          tau * (y - b) + max (-(y - b)) 0 := by
        intro y
        by_cases hy : y ∈ Iic a
        · rw [indicator_of_mem hy]
          simp only [mem_Iic] at hy
          simp only [Pi.one_apply]
          rw [max_eq_left (by linarith), max_eq_left (by linarith)]
          linarith
        · rw [indicator_of_notMem hy]
          simp only [mem_Iic, not_le] at hy
          rw [max_eq_right (by linarith)]
          have := le_max_right (-(y - b)) 0
          nlinarith
      have hint' := integral_mono ((hI a).add
        (integrable_add_mul_sub_indicator P measurableSet_Iic (a - b) tau)) (hI b) hle
      simp only [Pi.add_apply] at hint'
      rw [integral_add_mul_sub_indicator P (hI a) measurableSet_Iic] at hint'
      nlinarith
    · have hle : ∀ y, tau * (y - a) + max (-(y - a)) 0 + (a - b) * (tau - (Iio a).indicator 1 y) ≤
          tau * (y - b) + max (-(y - b)) 0 := by
        intro y
        by_cases hy : y ∈ Iio a
        · rw [indicator_of_mem hy]
          simp only [mem_Iio] at hy
          simp only [Pi.one_apply]
          rw [max_eq_left (by linarith)]
          have := le_max_left (-(y - b)) 0
          nlinarith
        · rw [indicator_of_notMem hy]
          simp only [mem_Iio, not_lt] at hy
          rw [max_eq_right (by linarith)]
          have := le_max_right (-(y - b)) 0
          nlinarith
      have hint' := integral_mono ((hI a).add
        (integrable_add_mul_sub_indicator P measurableSet_Iio (a - b) tau)) (hI b) hle
      simp only [Pi.add_apply] at hint'
      rw [integral_add_mul_sub_indicator P (hI a) measurableSet_Iio] at hint'
      nlinarith

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
