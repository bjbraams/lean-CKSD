module

public import CKSD.LinearModels.Basic
public import CKSD.Asymptotics.Basic
public import Mathlib.Probability.CramerWold
public import TauCeti.Probability.Distributions.Gaussian.Transforms
import CKSD.Asymptotics.ConvexRegression.Basic


/-!
# Quantile regression and two-stage least squares

The check loss `ρ_τ(u) = u (τ - 1{u < 0})`, quantile regression with fixed design, and the
two-stage least-squares estimator. Its limit theory in the linear instrumental-variable model is
in `CKSD.LinearModels.InstrumentalVariables`.

## Main definitions

* `CKSD.quantileCheckLoss`, `CKSD.quantileRegressionObjective`,
  `CKSD.IsQuantileRegressionEstimator`: the check loss, the objective
  `β ↦ ∑ᵢ ρ_τ(yᵢ - ⟪xᵢ, β⟫)` and its minimizers.
* `CKSD.expectedQuantileCheckLoss`: the risk `a ↦ E ρ_τ(Y - a)` of a location candidate.
* `CKSD.twoStageLeastSquares`: `β̂ = (Xᵀ P_Z X)⁻¹ Xᵀ P_Z y` with `P_Z = Z (Zᵀ Z)⁻¹ Zᵀ`.

## Main results

* `CKSD.minimizes_expected_quantile_check_loss_iff`: the minimizers of the expected check loss are
  exactly the `τ`-quantiles, `P(Y < a) ≤ τ ≤ P(Y ≤ a)`.
* `CKSD.tendsto_in_distribution_quantile_regression`: the fixed-design quantile-regression
  central limit theorem, `√n (β̂ - β) ⇒ N(0, τ(1-τ) D₁⁻¹ D₀ D₁⁻¹)`.

The quantile characterization uses Mathlib's continuity of measure (`Monotone.measure_iUnion`)
and the right continuity of `ProbabilityTheory.cdf`.

## References

* R. Koenker, *Quantile Regression*, Cambridge University Press, 2005, §4.2.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

/-- The quantile-regression check loss `ρ_τ(u) = u (τ - 1{u < 0})`; it vanishes at `u = 0`. -/
def quantileCheckLoss (τ u : ℝ) : ℝ := u * (τ - if u < 0 then 1 else 0)

/-- The fixed-design quantile-regression objective `β ↦ ∑ᵢ ρ_τ(yᵢ - ⟪xᵢ, β⟫)`. -/
def quantileRegressionObjective {n p : ℕ} (τ : ℝ) (x : Fin n → EuclideanSpace ℝ (Fin p))
    (y : Fin n → ℝ) (β : EuclideanSpace ℝ (Fin p)) : ℝ :=
  ∑ i, quantileCheckLoss τ (y i - inner ℝ (x i) β)

/-- A quantile-regression estimate minimizes the check-loss objective. -/
def IsQuantileRegressionEstimator {n p : ℕ} (τ : ℝ)
    (x : Fin n → EuclideanSpace ℝ (Fin p)) (y : Fin n → ℝ)
    (β : EuclideanSpace ℝ (Fin p)) : Prop :=
  ∀ b, quantileRegressionObjective τ x y β ≤ quantileRegressionObjective τ x y b

/-- The check loss is nonnegative for a level `τ ∈ [0, 1]`. -/
theorem quantile_check_loss_nonneg (τ u : ℝ) (hτ : τ ∈ Icc 0 1) :
    0 ≤ quantileCheckLoss τ u := by
  unfold quantileCheckLoss
  split_ifs with h
  · exact mul_nonneg_of_nonpos_of_nonpos h.le (by linarith [hτ.2])
  · exact mul_nonneg (le_of_not_gt h) (by simpa using hτ.1)

/-- The two-stage least-squares coefficient `(Xᵀ P_Z X)⁻¹ Xᵀ P_Z y`, with the instrument
projection `P_Z = Z (Zᵀ Z)⁻¹ Zᵀ` (matrix inverses are Mathlib's, zero for singular matrices). -/
def twoStageLeastSquares {n p k : ℕ} (X : Matrix (Fin n) (Fin p) ℝ)
    (Z : Matrix (Fin n) (Fin k) ℝ) (y : Fin n → ℝ) : Fin p → ℝ :=
  let P := Z * (Z.transpose * Z)⁻¹ * Z.transpose
  (X.transpose * P * X)⁻¹.mulVec ((X.transpose * P).mulVec y)

/-- Expected check loss for a scalar location candidate. -/
def expectedQuantileCheckLoss (P : Measure ℝ) (tau a : ℝ) : ℝ :=
  ∫ y, quantileCheckLoss tau (y - a) ∂P

/-- The check loss as a linear part plus a negative part. -/
theorem quantile_check_loss_eq_add_max (τ u : ℝ) :
    quantileCheckLoss τ u = τ * u + max (-u) 0 := by
  unfold quantileCheckLoss
  split_ifs with h
  · rw [max_eq_left (by linarith)]; ring
  · rw [max_eq_right (by linarith)]; ring

/-- Measurability of the check loss. -/
theorem measurable_quantile_check_loss (τ : ℝ) : Measurable (quantileCheckLoss τ) := by
  have : quantileCheckLoss τ = fun u ↦ τ * u + max (-u) 0 :=
    funext (quantile_check_loss_eq_add_max τ)
  rw [this]
  fun_prop

/-- The check loss at a translated location is integrable when the law has a first moment. -/
theorem integrable_quantile_check_loss_sub (P : Measure ℝ) [IsProbabilityMeasure P]
    (hint : Integrable id P) (τ a : ℝ) :
    Integrable (fun y ↦ quantileCheckLoss τ (y - a)) P := by
  refine Integrable.mono' (((hint.norm.add (integrable_const |a|))).const_mul (|τ| + 1)) ?_ ?_
  · exact ((measurable_quantile_check_loss τ).comp (measurable_id.sub_const a)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun y ↦ ?_
    rw [quantile_check_loss_eq_add_max, Real.norm_eq_abs]
    simp only [Pi.add_apply, id, Real.norm_eq_abs]
    have h1 : |y - a| ≤ |y| + |a| := abs_sub _ _
    have h2 : |τ * (y - a) + max (-(y - a)) 0| ≤ (|τ| + 1) * |y - a| := by
      calc |τ * (y - a) + max (-(y - a)) 0| ≤ |τ * (y - a)| + |max (-(y - a)) 0| :=
            abs_add_le _ _
        _ ≤ |τ| * |y - a| + |y - a| := by
            rw [abs_mul, abs_of_nonneg (le_max_right (-(y - a)) 0)]
            exact add_le_add le_rfl (max_le (neg_le_abs _) (abs_nonneg _))
        _ = (|τ| + 1) * |y - a| := by ring
    exact h2.trans (mul_le_mul_of_nonneg_left h1 (by positivity))

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

/-- Integrating a pointwise bound `g₁ ≤ g₂ + c (τ - 1_s)`. -/
theorem integral_le_integral_add_mul_sub_indicator (P : Measure ℝ) [IsProbabilityMeasure P]
    {g₁ g₂ : ℝ → ℝ} (hg₁ : Integrable g₁ P) (hg₂ : Integrable g₂ P) {s : Set ℝ}
    (hs : MeasurableSet s) (c τ : ℝ) (hle : ∀ y, g₁ y ≤ g₂ y + c * (τ - s.indicator 1 y)) :
    (∫ y, g₁ y ∂P) ≤ (∫ y, g₂ y ∂P) + c * (τ - P.real s) := by
  have h := integral_mono hg₁ (hg₂.add (integrable_add_mul_sub_indicator P hs c τ)) hle
  simp only [Pi.add_apply] at h
  rwa [integral_add_mul_sub_indicator P hg₂ hs] at h

/-- Integrating a pointwise bound `g₂ + c (τ - 1_s) ≤ g₁`. -/
theorem integral_add_mul_sub_indicator_le_integral (P : Measure ℝ) [IsProbabilityMeasure P]
    {g₁ g₂ : ℝ → ℝ} (hg₁ : Integrable g₁ P) (hg₂ : Integrable g₂ P) {s : Set ℝ}
    (hs : MeasurableSet s) (c τ : ℝ) (hle : ∀ y, g₂ y + c * (τ - s.indicator 1 y) ≤ g₁ y) :
    (∫ y, g₂ y ∂P) + c * (τ - P.real s) ≤ ∫ y, g₁ y ∂P := by
  have h := integral_mono (hg₂.add (integrable_add_mul_sub_indicator P hs c τ)) hg₁ hle
  simp only [Pi.add_apply] at h
  rwa [integral_add_mul_sub_indicator P hg₂ hs] at h

/-- GAPS 105.5: expected check-loss minimizers are precisely the distributional quantiles.
This characterization allows atoms; finite first moment makes every displayed risk finite. -/
theorem minimizes_expected_quantile_check_loss_iff (P : Measure ℝ) [IsProbabilityMeasure P]
    (hint : Integrable id P) (tau : ℝ) (htau : tau ∈ Ioo 0 1) (a : ℝ) :
    (∀ b, expectedQuantileCheckLoss P tau a ≤ expectedQuantileCheckLoss P tau b) ↔
      P.real (Iio a) ≤ tau ∧ tau ≤ P.real (Iic a) := by
  have hI := fun c ↦ integrable_quantile_check_loss_sub P hint tau c
  simp only [quantile_check_loss_eq_add_max] at hI
  unfold expectedQuantileCheckLoss
  simp only [quantile_check_loss_eq_add_max]
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
      have hint' := integral_le_integral_add_mul_sub_indicator P (hI (a - h)) (hI a)
        measurableSet_Iic h tau hle
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
      have hint' := integral_le_integral_add_mul_sub_indicator P (hI (a + h)) (hI a)
        measurableSet_Iic (-h) tau hle'
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
      have hint' := integral_add_mul_sub_indicator_le_integral P (hI b) (hI a)
        measurableSet_Iic (a - b) tau hle
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
      have hint' := integral_add_mul_sub_indicator_le_integral P (hI b) (hI a)
        measurableSet_Iio (a - b) tau hle
      nlinarith

/-- Normalized weighted design second-moment matrix. -/
def weightedDesignMoment {p : ℕ} (x : ℕ → EuclideanSpace ℝ (Fin p))
    (w : ℕ → ℝ) (n : ℕ) : Matrix (Fin p) (Fin p) ℝ :=
  fun j k ↦ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, w i * x i j * x i k

section QuantileRegressionAsymptotics

/-- The check loss is convex. -/
private lemma convex_on_quantile_check_loss (tau : ℝ) : ConvexOn ℝ univ (quantileCheckLoss tau) := by
  refine ⟨convex_univ, fun u _ v _ a b ha hb hab ↦ ?_⟩
  simp only [quantile_check_loss_eq_add_max, smul_eq_mul]
  have hu := le_max_left (-u) 0
  have hu' := le_max_right (-u) 0
  have hv := le_max_left (-v) 0
  have hv' := le_max_right (-v) 0
  have hmax : max (-(a * u + b * v)) 0 ≤ a * max (-u) 0 + b * max (-v) 0 :=
    max_le (by nlinarith) (by positivity)
  nlinarith

/-- The right derivative `ψ_τ(u) = τ - 1{u < 0}` of the check loss. -/
private lemma has_deriv_within_at_quantile_check_loss (tau u : ℝ) :
    HasDerivWithinAt (quantileCheckLoss tau) (tau - if u < 0 then 1 else 0) (Ioi u) u := by
  rcases lt_or_ge u 0 with hu | hu
  · have h : HasDerivAt (fun v ↦ (tau - 1) * v) (tau - 1) u := by
      simpa using (hasDerivAt_id u).const_mul (tau - 1)
    have h' : quantileCheckLoss tau =ᶠ[𝓝 u] fun v ↦ (tau - 1) * v := by
      filter_upwards [eventually_lt_nhds hu] with v hv
      simp [quantileCheckLoss, hv, mul_comm]
    simpa [hu] using (h.congr_of_eventuallyEq h').hasDerivWithinAt
  · have h : HasDerivWithinAt (fun v ↦ tau * v) tau (Ioi u) u := by
      simpa using ((hasDerivAt_id u).const_mul tau).hasDerivWithinAt
    have h' := h.congr (f₁ := quantileCheckLoss tau) (fun v (hv : u < v) ↦ by
      simp [quantileCheckLoss, not_lt.2 (hu.trans hv.le), mul_comm])
      (by simp [quantileCheckLoss, not_lt.2 hu, mul_comm])
    simpa [not_lt.2 hu] using h'

/-- A law with a density has no atoms. -/
private lemma null_singleton_class_of_has_density {Q : Measure ℝ} {f : ℝ → ℝ}
    (hf : HasDensity Q volume f) : NullSingletonClass Q :=
  ⟨fun c ↦ by
    rw [hf.2.2]
    exact withDensity_absolutelyContinuous _ _ (Real.volume_singleton)⟩

/-- `∫ (A + B 1{y < c}) dQ = A + B Q(y < c)`. -/
private lemma integral_add_mul_ite_sub_lt_zero (Q : Measure ℝ) [IsProbabilityMeasure Q]
    (A B c : ℝ) :
    ∫ y, (A + B * if y - c < 0 then 1 else 0) ∂Q = A + B * Q.real (Iio c) := by
  have h : (fun y : ℝ ↦ A + B * if y - c < 0 then (1 : ℝ) else 0) =
      fun y ↦ A + B * (Iio c).indicator 1 y := by
    ext y; simp [Set.indicator, sub_neg]
  have hI : Integrable ((Iio c).indicator (1 : ℝ → ℝ)) Q :=
    (integrable_const (1 : ℝ)).indicator measurableSet_Iio
  rw [h, integral_add (integrable_const _) (hI.const_mul B), integral_const_mul, integral_indicator_one measurableSet_Iio]
  simp

/-- Distribution function increments are integrals of the density:
`Q(y ≤ d) - Q(y ≤ c) = ∫_c^d f`. -/
private lemma measure_real_iic_sub_eq_integral {Q : Measure ℝ} [IsProbabilityMeasure Q]
    {f : ℝ → ℝ} (hf : HasDensity Q volume f) (c d : ℝ) :
    Q.real (Iic d) - Q.real (Iic c) = ∫ y in c..d, f y := by
  have key : ∀ c d : ℝ, c ≤ d → Q.real (Iic d) - Q.real (Iic c) = ∫ y in c..d, f y := by
    intro c d hcd
    have hIoc : Q.real (Ioc c d) = ∫ y in Ioc c d, f y := by
      rw [measureReal_def, hf.2.2, withDensity_apply _ measurableSet_Ioc,
        integral_eq_lintegral_of_nonneg_ae (ae_restrict_of_ae hf.2.1) hf.1.aestronglyMeasurable]
    rw [← Iic_union_Ioc_eq_Iic hcd, measureReal_union (Iic_disjoint_Ioc le_rfl) measurableSet_Ioc,
      intervalIntegral.integral_of_le hcd, hIoc]
    ring
  rcases le_total c d with h | h
  · exact key c d h
  · rw [intervalIntegral.integral_symm, ← key d c h]; ring

/-- A density bounded by `C` on `[c - r, c + r]` gives this interval mass at most `2 C r`. -/
private lemma measure_icc_le_of_has_density {Q : Measure ℝ} {f : ℝ → ℝ}
    (hf : HasDensity Q volume f) {c r C : ℝ} (hC : 0 ≤ C)
    (hfC : ∀ y ∈ Icc (c - r) (c + r), f y ≤ C) :
    Q (Icc (c - r) (c + r)) ≤ ENNReal.ofReal (C * (2 * r)) := by
  rw [hf.2.2, withDensity_apply _ measurableSet_Icc]
  calc ∫⁻ y in Icc (c - r) (c + r), ENNReal.ofReal (f y)
      ≤ ∫⁻ _ in Icc (c - r) (c + r), ENNReal.ofReal C :=
        setLIntegral_mono measurable_const fun y hy ↦ ENNReal.ofReal_le_ofReal (hfC y hy)
    _ = ENNReal.ofReal C * volume (Icc (c - r) (c + r)) := setLIntegral_const _ _
    _ = ENNReal.ofReal (C * (2 * r)) := by
        rw [Real.volume_Icc, ← ENNReal.ofReal_mul hC]; ring_nf

/-- `L²` continuity of the quantile score: if the density of `Y` is at most `C` near `θ`, then
`E (ψ_τ(Y - θ - t) - ψ_τ(Y - θ))² ≤ 2 C |t|`. -/
private lemma lintegral_sq_quantile_score_sub_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {Y : Ω → ℝ} (hY : Measurable Y) {Q : Measure ℝ} (hlaw : P.map Y = Q)
    {f : ℝ → ℝ} (hf : HasDensity Q volume f) (tau θ t C : ℝ) (hC : 0 ≤ C)
    (hfC : ∀ y ∈ Icc (θ - |t|) (θ + |t|), f y ≤ C) :
    ∫⁻ ω, ENNReal.ofReal (((tau - if Y ω - θ - t < 0 then 1 else 0) -
      (tau - if Y ω - θ < 0 then 1 else 0)) ^ 2) ∂P ≤ ENNReal.ofReal (C * (2 * |t|)) := by
  have hS : MeasurableSet (Y ⁻¹' Icc (θ - |t|) (θ + |t|)) := hY measurableSet_Icc
  calc _ ≤ ∫⁻ ω, (Y ⁻¹' Icc (θ - |t|) (θ + |t|)).indicator 1 ω ∂P := by
        refine lintegral_mono fun ω ↦ ?_
        by_cases hm : Y ω ∈ Icc (θ - |t|) (θ + |t|)
        · rw [indicator_of_mem (show ω ∈ Y ⁻¹' Icc (θ - |t|) (θ + |t|) from hm), Pi.one_apply,
            ENNReal.ofReal_le_one]
          split_ifs <;> norm_num
        · rw [indicator_of_notMem (show ω ∉ Y ⁻¹' Icc (θ - |t|) (θ + |t|) from hm)]
          simp only [mem_Icc, not_and_or, not_le] at hm
          have h1 := le_abs_self t
          have h2 := neg_abs_le t
          have h3 := abs_nonneg t
          split_ifs with ha hb hb <;> first | (exfalso; rcases hm with hm | hm <;> linarith) | simp
    _ = Q (Icc (θ - |t|) (θ + |t|)) := by
        rw [lintegral_indicator_one hS, ← hlaw, Measure.map_apply hY measurableSet_Icc]
    _ ≤ _ := measure_icc_le_of_has_density hf hC hfC

/-- Curvature of the expected check loss: if `Y` has density `f`, `τ`-quantile `θ`, and
`|f y - f θ| ≤ η` for `|y - θ| ≤ |t|`, then
`|E [ρ_τ(Y - θ - t) - ρ_τ(Y - θ) + t ψ_τ(Y - θ)] - f(θ) t² / 2| ≤ η t²`. -/
private lemma abs_integral_quantile_remainder_sub_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {Y : Ω → ℝ} (hY : Measurable Y)
    {Q : Measure ℝ} [IsProbabilityMeasure Q] (hlaw : P.map Y = Q) {f : ℝ → ℝ}
    (hf : HasDensity Q volume f) (tau θ : ℝ) (hθ : cdf Q θ = tau) {t η : ℝ} (hη : 0 ≤ η)
    (hfη : ∀ y, |y - θ| ≤ |t| → |f y - f θ| ≤ η) :
    |∫ ω, (quantileCheckLoss tau (Y ω - θ - t) - quantileCheckLoss tau (Y ω - θ) +
        t * (tau - if Y ω - θ < 0 then 1 else 0)) ∂P - f θ * t ^ 2 / 2| ≤ η * t ^ 2 := by
  have := null_singleton_class_of_has_density hf
  set ψ : ℝ → ℝ := fun u ↦ tau - if u < 0 then 1 else 0 with hψ
  have hψm : Measurable ψ :=
    measurable_const.sub (Measurable.ite (measurableSet_lt measurable_id measurable_const)
      measurable_const measurable_const)
  have hψb : ∀ u, ‖ψ u‖ ≤ |tau| + 1 := fun u ↦ by
    simp only [hψ, Real.norm_eq_abs]
    refine (abs_sub _ _).trans ?_
    split_ifs <;> simp
  have hρc : Continuous (quantileCheckLoss tau) :=
    continuousOn_univ.1 ((convex_on_quantile_check_loss tau).continuousOn isOpen_univ)
  have he : Measurable fun ω ↦ Y ω - θ := hY.sub_const θ
  have hmap : ∀ g : ℝ → ℝ, Measurable g →
      ∫ ω, g (Y ω - θ) ∂P = ∫ z, g z ∂(P.map fun ω ↦ Y ω - θ) := fun g hg ↦
    (integral_map he.aemeasurable hg.aestronglyMeasurable).symm
  have hint : ∀ s : ℝ, Integrable (fun z ↦ ψ (z - s)) (P.map fun ω ↦ Y ω - θ) := fun s ↦
    Integrable.of_bound ((hψm.comp (measurable_id.sub_const s)).aestronglyMeasurable) _
      (ae_of_all _ fun z ↦ hψb _)
  have hlawQ : ∀ g : ℝ → ℝ, Measurable g → ∫ ω, g (Y ω) ∂P = ∫ y, g y ∂Q := fun g hg ↦ by
    rw [← hlaw, integral_map hY.aemeasurable hg.aestronglyMeasurable]
  have hIio : ∀ c, Q.real (Iio c) = Q.real (Iic c) := fun c ↦ by
    simp [measureReal_def, measure_congr (Iio_ae_eq_Iic (μ := Q))]
  have hG : ∀ s, ∫ z, ψ (z - s) ∂(P.map fun ω ↦ Y ω - θ) = -∫ y in θ..θ + s, f y := by
    intro s
    have e1 : ∫ z, ψ (z - s) ∂(P.map fun ω ↦ Y ω - θ) = ∫ ω, ψ (Y ω - θ - s) ∂P :=
      (hmap (fun z ↦ ψ (z - s)) (hψm.comp (measurable_id.sub_const s))).symm
    have e2 : ∫ ω, ψ (Y ω - θ - s) ∂P = ∫ y, ψ (y - θ - s) ∂Q :=
      hlawQ (fun y ↦ ψ (y - θ - s)) (hψm.comp ((measurable_id.sub_const θ).sub_const s))
    have e3 : (fun y ↦ ψ (y - θ - s)) =
        fun y ↦ tau + (-1) * if y - (θ + s) < 0 then 1 else 0 := by
      funext y; simp only [hψ, sub_sub]; ring
    rw [e1, e2, e3, integral_add_mul_ite_sub_lt_zero, hIio,
      ← measure_real_iic_sub_eq_integral hf θ (θ + s), ← hθ, cdf_eq_real]
    ring
  have hψ0 : ∫ z, ψ z ∂(P.map fun ω ↦ Y ω - θ) = 0 := by
    simpa using hG 0
  have hfi : ∀ c d, IntervalIntegrable f volume c d := fun c d ↦
    (integrable_of_has_density _ _ hf).intervalIntegrable
  have key := abs_integral_remainder_sub_le (P.map fun ω ↦ Y ω - θ)
    (convex_on_quantile_check_loss tau) (fun u ↦ has_deriv_within_at_quantile_check_loss tau u) hψm
    (by simpa using hint 0) hψ0 (t := t) (γ := f θ) hη (fun s _ ↦ hint s) fun s hs ↦ by
      rw [hG s]
      have hsplit : (-∫ y in θ..θ + s, f y) + f θ * s = -∫ y in θ..θ + s, (f y - f θ) := by
        rw [intervalIntegral.integral_sub (hfi _ _) intervalIntegrable_const,
          intervalIntegral.integral_const, smul_eq_mul]
        ring
      rw [hsplit, abs_neg]
      have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := θ) (b := θ + s)
        (C := η) (f := fun y ↦ f y - f θ) fun y hy ↦ by
          rw [Real.norm_eq_abs]
          refine hfη y ?_
          refine le_trans ?_ hs
          rcases le_total 0 s with h0 | h0
          · rw [uIoc_of_le (by linarith)] at hy
            rw [abs_of_nonneg (by linarith [hy.1]), abs_of_nonneg h0]; linarith [hy.2]
          · rw [uIoc_of_ge (by linarith)] at hy
            rw [abs_of_nonpos (by linarith [hy.2]), abs_of_nonpos h0]; linarith [hy.1]
      rwa [Real.norm_eq_abs, add_sub_cancel_left] at hb
  have e : ∫ ω, (quantileCheckLoss tau (Y ω - θ - t) - quantileCheckLoss tau (Y ω - θ) +
      t * (tau - if Y ω - θ < 0 then 1 else 0)) ∂P =
      ∫ z, (quantileCheckLoss tau (z - t) - quantileCheckLoss tau z + t * ψ z)
        ∂(P.map fun ω ↦ Y ω - θ) :=
    hmap (fun z ↦ quantileCheckLoss tau (z - t) - quantileCheckLoss tau z + t * ψ z)
      (((hρc.measurable.comp (measurable_id.sub_const t)).sub hρc.measurable).add
        (hψm.const_mul t))
  rwa [e]

end QuantileRegressionAsymptotics

/-- GAPS 105.5: fixed-design quantile-regression central limit theorem. Let the responses
`Yᵢ` be independent with laws `Qᵢ` having densities `fᵢ`, with `τ`-quantile `⟪xᵢ, β⟫`, and
`fᵢ(⟪xᵢ, β⟫) ∈ [a, b]` with `a > 0`, the densities equicontinuous at these quantiles. If
`n⁻¹ ∑ xᵢ xᵢᵀ → D₀` (positive definite), `n⁻¹ ∑ fᵢ(⟪xᵢ, β⟫) xᵢ xᵢᵀ → D₁`, and
`maxᵢ ‖xᵢ‖ / √n → 0`, then every sequence of quantile-regression estimates satisfies
`√n (β̂ - β) ⇒ N(0, τ(1-τ) D₁⁻¹ D₀ D₁⁻¹)`. The limit `D₁ ≥ a D₀` is then positive definite.
No identical-distribution assumption is imposed on the responses. -/
theorem tendsto_in_distribution_quantile_regression
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (Q : ℕ → Measure ℝ) (f : ℕ → ℝ → ℝ)
    (hf : ∀ i, HasDensity (Q i) volume (f i))
    (Y : ℕ → Ω → ℝ) (hY : ∀ i, Measurable (Y i)) (hind : iIndepFun Y P)
    (hlaw : ∀ i, P.map (Y i) = Q i) (x : ℕ → EuclideanSpace ℝ (Fin p))
    (beta : EuclideanSpace ℝ (Fin p)) (tau : ℝ) (htau : tau ∈ Ioo 0 1)
    (hquantile : ∀ i, cdf (Q i) (inner ℝ (x i) beta) = tau)
    (a b : ℝ) (ha : 0 < a)
    (hbound : ∀ i, f i (inner ℝ (x i) beta) ∈ Icc a b)
    (hequi : ∀ eps > 0, ∃ delta > 0, ∀ i t,
      |t - inner ℝ (x i) beta| < delta → |f i t - f i (inner ℝ (x i) beta)| < eps)
    (D₀ D₁ : Matrix (Fin p) (Fin p) ℝ) (hD₀ : D₀.PosDef)
    (hdesign : Tendsto (weightedDesignMoment x (fun _ ↦ 1)) atTop (𝓝 D₀))
    (hweighted : Tendsto (weightedDesignMoment x (fun i ↦ f i (inner ℝ (x i) beta)))
      atTop (𝓝 D₁))
    (hleverage : Tendsto (fun n : ℕ ↦ sSup (range fun i : Fin n ↦ ‖x i.val‖) /
      Real.sqrt n) atTop (𝓝 0))
    (T : ℕ → Ω → EuclideanSpace ℝ (Fin p)) (hT : ∀ n, Measurable (T n))
    (hmin : ∀ n : ℕ, 0 < n → ∀ᵐ ω ∂P, IsQuantileRegressionEstimator tau
      (fun i : Fin n ↦ x i.val) (fun i : Fin n ↦ Y i.val ω) (T n ω)) :
    TendstoInDistribution (fun (n : ℕ) ω ↦ Real.sqrt n • (T n ω - beta)) atTop id (fun _ ↦ P)
      (multivariateGaussian 0 ((tau * (1 - tau)) • (D₁⁻¹ * D₀ * D₁⁻¹))) := by
  set θ : ℕ → ℝ := fun i ↦ inner ℝ (x i) beta with hθ_def
  set e : ℕ → Ω → ℝ := fun i ω ↦ Y i ω - θ i with he_def
  set ψ : ℝ → ℝ := fun u ↦ tau - if u < 0 then 1 else 0 with hψ
  have hQp : ∀ i, IsProbabilityMeasure (Q i) := fun i ↦ by rw [← hlaw i]; infer_instance
  have hite : ∀ c : ℝ, Measurable fun y : ℝ ↦ if y - c < 0 then (1 : ℝ) else 0 := fun c ↦
    Measurable.ite (measurableSet_lt (measurable_id.sub_const c) measurable_const)
      measurable_const measurable_const
  have hψm : Measurable ψ := by
    have h := hite 0
    simp only [sub_zero] at h
    exact measurable_const.sub h
  have hψb : ∀ u, ‖ψ u‖ ≤ 1 := fun u ↦ by
    simp only [hψ, Real.norm_eq_abs, abs_le]
    split_ifs <;> constructor <;> linarith [htau.1, htau.2]
  have he : ∀ i, Measurable (e i) := fun i ↦ (hY i).sub_const _
  have hinde : iIndepFun e P := hind.comp (fun i y ↦ y - θ i) fun i ↦ measurable_id.sub_const _
  have hIio : ∀ i, (Q i).real (Iio (θ i)) = tau := fun i ↦ by
    have := null_singleton_class_of_has_density (hf i)
    have h1 : (Q i).real (Iio (θ i)) = (Q i).real (Iic (θ i)) := by
      simp [measureReal_def, measure_congr (Iio_ae_eq_Iic (μ := Q i))]
    rw [h1, ← cdf_eq_real, hquantile i]
  have hmom : ∀ i (A B : ℝ), ∫ ω, (A + B * if e i ω < 0 then 1 else 0) ∂P = A + B * tau := by
    intro i A B
    calc ∫ ω, (A + B * if e i ω < 0 then 1 else 0) ∂P
        = ∫ y, (A + B * if y - θ i < 0 then 1 else 0) ∂(Q i) := by
          rw [← hlaw i]
          exact (integral_map (hY i).aemeasurable
            (f := fun y ↦ A + B * if y - θ i < 0 then 1 else 0)
            (measurable_const.add (measurable_const.mul (hite (θ i)))).aestronglyMeasurable).symm
      _ = A + B * tau := by rw [integral_add_mul_ite_sub_lt_zero, hIio i]
  have hψ0 : ∀ i, ∫ ω, ψ (e i ω) ∂P = 0 := fun i ↦ by
    calc ∫ ω, ψ (e i ω) ∂P = ∫ ω, (tau + (-1) * if e i ω < 0 then 1 else 0) ∂P :=
          integral_congr_ae (ae_of_all _ fun ω ↦ by simp only [hψ]; ring)
      _ = 0 := by rw [hmom]; ring
  have hψvar : ∀ i, ∫ ω, ψ (e i ω) ^ 2 ∂P = tau * (1 - tau) := fun i ↦ by
    calc ∫ ω, ψ (e i ω) ^ 2 ∂P = ∫ ω, (tau ^ 2 + (1 - 2 * tau) * if e i ω < 0 then 1 else 0) ∂P :=
          integral_congr_ae (ae_of_all _ fun ω ↦ by simp only [hψ]; split_ifs <;> ring)
      _ = tau * (1 - tau) := by rw [hmom]; ring
  have hψ2 : ∀ i, MemLp (fun ω ↦ ψ (e i ω)) 2 P := fun i ↦
    MemLp.of_bound ((hψm.comp (he i)).aestronglyMeasurable) 1 (ae_of_all _ fun ω ↦ hψb _)
  have hUI : ∀ η > 0, ∃ K : ℝ, ∀ i,
      ∫ ω, (if K < |ψ (e i ω)| then ψ (e i ω) ^ 2 else 0) ∂P ≤ η := fun η hη ↦ ⟨1, fun i ↦ by
    have h : ∀ ω, ¬ (1 < |ψ (e i ω)|) := fun ω ↦
      not_lt.2 (by simpa [Real.norm_eq_abs] using hψb (e i ω))
    simp [h, hη.le]⟩
  have hsub : ∀ u v, quantileCheckLoss tau u + ψ u * (v - u) ≤ quantileCheckLoss tau v :=
    fun u v ↦ add_mul_sub_le_of_convex_on_of_has_deriv_within_at (convex_on_quantile_check_loss tau)
      (has_deriv_within_at_quantile_check_loss tau u) v
  have hb0 : 0 ≤ b := (ha.le.trans (hbound 0).1).trans (hbound 0).2
  have hw : ∀ η > 0, ∃ δ > 0, ∀ i t, |t| < δ →
      ∫⁻ ω, ENNReal.ofReal ((ψ (e i ω - t) - ψ (e i ω)) ^ 2) ∂P ≤ ENNReal.ofReal η := by
    intro η hη
    obtain ⟨δe, hδe, hequi1⟩ := hequi 1 one_pos
    refine ⟨min δe (η / (2 * (b + 1))), lt_min hδe (by positivity), fun i t ht ↦ ?_⟩
    have hfC : ∀ y ∈ Icc (θ i - |t|) (θ i + |t|), f i y ≤ b + 1 := by
      intro y hy
      have hyt : |y - θ i| < δe :=
        (abs_sub_le_iff.2 ⟨by linarith [hy.2], by linarith [hy.1]⟩).trans_lt
          (ht.trans_le (min_le_left _ _))
      have h1 := hequi1 i y hyt
      have h2 := (hbound i).2
      rw [abs_lt] at h1
      linarith
    refine (lintegral_sq_quantile_score_sub_le P (hY i) (hlaw i) (hf i) tau (θ i) t (b + 1)
      (by linarith) hfC).trans (ENNReal.ofReal_le_ofReal ?_)
    have h := ht.trans_le (min_le_right _ _)
    rw [lt_div_iff₀ (by positivity)] at h
    nlinarith [abs_nonneg t]
  have hm : ∀ η > 0, ∃ δ > 0, ∀ i t, |t| < δ →
      |∫ ω, (quantileCheckLoss tau (e i ω - t) - quantileCheckLoss tau (e i ω) +
        t * ψ (e i ω)) ∂P - f i (θ i) * t ^ 2 / 2| ≤ η * t ^ 2 := by
    intro η hη
    obtain ⟨δe, hδe, hq⟩ := hequi η hη
    refine ⟨δe, hδe, fun i t ht ↦ ?_⟩
    have := hQp i
    exact abs_integral_quantile_remainder_sub_le P (hY i) (hlaw i) (hf i) tau (θ i)
      (hquantile i) hη.le fun y hy ↦ (hq i y (hy.trans_lt ht)).le
  have hdesign' : Tendsto (fun n : ℕ ↦ Matrix.of fun j k ↦ (n : ℝ)⁻¹ *
      ∑ i ∈ Finset.range n, x i j * x i k) atTop (𝓝 D₀) := by
    convert hdesign using 2 with n
    ext j k
    simp [weightedDesignMoment]
  have hD₁ : D₁.PosDef := by
    have hentry : ∀ (w : ℕ → ℝ) {M : Matrix (Fin p) (Fin p) ℝ},
        Tendsto (weightedDesignMoment x w) atTop (𝓝 M) → ∀ j k,
        Tendsto (fun n ↦ weightedDesignMoment x w n j k) atTop (𝓝 (M j k)) :=
      fun w M hM j k ↦ ((continuous_id.matrix_elem j k).tendsto M).comp hM
    have hsymm : D₁.IsHermitian := by
      rw [Matrix.isHermitian_iff_isSymm]
      ext j k
      refine tendsto_nhds_unique ((hentry _ hweighted k j).congr fun n ↦ ?_)
        (hentry _ hweighted j k)
      simp only [weightedDesignMoment]
      congr 1
      exact Finset.sum_congr rfl fun i _ ↦ by ring
    refine Matrix.posDef_iff_dotProduct_mulVec.2 ⟨hsymm, fun v hv ↦ ?_⟩
    simp only [star_trivial]
    have h1 := tendsto_sum_mul_sq_inv_sqrt_mul_inner x (fun i ↦ f i (θ i)) hweighted
      (WithLp.toLp 2 v)
    have h0 := tendsto_sum_mul_sq_inv_sqrt_mul_inner x (fun _ ↦ 1) hdesign (WithLp.toLp 2 v)
    have hle : ∀ n : ℕ, a * ∑ i ∈ Finset.range n,
        (fun _ ↦ (1 : ℝ)) i * ((Real.sqrt n)⁻¹ * inner ℝ (x i) (WithLp.toLp 2 v)) ^ 2 ≤
        ∑ i ∈ Finset.range n,
          f i (θ i) * ((Real.sqrt n)⁻¹ * inner ℝ (x i) (WithLp.toLp 2 v)) ^ 2 := fun n ↦ by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ ↦ by
        simp only [one_mul]
        exact mul_le_mul_of_nonneg_right (hbound i).1 (sq_nonneg _)
    have hlim := le_of_tendsto_of_tendsto' (h0.const_mul a) h1 hle
    have hpos := (Matrix.posDef_iff_dotProduct_mulVec.1 hD₀).2 hv
    simp only [star_trivial] at hpos
    nlinarith
  have hmin' : ∀ n : ℕ, 0 < n → ∀ᵐ ω ∂P, ∀ c, ∑ i ∈ Finset.range n,
      quantileCheckLoss tau (e i ω - inner ℝ (x i) (T n ω - beta)) ≤
        ∑ i ∈ Finset.range n, quantileCheckLoss tau (e i ω - inner ℝ (x i) (c - beta)) := by
    intro n hn
    filter_upwards [hmin n hn] with ω hω c
    have hobj : ∀ c, quantileRegressionObjective tau (fun i : Fin n ↦ x i.val)
        (fun i : Fin n ↦ Y i.val ω) c = ∑ i ∈ Finset.range n,
          quantileCheckLoss tau (e i ω - inner ℝ (x i) (c - beta)) := fun c ↦ by
      rw [Finset.sum_range]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      simp only [he_def, hθ_def, inner_sub_right]
      congr 1
      ring
    have := hω c
    rwa [hobj, hobj] at this
  exact (tendsto_in_measure_and_tendsto_in_distribution_convex_regression P e he hinde
    (convex_on_quantile_check_loss tau) hψm hsub hψ2 hψ0 hψvar hUI hw (fun i ↦ f i (θ i)) hm x
    hD₀.posSemidef hD₁ hdesign' hweighted hleverage beta T hT hmin').2.2

end CKSD
