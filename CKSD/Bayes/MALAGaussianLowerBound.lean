module

public import CKSD.Bayes.MALABasic
public import CKSD.Bayes.MALAGaussianRejection
public import CKSD.Bayes.GaussianGibbs
import Mathlib.MeasureTheory.Measure.TightNormed
/-!
# Gaussian MALA laws that remain far from equilibrium for a prescribed finite budget

For every positive physical step and finite budget, a sufficiently concentrated isotropic
Gaussian target makes typical proposals from an upper-quartile halfspace reject. A four-warm
law supported on that halfspace retains enough mass to stay at total variation distance at
least `3/8` throughout the budget. The target scale is chosen after the step and budget.

Mathlib tightness supplies a bounded high-probability Gaussian noise event and its Bernoulli
inequality controls retained mass over iterations. The Gaussian acceptance algebra and warm
halfspace law are imported from the preceding modules. Chewi, *Log-Concave Sampling*,
Theorem 7.6.5, printed page 210 (PDF page 222), gives the sampling context and a stronger
normalized-curvature result. This module supports the scale-adaptive scope of GAPS 104.47;
it does not prove one fixed normalized target is hard for every step size.
-/

public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology
namespace CKSD
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- A probability law on Euclidean space gives arbitrarily high mass to a bounded ball. -/
theorem exists_closed_ball_real_ge (μ : Measure E) [IsProbabilityMeasure μ]
    {r : ℝ} (hr : 0 < r) :
    ∃ R : ℝ, 0 ≤ R ∧ 1 - r ≤ μ.real (Metric.closedBall 0 R) := by
  have htight : IsTightMeasureSet {μ} := isTightMeasureSet_singleton
  have ht : Tendsto (fun R : ℝ ↦ μ (Metric.closedBall 0 R)ᶜ) atTop (𝓝 0) := by
    simpa only [iSup_singleton] using
      (tendsto_measure_compl_closedBall_of_isTightMeasureSet
        htight (0 : E))
  obtain ⟨R, hR⟩ := ENNReal.tendsto_atTop_zero.mp ht (ENNReal.ofReal r)
    (ENNReal.ofReal_pos.mpr hr)
  refine ⟨max R 0, le_max_right _ _, ?_⟩
  have hc : μ.real (Metric.closedBall 0 (max R 0))ᶜ ≤ r := by
    simpa only [Measure.real, ENNReal.toReal_ofReal hr.le] using
      ENNReal.toReal_mono (by simp) (hR (max R 0) (le_max_left _ _))
  have he := probReal_add_probReal_compl (μ := μ)
    (Metric.isClosed_closedBall.measurableSet : MeasurableSet (Metric.closedBall (0 : E) (max R 0)))
  linarith

/-- A large effective step makes a prescribed noise ball typical and its acceptance bound small. -/
theorem exists_large_gaussian_step {a r R : ℝ} (ha : 0 < a) (hr : 0 < r) :
    ∃ H : ℝ, 4 ≤ H ∧ R ≤ a * Real.sqrt H / 8 ∧ Real.exp ( - (H ^ 3 * a ^ 2 / 32)) < r := by
  have hrad : Tendsto (fun H : ℝ ↦ a * Real.sqrt H / 8) atTop atTop := by
    exact (Real.tendsto_sqrt_atTop.const_mul_atTop ha).atTop_div_const (by norm_num)
  have hpow : Tendsto (fun H : ℝ ↦ H ^ 3 * a ^ 2 / 32) atTop atTop := by
    exact ((tendsto_pow_atTop (by decide : (3 : ℕ)≠0)).atTop_mul_const
      (sq_pos_of_pos ha)).atTop_div_const (by norm_num)
  have hexp : Tendsto (fun H : ℝ ↦ Real.exp ( - (H ^ 3 * a ^ 2 / 32))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hpow)
  obtain ⟨H, ⟨hH, hR⟩, he⟩ := ((eventually_ge_atTop (4 : ℝ)).and
    (hrad.eventually (eventually_ge_atTop R))).and
      (hexp.eventually (gt_mem_nhds hr)) |>.exists
  exact ⟨H, hH, hR, he⟩

/-- Uniform small acceptance on a high-probability noise event gives a real retained-mass bound. -/
theorem mala_step_law_real_apply_ge_of_acceptance_lt
    (V : E → ℝ) (G : E → E) (h : ℝ) (hV : Measurable V) (hG : Measurable G)
    (μ : Measure E) [IsProbabilityMeasure μ] (A B : Set E) (hA : MeasurableSet A)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hB : 1 - r ≤ (stdGaussian E).real B)
    (hacc : ∀x∈A, ∀z∈B, malaAcceptance V G h x
      (x - h • G x + Real.sqrt (2 * h) • z) < r) :
    (1 - 2 * r) * μ.real A ≤ (malaStepLaw V G h μ).real A := by
  have hp := mala_step_law_apply_ge_of_acceptance_lt V G h hV hG μ A B hA r hr hacc
  have hm := is_probability_measure_mala_step_law V G h hV hG μ
  have hp' : μ.real A * (stdGaussian E).real B * (1 - r) ≤
      (malaStepLaw V G h μ).real A := by
    simpa only [Measure.real, ENNReal.toReal_mul, ENNReal.toReal_ofReal (sub_nonneg.mpr hr1)]
      using ENNReal.toReal_mono (measure_ne_top _ _) hp
  have hmul := mul_le_mul_of_nonneg_left hB (measureReal_nonneg (μ := μ) (s := A))
  have hmul' := mul_le_mul_of_nonneg_right hmul (sub_nonneg.mpr hr1)
  have hsq := mul_nonneg (sq_nonneg r) (measureReal_nonneg (μ := μ) (s := A))
  nlinarith

/-- The retained-mass bound iterates, and every lazy MALA iterate is a probability law. -/
theorem mala_step_law_iterate_real_apply_ge
    (V : E → ℝ) (G : E → E) (h : ℝ) (hV : Measurable V) (hG : Measurable G)
    (μ : Measure E) [IsProbabilityMeasure μ] (A B : Set E) (hA : MeasurableSet A)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1 / 2)
    (hB : 1 - r ≤ (stdGaussian E).real B)
    (hacc : ∀x∈A, ∀z∈B, malaAcceptance V G h x
      (x - h • G x + Real.sqrt (2 * h) • z) < r) (n : ℕ) :
    IsProbabilityMeasure ((malaStepLaw V G h)^[n] μ) ∧
      (1 - 2 * r) ^ n * μ.real A ≤ ((malaStepLaw V G h)^[n] μ).real A := by
  induction n with
  | zero =>
    simp only [Function.iterate_zero_apply, pow_zero, one_mul]
    exact ⟨inferInstance, le_rfl⟩
  | succ n ih =>
    have := ih.1
    have := is_probability_measure_mala_step_law V G h hV hG ((malaStepLaw V G h)^[n] μ)
    rw [Function.iterate_succ_apply']
    refine ⟨inferInstance, ?_⟩
    calc
      _ = (1 - 2 * r) * ((1 - 2 * r) ^ n * μ.real A) := by ring
      _ ≤ (1 - 2 * r) * ((malaStepLaw V G h)^[n] μ).real A :=
        mul_le_mul_of_nonneg_left ih.2 (by linarith)
      _ ≤ _ := mala_step_law_real_apply_ge_of_acceptance_lt V G h hV hG _ A B hA hr
        (by linarith) hB hacc

/-- A warm event retaining seven eighths of its mass stays far from a target
giving it at most half. -/
theorem mala_step_law_iterate_far_of_acceptance_lt
    (V : E → ℝ) (G : E → E) (h : ℝ) (hV : Measurable V) (hG : Measurable G)
    (μ π : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
    (A B : Set E) (hA : MeasurableSet A) (hμ : μ.real A = 1) (hπ : π.real A ≤ 1 / 2)
    (N : ℕ) {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1 / 2) (hrN : 2 * r * (N : ℝ) ≤ 1 / 8)
    (hB : 1 - r ≤ (stdGaussian E).real B)
    (hacc : ∀x∈A, ∀z∈B, malaAcceptance V G h x
      (x - h • G x + Real.sqrt (2 * h) • z) < r)
    (n : ℕ) (hn : n ≤ N) :
    3 / 8 ≤ totalVariationDistance ((malaStepLaw V G h)^[n] μ) π := by
  have hi := mala_step_law_iterate_real_apply_ge V G h hV hG μ A B hA hr hr1 hB hacc n
  have := hi.1
  have hp : 1 - 2 * r * (n : ℝ) ≤ (1 - 2 * r) ^ n := by
    convert one_add_mul_le_pow (by linarith : ( - 2 : ℝ) ≤ - 2 * r) n using 1 <;> ring
  have hm : 7 / 8 ≤ ((malaStepLaw V G h)^[n] μ).real A := by
    have hi2 := hi.2
    rw [hμ, mul_one] at hi2
    have hn' : (n : ℝ) ≤ N := by exact_mod_cast hn
    nlinarith [mul_le_mul_of_nonneg_left hn' (by positivity : 0 ≤ 2 * r)]
  have htv := abs_measure_real_sub_le_total_variation_distance
    ((malaStepLaw V G h)^[n] μ) π A hA
  have hab := le_abs_self (((malaStepLaw V G h)^[n] μ).real A - π.real A)
  linarith

/-- For any finite budget and positive step, a scaled Gaussian admits a four-warm law whose
lazy MALA iterates stay at total variation distance at least three eighths. -/
theorem exists_scaled_gaussian_mala_far {a h : ℝ} (ha : 0 < a)
    (hqa : (gaussianReal 0 1).real (Ioi a) = 1 / 4) (hh : 0 < h) (i : Fin d) (N : ℕ) :
    ∃ σ : ℝ, 0 < σ ∧ ∃ μ : Measure E, IsProbabilityMeasure μ ∧
      μ ≤ (4 : ℝ≥0∞) • gibbsMeasure (gaussianPrecisionPotential ((σ⁻¹) ^ 2)) ∧
      ∀n ≤ N, 3 / 8 ≤ totalVariationDistance
        ((malaStepLaw (gaussianPrecisionPotential ((σ⁻¹) ^ 2))
          (gaussianPrecisionGradient ((σ⁻¹) ^ 2)) h)^[n] μ)
        (gibbsMeasure (gaussianPrecisionPotential ((σ⁻¹) ^ 2))) := by
  let r : ℝ := 1 / (16 * ((N : ℝ) + 1))
  have hr : 0 < r := by dsimp [r]; positivity
  have hr1 : r ≤ 1 / 2 := by
    dsimp [r]
    apply (div_le_iff₀ (by positivity : 0 < 16 * ((N : ℝ) + 1))).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  have hrN : 2 * r * (N : ℝ) ≤ 1 / 8 := by
    dsimp [r]
    field_simp
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  obtain ⟨R, hR0, hR⟩ := exists_closed_ball_real_ge (stdGaussian E) hr
  obtain ⟨H, hH, hRH, hHe⟩ := exists_large_gaussian_step (R := R) ha hr
  have hH0 : 0 < H := by linarith
  let σ := Real.sqrt (h / H)
  have hσ : 0 < σ := Real.sqrt_pos.mpr (div_pos hh hH0)
  have hs2 : σ ^ 2 = h / H := Real.sq_sqrt (div_pos hh hH0).le
  have hscaled : h / σ ^ 2 = H := by rw [hs2]; field_simp
  obtain ⟨μ, hμ, hμwarm, hμA, hπA⟩ := exists_quadratic_gibbs_halfspace_warm_start hσ hqa i
  have := hμ
  let V : E → ℝ := gaussianPrecisionPotential ((σ⁻¹) ^ 2)
  let G : E → E := gaussianPrecisionGradient ((σ⁻¹) ^ 2)
  let A : Set E := {x | σ * a < x i}
  let B : Set E := Metric.closedBall 0 R
  have hπ : IsProbabilityMeasure (gibbsMeasure V) := by
    dsimp only [V]
    rw [gaussian_precision_potential_def, gibbs_measure_quadratic_eq_map_std_gaussian hσ]
    infer_instance
  have := hπ
  have hV : Measurable V := by
    dsimp only [V]
    rw [gaussian_precision_potential_def]
    fun_prop
  have hG : Measurable G := by
    dsimp only [G]
    rw [gaussian_precision_gradient_def]
    fun_prop
  have hAm : MeasurableSet A := by apply measurableSet_lt <;> fun_prop
  have hacc : ∀x∈A, ∀z∈B, malaAcceptance V G h x
      (x - h • G x + Real.sqrt (2 * h) • z) < r := by
    intro x hx z hz
    let u : E := σ⁻¹ • x
    have hxu : x = σ • u := by simp [u, smul_smul, ne_of_gt hσ]
    have hu : a ≤ ‖u‖ := by
      have hxcoord : σ * a < x i := hx
      have hiu : σ * a < σ * u i := by
        simpa only [hxu, PiLp.smul_apply, smul_eq_mul] using hxcoord
      have hai : a < u i := by nlinarith
      have hcoord := PiLp.norm_apply_le u i
      rw [Real.norm_eq_abs] at hcoord
      exact hai.le.trans ((le_abs_self _).trans hcoord)
    have hz' : ‖z‖ ≤ a * Real.sqrt H / 8 := by
      apply le_trans _ hRH
      have hzball : z ∈ Metric.closedBall 0 R := hz
      simpa only [Metric.mem_closedBall, dist_zero_right] using hzball
    dsimp only [V, G]
    rw [hxu, gaussian_proposal_rescale hσ hh, mala_acceptance_gaussian_rescale hσ hh, hscaled]
    exact (mala_acceptance_gaussian_one_le_exp hH ha.le u z hu hz').trans_lt hHe
  refine ⟨σ, hσ, μ, hμ, hμwarm, ?_⟩
  intro n hn
  apply mala_step_law_iterate_far_of_acceptance_lt V G h hV hG μ (gibbsMeasure V)
    A B hAm _ _ N hr.le hr1 hrN hR hacc n hn
  · simp only [Measure.real, A, hμA, ENNReal.toReal_one]
  · have hπreal : (gibbsMeasure V).real A = 1 / 4 := hπA
    linarith
end CKSD
