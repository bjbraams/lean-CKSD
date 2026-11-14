module

public import CKSD.Inference.Model
public import CKSD.Inference.Density
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Probability.Moments.Covariance

/-!
# Analyticity and moments of the log partition function

For a natural exponential family with base measure `ν` on a finite-dimensional real inner product
space `E` and statistic the identity, the log partition function `A = logPartition ν id` is real
analytic on the interior of the natural parameter space; its gradient is the mean and its Hessian
the covariance of the law `exponentialFamilyMeasure ν id η`.

## Main results

* `CKSD.analyticOnNhd_logPartition`: `A` is analytic on the interior of the natural parameter
  space.
* `CKSD.hasFDerivAt_logPartition`: the derivative of `A` at an interior point `η` is
  `⟪∫ x dP_η, ·⟫`.
* `CKSD.fderiv_fderiv_logPartition_apply`: the second derivative of `A` at `η` is the
  covariance form of `P_η`.
* `CKSD.isProbabilityMeasure_exponentialFamilyMeasure`,
  `CKSD.integrable_id_exponentialFamilyMeasure`, `CKSD.memLp_inner_exponentialFamilyMeasure`: at
  interior points `P_η` is a probability measure with a first moment under which linear
  functionals are square integrable.

## Implementation notes

At an interior point `η`, `exp (⟪η, x⟫ + r ‖x‖)` is integrable for some `r > 0`; the partition
function then has the explicit power series `h ↦ ∑ₙ ∫ e^{⟪η, x⟫} ⟪x, h⟫ⁿ / n! dν` on the ball of
radius `r`, whose coefficients are Bochner integrals of continuous multilinear maps (Mathlib's
`hasSum_integral_of_dominated_convergence` and `HasFPowerSeriesOnBall`). The gradient and Hessian
are read off from the first coefficients of the series of `Z` and of
`ζ ↦ ∫ ⟪v, x⟫ e^{⟪ζ, x⟫} dν`, together with Mathlib's `covariance_eq_sub`.
-/
@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace CKSD

attribute [local instance] Classical.propDecidable

section LogPartition

open scoped Nat

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The norm is at most the sum of the absolute coordinates in an orthonormal basis. -/
private theorem norm_le_sum_abs_inner_basis {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (x : E) : ‖x‖ ≤ ∑ i, |inner ℝ (b i) x| := by
  conv_lhs => rw [← b.sum_repr' x]
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ ↦ ?_))
  rw [norm_smul, b.orthonormal.1 i, mul_one, Real.norm_eq_abs]

/-- At an interior point `η` of the natural parameter space, `exp (⟪η, x⟫ + r ‖x‖)` is integrable
for some `r > 0`; the bound uses the parameters `η ± K bᵢ` along an orthonormal basis. -/
private theorem exists_integrable_exp_inner_add_mul_norm [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (ν : Measure E) {η : E} (hη : naturalParameterSpace ν id ∈ 𝓝 η) :
    ∃ r : ℝ≥0, 0 < r ∧ Integrable (fun x ↦ Real.exp (inner ℝ η x + r * ‖x‖)) ν := by
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.1 hη
  set d := Module.finrank ℝ E
  let b := stdOrthonormalBasis ℝ E
  set K : ℝ := ρ / 2 with hK
  have hK0 : 0 < K := by positivity
  set r : ℝ := K / (d + 1) with hr
  have hr0 : 0 < r := by positivity
  have hmem : ∀ i (s : ℝ), |s| = 1 →
      Integrable (fun x ↦ Real.exp (inner ℝ (η + (s * K) • b i) x)) ν := fun i s hs ↦ hball (by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, b.orthonormal.1 i,
      mul_one, Real.norm_eq_abs, abs_mul, hs, one_mul, abs_of_pos hK0]
    linarith)
  have hη0 : Integrable (fun x ↦ Real.exp (inner ℝ η x)) ν := hball (Metric.mem_ball_self hρ)
  let S : E → ℝ := fun x ↦ ∑ i, (Real.exp (inner ℝ (η + (1 * K) • b i) x) +
      Real.exp (inner ℝ (η + (-1 * K) • b i) x))
  have hS : Integrable S ν := integrable_finsetSum _ fun i _ ↦
    (hmem i 1 (by simp)).add (hmem i (-1) (by simp))
  refine ⟨⟨r, hr0.le⟩, hr0, (hη0.add hS).mono' (by fun_prop) (ae_of_all _ fun x ↦ ?_)⟩

  rw [Pi.add_apply, Real.norm_of_nonneg (Real.exp_pos _).le]
  have hS0 : 0 ≤ S x := Finset.sum_nonneg fun i _ ↦ by positivity
  rcases isEmpty_or_nonempty (Fin d) with hd | hd
  · have hx : ‖x‖ = 0 :=
      le_antisymm (by simpa using norm_le_sum_abs_inner_basis b x) (norm_nonneg _)
    rw [hx, mul_zero, add_zero]
    linarith
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun i ↦ |inner ℝ (b i) x|)
    Finset.univ_nonempty
  have h3 : r * ‖x‖ ≤ K * |inner ℝ (b j) x| := by
    have h4 := (norm_le_sum_abs_inner_basis b x).trans
      (Finset.sum_le_card_nsmul _ _ _ fun i hi ↦ hj i hi)
    simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h4
    have hrd : r * d ≤ K := by
      rw [hr, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; nlinarith
    calc r * ‖x‖ ≤ r * (d * |inner ℝ (b j) x|) := mul_le_mul_of_nonneg_left h4 hr0.le
      _ = (r * d) * |inner ℝ (b j) x| := by ring
      _ ≤ K * |inner ℝ (b j) x| := mul_le_mul_of_nonneg_right hrd (abs_nonneg _)
  have hj1 : inner ℝ (η + (1 * K) • b j) x = inner ℝ η x + K * inner ℝ (b j) x := by
    rw [inner_add_left, inner_smul_left]; simp
  have hj2 : inner ℝ (η + (-1 * K) • b j) x = inner ℝ η x - K * inner ℝ (b j) x := by
    rw [inner_add_left, inner_smul_left]; simp; ring
  have hle : Real.exp (inner ℝ η x + r * ‖x‖) ≤ S x := by
    refine le_trans ?_ (Finset.single_le_sum (f := fun i ↦ Real.exp (inner ℝ (η + (1 * K) • b i) x)
      + Real.exp (inner ℝ (η + (-1 * K) • b i) x)) (fun i _ ↦ by positivity) (Finset.mem_univ j))
    simp only [hj1, hj2]
    rcases le_total 0 (inner ℝ (b j) x) with h | h
    · rw [abs_of_nonneg h] at h3
      have := Real.exp_le_exp.2 (by linarith : inner ℝ η x + r * ‖x‖ ≤
        inner ℝ η x + K * inner ℝ (b j) x)
      linarith [Real.exp_pos (inner ℝ η x - K * inner ℝ (b j) x)]
    · rw [abs_of_nonpos h] at h3
      have := Real.exp_le_exp.2 (by linarith : inner ℝ η x + r * ‖x‖ ≤
        inner ℝ η x - K * inner ℝ (b j) x)
      linarith [Real.exp_pos (inner ℝ η x + K * inner ℝ (b j) x)]
  change Real.exp (inner ℝ η x + r * ‖x‖) ≤ _
  linarith [Real.exp_pos (inner ℝ η x)]

/-- The continuous multilinear map `(h₁, …, hₙ) ↦ ∏ ⟪x, hᵢ⟫`. -/
private def innerProdML (n : ℕ) (x : E) : ContinuousMultilinearMap ℝ (fun _ : Fin n ↦ E) ℝ :=
  (ContinuousMultilinearMap.mkPiAlgebraFin ℝ n ℝ).compContinuousLinearMap fun _ ↦ innerSL ℝ x

/-- Evaluation: `innerProdML n x (h₁, …, hₙ) = ∏ ⟪x, hᵢ⟫`. -/
private theorem innerProdML_apply (n : ℕ) (x : E) (m : Fin n → E) :
    innerProdML n x m = ∏ i, inner ℝ x (m i) := by
  simp [innerProdML, ContinuousMultilinearMap.mkPiAlgebraFin_apply, List.prod_ofFn]

/-- The operator norm bound `‖innerProdML n x‖ ≤ ‖x‖ⁿ`. -/
private theorem norm_innerProdML_le (n : ℕ) (x : E) : ‖innerProdML n x‖ ≤ ‖x‖ ^ n := by
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  simp only [innerSL_apply_norm, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact mul_le_of_le_one_left (by positivity)
    (ContinuousMultilinearMap.norm_mkPiAlgebraFin_le.trans (by simp))

/-- `x ↦ innerProdML n x` is continuous. -/
private theorem continuous_innerProdML (n : ℕ) : Continuous (innerProdML (E := E) n) :=
  ((ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℝ
    (fun _ : Fin n ↦ E) (fun _ ↦ ℝ) ℝ).coe_continuous.comp
      (continuous_pi fun _ ↦ (innerSL ℝ (E := E)).continuous)).clm_apply continuous_const


omit [InnerProductSpace ℝ E] in
/-- `(r ‖x‖)ⁿ / n! ≤ exp (r ‖x‖)`, in the form `‖x‖ⁿ / n! ≤ r⁻ⁿ exp (r ‖x‖)`. -/
private theorem pow_norm_div_factorial_le (r : ℝ≥0) (hr : 0 < r) (x : E) (n : ℕ) :
    ‖x‖ ^ n / n ! ≤ ((r : ℝ) ^ n)⁻¹ * Real.exp (r * ‖x‖) := by
  have h := Real.pow_div_factorial_le_exp (r * ‖x‖) (by positivity) n
  rw [le_inv_mul_iff₀ (by positivity), ← mul_div_assoc, ← mul_pow]
  exact h

/-- The formal series of the moments `(h₁, …, hₙ) ↦ ∫ g(x) e^{⟪η, x⟫} ∏ ⟪x, hᵢ⟫ / n! dν`. -/
private def expMomentSeries [MeasurableSpace E] (ν : Measure E) (g : E → ℝ) (η : E) :
    FormalMultilinearSeries ℝ E ℝ :=
  fun n ↦ ∫ x, (g x * Real.exp (inner ℝ η x) / n !) • innerProdML n x ∂ν

section PowerSeries

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {ν : Measure E}
  {g : E → ℝ} {η : E} {r : ℝ≥0}

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The pointwise bound `|g| e^{⟪η,x⟫} ‖x‖ⁿ / n! ≤ r⁻ⁿ |g| e^{⟪η,x⟫ + r‖x‖}`. -/
private theorem abs_mul_exp_mul_pow_le (hr : 0 < r) (x : E) (n : ℕ) :
    |g x| * Real.exp (inner ℝ η x) * (‖x‖ ^ n / n !) ≤
      ((r : ℝ) ^ n)⁻¹ * (|g x| * Real.exp (inner ℝ η x + r * ‖x‖)) := by
  calc |g x| * Real.exp (inner ℝ η x) * (‖x‖ ^ n / n !) ≤
        |g x| * Real.exp (inner ℝ η x) * (((r : ℝ) ^ n)⁻¹ * Real.exp (r * ‖x‖)) := by
        gcongr; exact pow_norm_div_factorial_le r hr x n
    _ = ((r : ℝ) ^ n)⁻¹ * (|g x| * Real.exp (inner ℝ η x + r * ‖x‖)) := by
        rw [Real.exp_add]; ring

omit [FiniteDimensional ℝ E] in
/-- The moment integrands are integrable. -/
private theorem integrable_abs_mul_exp_mul_pow (hg : AEStronglyMeasurable g ν) (hr : 0 < r)
    (hint : Integrable (fun x ↦ |g x| * Real.exp (inner ℝ η x + r * ‖x‖)) ν) (n : ℕ) :
    Integrable (fun x ↦ |g x| * Real.exp (inner ℝ η x) * (‖x‖ ^ n / n !)) ν := by
  refine (hint.const_mul ((r : ℝ) ^ n)⁻¹).mono' ?_ (ae_of_all _ fun x ↦ ?_)
  · have : AEStronglyMeasurable (fun x ↦ |g x|) ν := by
      simpa only [Real.norm_eq_abs] using hg.norm
    exact (this.mul (by fun_prop : Continuous fun x : E ↦ Real.exp (inner ℝ η x)
      ).aestronglyMeasurable).mul (by fun_prop : Continuous fun x : E ↦ ‖x‖ ^ n / n !
      ).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (by positivity)]
    exact abs_mul_exp_mul_pow_le hr x n

/-- The terms of `expMomentSeries` are Bochner integrals of integrable functions. -/
private theorem integrable_expMoment (hg : AEStronglyMeasurable g ν) (hr : 0 < r)
    (hint : Integrable (fun x ↦ |g x| * Real.exp (inner ℝ η x + r * ‖x‖)) ν) (n : ℕ) :
    Integrable (fun x ↦ (g x * Real.exp (inner ℝ η x) / n !) • innerProdML n x) ν := by
  refine (integrable_abs_mul_exp_mul_pow hg hr hint n).mono' ?_ (ae_of_all _ fun x ↦ ?_)
  · exact ((continuous_id.div_const _).comp_aestronglyMeasurable
      (hg.mul (by fun_prop : Continuous fun x : E ↦ Real.exp (inner ℝ η x)
      ).aestronglyMeasurable)).smul (continuous_innerProdML n).aestronglyMeasurable
  · rw [norm_smul, Real.norm_eq_abs, abs_div, abs_mul, Real.abs_exp,
      abs_of_pos (by positivity : (0 : ℝ) < n !), div_mul_eq_mul_div, mul_div_assoc]
    gcongr
    exact norm_innerProdML_le n x

/-- Evaluation of the terms of `expMomentSeries`. -/
private theorem expMomentSeries_apply (hg : AEStronglyMeasurable g ν) (hr : 0 < r)
    (hint : Integrable (fun x ↦ |g x| * Real.exp (inner ℝ η x + r * ‖x‖)) ν) (n : ℕ)
    (m : Fin n → E) :
    expMomentSeries ν g η n m =
      ∫ x, g x * Real.exp (inner ℝ η x) / n ! * ∏ i, inner ℝ x (m i) ∂ν := by
  rw [expMomentSeries, ContinuousMultilinearMap.integral_apply (integrable_expMoment hg hr hint n)]
  simp only [smul_apply, innerProdML_apply, smul_eq_mul]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The exponential series in the form used for the moment series. -/
private theorem hasSum_abs_mul_exp_mul_pow (x : E) (s : ℝ) :
    HasSum (fun n : ℕ ↦ |g x| * Real.exp (inner ℝ η x) * ((s * ‖x‖) ^ n / n !))
      (|g x| * Real.exp (inner ℝ η x + s * ‖x‖)) := by
  rw [Real.exp_add, ← mul_assoc, Real.exp_eq_exp_ℝ]
  exact (NormedSpace.expSeries_div_hasSum_exp (s * ‖x‖)).mul_left _

/-- **Power series of exponential moments.** If `|g| e^{⟪η, x⟫ + r‖x‖}` is `ν`-integrable, then
`ζ ↦ ∫ g(x) e^{⟪ζ, x⟫} dν` has the power series `expMomentSeries ν g η` on the ball of radius `r`
about `η`. -/
private theorem hasFPowerSeriesOnBall_integral_mul_exp_inner (hg : AEStronglyMeasurable g ν)
    (hr : 0 < r) (hint : Integrable (fun x ↦ |g x| * Real.exp (inner ℝ η x + r * ‖x‖)) ν) :
    HasFPowerSeriesOnBall (fun ζ ↦ ∫ x, g x * Real.exp (inner ℝ ζ x) ∂ν)
      (expMomentSeries ν g η) η r := by
  have hgabs : AEStronglyMeasurable (fun x ↦ |g x|) ν := by
    simpa only [Real.norm_eq_abs] using hg.norm
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable
      (fun x ↦ |g x| * Real.exp (inner ℝ η x) * ((r * ‖x‖) ^ n / n !)) ν := fun n ↦
    (hgabs.mul (by fun_prop : Continuous fun x : E ↦ Real.exp (inner ℝ η x)
      ).aestronglyMeasurable).mul (by fun_prop : Continuous fun x : E ↦ ((r : ℝ) * ‖x‖) ^ n / n !
      ).aestronglyMeasurable
  have hint' : Integrable (fun x ↦ ∑' n : ℕ,
      |g x| * Real.exp (inner ℝ η x) * ((r * ‖x‖) ^ n / n !)) ν :=
    hint.congr (ae_of_all _ fun x ↦ (hasSum_abs_mul_exp_mul_pow x r).tsum_eq.symm)
  refine ⟨?_, by exact_mod_cast hr, fun {y} hy ↦ ?_⟩
  · refine FormalMultilinearSeries.le_radius_of_summable _ ?_
    have hB := hasSum_integral_of_dominated_convergence
      (fun n x ↦ |g x| * Real.exp (inner ℝ η x) * ((r * ‖x‖) ^ n / n !)) hmeas
      (fun n ↦ ae_of_all _ fun x ↦ le_of_eq (Real.norm_of_nonneg (by positivity)))
      (ae_of_all _ fun x ↦ (hasSum_abs_mul_exp_mul_pow x r).summable) hint'
      (ae_of_all _ fun x ↦ hasSum_abs_mul_exp_mul_pow (g := g) (η := η) x r)
    refine Summable.of_nonneg_of_le (fun n ↦ by positivity) (fun n ↦ ?_) hB.summable
    have hn := norm_integral_le_of_norm_le (integrable_abs_mul_exp_mul_pow hg hr hint n)
      (ae_of_all _ fun x ↦ show ‖(g x * Real.exp (inner ℝ η x) / n !) • innerProdML n x‖ ≤ _ by
        rw [norm_smul, Real.norm_eq_abs, abs_div, abs_mul, Real.abs_exp,
          abs_of_pos (by positivity : (0 : ℝ) < n !), div_mul_eq_mul_div, mul_div_assoc]
        gcongr
        exact norm_innerProdML_le n x)
    calc ‖expMomentSeries ν g η n‖ * (r : ℝ) ^ n ≤
          (∫ x, |g x| * Real.exp (inner ℝ η x) * (‖x‖ ^ n / n !) ∂ν) * (r : ℝ) ^ n := by
          gcongr; exact hn
      _ = _ := by
          rw [← integral_mul_const]
          congr 1; funext x; rw [mul_pow]; ring
  · have hy' : ‖y‖ < r := by
      simpa [Metric.mem_eball, edist_zero_right, enorm_eq_nnnorm] using hy
    simp only [expMomentSeries_apply hg hr hint, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
    refine hasSum_integral_of_dominated_convergence
      (fun n x ↦ |g x| * Real.exp (inner ℝ η x) * ((r * ‖x‖) ^ n / n !))
      (fun n ↦ ?_) (fun n ↦ ae_of_all _ fun x ↦ ?_)
      (ae_of_all _ fun x ↦ (hasSum_abs_mul_exp_mul_pow x r).summable) hint'
      (ae_of_all _ fun x ↦ ?_)
    · exact ((continuous_id.div_const _).comp_aestronglyMeasurable
        (hg.mul (by fun_prop : Continuous fun x : E ↦ Real.exp (inner ℝ η x)
        ).aestronglyMeasurable)).mul
        (by fun_prop : Continuous fun x : E ↦ inner ℝ x y ^ n).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul, abs_div, abs_mul, Real.abs_exp, abs_pow,
        abs_of_pos (by positivity : (0 : ℝ) < n !)]
      have hxy : |inner ℝ x y| ≤ r * ‖x‖ :=
        calc |inner ℝ x y| ≤ ‖x‖ * ‖y‖ := abs_real_inner_le_norm x y
          _ ≤ r * ‖x‖ := by rw [mul_comm]; gcongr
      calc _ = |g x| * Real.exp (inner ℝ η x) * (|inner ℝ x y| ^ n / n !) := by ring
        _ ≤ _ := by gcongr
    · have h := (NormedSpace.expSeries_div_hasSum_exp (inner ℝ x y)).mul_left
        (g x * Real.exp (inner ℝ η x))
      rw [← Real.exp_eq_exp_ℝ] at h
      convert h using 1
      · funext n; ring
      · rw [inner_add_left, Real.exp_add, real_inner_comm y x, mul_assoc]

/-- The derivative of `ζ ↦ ∫ g(x) e^{⟪ζ, x⟫} dν` at `η` is `h ↦ ∫ g(x) e^{⟪η, x⟫} ⟪h, x⟫ dν`. -/
private theorem exists_hasFDerivAt_integral_mul_exp_inner (hg : AEStronglyMeasurable g ν)
    (hr : 0 < r) (hint : Integrable (fun x ↦ |g x| * Real.exp (inner ℝ η x + r * ‖x‖)) ν) :
    ∃ Φ : E →L[ℝ] ℝ, HasFDerivAt (fun ζ ↦ ∫ x, g x * Real.exp (inner ℝ ζ x) ∂ν) Φ η ∧
      ∀ h, Φ h = ∫ x, g x * Real.exp (inner ℝ η x) * inner ℝ h x ∂ν := by
  refine ⟨_, (hasFPowerSeriesOnBall_integral_mul_exp_inner hg hr hint).hasFPowerSeriesAt
    |>.hasFDerivAt, fun h ↦ ?_⟩
  rw [continuousMultilinearCurryFin1_apply, expMomentSeries_apply hg hr hint]
  congr 1; funext x
  simp [real_inner_comm]

omit [FiniteDimensional ℝ E] in
/-- Linear weights: `|⟪v, x⟫| e^{⟪η, x⟫ + (r/2)‖x‖}` is integrable when `e^{⟪η, x⟫ + r‖x‖}` is. -/
private theorem integrable_abs_inner_mul_exp (hr : 0 < r)
    (hint : Integrable (fun x ↦ Real.exp (inner ℝ η x + r * ‖x‖)) ν) (v : E) :
    Integrable (fun x ↦ |inner ℝ v x| * Real.exp (inner ℝ η x + ((r / 2 : ℝ≥0) : ℝ) * ‖x‖)) ν := by
  have hr2 : 0 < r / 2 := by positivity
  refine (hint.const_mul (‖v‖ * ((r / 2 : ℝ≥0) : ℝ)⁻¹)).mono' (by fun_prop)
    (ae_of_all _ fun x ↦ ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  have h1 := pow_norm_div_factorial_le (r / 2) hr2 x 1
  simp only [pow_one, Nat.factorial_one, Nat.cast_one, div_one] at h1
  have h2 : |inner ℝ v x| ≤ ‖v‖ * ‖x‖ := abs_real_inner_le_norm v x
  have hsplit : Real.exp (inner ℝ η x + r * ‖x‖) = Real.exp (((r / 2 : ℝ≥0) : ℝ) * ‖x‖) *
      Real.exp (inner ℝ η x + ((r / 2 : ℝ≥0) : ℝ) * ‖x‖) := by
    rw [← Real.exp_add]; congr 1; push_cast; ring
  rw [hsplit]
  calc |inner ℝ v x| * Real.exp (inner ℝ η x + ((r / 2 : ℝ≥0) : ℝ) * ‖x‖) ≤
        (‖v‖ * (((r / 2 : ℝ≥0) : ℝ)⁻¹ * Real.exp (((r / 2 : ℝ≥0) : ℝ) * ‖x‖))) *
          Real.exp (inner ℝ η x + ((r / 2 : ℝ≥0) : ℝ) * ‖x‖) := by
        gcongr; exact h2.trans (by gcongr)
    _ = _ := by ring

omit [FiniteDimensional ℝ E] in
/-- Polynomial weights: `‖x‖ᵏ e^{⟪η, x⟫}` is integrable when `e^{⟪η, x⟫ + r‖x‖}` is. -/
private theorem integrable_pow_norm_mul_exp (hr : 0 < r)
    (hint : Integrable (fun x ↦ Real.exp (inner ℝ η x + r * ‖x‖)) ν) (k : ℕ) :
    Integrable (fun x ↦ ‖x‖ ^ k * Real.exp (inner ℝ η x)) ν := by
  have := (integrable_abs_mul_exp_mul_pow (g := fun _ ↦ (1 : ℝ)) aestronglyMeasurable_const hr
    (by simpa using hint) k).const_mul (k ! : ℝ)
  refine this.congr (ae_of_all _ fun x ↦ ?_)
  simp only [abs_one, one_mul]
  field_simp

end PowerSeries

end LogPartition

/-- Analyticity, gradient and Hessian of the log partition function (combined form). -/
private theorem logPartition_analytic_and_moments
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (ν : Measure E) (hne : ν ≠ 0) :
    AnalyticOnNhd ℝ (logPartition ν id) (interior (naturalParameterSpace ν id)) ∧
      ∀ η ∈ interior (naturalParameterSpace ν id),
        HasFDerivAt (logPartition ν id)
          (innerSL ℝ (∫ x, x ∂exponentialFamilyMeasure ν id η)) η ∧
        IsProbabilityMeasure (exponentialFamilyMeasure ν id η) ∧
        Integrable (fun x ↦ x) (exponentialFamilyMeasure ν id η) ∧
        (∀ w : E, MemLp (fun x ↦ inner ℝ w x) 2 (exponentialFamilyMeasure ν id η)) ∧
        ∀ u v : E, fderiv ℝ (fderiv ℝ (logPartition ν id)) η u v =
          cov[fun x ↦ inner ℝ u x, fun x ↦ inner ℝ v x;
            exponentialFamilyMeasure ν id η] := by
  set N := naturalParameterSpace ν id with hNdef
  have : NeZero ν := ⟨hne⟩
  set Z : E → ℝ := fun ζ ↦ ∫ x, Real.exp (inner ℝ ζ x) ∂ν with hZdef
  have hA : logPartition ν id = fun ζ ↦ Real.log (Z ζ) := rfl
  have hZF : Z = fun ζ ↦ ∫ x, (fun _ ↦ (1 : ℝ)) x * Real.exp (inner ℝ ζ x) ∂ν := by
    funext ζ; simp [Z]
  have hloc : ∀ ζ ∈ interior N, ∃ r : ℝ≥0, 0 < r ∧
      Integrable (fun x ↦ Real.exp (inner ℝ ζ x + r * ‖x‖)) ν :=
    fun ζ hζ ↦ exists_integrable_exp_inner_add_mul_norm ν (mem_interior_iff_mem_nhds.1 hζ)
  have hZpos : ∀ ζ ∈ interior N, 0 < Z ζ := fun ζ hζ ↦
    integral_exp_pos (f := fun x ↦ inner ℝ ζ x) (interior_subset hζ : ζ ∈ N)
  -- First derivatives of `Z` and of `log Z` at interior points.
  have hZd : ∀ ζ ∈ interior N, ∃ Φ : E →L[ℝ] ℝ, HasFDerivAt Z Φ ζ ∧
      ∀ h, Φ h = ∫ x, Real.exp (inner ℝ ζ x) * inner ℝ h x ∂ν := by
    intro ζ hζ
    obtain ⟨r, hr, hint⟩ := hloc ζ hζ
    obtain ⟨Φ, hΦ, hΦh⟩ := exists_hasFDerivAt_integral_mul_exp_inner
      (g := fun _ ↦ (1 : ℝ)) aestronglyMeasurable_const hr (by simpa using hint)
    exact ⟨Φ, hZF ▸ hΦ, fun h ↦ by simp [hΦh h]⟩
  have hAd : ∀ ζ ∈ interior N, ∃ Φ : E →L[ℝ] ℝ, HasFDerivAt (logPartition ν id)
      ((Z ζ)⁻¹ • Φ) ζ ∧ ∀ h, Φ h = ∫ x, Real.exp (inner ℝ ζ x) * inner ℝ h x ∂ν := by
    intro ζ hζ
    obtain ⟨Φ, hΦ, hΦh⟩ := hZd ζ hζ
    exact ⟨Φ, hA ▸ hΦ.log (hZpos ζ hζ).ne', hΦh⟩
  -- Analyticity.
  have hanalytic : AnalyticOnNhd ℝ (logPartition ν id) (interior N) := by
    intro ζ hζ
    obtain ⟨r, hr, hint⟩ := hloc ζ hζ
    have hZa : AnalyticAt ℝ Z ζ := (hZF ▸ hasFPowerSeriesOnBall_integral_mul_exp_inner
      (g := fun _ ↦ (1 : ℝ)) aestronglyMeasurable_const hr (by simpa using hint)).analyticAt
    rw [hA]
    exact (analyticAt_log (hZpos ζ hζ)).comp hZa
  refine ⟨hanalytic, fun η hη ↦ ?_⟩
  obtain ⟨r, hr, hint⟩ := hloc η hη
  have hηN : η ∈ N := interior_subset hη
  have hZη := hZpos η hη
  set P := exponentialFamilyMeasure ν id η with hPdef
  set dens : E → ℝ := fun x ↦ Real.exp (inner ℝ η x - logPartition ν id η) with hdensdef
  have hP : P = ν.withDensity fun x ↦ ENNReal.ofReal (dens x) := rfl
  have hdens : ∀ x, dens x = (Z η)⁻¹ * Real.exp (inner ℝ η x) := fun x ↦ by
    simp only [dens, Real.exp_sub, hA, Real.exp_log hZη]; ring
  have hdm : Measurable dens := by fun_prop
  have hd0 : ∀ x, 0 ≤ dens x := fun x ↦ (Real.exp_pos _).le
  have hintP : ∀ F : E → ℝ, ∫ x, F x ∂P = (Z η)⁻¹ * ∫ x, Real.exp (inner ℝ η x) * F x ∂ν :=
    fun F ↦ by
    rw [hP, integral_withDensity_ofReal ν hdm hd0, ← integral_const_mul]
    congr 1; funext x; rw [hdens, mul_assoc]
  have hiP : ∀ F : E → ℝ, Integrable (fun x ↦ Real.exp (inner ℝ η x) * F x) ν →
      Integrable F P := fun F hF ↦ by
    rw [hP, integrable_withDensity_ofReal_iff ν hdm hd0]
    exact (hF.const_mul (Z η)⁻¹).congr (ae_of_all _ fun x ↦ by simp only [hdens]; ring)
  have hn1 := integrable_pow_norm_mul_exp hr hint 1
  have hn2 := integrable_pow_norm_mul_exp hr hint 2
  have hidP : Integrable (fun x : E ↦ x) P := by
    rw [hP, integrable_withDensity_iff_integrable_smul' hdm.ennreal_ofReal
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
    refine (hn1.const_mul (Z η)⁻¹).mono'
      ((hdm.ennreal_ofReal.ennreal_toReal.smul measurable_id).aestronglyMeasurable)
      (ae_of_all _ fun x ↦ ?_)
    rw [norm_smul, ENNReal.toReal_ofReal (hd0 x), Real.norm_of_nonneg (hd0 x), hdens]
    exact le_of_eq (by ring)
  -- The first derivative.
  obtain ⟨Φ, hΦ, hΦh⟩ := hAd η hη
  have hmean : (Z η)⁻¹ • Φ = innerSL ℝ (∫ x, x ∂P) := by
    ext h
    rw [smul_apply, hΦh, innerSL_apply_apply, real_inner_comm,
      ← integral_inner hidP h, hintP, smul_eq_mul]
  -- The law is a probability measure with square-integrable linear functionals.
  have hprob : IsProbabilityMeasure P := by
    constructor
    have hdi : Integrable dens ν :=
      ((hηN : Integrable (fun x ↦ Real.exp (inner ℝ η x)) ν).const_mul (Z η)⁻¹).congr
        (ae_of_all _ fun x ↦ (hdens x).symm)
    rw [hP, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hdi (ae_of_all _ hd0)]
    simp_rw [hdens]
    rw [integral_const_mul, inv_mul_cancel₀ hZη.ne', ENNReal.ofReal_one]
  have hL2 : ∀ w : E, MemLp (fun x ↦ inner ℝ w x) 2 P := fun w ↦ by
    have hmeas : AEStronglyMeasurable (fun x ↦ inner ℝ w x) P :=
      (by fun_prop : Continuous fun x : E ↦ inner ℝ w x).aestronglyMeasurable
    refine (memLp_two_iff_integrable_sq hmeas).2 (hiP _ ?_)
    refine (hn2.const_mul (‖w‖ ^ 2)).mono' (by fun_prop) (ae_of_all _ fun x ↦ ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    have h1 : inner ℝ w x ^ 2 ≤ (‖w‖ * ‖x‖) ^ 2 := by
      rw [← sq_abs]; gcongr; exact abs_real_inner_le_norm w x
    calc Real.exp (inner ℝ η x) * inner ℝ w x ^ 2 ≤
          Real.exp (inner ℝ η x) * (‖w‖ * ‖x‖) ^ 2 := by gcongr
      _ = _ := by ring
  refine ⟨hmean ▸ hΦ, hprob, hidP, hL2, fun u v ↦ ?_⟩
  -- The second derivative, from the quotient `G_v / Z` with `G_v ζ = ∫ ⟪v, x⟫ e^{⟪ζ, x⟫} dν`.
  obtain ⟨Ψ, hΨ, hΨh⟩ := exists_hasFDerivAt_integral_mul_exp_inner (g := fun x ↦ inner ℝ v x)
    (by fun_prop : Continuous fun x : E ↦ inner ℝ v x).aestronglyMeasurable
    (r := r / 2) (by positivity) (integrable_abs_inner_mul_exp hr hint v)
  obtain ⟨ΦZ, hΦZ, hΦZh⟩ := hZd η hη
  have hinvZ : HasFDerivAt (fun ζ ↦ (Z ζ)⁻¹) ((-(Z η ^ 2)⁻¹) • ΦZ) η :=
    (hasDerivAt_inv hZη.ne').comp_hasFDerivAt η hΦZ
  have hprod := hinvZ.mul hΨ
  have heq : (fun ζ ↦ fderiv ℝ (logPartition ν id) ζ v) =ᶠ[𝓝 η]
      ((fun ζ ↦ (Z ζ)⁻¹) * fun ζ ↦ ∫ x, inner ℝ v x * Real.exp (inner ℝ ζ x) ∂ν) := by
    filter_upwards [isOpen_interior.mem_nhds hη] with ζ hζ
    obtain ⟨Φ', hΦ', hΦ'h⟩ := hAd ζ hζ
    rw [hΦ'.fderiv, smul_apply, hΦ'h, Pi.mul_apply, smul_eq_mul]
    congr 2; funext x; ring
  have hD2 : HasFDerivAt (fderiv ℝ (logPartition ν id))
      (fderiv ℝ (fderiv ℝ (logPartition ν id)) η) η :=
    ((hanalytic η hη).fderiv).differentiableAt.hasFDerivAt
  have huniq := (hD2.clm_apply (hasFDerivAt_const v η)).unique
    (hprod.congr_of_eventuallyEq heq)
  have key := congrArg (fun L : E →L[ℝ] ℝ ↦ L u) huniq
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    zero_apply, map_zero, zero_add, ContinuousLinearMap.flip_apply,
    smul_apply, smul_eq_mul, hΨh, hΦZh] at key
  rw [covariance_eq_sub (hL2 u) (hL2 v), hintP, hintP, hintP, key]
  have e1 : ∫ x, inner ℝ v x * Real.exp (inner ℝ η x) * inner ℝ u x ∂ν =
      ∫ x, Real.exp (inner ℝ η x) * ((fun x ↦ inner ℝ u x) * fun x ↦ inner ℝ v x) x ∂ν := by
    congr 1; funext x; simp only [Pi.mul_apply]; ring
  have e2 : ∫ x, inner ℝ v x * Real.exp (inner ℝ η x) ∂ν =
      ∫ x, Real.exp (inner ℝ η x) * inner ℝ v x ∂ν := by
    congr 1; funext x; ring
  rw [e1, e2]
  field_simp
  ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The log partition function `η ↦ log ∫ e^{⟪η, x⟫} dν` of a nonzero measure on a
finite-dimensional real inner product space is real analytic on the interior of the natural
parameter space. -/
theorem analyticOnNhd_logPartition (ν : Measure E) (hne : ν ≠ 0) :
    AnalyticOnNhd ℝ (logPartition ν id) (interior (naturalParameterSpace ν id)) :=
  (logPartition_analytic_and_moments ν hne).1

/-- At an interior point `η` of the natural parameter space, the derivative of the log partition
function is `⟪m, ·⟫`, where `m = ∫ x dP_η` is the mean of the law `P_η`. -/
theorem hasFDerivAt_logPartition (ν : Measure E) (hne : ν ≠ 0) {η : E}
    (hη : η ∈ interior (naturalParameterSpace ν id)) :
    HasFDerivAt (logPartition ν id) (innerSL ℝ (∫ x, x ∂exponentialFamilyMeasure ν id η)) η :=
  ((logPartition_analytic_and_moments ν hne).2 η hη).1

/-- At an interior point `η` of the natural parameter space, the second derivative of the log
partition function is the covariance form `(u, v) ↦ Cov_{P_η}(⟪u, X⟫, ⟪v, X⟫)`. -/
theorem fderiv_fderiv_logPartition_apply (ν : Measure E) (hne : ν ≠ 0) {η : E}
    (hη : η ∈ interior (naturalParameterSpace ν id)) (u v : E) :
    fderiv ℝ (fderiv ℝ (logPartition ν id)) η u v =
      cov[fun x ↦ inner ℝ u x, fun x ↦ inner ℝ v x; exponentialFamilyMeasure ν id η] :=
  ((logPartition_analytic_and_moments ν hne).2 η hη).2.2.2.2 u v

/-- At an interior point `η` of the natural parameter space, `P_η` is a probability measure. -/
theorem isProbabilityMeasure_exponentialFamilyMeasure (ν : Measure E) (hne : ν ≠ 0) {η : E}
    (hη : η ∈ interior (naturalParameterSpace ν id)) :
    IsProbabilityMeasure (exponentialFamilyMeasure ν id η) :=
  ((logPartition_analytic_and_moments ν hne).2 η hη).2.1

/-- At an interior point `η` of the natural parameter space, `P_η` has a first moment. -/
theorem integrable_id_exponentialFamilyMeasure (ν : Measure E) (hne : ν ≠ 0) {η : E}
    (hη : η ∈ interior (naturalParameterSpace ν id)) :
    Integrable (fun x ↦ x) (exponentialFamilyMeasure ν id η) :=
  ((logPartition_analytic_and_moments ν hne).2 η hη).2.2.1

/-- At an interior point `η` of the natural parameter space, every linear functional `⟪w, ·⟫` is
square integrable under `P_η`. -/
theorem memLp_inner_exponentialFamilyMeasure (ν : Measure E) (hne : ν ≠ 0) {η : E}
    (hη : η ∈ interior (naturalParameterSpace ν id)) (w : E) :
    MemLp (fun x ↦ inner ℝ w x) 2 (exponentialFamilyMeasure ν id η) :=
  ((logPartition_analytic_and_moments ν hne).2 η hη).2.2.2.1 w

end CKSD
