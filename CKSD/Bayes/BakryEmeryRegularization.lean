module
public import CKSD.Bayes.BakryEmeryInterpolation
public import CKSD.Bayes.BoundedPerturbation
public import TauCeti.Analysis.Calculus.BumpFunction.LipschitzCutoff
public import TauCeti.Probability.Density
/-!
# Compactly supported tests in the Bakry–Émery inequality

The Prékopa–Leindler entropy estimate is normalized to the Gibbs law. Applying it to
`log (ε + f²)` for smooth compactly supported `f`, then sending `ε` to zero, gives the sharp
logarithmic Sobolev bound for these tests. Compact support controls the derivatives of the
regularized logarithm. The temporal interpolation does not change the sharp constant.

Mathlib supplies smooth compact-support derivative bounds and dominated convergence;
TauCeti supplies real-density integration. The interpolation estimate is local project code.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators ContDiff
namespace CKSD

/-- A Lipschitz derivative gives a global quadratic upper Taylor bound. -/
theorem quadratic_upper_bound_of_lipschitz_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : E → ℝ) (hg : Differentiable ℝ g) {L : ℝ≥0}
    (hL : LipschitzWith L (fderiv ℝ g)) (x z : E) :
    g x ≤ g z + fderiv ℝ g z (x - z) + (L : ℝ) * ‖x - z‖ ^ 2 := by
  let F : E → ℝ := fun y ↦ g y - fderiv ℝ g z (y - z)
  have hFd (y : E) : HasFDerivAt F (fderiv ℝ g y - fderiv ℝ g z) y := by
    exact (hg y).hasFDerivAt.sub (((fderiv ℝ g z).hasFDerivAt.comp y
      ((hasFDerivAt_id y).sub_const z)))
  have hbd (y : E) (hy : y ∈ Metric.closedBall z ‖x - z‖) :
      ‖fderiv ℝ g y - fderiv ℝ g z‖ ≤ (L : ℝ) * ‖x - z‖ := by
    refine (hL.norm_sub_le y z).trans ?_
    exact mul_le_mul_of_nonneg_left (mem_closedBall_iff_norm.1 hy) L.coe_nonneg
  have h := (convex_closedBall z ‖x - z‖).norm_image_sub_le_of_norm_hasFDerivWithin_le (x := z) (y := x)
    (fun y _ ↦ (hFd y).hasFDerivWithinAt) hbd
    (Metric.mem_closedBall_self (norm_nonneg _))
    (mem_closedBall_iff_norm.2 le_rfl)
  change ‖F x - F z‖ ≤ (L : ℝ) * ‖x - z‖ * ‖x - z‖ at h
  have hle := (le_abs_self (F x - F z)).trans (by simpa only [Real.norm_eq_abs] using h)
  dsimp [F] at hle
  simp only [sub_self, map_zero, sub_zero] at hle
  nlinarith

/-- Integration against the Gibbs law is normalized weighted Lebesgue integration. -/
theorem integral_gibbsMeasure {d : ℕ} (V : EuclideanSpace ℝ (Fin d) → ℝ)
    (hVm : Measurable V) (hV : Integrable (fun x ↦ Real.exp (-V x)))
    (f : EuclideanSpace ℝ (Fin d) → ℝ) :
    (∫ x, f x ∂gibbsMeasure V) = (∫ x, Real.exp (-V x) * f x) / ∫ x, Real.exp (-V x) := by
  have hZ : 0 < ∫ x, Real.exp (-V x) := integral_exp_pos hV
  rw [gibbsMeasure, TauCeti.Probability.integral_withDensity_ofReal
    (ρ := fun x ↦ Real.exp (-V x) / ∫ x, Real.exp (-V x)) ((hVm.neg.exp.div_const _).aemeasurable)
    (ae_of_all _ fun x ↦ div_nonneg (Real.exp_pos _).le hZ.le)]
  simp only [smul_eq_mul]
  rw [← integral_div]
  congr 1
  funext x
  ring

/-- Bounded logarithmic perturbations satisfy the Gibbs entropy-energy bound with sharp constant. -/
theorem entropy_gibbs_exponential_le {d : ℕ}
    (V : EuclideanSpace ℝ (Fin d) → ℝ)
    (G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (m : ℝ) (hm0 : 0 < m)
    (hG : ∀ x, HasGradientAt V (G x) x) (hm : IsStronglyMonotoneGradient G m)
    (g : EuclideanSpace ℝ (Fin d) → ℝ)
    (Dg : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (H : ℝ)
    (hg : ∀ x z, g x ≤ g z + Dg z (x - z) + H / 2 * ‖x - z‖ ^ 2)
    (hgm : Measurable g) (hDgm : Measurable fun x ↦ ‖Dg x‖)
    {M : ℝ} (hM : 0 ≤ M) (hgM : ∀ x, |g x| ≤ M) (hDgM : ∀ x, ‖Dg x‖ ^ 2 ≤ M)
    (hZ : Integrable (fun x ↦ Real.exp (-V x))) :
    (gibbsMeasure V).entropy (fun x ↦ Real.exp (g x)) ≤
      (1 / (2 * m)) * ∫ x, Real.exp (g x) * ‖Dg x‖ ^ 2 ∂gibbsMeasure V := by
  have hVm : Measurable V :=
    (continuous_iff_continuousAt.2 fun x ↦ (hG x).hasFDerivAt.continuousAt).measurable
  have hI : Integrable (fun x ↦ Real.exp (g x - V x)) := by
    refine (hZ.const_mul (Real.exp M)).mono' ((hgm.sub hVm).exp.aestronglyMeasurable) (ae_of_all _ fun x ↦ ?_)
    rw [Real.norm_eq_abs, Real.abs_exp, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith [(le_abs_self (g x)).trans (hgM x)])
  have hA : 0 < ∫ x, Real.exp (g x - V x) := integral_exp_pos hI
  have hZ0 : 0 < ∫ x, Real.exp (-V x) := integral_exp_pos hZ
  have hmain := entropy_exponential_le_of_quadratic_upper_bound V G m hm0 hG hm g Dg H hg hgm hDgm
    hM hgM hDgM hZ
  have hmean : (∫ x, Real.exp (g x) ∂gibbsMeasure V) =
      (∫ x, Real.exp (g x - V x)) / ∫ x, Real.exp (-V x) := by
    rw [integral_gibbsMeasure V hVm hZ]
    congr 1
    apply integral_congr_ae
    exact ae_of_all _ fun x ↦ by dsimp only; rw [← Real.exp_add]; congr 1; ring
  have hlog : (∫ x, Real.exp (g x) * Real.log (Real.exp (g x)) ∂gibbsMeasure V) =
      (∫ x, Real.exp (g x - V x) * g x) / ∫ x, Real.exp (-V x) := by
    rw [integral_gibbsMeasure V hVm hZ]
    congr 1
    apply integral_congr_ae
    exact ae_of_all _ fun x ↦ by dsimp only; rw [Real.log_exp, ← mul_assoc, ← Real.exp_add]; congr 2; ring
  have henergy : (∫ x, Real.exp (g x) * ‖Dg x‖ ^ 2 ∂gibbsMeasure V) =
      (∫ x, Real.exp (g x - V x) * ‖Dg x‖ ^ 2) / ∫ x, Real.exp (-V x) := by
    rw [integral_gibbsMeasure V hVm hZ]
    congr 1
    apply integral_congr_ae
    exact ae_of_all _ fun x ↦ by dsimp only; rw [← mul_assoc, ← Real.exp_add]; congr 2; ring
  rw [Measure.entropy_def, hmean, hlog, henergy, Real.log_div hA.ne' hZ0.ne']
  have hh := div_le_div_of_nonneg_right hmain hZ0.le
  convert hh using 1 <;> ring

/-- A smooth function constant off a compact set has bounded derivative and a quadratic upper bound. -/
theorem exists_bounded_quadratic_upper_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : E → ℝ) (hg : ContDiff ℝ ∞ g) (c : ℝ) (hc : HasCompactSupport (fun x ↦ g x - c)) :
    ∃ M H : ℝ, 0 ≤ M ∧ (∀ x, |g x| ≤ M) ∧ (∀ x, ‖fderiv ℝ g x‖ ^ 2 ≤ M) ∧
      ∀ x z, g x ≤ g z + fderiv ℝ g z (x - z) + H / 2 * ‖x - z‖ ^ 2 := by
  have hdc : fderiv ℝ (fun x ↦ g x - c) = fderiv ℝ g := funext fun x ↦ fderiv_sub_const c
  have hcomp1 : HasCompactSupport (fderiv ℝ g) := hdc ▸ hc.fderiv (𝕜 := ℝ)
  have hcomp2 := hcomp1.fderiv (𝕜 := ℝ)
  have hgs : ContDiff ℝ ∞ (fderiv ℝ g) := hg.fderiv_right (by simp)
  obtain ⟨C₀, hC₀⟩ := (hg.continuous.sub continuous_const).bounded_above_of_compact_support hc
  obtain ⟨C₁, hC₁⟩ := hgs.continuous.bounded_above_of_compact_support hcomp1
  obtain ⟨C₂, hC₂⟩ := (hgs.continuous_fderiv (by simp)).bounded_above_of_compact_support hcomp2
  let L := Real.toNNReal (max C₂ 0)
  have hLip : LipschitzWith L (fderiv ℝ g) := by
    apply lipschitzWith_of_nnnorm_fderiv_le (hgs.differentiable (by simp))
    intro x
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ (le_max_right _ _)]
    exact (hC₂ x).trans (le_max_left _ _)
  let M := max 0 (max (C₀ + |c|) (C₁ ^ 2))
  refine ⟨M, 2 * L, le_max_left _ _, ?_, ?_, ?_⟩
  · intro x
    have h := hC₀ x
    simp only [Real.norm_eq_abs, Pi.sub_apply] at h
    have hg : |g x| ≤ C₀ + |c| := by
      have := abs_add_le (g x - c) c
      rw [sub_add_cancel] at this
      linarith
    exact hg.trans ((le_max_left _ _).trans (le_max_right _ _))
  · intro x
    have hnorm := hC₁ x
    have hs : ‖fderiv ℝ g x‖ ^ 2 ≤ C₁ ^ 2 := by nlinarith [norm_nonneg (fderiv ℝ g x)]
    exact hs.trans ((le_max_right _ _).trans (le_max_right _ _))
  · intro x z
    simpa only [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using
      quadratic_upper_bound_of_lipschitz_fderiv g (hg.differentiable (by simp)) hLip x z

/-- The logarithm of a regularized smooth compactly supported square is an admissible
bounded perturbation in the sharp entropy estimate. -/
theorem exists_log_regularization_bounds {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    {ε : ℝ} (hε : 0 < ε) :
    let g := fun x ↦ Real.log (ε + f x ^ 2);
    ContDiff ℝ ∞ g ∧ ∃ M H : ℝ, 0 ≤ M ∧ (∀ x, |g x| ≤ M) ∧
      (∀ x, ‖fderiv ℝ g x‖ ^ 2 ≤ M) ∧
      ∀ x z, g x ≤ g z + fderiv ℝ g z (x - z) + H / 2 * ‖x - z‖ ^ 2 := by
  intro g
  have hg : ContDiff ℝ ∞ g := (contDiff_const.add (hf.pow 2)).log (fun x ↦ by positivity)
  have hcomp : HasCompactSupport (fun x ↦ g x - Real.log ε) := by
    simpa only [Function.comp_def] using
      hfc.comp_left (g := fun s : ℝ ↦ Real.log (ε + s ^ 2) - Real.log ε) (by simp)
  exact ⟨hg, exists_bounded_quadratic_upper_bound g hg (Real.log ε) hcomp⟩

/-- Dominated convergence of both entropy moments gives convergence of entropy. -/
theorem tendsto_entropy_of_dominated_convergence {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : ℕ → X → ℝ) (g : X → ℝ) (B D : X → ℝ)
    (hfm : ∀ n, AEStronglyMeasurable (f n) μ) (hB : Integrable B μ) (hD : Integrable D μ)
    (hfB : ∀ n, ∀ᵐ x ∂μ, ‖f n x‖ ≤ B x)
    (hfD : ∀ n, ∀ᵐ x ∂μ, ‖f n x * Real.log (f n x)‖ ≤ D x)
    (hfg : ∀ᵐ x ∂μ, Tendsto (fun n ↦ f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n ↦ μ.entropy (f n)) atTop (𝓝 (μ.entropy g)) := by
  have hmean := tendsto_integral_of_dominated_convergence B hfm hB hfB hfg
  have hlog := tendsto_integral_of_dominated_convergence D
    (fun n ↦ Real.continuous_mul_log.comp_aestronglyMeasurable (hfm n)) hD hfD
    (hfg.mono fun x hx ↦ (Real.continuous_mul_log.tendsto _).comp hx)
  simpa only [Measure.entropy_def,Function.comp_apply] using hlog.sub ((Real.continuous_mul_log.tendsto _).comp hmean)

/-- Regularization of a square preserves the sharp gradient-energy upper bound. -/
theorem regularized_log_gradient_energy_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (hf : Differentiable ℝ f) {ε : ℝ} (hε : 0 < ε) (x : E) :
    (ε + f x ^ 2) * ‖fderiv ℝ (fun y ↦ Real.log (ε + f y ^ 2)) x‖ ^ 2 ≤
      4 * ‖fderiv ℝ f x‖ ^ 2 := by
  have hpos : 0 < ε + f x ^ 2 := add_pos_of_pos_of_nonneg hε (sq_nonneg _)
  have hd := (((hf x).hasFDerivAt.pow 2).const_add ε).log hpos.ne'
  have heq : fderiv ℝ (fun y ↦ Real.log (ε + f y ^ 2)) x =
      (2 * f x / (ε + f x ^ 2)) • fderiv ℝ f x := by
    rw [hd.fderiv]
    simp only [Nat.add_one_sub_one, pow_one, smul_smul]
    congr 1
    ring
  rw [heq, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have he : (ε + f x ^ 2) * ((2 * f x / (ε + f x ^ 2)) ^ 2 * ‖fderiv ℝ f x‖ ^ 2) =
      4 * (f x ^ 2 / (ε + f x ^ 2)) * ‖fderiv ℝ f x‖ ^ 2 := by field_simp; ring
  rw [he]
  have hratio : f x ^ 2 / (ε + f x ^ 2) ≤ 1 := (div_le_one hpos).2 (by linarith)
  nlinarith [mul_le_mul_of_nonneg_right hratio (sq_nonneg ‖fderiv ℝ f x‖)]

/-- A regularized compactly supported square satisfies the sharp logarithmic Sobolev bound. -/
theorem entropy_gibbs_regularized_sq_le {d : ℕ}
    (V : EuclideanSpace ℝ (Fin d) → ℝ)
    (G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (m : ℝ) (hm0 : 0 < m)
    (hG : ∀ x, HasGradientAt V (G x) x) (hm : IsStronglyMonotoneGradient G m)
    (hZ : Integrable (fun x ↦ Real.exp (-V x)))
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    {ε : ℝ} (hε : 0 < ε) :
    (gibbsMeasure V).entropy (fun x ↦ ε + f x ^ 2) ≤
      (2 / m) * ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂gibbsMeasure V := by
  let g := fun x ↦ Real.log (ε + f x ^ 2)
  obtain ⟨hg, M, H, hM, hgM, hDgM, hquad⟩ := exists_log_regularization_bounds f hf hfc hε
  have hmain := entropy_gibbs_exponential_le V G m hm0 hG hm g (fderiv ℝ g) H hquad
    hg.continuous.measurable (hg.continuous_fderiv (by simp)).norm.measurable hM hgM hDgM hZ
  have hexp : (fun x ↦ Real.exp (g x)) = (fun x ↦ ε + f x ^ 2) :=
    funext fun x ↦ Real.exp_log (by positivity)
  simp_rw [show ∀ x, Real.exp (g x) = ε + f x ^ 2 from fun x ↦ congrFun hexp x] at hmain
  have : IsProbabilityMeasure (gibbsMeasure V) := isProbabilityMeasure_gibbsMeasure hZ
  obtain ⟨C, hC⟩ := (hf.continuous_fderiv (by simp)).bounded_above_of_compact_support (hfc.fderiv (𝕜 := ℝ))
  have hDint : Integrable (fun x ↦ ‖fderiv ℝ f x‖ ^ 2) (gibbsMeasure V) := by
    refine Integrable.of_bound (by fun_prop) (C ^ 2) (ae_of_all _ fun x ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [hC x, norm_nonneg (fderiv ℝ f x)]
  have hbd (x) : (ε + f x ^ 2) * ‖fderiv ℝ g x‖ ^ 2 ≤ 4 * ‖fderiv ℝ f x‖ ^ 2 :=
    regularized_log_gradient_energy_le f (hf.differentiable (by simp)) hε x
  have hEint : Integrable (fun x ↦ (ε + f x ^ 2) * ‖fderiv ℝ g x‖ ^ 2) (gibbsMeasure V) := by
    refine (hDint.const_mul 4).mono' (((continuous_const.add (hf.continuous.pow 2)).mul
      ((hg.continuous_fderiv (by simp)).norm.pow 2)).aestronglyMeasurable) (ae_of_all _ fun x ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hbd x
  have hint := integral_mono hEint (hDint.const_mul 4) hbd
  rw [integral_const_mul] at hint
  have hh := mul_le_mul_of_nonneg_left hint (by positivity : 0 ≤ 1 / (2 * m))
  calc (gibbsMeasure V).entropy (fun x ↦ ε + f x ^ 2) ≤ _ := hmain
    _ ≤ (2 / m) * ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂gibbsMeasure V := by
      convert hh using 1; ring

/-- Adding positive constants tending to zero preserves the entropy of a bounded nonnegative function. -/
theorem tendsto_entropy_add_inv {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (q : X → ℝ) (hq : Measurable q)
    {C : ℝ} (_hC : 0 ≤ C) (hqC : ∀ x, q x ∈ Icc 0 C) :
    Tendsto (fun n : ℕ ↦ μ.entropy (fun x ↦ 1 / ((n : ℝ) + 1) + q x)) atTop (𝓝 (μ.entropy q)) := by
  obtain ⟨D, hD⟩ := isCompact_Icc.bddAbove_image
    ((Real.continuous_mul_log.norm).continuousOn (s := Icc (0 : ℝ) (1 + C)))
  have heps (n : ℕ) : 0 < 1 / ((n : ℝ) + 1) ∧ 1 / ((n : ℝ) + 1) ≤ 1 := by
    constructor
    · positivity
    · exact (div_le_one (by positivity)).2 (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
  apply tendsto_entropy_of_dominated_convergence μ (fun n x ↦ 1 / ((n : ℝ) + 1) + q x) q (fun _ ↦ 1 + C) (fun _ ↦ D)
    (fun n ↦ (measurable_const.add hq).aestronglyMeasurable) (integrable_const _) (integrable_const _)
  · intro n
    refine ae_of_all _ fun x ↦ ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [(heps n).1, (hqC x).1])]
    linarith [(heps n).2, (hqC x).2]
  · intro n
    exact ae_of_all _ fun x ↦ hD (mem_image_of_mem _ ⟨by linarith [(heps n).1, (hqC x).1],
      by linarith [(heps n).2, (hqC x).2]⟩)
  · exact ae_of_all _ fun x ↦ by
      simpa only [zero_add] using tendsto_one_div_add_atTop_nhds_zero_nat.add_const (q x)

/-- Smooth compactly supported tests satisfy the sharp Bakry–Émery logarithmic Sobolev bound. -/
theorem entropy_gibbs_sq_le_of_hasCompactSupport {d : ℕ}
    (V : EuclideanSpace ℝ (Fin d) → ℝ)
    (G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (m : ℝ) (hm0 : 0 < m)
    (hG : ∀ x, HasGradientAt V (G x) x) (hm : IsStronglyMonotoneGradient G m)
    (hZ : Integrable (fun x ↦ Real.exp (-V x)))
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    (gibbsMeasure V).entropy (fun x ↦ f x ^ 2) ≤
      (2 / m) * ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂gibbsMeasure V := by
  have : IsProbabilityMeasure (gibbsMeasure V) := isProbabilityMeasure_gibbsMeasure hZ
  obtain ⟨C, hC⟩ := hf.continuous.bounded_above_of_compact_support hfc
  have hq (x) : f x ^ 2 ∈ Icc (0 : ℝ) (C ^ 2) := by
    constructor
    · positivity
    · have hx := hC x
      rw [Real.norm_eq_abs] at hx
      nlinarith [abs_nonneg (f x), sq_abs (f x)]
  have hlim := tendsto_entropy_add_inv (gibbsMeasure V) (fun x ↦ f x ^ 2)
    (hf.continuous.measurable.pow_const (2 : ℕ)) (sq_nonneg C) hq
  apply le_of_tendsto hlim
  exact Eventually.of_forall fun n ↦ entropy_gibbs_regularized_sq_le V G m hm0 hG hm hZ f hf hfc (by positivity)

end CKSD
