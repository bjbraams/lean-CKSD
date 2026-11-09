module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import TauCeti.Analysis.Distribution.SchwartzSpace.Gaussian
public import TauCeti.Probability.Distributions.Gaussian.Density

/-!
# Gaussian smoothing and conditional scores

A probability measure convolved with an isotropic Gaussian has a smooth strictly positive
Lebesgue density. Its derivative is obtained by differentiating the Gaussian likelihood under
the integral. Conditional expectations are expressed as density-weighted integrals, so the
Gaussian score can be identified with the conditional mean of the added noise.

The analytic estimates reuse Mathlib's Schwartz-function seminorms and differentiation under
the integral, and TauCeti's `SchwartzMap.gaussian`. The Gaussian change of variables reuses
TauCeti's `stdGaussian_eq_withDensity_norm` and `Measure.map_affine_withDensity`.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology SchwartzMap ContDiff

namespace CKSD

universe u
variable {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A translate of a Schwartz function is integrable under every finite measure. -/
theorem integrable_schwartz_sub (ν : Measure E) [IsFiniteMeasure ν] (f : 𝓢(E, F)) (x : E) :
    Integrable (fun y ↦ f (x - y)) ν := by
  refine Integrable.of_bound (f.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    (SchwartzMap.seminorm ℝ 0 0 f) (ae_of_all _ fun y ↦ ?_)
  exact f.norm_le_seminorm ℝ (x - y)

/-- Differentiation commutes with averaging translates of a Schwartz function under a finite measure. -/
theorem hasFDerivAt_integral_schwartz_sub (ν : Measure E) [IsFiniteMeasure ν] (f : 𝓢(E, F)) (x : E) :
    HasFDerivAt (fun x ↦ ∫ y, f (x - y) ∂ν)
      (∫ y, fderiv ℝ f (x - y) ∂ν) x := by
  have hcont : Continuous (fderiv ℝ f) := (f.smooth ⊤).continuous_fderiv (by simp)
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ)
    (F := fun x y ↦ f (x - y)) (F' := fun x y ↦ fderiv ℝ f (x - y)) (μ := ν) (s := univ) (bound := fun _ ↦
    SchwartzMap.seminorm ℝ 0 1 f) (Filter.univ_mem) ?_ ?_ ?_ ?_ (integrable_const _) ?_
  · exact Eventually.of_forall fun x ↦
      (f.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · exact Integrable.of_bound
      (f.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      (SchwartzMap.seminorm ℝ 0 0 f) (ae_of_all _ fun y ↦ f.norm_le_seminorm ℝ (x - y))
  · exact (hcont.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · exact ae_of_all _ fun y x _ ↦ by
      simpa [norm_iteratedFDeriv_one] using f.norm_iteratedFDeriv_le_seminorm ℝ 1 (x - y)
  · exact ae_of_all _ fun y x _ ↦ by
      simpa [Function.comp_def] using (f.differentiableAt).hasFDerivAt.comp x
        ((hasFDerivAt_id x).sub_const y)


/-- A finite-measure average of Schwartz translates has derivatives of every finite order. -/
theorem contDiff_integral_schwartz_sub_nat (ν : Measure E) [IsFiniteMeasure ν] (n : ℕ)
    (f : 𝓢(E, F)) : ContDiff ℝ n (fun x ↦ ∫ y, f (x - y) ∂ν) := by
  induction n generalizing F with
  | zero =>
    change ContDiff ℝ 0 _
    rw [contDiff_zero]
    exact Differentiable.continuous (fun x ↦ (hasFDerivAt_integral_schwartz_sub ν f x).differentiableAt)
  | succ n ih =>
    rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 by simp,
      contDiff_succ_iff_fderiv]
    refine ⟨fun x ↦ (hasFDerivAt_integral_schwartz_sub ν f x).differentiableAt, by simp, ?_⟩
    have heq : fderiv ℝ (fun x ↦ ∫ y, f (x - y) ∂ν) =
        fun x ↦ ∫ y, (SchwartzMap.fderivCLM ℝ E F f) (x - y) ∂ν := by
      funext x
      exact (hasFDerivAt_integral_schwartz_sub ν f x).fderiv
    rw [heq]
    exact ih _

/-- A finite-measure average of translates of a Schwartz function is smooth. -/
theorem contDiff_integral_schwartz_sub (ν : Measure E) [IsFiniteMeasure ν]
    (f : 𝓢(E, F)) : ContDiff ℝ ∞ (fun x ↦ ∫ y, f (x - y) ∂ν) := by
  rw [contDiff_infty]
  intro n
  exact contDiff_integral_schwartz_sub_nat ν n f

end CKSD

namespace CKSD
open scoped SchwartzMap

/-- The Lebesgue density of the centered isotropic Gaussian with standard deviation `σ`. -/
def gaussianSmoothingKernel {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (σ : ℝ) (x : E) : ℝ :=
  |σ|⁻¹ ^ Module.finrank ℝ E * (2 * Real.pi) ^ (-(Module.finrank ℝ E : ℝ) / 2) *
    Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2))

/-- At positive scale the isotropic Gaussian density is a Schwartz function, using TauCeti's Gaussian. -/
theorem exists_schwartz_gaussianSmoothingKernel {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {σ : ℝ} (hσ : 0 < σ) :
    ∃ f : 𝓢(E, ℝ), (f : E → ℝ) = gaussianSmoothingKernel σ := by
  have hb : 0 < (((2 * σ ^ 2)⁻¹ : ℝ) : ℂ).re := by
    change 0 < (2 * σ ^ 2)⁻¹
    positivity
  refine ⟨(|σ|⁻¹ ^ Module.finrank ℝ E *
    (2 * Real.pi) ^ (-(Module.finrank ℝ E : ℝ) / 2)) •
    ((SchwartzMap.gaussian (V := E) hb).postcompCLM Complex.reCLM), ?_⟩
  funext x
  simp only [smul_apply, SchwartzMap.postcompCLM_apply,
    SchwartzMap.gaussian_apply, Complex.reCLM_apply, smul_eq_mul]
  rw [gaussianSmoothingKernel, ← Complex.ofReal_pow, ← Complex.ofReal_neg,
    ← Complex.ofReal_mul, Complex.exp_ofReal_re]
  congr 2
  ring

/-- An affine image of the standard Gaussian has the translated isotropic Gaussian density.
The change of variables uses TauCeti's `Measure.map_affine_withDensity`. -/
theorem map_affine_stdGaussian_eq_withDensity {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {σ : ℝ} (hσ : 0 < σ) (y : E) :
    (stdGaussian E).map (fun z ↦ y + σ • z) =
      volume.withDensity (fun x ↦ ENNReal.ofReal (gaussianSmoothingKernel σ (x - y))) := by
  let A : E ≃L[ℝ] E := ContinuousLinearEquiv.smulLeft (Units.mk0 σ hσ.ne')
  have hA (x : E) : A x = σ • x := by simp [A, Units.smul_def]
  have hAinv (x : E) : A.symm x = σ⁻¹ • x := by
    apply A.injective
    rw [A.apply_symm_apply, hA]
    simp [smul_smul, hσ.ne']
  have hAlin : (A : E →ₗ[ℝ] E) = σ • LinearMap.id := by ext x; simp [hA]
  have hAdet : LinearMap.det (A : E →ₗ[ℝ] E) = σ ^ Module.finrank ℝ E := by
    rw [hAlin, LinearMap.det_smul, LinearMap.det_id, mul_one]
  rw [TauCeti.Probability.stdGaussian_eq_withDensity_norm]
  simp_rw [← hA]
  rw [Measure.map_affine_withDensity]
  refine withDensity_congr_ae (ae_of_all _ fun x ↦ ?_)
  dsimp only
  rw [hAdet, hAinv, ← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 1
  simp only [gaussianSmoothingKernel, norm_smul, Real.norm_eq_abs, abs_inv, inv_pow, abs_pow,
    mul_pow]
  rw [mul_assoc]
  congr 2
  congr 1
  rw [sq_abs]
  ring

end CKSD

namespace CKSD

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
/-- The isotropic Gaussian density is strictly positive at positive scale. -/
theorem gaussianSmoothingKernel_pos {σ : ℝ} (hσ : 0 < σ) (x : E) :
    0 < gaussianSmoothingKernel σ x := by
  unfold gaussianSmoothingKernel
  positivity

omit [MeasurableSpace E] [BorelSpace E] in
/-- The isotropic Gaussian density is smooth at positive scale. -/
theorem contDiff_gaussianSmoothingKernel {σ : ℝ} (hσ : 0 < σ) :
    ContDiff ℝ ∞ (gaussianSmoothingKernel σ : E → ℝ) := by
  obtain ⟨f, hf⟩ := exists_schwartz_gaussianSmoothingKernel (E := E) hσ
  rw [← hf]
  exact f.smooth ⊤

/-- Convolving any probability measure with a nondegenerate isotropic Gaussian gives a smooth
strictly positive density. -/
theorem smooth_positive_gaussianSmoothing (ν : Measure E) [IsProbabilityMeasure ν]
    {σ : ℝ} (hσ : 0 < σ) :
    ContDiff ℝ ∞ (fun x ↦ ∫ y, gaussianSmoothingKernel σ (x - y) ∂ν) ∧
      ∀ x, 0 < ∫ y, gaussianSmoothingKernel σ (x - y) ∂ν := by
  obtain ⟨f, hf⟩ := exists_schwartz_gaussianSmoothingKernel (E := E) hσ
  refine ⟨?_, fun x ↦ ?_⟩
  · simpa only [hf] using contDiff_integral_schwartz_sub ν f
  · have hi : Integrable (fun y ↦ gaussianSmoothingKernel σ (x - y)) ν := by
      simpa only [hf] using integrable_schwartz_sub ν f x
    apply (integral_pos_iff_support_of_nonneg (fun y ↦ (gaussianSmoothingKernel_pos hσ _).le) hi).2
    have hsupp : Function.support (fun y ↦ gaussianSmoothingKernel σ (x - y)) = univ := by
      ext y
      simp [Function.mem_support, (gaussianSmoothingKernel_pos hσ (x-y)).ne']
    rw [hsupp, measure_univ]
    exact zero_lt_one

/-- The law of the sum of independent signals and Gaussian noise has the averaged Gaussian density. -/
theorem map_add_gaussian_eq_withDensity (ν : Measure E) [IsProbabilityMeasure ν]
    {σ : ℝ} (hσ : 0 < σ) :
    (ν.prod (stdGaussian E)).map (fun p ↦ p.1 + σ • p.2) =
      volume.withDensity (fun x ↦ ENNReal.ofReal (∫ y, gaussianSmoothingKernel σ (x - y) ∂ν)) := by
  have hq : Continuous (gaussianSmoothingKernel σ : E → ℝ) :=
    (contDiff_gaussianSmoothingKernel hσ).continuous
  have hj : Measurable (fun p : E × E ↦ ENNReal.ofReal (gaussianSmoothingKernel σ (p.2 - p.1))) :=
    (hq.comp (continuous_snd.sub continuous_fst)).measurable.ennreal_ofReal
  have hqi (x : E) : Integrable (fun y ↦ gaussianSmoothingKernel σ (x - y)) ν := by
    obtain ⟨f, hf⟩ := exists_schwartz_gaussianSmoothingKernel (E := E) hσ
    simpa only [hf] using integrable_schwartz_sub ν f x
  ext s hs
  rw [Measure.map_apply (by fun_prop) hs, Measure.prod_apply ((by fun_prop : Measurable (fun p : E × E ↦ p.1 + σ • p.2)) hs), withDensity_apply _ hs]
  have hpt (y : E) : (stdGaussian E) (Prod.mk y ⁻¹' ((fun p : E × E ↦ p.1 + σ • p.2) ⁻¹' s)) =
      ∫⁻ x in s, ENNReal.ofReal (gaussianSmoothingKernel σ (x - y)) := by
    have h := congrArg (fun μ : Measure E ↦ μ s) (map_affine_stdGaussian_eq_withDensity hσ y)
    change (stdGaussian E) ((fun z ↦ y + σ • z) ⁻¹' s) = _
    simpa only [Measure.map_apply (by fun_prop : Measurable (fun z : E ↦ y + σ • z)) hs,
      withDensity_apply _ hs] using h
  simp_rw [hpt]
  rw [lintegral_lintegral_swap]
  · apply lintegral_congr_ae
    exact ae_of_all _ fun x ↦ (ofReal_integral_eq_lintegral_ofReal (hqi x)
      (ae_of_all _ fun y ↦ (gaussianSmoothingKernel_pos hσ _).le)).symm
  · exact hj.aemeasurable

end CKSD

namespace CKSD

variable {Ω E F : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] [MeasurableSpace F]
    [BorelSpace F] [SecondCountableTopology F]

/-- Conditional expectation from a joint density: divide the density-weighted numerator by the
positive marginal density. The observation space needs no topological structure. -/
theorem condExp_of_joint_density (P : Measure Ω) [IsProbabilityMeasure P]
    (ν μ : Measure E) [SFinite ν] [SFinite μ]
    (Y X : Ω → E) (hY : Measurable Y) (hX : Measurable X)
    (q : E × E → ℝ) (hq : Measurable q) (hq0 : ∀ p, 0 ≤ q p)
    (m : E → ℝ) (hm : Measurable m) (hmpos : ∀ x, 0 < m x)
    (hYX : P.map (fun w ↦ (Y w, X w)) = (ν.prod μ).withDensity (fun p ↦ ENNReal.ofReal (q p)))
    (hXm : P.map X = μ.withDensity (fun x ↦ ENNReal.ofReal (m x)))
    (H : E × E → F) (hH : Measurable H) (hHi : Integrable (fun w ↦ H (Y w, X w)) P) :
    (fun w ↦ (m (X w))⁻¹ • ∫ y, q (y, X w) • H (y, X w) ∂ν) =ᵐ[P]
      P[(fun w ↦ H (Y w, X w)) | MeasurableSpace.comap X inferInstance] := by
  let W : E × E → F := fun p ↦ q p • H p
  let N : E → F := fun x ↦ ∫ y, W (y, x) ∂ν
  let g : E → F := fun x ↦ (m x)⁻¹ • N x
  have hWm : Measurable W := hq.smul hH
  have hNm : Measurable N := hWm.stronglyMeasurable.integral_prod_left'.measurable
  have hgm : Measurable g := hm.inv.smul hNm
  have hwHi : Integrable W (ν.prod μ) := by
    have hi : Integrable H (P.map fun w ↦ (Y w, X w)) :=
      (integrable_map_measure hH.aestronglyMeasurable (hY.prodMk hX).aemeasurable).2 hHi
    rw [hYX] at hi
    simpa only [ENNReal.toReal_ofReal (hq0 _)] using
      (integrable_withDensity_iff_integrable_smul' hq.ennreal_ofReal
        (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)).1 hi
  have hmg (x : E) : m x • g x = N x := by
    simp only [g, smul_smul, mul_inv_cancel₀ (hmpos x).ne', one_smul]
  have hgi : Integrable g (P.map X) := by
    rw [hXm, integrable_withDensity_iff_integrable_smul' hm.ennreal_ofReal
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
    simpa only [ENNReal.toReal_ofReal (hmpos _).le, hmg] using hwHi.integral_prod_right
  have hgPi : Integrable (fun w ↦ g (X w)) P := hgi.comp_measurable hX
  apply ae_eq_condExp_of_forall_setIntegral_eq hX.comap_le hHi
  · intro s hs _
    exact hgPi.integrableOn
  · rintro _ ⟨s, hs, rfl⟩ _
    change ∫ w in X ⁻¹' s, g (X w) ∂P = ∫ w in X ⁻¹' s, H (Y w, X w) ∂P
    rw [← setIntegral_map hs hgm.aestronglyMeasurable hX.aemeasurable, hXm,
      setIntegral_withDensity_eq_setIntegral_toReal_smul₀ hm.ennreal_ofReal.aemeasurable
        (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top) g hs]
    simp only [ENNReal.toReal_ofReal (hmpos _).le, hmg]
    rw [← integral_indicator hs]
    have hR : ∫ w in X ⁻¹' s, H (Y w, X w) ∂P =
        ∫ p, (Prod.snd ⁻¹' s).indicator H p ∂(ν.prod μ).withDensity
          (fun p ↦ ENNReal.ofReal (q p)) := by
      rw [← hYX, integral_map (hY.prodMk hX).aemeasurable
        (hH.indicator (measurable_snd hs)).aestronglyMeasurable,
        ← integral_indicator (hX hs)]
      rfl
    rw [hR, integral_withDensity_eq_integral_toReal_smul hq.ennreal_ofReal
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
    simp only [ENNReal.toReal_ofReal (hq0 _)]
    have heq : (fun p : E × E ↦ q p • (Prod.snd ⁻¹' s).indicator H p) =
        (Prod.snd ⁻¹' s).indicator W := by
      funext p
      by_cases hp : p.2 ∈ s <;> simp [hp, W]
    rw [heq, integral_prod_symm _ (hwHi.indicator (measurable_snd hs))]
    apply integral_congr_ae (ae_of_all _ fun x ↦ ?_)
    by_cases hx : x ∈ s <;> simp [hx, N]
  · exact (hgm.comp (measurable_iff_comap_le.2 le_rfl)).aestronglyMeasurable

end CKSD

namespace CKSD

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
/-- The derivative of the isotropic Gaussian density is its density times the linear score. -/
theorem fderiv_gaussianSmoothingKernel {σ : ℝ} (hσ : 0 < σ) (x : E) :
    fderiv ℝ (gaussianSmoothingKernel σ : E → ℝ) x =
      gaussianSmoothingKernel σ x • (-(σ ^ 2)⁻¹ • innerSL ℝ x) := by
  have hd := (((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul (-(2 * σ ^ 2)⁻¹)).exp).const_mul
    (|σ|⁻¹ ^ Module.finrank ℝ E * (2 * Real.pi) ^ (-(Module.finrank ℝ E : ℝ) / 2))
  have he : HasFDerivAt (gaussianSmoothingKernel σ : E → ℝ)
      (gaussianSmoothingKernel σ x • (-(σ ^ 2)⁻¹ • innerSL ℝ x)) x := by
    have hfun : (gaussianSmoothingKernel σ : E → ℝ) = fun z ↦
        (|σ|⁻¹ ^ Module.finrank ℝ E * (2 * Real.pi) ^ (-(Module.finrank ℝ E : ℝ) / 2)) *
          Real.exp (-(2 * σ ^ 2)⁻¹ * ‖z‖ ^ 2) := by
      funext z
      unfold gaussianSmoothingKernel
      congr 1
      congr 1
      ring
    rw [hfun]
    convert hd using 1
    ext z
    simp only [smul_eq_mul, smul_apply, innerSL_apply_apply]
    field_simp
    ring
  exact he.fderiv

/-- The gradient of a Gaussian convolution is the average of the Gaussian density gradients. -/
theorem gradient_gaussianSmoothing (ν : Measure E) [IsProbabilityMeasure ν]
    {σ : ℝ} (hσ : 0 < σ) (x : E) :
    gradient (fun x ↦ ∫ y, gaussianSmoothingKernel σ (x - y) ∂ν) x =
      -(σ ^ 2)⁻¹ • ∫ y, gaussianSmoothingKernel σ (x - y) • (x - y) ∂ν := by
  obtain ⟨f, hf⟩ := exists_schwartz_gaussianSmoothingKernel (E := E) hσ
  have hd : fderiv ℝ (fun x ↦ ∫ y, gaussianSmoothingKernel σ (x - y) ∂ν) x =
      ∫ y, fderiv ℝ (gaussianSmoothingKernel σ : E → ℝ) (x - y) ∂ν := by
    simpa only [hf] using (hasFDerivAt_integral_schwartz_sub ν f x).fderiv
  have hi : Integrable (fun y ↦ fderiv ℝ (gaussianSmoothingKernel σ : E → ℝ) (x-y)) ν := by
    simpa only [SchwartzMap.fderivCLM_apply, hf] using
      integrable_schwartz_sub ν (SchwartzMap.fderivCLM ℝ E ℝ f) x
  simp only [gradient, hd]
  change ((InnerProductSpace.toDual ℝ E).symm.toContinuousLinearMap) (∫ y,
    fderiv ℝ (gaussianSmoothingKernel σ : E → ℝ) (x-y) ∂ν) = _
  rw [← ContinuousLinearMap.integral_comp_comm _ hi]
  simp only [fderiv_gaussianSmoothingKernel hσ, map_smul]
  have hpt (y : E) : (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearMap (innerSL ℝ y) = y := by
    exact (InnerProductSpace.toDual ℝ E).symm_apply_apply y
  simp only [hpt]
  rw [← integral_smul]
  apply integral_congr_ae (ae_of_all _ fun y ↦ ?_)
  rw [smul_comm]

end CKSD

namespace CKSD

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The joint law of a signal and its sum with independent Gaussian noise has the Gaussian
likelihood density relative to signal law times Lebesgue measure. -/
theorem map_pair_add_gaussian_eq_withDensity (ν : Measure E) [IsProbabilityMeasure ν]
    {σ : ℝ} (hσ : 0 < σ) :
    (ν.prod (stdGaussian E)).map (fun p ↦ (p.1, p.1 + σ • p.2)) =
      (ν.prod volume).withDensity (fun p ↦ ENNReal.ofReal (gaussianSmoothingKernel σ (p.2 - p.1))) := by
  have hq : Continuous (gaussianSmoothingKernel σ : E → ℝ) :=
    (contDiff_gaussianSmoothingKernel hσ).continuous
  have hj : Measurable (fun p : E × E ↦ ENNReal.ofReal (gaussianSmoothingKernel σ (p.2 - p.1))) :=
    (hq.comp (continuous_snd.sub continuous_fst)).measurable.ennreal_ofReal
  have hT : Measurable (fun p : E × E ↦ (p.1, p.1 + σ • p.2)) := by fun_prop
  ext s hs
  rw [Measure.map_apply hT hs, Measure.prod_apply (hT hs), withDensity_apply _ hs,
    ← lintegral_indicator hs, lintegral_prod _ (hj.indicator hs).aemeasurable]
  apply lintegral_congr_ae (ae_of_all _ fun y ↦ ?_)
  have hslice : MeasurableSet (Prod.mk y ⁻¹' s) := (measurable_const.prodMk measurable_id) hs
  have h := congrArg (fun μ : Measure E ↦ μ (Prod.mk y ⁻¹' s))
    (map_affine_stdGaussian_eq_withDensity (E := E) hσ y)
  rw [Measure.map_apply (by fun_prop) hslice, withDensity_apply _ hslice,
    ← lintegral_indicator hslice] at h
  convert h using 1
  · rfl
  · apply lintegral_congr_ae (ae_of_all _ fun x ↦ ?_)
    by_cases hx : (y,x) ∈ s <;> simp [hx]

end CKSD
