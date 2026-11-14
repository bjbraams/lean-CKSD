module

public import CKSD.Geometry.Basic
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import TauCeti.Analysis.Bochner.Fourier.Nonneg
public import TauCeti.Probability.Density
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Normed.Module.RCLike.Real


/-!
# Characteristic translation-invariant spectral kernels

For the cosine kernel represented by a finite measure `L`, squared MMD is the `L`-integral of
the squared difference between characteristic functions. Charging every open ball therefore
makes the kernel characteristic, by continuity and uniqueness of characteristic functions.

Conversely, a ball missing from a symmetric spectral measure supports an even smooth Fourier
perturbation vanishing at the origin. Its inverse Fourier transform is a real integrable function
of integral zero. The normalized densities `|g| + g` and `|g|` give distinct probability laws
whose characteristic functions agree `L`-almost everywhere. Thus, on a positive-dimensional
finite-dimensional real inner product space, a finite symmetric spectral measure represents a
characteristic kernel exactly when its support is the whole space.

Mathlib supplies the characteristic-function uniqueness theorem, Schwartz Fourier inversion and
smooth bump functions. TauCeti supplies the real inverse-Fourier-transform and density bridges.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators FourierTransform ContDiff
open FourierTransform ComplexConjugate
namespace CKSD

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [SecondCountableTopology E] in
/-- The cosine moment is the real part of the characteristic function. -/
theorem integral_cos_inner_eq_re_char_fun (μ : Measure E) [IsFiniteMeasure μ] (w : E) :
    (∫ x, Real.cos (inner ℝ w x) ∂μ) = (charFun μ w).re := by
  have hint := (BoundedContinuousFunction.innerProbChar w).integrable μ
  have hre := Complex.reCLM.integral_comp_comm hint
  change (∫ x, ((BoundedContinuousFunction.innerProbChar w) x).re ∂μ) =
    (∫ x, (BoundedContinuousFunction.innerProbChar w) x ∂μ).re at hre
  rw [charFun_eq_integral_innerProbChar, ← hre]
  apply integral_congr_ae
  apply ae_of_all
  intro x
  simp [BoundedContinuousFunction.innerProbChar_apply, Complex.exp_re, real_inner_comm]

omit [SecondCountableTopology E] in
/-- The sine moment is the imaginary part of the characteristic function. -/
theorem integral_sin_inner_eq_im_char_fun (μ : Measure E) [IsFiniteMeasure μ] (w : E) :
    (∫ x, Real.sin (inner ℝ w x) ∂μ) = (charFun μ w).im := by
  have hint := (BoundedContinuousFunction.innerProbChar w).integrable μ
  have him := Complex.imCLM.integral_comp_comm hint
  change (∫ x, ((BoundedContinuousFunction.innerProbChar w) x).im ∂μ) =
    (∫ x, (BoundedContinuousFunction.innerProbChar w) x ∂μ).im at him
  rw [charFun_eq_integral_innerProbChar, ← him]
  apply integral_congr_ae
  apply ae_of_all
  intro x
  simp [BoundedContinuousFunction.innerProbChar_apply, Complex.exp_im, real_inner_comm]

/-- The cosine of a projected difference is integrable under every finite product law. -/
theorem integrable_cos_inner_sub_prod (P Q : Measure E) [IsFiniteMeasure P]
    [IsFiniteMeasure Q] (w : E) :
    Integrable (fun z : E × E ↦ Real.cos (inner ℝ w (z.1 - z.2))) (P.prod Q) :=
  Integrable.of_bound (by fun_prop) 1 (ae_of_all _ fun z ↦ by
    simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (inner ℝ w (z.1 - z.2)))

/-- The product-law cosine moment is the Euclidean pairing of characteristic functions. -/
theorem integral_cos_inner_sub_prod (P Q : Measure E) [IsFiniteMeasure P]
    [IsFiniteMeasure Q] (w : E) :
    (∫ z : E × E, Real.cos (inner ℝ w (z.1 - z.2)) ∂P.prod Q) =
      (charFun P w).re * (charFun Q w).re + (charFun P w).im * (charFun Q w).im := by
  have hc (μ : Measure E) [IsFiniteMeasure μ] : Integrable (fun x ↦ Real.cos (inner ℝ w x)) μ :=
    Integrable.of_bound (by fun_prop) 1 (ae_of_all _ fun x ↦ by
      simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (inner ℝ w x))
  have hs (μ : Measure E) [IsFiniteMeasure μ] : Integrable (fun x ↦ Real.sin (inner ℝ w x)) μ :=
    Integrable.of_bound (by fun_prop) 1 (ae_of_all _ fun x ↦ by
      simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one (inner ℝ w x))
  simp_rw [inner_sub_right, Real.cos_sub]
  rw [integral_add ((hc P).mul_prod (hc Q)) ((hs P).mul_prod (hs Q)),
    integral_prod_mul (fun x ↦ Real.cos (inner ℝ w x)) (fun x ↦ Real.cos (inner ℝ w x)),
    integral_prod_mul (fun x ↦ Real.sin (inner ℝ w x)) (fun x ↦ Real.sin (inner ℝ w x)),
    integral_cos_inner_eq_re_char_fun,
    integral_cos_inner_eq_re_char_fun, integral_sin_inner_eq_im_char_fun,
    integral_sin_inner_eq_im_char_fun]

/-- Integrating a translation-invariant spectral kernel against a product law interchanges
its spectral and observation integrals. -/
theorem integral_spectral_kernel_prod (L P Q : Measure E) [IsFiniteMeasure L]
    [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    (∫ z : E × E, (∫ w, Real.cos (inner ℝ w (z.1 - z.2)) ∂L) ∂P.prod Q) =
      ∫ w, (charFun P w).re * (charFun Q w).re +
        (charFun P w).im * (charFun Q w).im ∂L := by
  have hint : Integrable (fun z : E × (E × E) ↦ Real.cos (inner ℝ z.1 (z.2.1 - z.2.2)))
      (L.prod (P.prod Q)) := Integrable.of_bound (by fun_prop) 1 (ae_of_all _ fun z ↦ by
        simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one _)
  rw [← integral_integral_swap hint]
  apply integral_congr_ae
  exact ae_of_all _ fun w ↦ integral_cos_inner_sub_prod P Q w

/-- The spectral expression for squared MMD is the weighted squared distance between
characteristic functions. -/
theorem squared_mmd_spectral_kernel_eq_integral (L P Q : Measure E) [IsFiniteMeasure L]
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    squaredMMD (fun x y ↦ ∫ w, Real.cos (inner ℝ w (x - y)) ∂L) P Q =
      ∫ w, ‖charFun P w - charFun Q w‖ ^ 2 ∂L := by
  have hbound (μ : Measure E) [IsProbabilityMeasure μ] (w : E) :
      |(charFun μ w).re| ≤ 1 ∧ |(charFun μ w).im| ≤ 1 :=
    ⟨(Complex.abs_re_le_norm _).trans (norm_charFun_le_one _),
      (Complex.abs_im_le_norm _).trans (norm_charFun_le_one _)⟩
  have hint (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
      Integrable (fun w ↦ (charFun μ w).re * (charFun ν w).re +
        (charFun μ w).im * (charFun ν w).im) L := by
    refine Integrable.of_bound (by fun_prop) 2 (ae_of_all _ fun w ↦ ?_)
    rw [Real.norm_eq_abs]
    refine (abs_add_le _ _).trans ?_
    have hre := mul_le_mul (hbound μ w).1 (hbound ν w).1 (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
    have him := mul_le_mul (hbound μ w).2 (hbound ν w).2 (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
    simp only [abs_mul] at *
    linarith
  have hsum : Integrable (fun w ↦
      ((charFun P w).re * (charFun P w).re + (charFun P w).im * (charFun P w).im) +
      ((charFun Q w).re * (charFun Q w).re + (charFun Q w).im * (charFun Q w).im)) L :=
    (hint P P).add (hint Q Q)
  have hmul : Integrable (fun w ↦ 2 *
      ((charFun P w).re * (charFun Q w).re + (charFun P w).im * (charFun Q w).im)) L :=
    (hint P Q).const_mul 2
  rw [squaredMMD, integral_spectral_kernel_prod, integral_spectral_kernel_prod,
    integral_spectral_kernel_prod, ← integral_add (hint P P) (hint Q Q),
    ← integral_const_mul 2, ← integral_sub hsum hmul]
  apply integral_congr_ae
  apply ae_of_all
  intro w
  dsimp only
  rw [Complex.sq_norm]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
  ring

/-- A spectral measure charging every ball produces a characteristic translation-invariant
kernel, by uniqueness of characteristic functions. -/
theorem is_characteristic_kernel_spectral_of_full_support [CompleteSpace E]
    (L : Measure E) [IsFiniteMeasure L]
    (hfull : ∀ x, ∀ r > 0, 0 < L (Metric.ball x r)) :
    IsCharacteristicKernel (fun x y ↦ ∫ w, Real.cos (inner ℝ w (x - y)) ∂L) := by
  have : L.IsOpenPosMeasure := by
    constructor
    intro U hU hne
    obtain ⟨x, hx⟩ := hne
    obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU x hx
    exact ((hfull x r hr).trans_le (measure_mono hrU)).ne'
  intro P Q hP hQ _ _ _
  have := hP
  have := hQ
  rw [squared_mmd_spectral_kernel_eq_integral]
  constructor
  · intro hzero
    have hint : Integrable (fun w ↦ ‖charFun P w - charFun Q w‖ ^ 2) L := by
      refine Integrable.of_bound (by fun_prop) 4 (ae_of_all _ fun w ↦ ?_)
      have hn : ‖charFun P w - charFun Q w‖ ≤ 2 :=
        (norm_sub_le _ _).trans (add_le_add (norm_charFun_le_one (μ := P) w)
          (norm_charFun_le_one (μ := Q) w) |>.trans (by norm_num))
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith [norm_nonneg (charFun P w - charFun Q w)]
    have hae : charFun P =ᵐ[L] charFun Q := by
      have h0 := (integral_eq_zero_iff_of_nonneg (fun w ↦ sq_nonneg _) hint).1 hzero
      filter_upwards [h0] with w hw
      exact sub_eq_zero.1 (norm_eq_zero.1 ((sq_eq_zero_iff).1 hw))
    exact Measure.ext_of_charFun (Measure.eq_of_ae_eq hae continuous_charFun continuous_charFun)
  · intro hPQ
    subst Q
    simp

/-- A nonzero even smooth Fourier perturbation vanishing at the origin is the difference of two
probability characteristic functions up to a positive normalization. -/
theorem exists_probability_measures_char_fun_sub_eq_of_even_bump [FiniteDimensional ℝ E]
    (ψ : E → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hψeven : ∀ x, ψ (-x) = ψ x) (hψ0 : ψ 0 = 0) (hψne : ∃ x, ψ x ≠ 0) :
    ∃ (P Q : Measure E) (Z : ℝ), IsProbabilityMeasure P ∧ IsProbabilityMeasure Q ∧
      0 < Z ∧ P ≠ Q ∧ ∀ w, charFun P w - charFun Q w = (ψ w : ℂ) / Z := by
  let Φ : E → ℂ := fun w ↦ (ψ ((-2 * Real.pi) • w) : ℂ)
  have hscale : (-2 * Real.pi : ℝ) ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  have hΦ : ContDiff ℝ ∞ Φ :=
    Complex.ofRealCLM.contDiff.comp (hψ.comp (contDiff_const_smul _))
  have hΦc : HasCompactSupport Φ :=
    (hψc.comp_smul hscale).comp_left Complex.ofReal_zero
  let F : SchwartzMap E ℂ := hΦc.toSchwartzMap hΦ
  let G : SchwartzMap E ℂ := 𝓕⁻ F
  let g : E → ℝ := fun x ↦ (G x).re
  have hg : Integrable g := Complex.reCLM.integrable_comp G.integrable
  have hgc : Continuous g := Complex.continuous_re.comp G.continuous
  have hΦeven (x : E) : Φ (-x) = conj (Φ x) := by
    simp [Φ, smul_neg, hψeven]
  have hΦi : Integrable Φ := hΦ.continuous.integrable_of_hasCompactSupport hΦc
  have hGre (x : E) : G x = (g x : ℂ) := by
    change (𝓕⁻ F) x = (((𝓕⁻ F) x).re : ℂ)
    rw [SchwartzMap.fourierInv_coe]
    exact TauCeti.fourierInv_eq_re_of_map_neg_eq_conj Φ hΦeven hΦi x
  have hFG : 𝓕 (G : E → ℂ) = Φ := by
    have heq : (𝓕 G : SchwartzMap E ℂ) = F := fourier_fourierInv_eq F
    funext w
    calc _ = (𝓕 G : SchwartzMap E ℂ) w := by rw [SchwartzMap.fourier_coe]
      _ = F w := congrArg (fun H : SchwartzMap E ℂ ↦ H w) heq
      _ = Φ w := rfl
  have hscalecomp (w : E) : (-2 * Real.pi) • (-((2 * Real.pi)⁻¹) • w) = w := by
    rw [smul_smul]
    convert one_smul ℝ w using 1
    field_simp
  have htrans (w : E) : (∫ x, g x • Complex.exp ((inner ℝ x w : ℂ) * Complex.I)) =
      (ψ w : ℂ) := by
    have hpoint := congrFun hFG (-((2 * Real.pi)⁻¹) • w)
    rw [Real.fourier_eq'] at hpoint
    have hexp (x : E) : -2 * Real.pi * inner ℝ x (-((2 * Real.pi)⁻¹) • w) = inner ℝ x w := by
      rw [inner_smul_right]
      field_simp
    simp_rw [hexp, hGre] at hpoint
    dsimp only [Φ] at hpoint
    rw [hscalecomp] at hpoint
    simpa only [Complex.real_smul, smul_eq_mul, mul_comm] using hpoint
  have hgi0 : (∫ x, g x) = 0 := by
    have h0 := htrans 0
    simp only [inner_zero_right, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
      Complex.real_smul, mul_one, hψ0, integral_complex_ofReal] at h0
    exact Complex.ofReal_injective h0
  have hgne : ∃ x, g x ≠ 0 := by
    by_contra h
    push Not at h
    obtain ⟨w, hw⟩ := hψne
    have ht := htrans w
    simp only [h, zero_smul, integral_zero] at ht
    exact hw (Complex.ofReal_eq_zero.1 ht.symm)
  obtain ⟨x, hx⟩ := hgne
  let Z := ∫ x, |g x|
  have hZ : 0 < Z := integral_pos_of_integrable_nonneg_ne_zero hgc.abs hg.abs
    (fun _ ↦ abs_nonneg _) (abs_ne_zero.2 hx)
  let p : E → ℝ := fun x ↦ (|g x| + g x) / Z
  let q : E → ℝ := fun x ↦ |g x| / Z
  have hp0 (x : E) : 0 ≤ p x := div_nonneg (by linarith [neg_abs_le (g x)]) hZ.le
  have hq0 (x : E) : 0 ≤ q x := div_nonneg (abs_nonneg _) hZ.le
  have hpi : Integrable p := (hg.abs.add hg).div_const Z
  have hqi : Integrable q := hg.abs.div_const Z
  have hpm : Measurable p := (hgc.abs.add hgc).div_const Z |>.measurable
  have hqm : Measurable q := hgc.abs.div_const Z |>.measurable
  have hp1 : (∫ x, p x) = 1 := by
    rw [show p = fun x ↦ (|g x| + g x) / Z from rfl, integral_div, integral_add hg.abs hg,
      hgi0, add_zero, show (∫ x, |g x|) = Z from rfl, div_self hZ.ne']
  have hq1 : (∫ x, q x) = 1 := by
    rw [show q = fun x ↦ |g x| / Z from rfl, integral_div,
      show (∫ x, |g x|) = Z from rfl, div_self hZ.ne']
  let P := volume.withDensity fun x ↦ ENNReal.ofReal (p x)
  let Q := volume.withDensity fun x ↦ ENNReal.ofReal (q x)
  have hP : IsProbabilityMeasure P := by
    constructor
    change (volume.withDensity fun x ↦ ENNReal.ofReal (p x)) univ = 1
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hpi (ae_of_all _ hp0), hp1, ENNReal.ofReal_one]
  have hQ : IsProbabilityMeasure Q := by
    constructor
    change (volume.withDensity fun x ↦ ENNReal.ofReal (q x)) univ = 1
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hqi (ae_of_all _ hq0), hq1, ENNReal.ofReal_one]
  have hdiff (w : E) : charFun P w - charFun Q w = (ψ w : ℂ) / Z := by
    rw [charFun_apply, charFun_apply,
      TauCeti.Probability.integral_withDensity_ofReal hpm.aemeasurable (ae_of_all _ hp0),
      TauCeti.Probability.integral_withDensity_ofReal hqm.aemeasurable (ae_of_all _ hq0)]
    have hchar : AEStronglyMeasurable (fun x : E ↦ Complex.exp ((inner ℝ x w : ℂ) * Complex.I))
        volume := by fun_prop
    have hcharb : ∀ᵐ x : E, ‖Complex.exp ((inner ℝ x w : ℂ) * Complex.I)‖ ≤ 1 :=
      ae_of_all _ fun x ↦ by simp [Complex.norm_exp]
    have hip : Integrable (fun x ↦ p x • Complex.exp ((inner ℝ x w : ℂ) * Complex.I)) volume :=
      hpi.smul_bdd 1 hchar hcharb
    have hiq : Integrable (fun x ↦ q x • Complex.exp ((inner ℝ x w : ℂ) * Complex.I)) volume :=
      hqi.smul_bdd 1 hchar hcharb
    rw [← integral_sub hip hiq]
    have heq (x : E) : p x • Complex.exp ((inner ℝ x w : ℂ) * Complex.I) -
        q x • Complex.exp ((inner ℝ x w : ℂ) * Complex.I) =
        (Z⁻¹ : ℝ) • (g x • Complex.exp ((inner ℝ x w : ℂ) * Complex.I)) := by
      rw [← sub_smul, smul_smul]
      congr 1
      dsimp [p, q]
      ring
    simp_rw [heq]
    rw [integral_smul, htrans, Complex.real_smul]
    simp [div_eq_mul_inv, mul_comm]
  refine ⟨P, Q, Z, hP, hQ, hZ, ?_, hdiff⟩
  intro hPQ
  obtain ⟨w, hw⟩ := hψne
  have hd := hdiff w
  rw [hPQ, sub_self] at hd
  have hψw : (ψ w : ℂ) = 0 := ((div_eq_zero_iff).1 hd.symm).resolve_right (by exact_mod_cast hZ.ne')
  exact hw (Complex.ofReal_eq_zero.1 hψw)

omit [SecondCountableTopology E] in
/-- A ball missing from a symmetric spectral measure contains the support of a nonzero even
smooth Fourier perturbation which vanishes at the origin. -/
theorem exists_even_smooth_bump_of_spectral_gap [FiniteDimensional ℝ E] [Nontrivial E]
    (L : Measure E) (hsym : L.map (fun w ↦ -w) = L)
    (x : E) (r : ℝ) (hr : 0 < r) (hgap : L (Metric.ball x r) = 0) :
    ∃ ψ : E → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
      (∀ w, ψ (-w) = ψ w) ∧ ψ 0 = 0 ∧ (∃ w, ψ w ≠ 0) ∧ ∀ᵐ w ∂L, ψ w = 0 := by
  obtain ⟨c, hc0, hcx⟩ : ∃ c : E, c ≠ 0 ∧ dist c x < r := by
    by_cases hx : x = 0
    · obtain ⟨c, hc⟩ := exists_norm_eq E (half_pos hr).le
      refine ⟨c, ?_, ?_⟩
      · exact norm_ne_zero_iff.1 (hc.trans_ne (half_pos hr).ne')
      · simpa [hx, hc] using (half_lt_self hr)
    · exact ⟨x, hx, by simpa using hr⟩
  let ρ := min ((r - dist c x) / 2) (‖c‖ / 2)
  have hρ : 0 < ρ := lt_min (half_pos (sub_pos.2 hcx)) (half_pos (norm_pos_iff.2 hc0))
  have hρr : ρ ≤ (r - dist c x) / 2 := min_le_left _ _
  have hρc : ρ ≤ ‖c‖ / 2 := min_le_right _ _
  have hsub : Metric.ball c ρ ⊆ Metric.ball x r := by
    intro w hw
    have ht := dist_triangle w c x
    have hw' : dist w c < ρ := hw
    change dist w x < r
    linarith
  have hball : L (Metric.ball c ρ) = 0 := measure_mono_null hsub hgap
  have hnegball : L ((fun w : E ↦ -w) ⁻¹' Metric.ball c ρ) = 0 := by
    rw [← Measure.map_apply (by fun_prop) Metric.isOpen_ball.measurableSet, hsym, hball]
  let b : ContDiffBump c := ⟨ρ / 2, ρ, half_pos hρ, by linarith⟩
  let ψ : E → ℝ := fun w ↦ b w + b (-w)
  have hb0 : b 0 = 0 := by
    apply b.zero_of_le_dist
    change ρ ≤ dist 0 c
    rw [dist_zero_left]
    linarith [norm_nonneg c]
  have hbneg : HasCompactSupport (fun w ↦ b (-w)) := by
    simpa only [neg_one_smul] using b.hasCompactSupport.comp_smul (by norm_num : (-1 : ℝ) ≠ 0)
  refine ⟨ψ, b.contDiff.add (b.contDiff.comp contDiff_neg), b.hasCompactSupport.add hbneg,
    (fun w ↦ by simp [ψ, add_comm]), ?_, ?_, ?_⟩
  · simp [ψ, hb0]
  · refine ⟨c, ?_⟩
    have hbc : b c = 1 := b.one_of_mem_closedBall (by simp [b]; positivity)
    dsimp [ψ]
    have hbn : 0 ≤ b (-c) := b.nonneg
    rw [hbc]
    linarith
  · have hae := measure_eq_zero_iff_ae_notMem.1 hball
    have haen := measure_eq_zero_iff_ae_notMem.1 hnegball
    filter_upwards [hae, haen] with w hw hwn
    have hbw : b w = 0 := b.zero_of_le_dist (le_of_not_gt hw)
    have hbwn : b (-w) = 0 := b.zero_of_le_dist (le_of_not_gt hwn)
    simp [ψ, hbw, hbwn]

/-- A translation-invariant kernel with a finite symmetric spectral measure is characteristic
exactly when the spectral measure charges every open ball. -/
theorem is_characteristic_kernel_spectral_iff [FiniteDimensional ℝ E] [Nontrivial E]
    (L : Measure E) [IsFiniteMeasure L] (hsym : L.map (fun w ↦ -w) = L) :
    IsCharacteristicKernel (fun x y ↦ ∫ w, Real.cos (inner ℝ w (x - y)) ∂L) ↔
      ∀ x, ∀ r > 0, 0 < L (Metric.ball x r) := by
  refine ⟨?_, is_characteristic_kernel_spectral_of_full_support L⟩
  intro hk
  by_contra hnot
  push Not at hnot
  obtain ⟨x, r, hr, hgap⟩ := hnot
  have hgap0 : L (Metric.ball x r) = 0 := le_antisymm hgap bot_le
  obtain ⟨ψ, hψ, hψc, hψeven, hψ0, hψne, hψL⟩ :=
    exists_even_smooth_bump_of_spectral_gap L hsym x r hr hgap0
  obtain ⟨P, Q, Z, hP, hQ, hZ, hPQ, hdiff⟩ :=
    exists_probability_measures_char_fun_sub_eq_of_even_bump ψ hψ hψc hψeven hψ0 hψne
  have := hP
  have := hQ
  have hkm : Measurable (fun z : E × E ↦ ∫ w, Real.cos (inner ℝ w (z.1 - z.2)) ∂L) :=
    (show Measurable (fun z : (E × E) × E ↦
      Real.cos (inner ℝ z.2 (z.1.1 - z.1.2))) from by fun_prop).stronglyMeasurable.integral_prod_right'.measurable
  have hint (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
      Integrable (fun z : E × E ↦ ∫ w, Real.cos (inner ℝ w (z.1 - z.2)) ∂L) (μ.prod ν) := by
    refine Integrable.of_bound hkm.aestronglyMeasurable (L.real univ) (ae_of_all _ fun z ↦ ?_)
    have hb := norm_integral_le_of_norm_le_const (μ := L)
      (f := fun w ↦ Real.cos (inner ℝ w (z.1 - z.2))) (C := 1)
      (ae_of_all _ fun w ↦ by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one _)
    simpa only [one_mul] using hb
  have hzero : squaredMMD (fun x y ↦ ∫ w, Real.cos (inner ℝ w (x - y)) ∂L) P Q = 0 := by
    rw [squared_mmd_spectral_kernel_eq_integral]
    apply integral_eq_zero_of_ae
    filter_upwards [hψL] with w hw
    rw [hdiff, hw]
    simp
  exact hPQ ((hk P Q hP hQ (hint P P) (hint Q Q) (hint P Q)).1 hzero)

end CKSD
