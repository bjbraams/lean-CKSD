module

public import CKSD.Inference.Density
public import CKSD.Inference.Model
public import TauCeti.Probability.Distributions.Gaussian.Density
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import TauCeti.MeasureTheory.Integral.NormRpow
public import Mathlib.Probability.Distributions.Gaussian.Fernique


/-!
# Gaussian models: Stein's identity, James–Stein, Scheffé

Results of Section 101 on Gaussian models. Maximum likelihood in natural exponential families
is in `CKSD.Inference.ExponentialFamilyMLE`.

## Main results

* `CKSD.gaussian_integration_by_parts`: Stein's identity for `N(θ, v I)` (GAPS 101.64).
* `CKSD.james_stein_risk_eq_and_lt`: the risk of the James–Stein estimator (GAPS 101.57).
* `CKSD.scheffe_contrast_supremum`: the contrast supremum behind Scheffé's method (GAPS 101.60).

## References

The integration by parts writes the Gaussian law as a density against Lebesgue measure
(TauCeti's `multivariateGaussian_eq_withDensity`) and uses Mathlib's
`integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`. The James–Stein risk applies Stein's
identity to the regularized fields `(‖x‖² + ε)⁻¹ x` and passes to `ε → 0` by dominated
convergence; the integrability of `‖x‖⁻²` in dimension `p ≥ 3` uses TauCeti's
`integrableOn_norm_rpow_ball`.
-/
@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

attribute [local instance] Classical.propDecidable

variable {Θ X S V : Type*} [MeasurableSpace X] [MeasurableSpace S]
  [MeasurableSpace V]

/-- The isotropic Gaussian density `N(θ, v I)` in closed form: its value at `θ` times
`exp (-‖x - θ‖² / (2v))`. Stated for TauCeti's `multivariateGaussianPDFReal`. -/
theorem multivariate_gaussian_pdf_real_smul_one {p : ℕ} (θ : EuclideanSpace ℝ (Fin p)) (v : ℝ≥0)
    (hv : 0 < v) (x : EuclideanSpace ℝ (Fin p)) :
    TauCeti.Probability.multivariateGaussianPDFReal θ ((v : ℝ) • (1 : Matrix (Fin p) (Fin p) ℝ)) x =
      TauCeti.Probability.multivariateGaussianPDFReal θ
        ((v : ℝ) • (1 : Matrix (Fin p) (Fin p) ℝ)) θ *
        Real.exp (-((v : ℝ)⁻¹ * ‖x - θ‖ ^ 2) / 2) := by
  have hv' : (v : ℝ) ≠ 0 := (NNReal.coe_pos.2 hv).ne'
  have hinv : ((v : ℝ) • (1 : Matrix (Fin p) (Fin p) ℝ))⁻¹ = (v : ℝ)⁻¹ • 1 := by
    apply Matrix.inv_eq_left_inv
    rw [smul_mul_smul, Matrix.one_mul, inv_mul_cancel₀ hv', one_smul]
  simp only [TauCeti.Probability.multivariateGaussianPDFReal_def, hinv, sub_self, map_zero,
    inner_zero_left, neg_zero, zero_div, Real.exp_zero, mul_one]
  congr 2
  rw [map_smul, LinearMap.smul_apply, Matrix.toLpLin_one, LinearMap.id_apply, inner_smul_right,
    real_inner_self_eq_norm_sq]


/-- GAPS 101.64: Gaussian integration by parts (Stein's identity) for `X ~ N(θ, v I)` and a
continuously differentiable `g` with `g ∈ L²` and integrable partial derivatives:
`E[(Xᵢ - θᵢ) gᵢ(X)] = v E[∂ᵢ gᵢ(X)]`.
The proof writes the law as a density against Lebesgue measure
(TauCeti's `multivariateGaussian_eq_withDensity`) and applies Mathlib's
`integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`. -/
theorem gaussian_integration_by_parts {p : ℕ} (θ : EuclideanSpace ℝ (Fin p)) (v : ℝ≥0)
    (hv : 0 < v) (g : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p))
    (hg : ContDiff ℝ 1 g)
    (hL2 : MemLp g 2 (multivariateGaussian θ ((v : ℝ) • (1 : Matrix (Fin p) (Fin p) ℝ))))
    (hder : ∀ i, Integrable (fun x ↦ (fderiv ℝ g x (EuclideanSpace.single i 1)) i)
      (multivariateGaussian θ ((v : ℝ) • (1 : Matrix (Fin p) (Fin p) ℝ)))) (i : Fin p) :
    (∫ x, (x i - θ i) * g x i
        ∂multivariateGaussian θ ((v : ℝ) • (1 : Matrix (Fin p) (Fin p) ℝ))) =
      (v : ℝ) * ∫ x, (fderiv ℝ g x (EuclideanSpace.single i 1)) i
        ∂multivariateGaussian θ ((v : ℝ) • (1 : Matrix (Fin p) (Fin p) ℝ)) := by
  set P := multivariateGaussian θ ((v : ℝ) • (1 : Matrix (Fin p) (Fin p) ℝ)) with hPdef
  have hv' : (v : ℝ) ≠ 0 := (NNReal.coe_pos.2 hv).ne'
  have hS : ((v : ℝ) • (1 : Matrix (Fin p) (Fin p) ℝ)).PosDef :=
    Matrix.PosDef.one.smul (NNReal.coe_pos.2 hv)
  let φ := TauCeti.Probability.multivariateGaussianPDFReal θ
    ((v : ℝ) • (1 : Matrix (Fin p) (Fin p) ℝ))
  let e : EuclideanSpace ℝ (Fin p) := EuclideanSpace.single i 1
  have hφm : Measurable φ := TauCeti.Probability.measurable_multivariateGaussianPDFReal _ _
  have hφnn : ∀ x, 0 ≤ φ x := TauCeti.Probability.multivariateGaussianPDFReal_nonneg _ _
  have hden : HasDensity P volume φ :=
    ⟨hφm, ae_of_all _ hφnn, by
      show multivariateGaussian θ ((v : ℝ) • (1 : Matrix (Fin p) (Fin p) ℝ)) = _
      rw [TauCeti.Probability.multivariateGaussian_eq_withDensity hS θ,
        TauCeti.Probability.multivariateGaussianPDF_def]⟩
  have hint : ∀ h : EuclideanSpace ℝ (Fin p) → ℝ,
      Integrable h P ↔ Integrable (fun x ↦ φ x * h x) volume := by
    intro h
    rw [hden.2.2, integrable_withDensity_iff_integrable_smul' hφm.ennreal_ofReal
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
    simp only [ENNReal.toReal_ofReal (hφnn _), smul_eq_mul]
  -- the coordinate function `g i` and its partial derivative
  let gi : EuclideanSpace ℝ (Fin p) → ℝ := fun x ↦ g x i
  have hgd : Differentiable ℝ g := hg.differentiable one_ne_zero
  have hgi : ∀ x, HasFDerivAt gi ((EuclideanSpace.proj i).comp (fderiv ℝ g x)) x :=
    fun x ↦ (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin p) i).hasFDerivAt.comp x (hgd x).hasFDerivAt
  have hgi_fd : ∀ x, fderiv ℝ gi x e = fderiv ℝ g x e i := fun x ↦ by
    rw [(hgi x).fderiv]; rfl
  -- the derivative of the density
  let c := φ θ
  have hφeq : φ = fun x ↦ c * Real.exp (-((v : ℝ)⁻¹ * ‖x - θ‖ ^ 2) / 2) :=
    funext fun x ↦ multivariate_gaussian_pdf_real_smul_one θ v hv x
  have hφd : ∀ x, HasFDerivAt φ (c • (Real.exp (-((v : ℝ)⁻¹ * ‖x - θ‖ ^ 2) / 2) •
      ((-(v : ℝ)⁻¹ / 2) • (2 • (innerSL ℝ (x - θ)).comp (ContinuousLinearMap.id ℝ _))))) x := by
    intro x
    rw [hφeq]
    have h1 := HasFDerivAt.norm_sq ((hasFDerivAt_id x).sub_const θ)
    have h2 := (h1.const_mul (-(v : ℝ)⁻¹ / 2)).exp.const_mul c
    convert h2 using 2
    · simp only [id]; congr 1; ring_nf
    · simp only [id]; congr 2; ring_nf
  have hφ_fd : ∀ x, fderiv ℝ φ x e = -((v : ℝ)⁻¹ * (x i - θ i)) * φ x := fun x ↦ by
    rw [(hφd x).fderiv, hφeq]
    simp [e, EuclideanSpace.inner_single_right]
    ring_nf
  -- integrability under `P`
  have hmemLp_gi : MemLp gi 2 P :=
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin p) i).comp_memLp' hL2
  have hmemLp_x : MemLp (fun x : EuclideanSpace ℝ (Fin p) ↦ x i - θ i) 2 P :=
    (IsGaussian.memLp_dual (multivariateGaussian θ ((v : ℝ) • (1 : Matrix (Fin p) (Fin p) ℝ)))
      (EuclideanSpace.proj i) 2 (by simp)).sub (memLp_const _)
  have hxg : Integrable (fun x ↦ (x i - θ i) * gi x) P := hmemLp_x.integrable_mul hmemLp_gi
  have hgP : Integrable gi P := hmemLp_gi.integrable one_le_two
  have hf'g : Integrable (fun x ↦ fderiv ℝ φ x e * gi x) volume := by
    simp_rw [hφ_fd]
    refine (((hint _).1 hxg).const_mul (-(v : ℝ)⁻¹)).congr (ae_of_all _ fun x ↦ ?_)
    simp only
    ring
  have hfg' : Integrable (fun x ↦ φ x * fderiv ℝ gi x e) volume := by
    simp_rw [hgi_fd]
    exact (hint _).1 (hder i)
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hf'g hfg' ((hint _).1 hgP)
    (fun x _ ↦ (hφd x).differentiableAt) (fun x _ ↦ (hgi x).differentiableAt)
  rw [hden.integral_eq, hden.integral_eq]
  have hrw : (∫ x, φ x * (fderiv ℝ g x (EuclideanSpace.single i 1)) i) =
      ∫ x, φ x * fderiv ℝ gi x e := by
    simp_rw [hgi_fd]; rfl
  rw [hrw, hibp]
  simp_rw [hφ_fd]
  rw [← integral_neg, ← integral_const_mul]
  congr 1
  funext x
  field_simp
  ring

/-- The derivative of the regularized James–Stein shrinkage field `y ↦ (‖y‖² + ε)⁻¹ y`. -/
private theorem has_f_deriv_at_inv_norm_sq_add_smul {p : ℕ} {ε : ℝ} (hε : 0 < ε)
    (x : EuclideanSpace ℝ (Fin p)) :
    HasFDerivAt (fun y : EuclideanSpace ℝ (Fin p) ↦ (‖y‖ ^ 2 + ε)⁻¹ • y)
      ((‖x‖ ^ 2 + ε)⁻¹ • ContinuousLinearMap.id ℝ _ +
        ((-((‖x‖ ^ 2 + ε) ^ 2)⁻¹) •
          (2 • (innerSL ℝ x).comp (ContinuousLinearMap.id ℝ _))).smulRight x) x := by
  have h1 : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin p) ↦ ‖y‖ ^ 2 + ε)
      (2 • (innerSL ℝ x).comp (ContinuousLinearMap.id ℝ _)) x :=
    ((hasFDerivAt_id x).norm_sq).add_const ε
  have hne : ‖x‖ ^ 2 + ε ≠ 0 := by positivity
  have h2 := (hasDerivAt_inv hne).comp_hasFDerivAt x h1
  exact h2.smul (hasFDerivAt_id x)

/-- The diagonal partial derivatives of `y ↦ (‖y‖² + ε)⁻¹ y`. -/
private theorem fderiv_inv_norm_sq_add_smul_apply {p : ℕ} {ε : ℝ} (hε : 0 < ε)
    (x : EuclideanSpace ℝ (Fin p)) (i : Fin p) :
    fderiv ℝ (fun y : EuclideanSpace ℝ (Fin p) ↦ (‖y‖ ^ 2 + ε)⁻¹ • y) x
      (EuclideanSpace.single i 1) i =
      (‖x‖ ^ 2 + ε)⁻¹ - 2 * x i ^ 2 / (‖x‖ ^ 2 + ε) ^ 2 := by
  rw [(has_f_deriv_at_inv_norm_sq_add_smul hε x).fderiv]
  simp [EuclideanSpace.inner_single_right]
  ring

/-- The law `N(θ, I)` has a measurable, bounded, Lebesgue-integrable density, maximal at `θ`. -/
private theorem multivariate_gaussian_one_density {p : ℕ} (θ : EuclideanSpace ℝ (Fin p)) :
    let φ := TauCeti.Probability.multivariateGaussianPDFReal θ (1 : Matrix (Fin p) (Fin p) ℝ)
    Measurable φ ∧ (∀ x, 0 ≤ φ x) ∧ (∀ x, φ x ≤ φ θ) ∧
      multivariateGaussian θ 1 = volume.withDensity (fun x ↦ ENNReal.ofReal (φ x)) ∧
      Integrable φ volume := by
  intro φ
  have hφm : Measurable φ := TauCeti.Probability.measurable_multivariateGaussianPDFReal _ _
  have hφnn : ∀ x, 0 ≤ φ x := TauCeti.Probability.multivariateGaussianPDFReal_nonneg _ _
  have hden : multivariateGaussian θ 1 = volume.withDensity (fun x ↦ ENNReal.ofReal (φ x)) := by
    rw [TauCeti.Probability.multivariateGaussian_eq_withDensity Matrix.PosDef.one θ,
      TauCeti.Probability.multivariateGaussianPDF_def]
  refine ⟨hφm, hφnn, fun x ↦ ?_, hden, ?_⟩
  · have h := multivariate_gaussian_pdf_real_smul_one θ 1 one_pos x
    simp only [NNReal.coe_one, one_smul] at h
    change φ x ≤ φ θ
    rw [show φ x = _ from h]
    exact mul_le_of_le_one_right (hφnn θ) (Real.exp_le_one_iff.2 (by
      have := sq_nonneg ‖x - θ‖; simp only [inv_one, one_mul]; linarith))
  · refine ⟨hφm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ hφnn)]
    have h1 : (volume.withDensity (fun x ↦ ENNReal.ofReal (φ x))) univ = 1 := by
      rw [← hden]; exact measure_univ
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h1
    rw [h1]; exact ENNReal.one_lt_top

/-- In dimension `p ≥ 3`, `‖x‖⁻²` is integrable under `N(θ, I)`. -/
private theorem integrable_inv_norm_sq_multivariate_gaussian_one {p : ℕ} (hp : 3 ≤ p)
    (θ : EuclideanSpace ℝ (Fin p)) :
    Integrable (fun x : EuclideanSpace ℝ (Fin p) ↦ (‖x‖ ^ 2)⁻¹) (multivariateGaussian θ 1) := by
  obtain ⟨hφm, hφnn, hφle, hden, hφi⟩ := multivariate_gaussian_one_density θ
  set φ := TauCeti.Probability.multivariateGaussianPDFReal θ (1 : Matrix (Fin p) (Fin p) ℝ)
  rw [hden, integrable_withDensity_iff_integrable_smul' hφm.ennreal_ofReal
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (hφnn _), smul_eq_mul]
  have hball : IntegrableOn (fun x : EuclideanSpace ℝ (Fin p) ↦ ‖x‖ ^ (-2 : ℝ))
      (Metric.ball 0 1) volume :=
    TauCeti.integrableOn_norm_rpow_ball (by simp; omega)
  refine Integrable.mono' (((hball.integrable_indicator measurableSet_ball).const_mul (φ θ)).add
    hφi) (by fun_prop) (ae_of_all _ fun x ↦ ?_)
  rw [Real.norm_of_nonneg (mul_nonneg (hφnn x) (inv_nonneg.2 (sq_nonneg _)))]
  simp only [Pi.add_apply]
  by_cases hx : x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin p)) 1
  · rw [indicator_of_mem hx]
    have : (‖x‖ ^ 2)⁻¹ = ‖x‖ ^ (-2 : ℝ) := by
      rw [Real.rpow_neg (norm_nonneg _)]; norm_cast
    rw [this]
    have := mul_le_mul_of_nonneg_right (hφle x) (Real.rpow_nonneg (norm_nonneg x) (-2 : ℝ))
    linarith [hφnn x]
  · rw [indicator_of_notMem hx, mul_zero, zero_add]
    have h1 : 1 ≤ ‖x‖ := by simpa using hx
    have : (‖x‖ ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith)
    nlinarith [hφnn x]

/-- A squared coordinate is at most the squared Euclidean norm. -/
private theorem sq_apply_le_norm_sq {p : ℕ} (x : EuclideanSpace ℝ (Fin p)) (i : Fin p) :
    x i ^ 2 ≤ ‖x‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  exact Finset.single_le_sum (f := fun j ↦ x j ^ 2) (fun j _ ↦ sq_nonneg _) (Finset.mem_univ i)

/-- Stein's identity for the regularized shrinkage field `g(x) = (‖x‖² + ε)⁻¹ x` under
`N(θ, I)`: `E⟪X - θ, g X⟫ = E[p (‖X‖² + ε)⁻¹ - 2 ‖X‖² / (‖X‖² + ε)²]`. -/
private theorem integral_inner_inv_norm_sq_add_smul {p : ℕ} (θ : EuclideanSpace ℝ (Fin p)) {ε : ℝ}
    (hε : 0 < ε) :
    ∫ x, inner ℝ (x - θ) ((‖x‖ ^ 2 + ε)⁻¹ • x) ∂(multivariateGaussian θ 1) =
      ∫ x, ((p : ℝ) * (‖x‖ ^ 2 + ε)⁻¹ - 2 * ‖x‖ ^ 2 / (‖x‖ ^ 2 + ε) ^ 2)
        ∂(multivariateGaussian θ 1) := by
  set P := multivariateGaussian θ (1 : Matrix (Fin p) (Fin p) ℝ) with hPdef
  have hP : multivariateGaussian θ (((1 : ℝ≥0) : ℝ) • (1 : Matrix (Fin p) (Fin p) ℝ)) = P := by
    simp [hPdef]
  set g : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p) := fun y ↦ (‖y‖ ^ 2 + ε)⁻¹ • y
    with hg
  have hpos : ∀ x : EuclideanSpace ℝ (Fin p), 0 < ‖x‖ ^ 2 + ε := fun x ↦ by positivity
  have hgc : ContDiff ℝ 1 g := by
    have h1 : ContDiff ℝ 1 fun y : EuclideanSpace ℝ (Fin p) ↦ (‖y‖ ^ 2 + ε)⁻¹ :=
      ((contDiff_norm_sq ℝ).add contDiff_const).inv fun x ↦ (hpos x).ne'
    exact h1.smul contDiff_id
  have hgm : Measurable g := by fun_prop
  have hgL2 : MemLp g 2 P := by
    refine MemLp.of_le ((IsGaussian.memLp_two_id (μ := P)).const_smul ε⁻¹)
      hgm.aestronglyMeasurable (ae_of_all _ fun x ↦ ?_)
    simp only [g, norm_smul, Pi.smul_apply, id, Real.norm_eq_abs,
      abs_of_pos (inv_pos.2 (hpos x)), abs_of_pos (inv_pos.2 hε)]
    exact mul_le_mul_of_nonneg_right (inv_anti₀ hε (by linarith [sq_nonneg ‖x‖])) (norm_nonneg _)
  have hfd : ∀ (i : Fin p) (x : EuclideanSpace ℝ (Fin p)),
      fderiv ℝ g x (EuclideanSpace.single i 1) i =
        (‖x‖ ^ 2 + ε)⁻¹ - 2 * x i ^ 2 / (‖x‖ ^ 2 + ε) ^ 2 :=
    fun i x ↦ fderiv_inv_norm_sq_add_smul_apply hε x i
  have hdbound : ∀ (i : Fin p) (x : EuclideanSpace ℝ (Fin p)),
      |(‖x‖ ^ 2 + ε)⁻¹ - 2 * x i ^ 2 / (‖x‖ ^ 2 + ε) ^ 2| ≤ 3 / ε := by
    intro i x
    have h1 := sq_apply_le_norm_sq x i
    have h2 := hpos x
    have ha : (‖x‖ ^ 2 + ε)⁻¹ ≤ 1 / ε := by
      rw [one_div]; exact inv_anti₀ hε (by nlinarith [sq_nonneg ‖x‖])
    have hb : 2 * x i ^ 2 / (‖x‖ ^ 2 + ε) ^ 2 ≤ 2 / ε := by
      rw [div_le_div_iff₀ (by positivity) hε]
      nlinarith [sq_nonneg (x i), sq_nonneg ‖x‖]
    have hb0 : 0 ≤ 2 * x i ^ 2 / (‖x‖ ^ 2 + ε) ^ 2 := by positivity
    have ha0 : 0 ≤ (‖x‖ ^ 2 + ε)⁻¹ := (inv_pos.2 h2).le
    rw [abs_le]; constructor <;> [skip; skip] <;>
      · have : 3 / ε = 1 / ε + 2 / ε := by ring
        linarith
  have hdint : ∀ i, Integrable (fun x : EuclideanSpace ℝ (Fin p) ↦
      (‖x‖ ^ 2 + ε)⁻¹ - 2 * x i ^ 2 / (‖x‖ ^ 2 + ε) ^ 2) P := fun i ↦
    Integrable.of_bound (by fun_prop) (3 / ε) (ae_of_all _ fun x ↦ by
      rw [Real.norm_eq_abs]; exact hdbound i x)
  have hder : ∀ i, Integrable (fun x ↦ (fderiv ℝ g x (EuclideanSpace.single i 1)) i)
      (multivariateGaussian θ (((1 : ℝ≥0) : ℝ) • (1 : Matrix (Fin p) (Fin p) ℝ))) := by
    intro i; rw [hP]; simp_rw [hfd]; exact hdint i
  have hstein := fun i ↦ gaussian_integration_by_parts θ 1 one_pos g hgc (hP ▸ hgL2) hder i
  simp only [NNReal.coe_one, one_smul, one_mul, hfd] at hstein
  have hxi : ∀ i, MemLp (fun x : EuclideanSpace ℝ (Fin p) ↦ x i - θ i) 2 P := fun i ↦
    (IsGaussian.memLp_dual P (EuclideanSpace.proj i) 2 (by simp)).sub (memLp_const _)
  have hgi : ∀ i, MemLp (fun x ↦ g x i) 2 P := fun i ↦
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin p) i).comp_memLp' hgL2
  have hlhs : ∀ x : EuclideanSpace ℝ (Fin p), inner ℝ (x - θ) (g x) = ∑ i, (x i - θ i) * g x i :=
    fun x ↦ by simp [PiLp.inner_apply, mul_comm]
  have hrhs : ∀ x : EuclideanSpace ℝ (Fin p),
      (p : ℝ) * (‖x‖ ^ 2 + ε)⁻¹ - 2 * ‖x‖ ^ 2 / (‖x‖ ^ 2 + ε) ^ 2 =
        ∑ i, ((‖x‖ ^ 2 + ε)⁻¹ - 2 * x i ^ 2 / (‖x‖ ^ 2 + ε) ^ 2) := fun x ↦ by
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.mul_sum,
      ← EuclideanSpace.real_norm_sq_eq]
    simp
  change ∫ x, inner ℝ (x - θ) (g x) ∂P = _
  simp_rw [hlhs, hrhs]
  rw [integral_finsetSum (f := fun i x ↦ (x i - θ i) * g x i) _
      fun i _ ↦ (hxi i).integrable_mul (hgi i),
    integral_finsetSum _ fun i _ ↦ hdint i]
  exact Finset.sum_congr rfl fun i _ ↦ hstein i

/-- The risk of `X` itself: `E‖X - θ‖² = p` under `N(θ, I)`. -/
private theorem integral_norm_sub_sq_multivariate_gaussian_one {p : ℕ}
    (θ : EuclideanSpace ℝ (Fin p)) :
    ∫ x, ‖x - θ‖ ^ 2 ∂(multivariateGaussian θ 1) = p := by
  have hmean : ∀ i, ∫ x, x i ∂(multivariateGaussian θ (1 : Matrix (Fin p) (Fin p) ℝ)) = θ i :=
    fun i ↦ by
      simp
  have hvar : ∀ i, ∫ x, (x i - θ i) ^ 2 ∂(multivariateGaussian θ (1 : Matrix (Fin p) (Fin p) ℝ))
      = 1 := fun i ↦ by
    have h := variance_eval_multivariateGaussian (μ := θ) Matrix.PosSemidef.one i
    rw [variance_eq_integral (by fun_prop), hmean] at h
    simpa using h
  simp_rw [EuclideanSpace.real_norm_sq_eq, PiLp.sub_apply]
  rw [integral_finsetSum _ fun i _ ↦ ?_]
  · simp [hvar]
  · exact ((IsGaussian.memLp_dual _ (EuclideanSpace.proj i) 2 (by simp)).sub
      (memLp_const _)).integrable_sq

/-- The risk of the regularized James–Stein rule `x - c (‖x‖² + ε)⁻¹ x` under `N(θ, I)`. -/
private theorem integral_norm_sub_sub_smul_inv_norm_sq_add_smul_sq {p : ℕ}
    (θ : EuclideanSpace ℝ (Fin p)) {ε : ℝ} (hε : 0 < ε) (c : ℝ) :
    ∫ x, ‖x - θ - c • ((‖x‖ ^ 2 + ε)⁻¹ • x)‖ ^ 2 ∂(multivariateGaussian θ 1) =
      p - 2 * c * ∫ x, ((p : ℝ) * (‖x‖ ^ 2 + ε)⁻¹ - 2 * ‖x‖ ^ 2 / (‖x‖ ^ 2 + ε) ^ 2)
        ∂(multivariateGaussian θ 1) +
      c ^ 2 * ∫ x, ‖x‖ ^ 2 / (‖x‖ ^ 2 + ε) ^ 2 ∂(multivariateGaussian θ 1) := by
  set P := multivariateGaussian θ (1 : Matrix (Fin p) (Fin p) ℝ) with hPdef
  have hpos : ∀ x : EuclideanSpace ℝ (Fin p), 0 < ‖x‖ ^ 2 + ε := fun x ↦ by positivity
  have hid : MemLp (fun x : EuclideanSpace ℝ (Fin p) ↦ x) 2 P := IsGaussian.memLp_two_id
  have hsub : MemLp (fun x : EuclideanSpace ℝ (Fin p) ↦ x - θ) 2 P := hid.sub (memLp_const _)
  have hgle : ∀ x : EuclideanSpace ℝ (Fin p), ‖(‖x‖ ^ 2 + ε)⁻¹ • x‖ ≤ ε⁻¹ * ‖x‖ := fun x ↦ by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 (hpos x))]
    exact mul_le_mul_of_nonneg_right (inv_anti₀ hε (by linarith [sq_nonneg ‖x‖])) (norm_nonneg _)
  have hq : ∀ x : EuclideanSpace ℝ (Fin p), ‖(‖x‖ ^ 2 + ε)⁻¹ • x‖ ^ 2 =
      ‖x‖ ^ 2 / (‖x‖ ^ 2 + ε) ^ 2 := fun x ↦ by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 (hpos x)), mul_pow, inv_pow,
      div_eq_mul_inv, mul_comm]
  have hqb : ∀ x : EuclideanSpace ℝ (Fin p), ‖x‖ ^ 2 / (‖x‖ ^ 2 + ε) ^ 2 ≤ 1 / ε := fun x ↦ by
    rw [div_le_div_iff₀ (by positivity) hε]; nlinarith [sq_nonneg ‖x‖, hpos x]
  have hqint : Integrable (fun x : EuclideanSpace ℝ (Fin p) ↦ ‖x‖ ^ 2 / (‖x‖ ^ 2 + ε) ^ 2) P :=
    Integrable.of_bound (Measurable.aestronglyMeasurable (by fun_prop)) (1 / ε)
      (ae_of_all _ fun x ↦ by rw [Real.norm_of_nonneg (by positivity)]; exact hqb x)
  have hinner : Integrable (fun x : EuclideanSpace ℝ (Fin p) ↦
      inner ℝ (x - θ) ((‖x‖ ^ 2 + ε)⁻¹ • x)) P := by
    refine Integrable.mono' (((hsub.norm.integrable_mul hid.norm)).const_mul ε⁻¹)
      (by fun_prop) (ae_of_all _ fun x ↦ ?_)
    refine (norm_inner_le_norm _ _).trans ?_
    have := mul_le_mul_of_nonneg_left (hgle x) (norm_nonneg (x - θ))
    simp only [Pi.mul_apply]
    linarith [this]
  have hexp : ∀ x : EuclideanSpace ℝ (Fin p), ‖x - θ - c • ((‖x‖ ^ 2 + ε)⁻¹ • x)‖ ^ 2 =
      ‖x - θ‖ ^ 2 - 2 * c * inner ℝ (x - θ) ((‖x‖ ^ 2 + ε)⁻¹ • x) +
        c ^ 2 * (‖x‖ ^ 2 / (‖x‖ ^ 2 + ε) ^ 2) := fun x ↦ by
    rw [@norm_sub_sq_real, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, hq, inner_smul_right]
    ring
  have hsq : Integrable (fun x : EuclideanSpace ℝ (Fin p) ↦ ‖x - θ‖ ^ 2) P :=
    hsub.integrable_norm_pow (by norm_num)
  simp_rw [hexp]
  have h1 : Integrable (fun x : EuclideanSpace ℝ (Fin p) ↦
      ‖x - θ‖ ^ 2 - 2 * c * inner ℝ (x - θ) ((‖x‖ ^ 2 + ε)⁻¹ • x)) P := hsq.sub (hinner.const_mul _)
  rw [integral_add h1 (hqint.const_mul _),
    integral_sub hsq (hinner.const_mul _), integral_const_mul,
    integral_const_mul, integral_norm_sub_sq_multivariate_gaussian_one,
    integral_inner_inv_norm_sq_add_smul θ hε]

/-- GAPS 101.57: the James–Stein estimator `δ(x) = (1 - (p - 2) / ‖x‖²) x` for `X ~ N(θ, I)` in
dimension `p ≥ 3` has risk `p - (p - 2)² E‖X‖⁻²`, strictly smaller than the risk `p` of `X`. -/
theorem james_stein_risk_eq_and_lt {p : ℕ} (hp : 3 ≤ p) (θ : EuclideanSpace ℝ (Fin p)) :
    let P := multivariateGaussian θ (1 : Matrix (Fin p) (Fin p) ℝ);
    let δ := fun x : EuclideanSpace ℝ (Fin p) ↦ (1 - ((p : ℝ) - 2) / ‖x‖ ^ 2) • x;
    (∫ x, ‖δ x - θ‖ ^ 2 ∂P) = (p : ℝ) - ((p : ℝ) - 2) ^ 2 *
      (∫ x, (‖x‖ ^ 2)⁻¹ ∂P) ∧ (∫ x, ‖δ x - θ‖ ^ 2 ∂P) < p := by
  intro P δ
  set c : ℝ := (p : ℝ) - 2 with hc
  set J := ∫ x, (‖x‖ ^ 2)⁻¹ ∂P with hJ
  have hJi : Integrable (fun x : EuclideanSpace ℝ (Fin p) ↦ (‖x‖ ^ 2)⁻¹) P :=
    integrable_inv_norm_sq_multivariate_gaussian_one hp θ
  -- almost every point is nonzero
  have hne : ∀ᵐ x ∂P, x ≠ 0 := by
    obtain ⟨-, -, -, hden, -⟩ := multivariate_gaussian_one_density θ
    have hac : P ≪ volume := by
      rw [show P = _ from hden]; exact withDensity_absolutelyContinuous _ _
    have : NeZero p := ⟨by omega⟩
    exact hac (by simp)
  have hsq : Integrable (fun x : EuclideanSpace ℝ (Fin p) ↦ ‖x - θ‖ ^ 2) P :=
    ((IsGaussian.memLp_two_id (μ := P)).sub (memLp_const θ)).integrable_norm_pow (by norm_num)
  set ε : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1) with hεdef
  have hε0 : ∀ n, 0 < ε n := fun n ↦ by positivity
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  -- pointwise limit of `(‖x‖² + ε)⁻¹`
  have hinvlim : ∀ x : EuclideanSpace ℝ (Fin p), x ≠ 0 →
      Tendsto (fun n ↦ (‖x‖ ^ 2 + ε n)⁻¹) atTop (𝓝 (‖x‖ ^ 2)⁻¹) := fun x hx ↦ by
    have h := (tendsto_const_nhds (x := ‖x‖ ^ 2)).add hεlim
    rw [add_zero] at h
    exact h.inv₀ (by positivity)
  have hinvle : ∀ (n : ℕ) (x : EuclideanSpace ℝ (Fin p)), x ≠ 0 →
      (‖x‖ ^ 2 + ε n)⁻¹ ≤ (‖x‖ ^ 2)⁻¹ := fun n x hx ↦
    inv_anti₀ (by positivity) (by linarith [hε0 n])
  -- the regularized risks
  set R : ℕ → ℝ := fun n ↦ ∫ x, ‖x - θ - c • ((‖x‖ ^ 2 + ε n)⁻¹ • x)‖ ^ 2 ∂P with hR
  have hRlim : Tendsto R atTop (𝓝 (∫ x, ‖δ x - θ‖ ^ 2 ∂P)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun x ↦ 2 * ‖x - θ‖ ^ 2 + 2 * c ^ 2 * (‖x‖ ^ 2)⁻¹)
      (fun n ↦ Measurable.aestronglyMeasurable (by fun_prop))
      ((hsq.const_mul 2).add (hJi.const_mul _)) (fun n ↦ ?_) ?_
    · filter_upwards [hne] with x hx
      have hx2 : 0 < ‖x‖ ^ 2 := by positivity
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      have hg : ‖c • ((‖x‖ ^ 2 + ε n)⁻¹ • x)‖ ^ 2 ≤ c ^ 2 * (‖x‖ ^ 2)⁻¹ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_pos (inv_pos.2 (by linarith [hε0 n] : (0 : ℝ) < ‖x‖ ^ 2 + ε n)), mul_pow,
          mul_pow, sq_abs]
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
        have h1 := hinvle n x hx
        have h2 : (‖x‖ ^ 2 + ε n)⁻¹ ^ 2 * ‖x‖ ^ 2 ≤ (‖x‖ ^ 2)⁻¹ ^ 2 * ‖x‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) h1 2) hx2.le
        calc (‖x‖ ^ 2 + ε n)⁻¹ ^ 2 * ‖x‖ ^ 2 ≤ (‖x‖ ^ 2)⁻¹ ^ 2 * ‖x‖ ^ 2 := h2
          _ = (‖x‖ ^ 2)⁻¹ := by field_simp
      have h1 := norm_sub_le (x - θ) (c • ((‖x‖ ^ 2 + ε n)⁻¹ • x))
      have h2 := norm_nonneg (x - θ - c • ((‖x‖ ^ 2 + ε n)⁻¹ • x))
      have h5 := pow_le_pow_left₀ h2 h1 2
      nlinarith [sq_nonneg (‖x - θ‖ - ‖c • ((‖x‖ ^ 2 + ε n)⁻¹ • x)‖)]
    · filter_upwards [hne] with x hx
      have h := ((hinvlim x hx).smul_const x).const_smul c
      have h2 := (tendsto_const_nhds (x := x - θ)).sub h
      have h3 := (continuous_norm.tendsto _).comp h2 |>.pow 2
      have hδ : δ x - θ = x - θ - c • ((‖x‖ ^ 2)⁻¹ • x) := by
        change (1 - ((p : ℝ) - 2) / ‖x‖ ^ 2) • x - θ = _
        rw [sub_smul, one_smul, div_eq_mul_inv, mul_smul]
        abel
      rw [hδ]
      exact h3
  have hqle : ∀ (n : ℕ) (x : EuclideanSpace ℝ (Fin p)), x ≠ 0 →
      ‖x‖ ^ 2 / (‖x‖ ^ 2 + ε n) ^ 2 ≤ (‖x‖ ^ 2)⁻¹ := fun n x hx ↦ by
    have hx2 : 0 < ‖x‖ ^ 2 := by positivity
    rw [div_le_iff₀ (by positivity), inv_mul_eq_div, le_div_iff₀ hx2]
    nlinarith [hε0 n]
  have hqeq : ∀ (n : ℕ) (x : EuclideanSpace ℝ (Fin p)),
      ‖x‖ ^ 2 / (‖x‖ ^ 2 + ε n) ^ 2 = ‖x‖ ^ 2 * (‖x‖ ^ 2 + ε n)⁻¹ ^ 2 := fun n x ↦ by
    rw [div_eq_mul_inv, inv_pow]
  have hqlim : ∀ x : EuclideanSpace ℝ (Fin p), x ≠ 0 →
      Tendsto (fun n ↦ ‖x‖ ^ 2 / (‖x‖ ^ 2 + ε n) ^ 2) atTop (𝓝 (‖x‖ ^ 2)⁻¹) := fun x hx ↦ by
    have hx2 : 0 < ‖x‖ ^ 2 := by positivity
    simp_rw [hqeq]
    convert ((hinvlim x hx).pow 2).const_mul (‖x‖ ^ 2) using 2
    field_simp
  have hB : Tendsto (fun n ↦ ∫ x, ‖x‖ ^ 2 / (‖x‖ ^ 2 + ε n) ^ 2 ∂P) atTop (𝓝 J) :=
    tendsto_integral_of_dominated_convergence _
      (fun n ↦ Measurable.aestronglyMeasurable (by fun_prop)) hJi
      (fun n ↦ by
        filter_upwards [hne] with x hx
        rw [Real.norm_of_nonneg (by positivity)]
        exact hqle n x hx)
      (by filter_upwards [hne] with x hx; exact hqlim x hx)
  have hA : Tendsto (fun n ↦ ∫ x, ((p : ℝ) * (‖x‖ ^ 2 + ε n)⁻¹ - 2 * ‖x‖ ^ 2 /
      (‖x‖ ^ 2 + ε n) ^ 2) ∂P) atTop (𝓝 (c * J)) := by
    rw [hJ, ← integral_const_mul]
    refine tendsto_integral_of_dominated_convergence (fun x ↦ ((p : ℝ) + 2) * (‖x‖ ^ 2)⁻¹)
      (fun n ↦ Measurable.aestronglyMeasurable (by fun_prop)) (hJi.const_mul _)
      (fun n ↦ ?_) ?_
    · filter_upwards [hne] with x hx
      have h1 := hinvle n x hx
      have h2 := hqle n x hx
      have h3 : 0 ≤ (‖x‖ ^ 2 + ε n)⁻¹ := (inv_pos.2 (by linarith [hε0 n, sq_nonneg ‖x‖])).le
      have h4 : 0 ≤ ‖x‖ ^ 2 / (‖x‖ ^ 2 + ε n) ^ 2 := by positivity
      have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
      have h5 : 2 * ‖x‖ ^ 2 / (‖x‖ ^ 2 + ε n) ^ 2 = 2 * (‖x‖ ^ 2 / (‖x‖ ^ 2 + ε n) ^ 2) :=
        mul_div_assoc _ _ _
      have h6 : 0 ≤ (‖x‖ ^ 2)⁻¹ := inv_nonneg.2 (sq_nonneg _)
      have h7 := mul_le_mul_of_nonneg_left h1 hp0
      have h8 := mul_nonneg hp0 h3
      rw [Real.norm_eq_abs, abs_le, h5]
      constructor <;> nlinarith
    · filter_upwards [hne] with x hx
      have h := ((hinvlim x hx).const_mul (p : ℝ)).sub ((hqlim x hx).const_mul 2)
      convert h using 1
      · funext n; ring
      · rw [hc, sub_mul]
  have hRform : ∀ n, R n = p - 2 * c * (∫ x, ((p : ℝ) * (‖x‖ ^ 2 + ε n)⁻¹ - 2 * ‖x‖ ^ 2 /
      (‖x‖ ^ 2 + ε n) ^ 2) ∂P) + c ^ 2 * ∫ x, ‖x‖ ^ 2 / (‖x‖ ^ 2 + ε n) ^ 2 ∂P :=
    fun n ↦ integral_norm_sub_sub_smul_inv_norm_sq_add_smul_sq θ (hε0 n) c
  have hRlim' : Tendsto R atTop (𝓝 ((p : ℝ) - 2 * c * (c * J) + c ^ 2 * J)) := by
    rw [show R = _ from funext hRform]
    exact (tendsto_const_nhds.sub (hA.const_mul _)).add (hB.const_mul _)
  have heq := tendsto_nhds_unique hRlim hRlim'
  have hJpos : 0 < J := by
    have hJ0 : 0 ≤ J := integral_nonneg fun x ↦ inv_nonneg.2 (sq_nonneg _)
    refine lt_of_le_of_ne hJ0 fun h ↦ ?_
    have h0 := (integral_eq_zero_iff_of_nonneg (fun x ↦ inv_nonneg.2 (sq_nonneg _)) hJi).1 h.symm
    have : ∀ᵐ x ∂P, False := by
      filter_upwards [h0, hne] with x hx hx'
      have : 0 < (‖x‖ ^ 2)⁻¹ := by positivity
      simp only [Pi.zero_apply] at hx
      linarith
    exact this.exists.elim fun _ h ↦ h
  have hc1 : 1 ≤ c := by
    simp only [c]; have : (3 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  refine ⟨by rw [heq]; ring, ?_⟩
  rw [heq]
  nlinarith [mul_pos (by nlinarith : 0 < c ^ 2) hJpos]

/-- GAPS 101.60: the simultaneous-contrast supremum underlying Scheffé's method: for `v` in a
subspace `S`, `sup_{u ∈ S, u ≠ 0} ⟪u, v⟫² / (s² ‖u‖²) = ‖v‖² / s²` (the supremum is attained at
`u = v`; for `v = 0` it is `0`). The Gaussian pivot of the method is not included. -/
theorem scheffe_contrast_supremum {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (S : Submodule ℝ H) (v : H) (hv : v ∈ S) (s : ℝ) (hs : 0 < s) :
    sSup {r : ℝ | ∃ u ∈ S, u ≠ 0 ∧ r = inner ℝ u v ^ 2 / (s ^ 2 * ‖u‖ ^ 2)} =
      ‖v‖ ^ 2 / s ^ 2 := by
  by_cases hv0 : v = 0
  · subst v
    by_cases hS : ∃ u ∈ S, u ≠ (0 : H)
    · have hset : {r : ℝ | ∃ u ∈ S, u ≠ 0 ∧
          r = inner ℝ u (0 : H) ^ 2 / (s ^ 2 * ‖u‖ ^ 2)} = {0} := by
        ext r
        simp only [inner_zero_right, zero_pow two_ne_zero, zero_div, mem_ofPred_eq,
          mem_singleton_iff]
        exact ⟨fun ⟨_, _, _, hr⟩ ↦ hr, fun hr ↦ by
          obtain ⟨u, hu, hune⟩ := hS
          exact ⟨u, hu, hune, hr⟩⟩
      rw [hset]
      simp
    · have hset : {r : ℝ | ∃ u ∈ S, u ≠ 0 ∧
          r = inner ℝ u (0 : H) ^ 2 / (s ^ 2 * ‖u‖ ^ 2)} = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        rintro r ⟨u, hu, hune, _⟩
        exact hS ⟨u, hu, hune⟩
      rw [hset]
      simp
  · let R := {r : ℝ | ∃ u ∈ S, u ≠ 0 ∧ r = inner ℝ u v ^ 2 / (s ^ 2 * ‖u‖ ^ 2)}
    have hupper : ∀ r ∈ R, r ≤ ‖v‖ ^ 2 / s ^ 2 := by
      rintro r ⟨u, hu, hune, rfl⟩
      have hu0 : 0 < ‖u‖ := norm_pos_iff.mpr hune
      have hcs := real_inner_mul_inner_self_le u v
      rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hcs
      apply (div_le_div_iff₀ (mul_pos (sq_pos_of_pos hs) (sq_pos_of_pos hu0))
        (sq_pos_of_pos hs)).mpr
      nlinarith [mul_nonneg (sq_nonneg s)
        (show 0 ≤ ‖u‖ ^ 2 * ‖v‖ ^ 2 - inner ℝ u v ^ 2 by nlinarith)]
    have hmem : ‖v‖ ^ 2 / s ^ 2 ∈ R := by
      refine ⟨v, hv, hv0, ?_⟩
      rw [real_inner_self_eq_norm_sq]
      field_simp [ne_of_gt hs, norm_ne_zero_iff.mpr hv0]
    exact le_antisymm (csSup_le ⟨_, hmem⟩ hupper) (le_csSup ⟨_, hupper⟩ hmem)

end CKSD
