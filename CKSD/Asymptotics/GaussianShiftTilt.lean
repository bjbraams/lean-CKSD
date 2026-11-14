module

public import TauCeti.Probability.Distributions.Gaussian.Density
public import TauCeti.Probability.Distributions.Gaussian.Affine
public import TauCeti.Probability.Distributions.Gaussian.Transforms
/-!
# Gaussian likelihood tilts for local asymptotic normality

Completing the covariance quadratic form shows that an exponential linear tilt
of `N(0,I)` is `N(Ih,I)`. The score-coordinate image of `N(h,I⁻¹)` has the same
law. The limiting likelihood ratio has expectation one, including in dimension
zero. These identities supply the Gaussian step of van der Vaart, *Asymptotic
Statistics* (1998), Theorem 7.10, printed pp. 98–99 (PDF pp. 114–115).

Pinned TauCeti supplies the nondegenerate Gaussian density, affine image law and
scalar moment-generating function. Mathlib supplies matrix inverses and symmetric
quadratic forms; the local proof completes the square directly.
-/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace
namespace CKSD
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
/-- Inverse covariance cancels covariance on Euclidean vectors. -/
theorem inv_covariance_apply_covariance {I : Matrix (Fin d) (Fin d) ℝ} (hI : I.PosDef) (h : E) :
    I⁻¹.toEuclideanLin (I.toEuclideanLin h) = h := by
  have he := congrArg (fun M : Matrix (Fin d) (Fin d) ℝ ↦ M.toEuclideanLin h)
    (I.nonsing_inv_mul (isUnit_iff_ne_zero.mpr hI.det_pos.ne'))
  simpa only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same, LinearMap.comp_apply,
    Matrix.toLpLin_one, LinearMap.id_apply] using he
/-- Completing the square in a Gaussian covariance quadratic form. -/
theorem covariance_quadratic_sub_covariance {I : Matrix (Fin d) (Fin d) ℝ}
    (hI : I.PosDef) (h x : E) :
    inner ℝ (x-I.toEuclideanLin h) (I⁻¹.toEuclideanLin (x-I.toEuclideanLin h)) =
      inner ℝ x (I⁻¹.toEuclideanLin x)-2*inner ℝ h x+inner ℝ h (I.toEuclideanLin h) := by
  have hs := Matrix.isSymmetric_toEuclideanLin_iff.mpr hI.isHermitian
  have hcross : inner ℝ (I.toEuclideanLin h) (I⁻¹.toEuclideanLin x) = inner ℝ h x := by
    rw [hs h (I⁻¹.toEuclideanLin x)]
    have he := congrArg (fun M : Matrix (Fin d) (Fin d) ℝ ↦ M.toEuclideanLin x)
      (I.mul_nonsing_inv (isUnit_iff_ne_zero.mpr hI.det_pos.ne'))
    have hh : I.toEuclideanLin (I⁻¹.toEuclideanLin x) = x := by
      simpa only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same, LinearMap.comp_apply,
        Matrix.toLpLin_one, LinearMap.id_apply] using he
    rw [hh]
  rw [map_sub, inv_covariance_apply_covariance hI]
  simp only [inner_sub_left, inner_sub_right]
  rw [hcross, real_inner_comm x h, real_inner_comm (I.toEuclideanLin h) h]
  ring
/-- Gaussian likelihood ratios shift the mean by covariance times the tilt vector. -/
theorem multivariate_gaussian_with_density_exp_inner
    {I : Matrix (Fin d) (Fin d) ℝ} (hI : I.PosDef) (h : E) :
    (multivariateGaussian (0:E) I).withDensity (fun x ↦ ENNReal.ofReal
      (Real.exp (inner ℝ h x-inner ℝ h (I.toEuclideanLin h)/2))) =
      multivariateGaussian (I.toEuclideanLin h) I := by
  rw [TauCeti.Probability.multivariateGaussian_eq_withDensity hI,
    TauCeti.Probability.multivariateGaussian_eq_withDensity hI]
  rw [← withDensity_mul volume (TauCeti.Probability.measurable_multivariateGaussianPDF 0 I)
    (by fun_prop)]
  congr 1
  funext x
  rw [Pi.mul_apply, TauCeti.Probability.multivariateGaussianPDF_def,
    TauCeti.Probability.multivariateGaussianPDF_def]
  rw [← ENNReal.ofReal_mul (TauCeti.Probability.multivariateGaussianPDFReal_nonneg 0 I x)]
  congr 1
  rw [TauCeti.Probability.multivariateGaussianPDFReal_def,
    TauCeti.Probability.multivariateGaussianPDFReal_def]
  simp only [sub_zero]
  rw [mul_assoc, ← Real.exp_add, covariance_quadratic_sub_covariance hI]
  congr 2
  ring
/-- The Gaussian score coordinate sends the shift experiment to covariance-shifted means. -/
theorem map_covariance_multivariate_gaussian_inverse
    {I : Matrix (Fin d) (Fin d) ℝ} (hI : I.PosDef) (h : E) :
    (multivariateGaussian h I⁻¹).map (Matrix.toEuclideanCLM (𝕜 := ℝ) I) =
      multivariateGaussian (I.toEuclideanLin h) I := by
  have ht : I.transpose = I := by
    ext i j
    simpa only [Matrix.transpose_apply, Matrix.conjTranspose_apply, star_trivial] using
      congrArg (fun A : Matrix (Fin d) (Fin d) ℝ ↦ A i j) hI.isHermitian.eq
  have hc : I*I⁻¹*I.transpose=I := by
    rw [I.mul_nonsing_inv (isUnit_iff_ne_zero.mpr hI.det_pos.ne'),Matrix.one_mul,ht]
  have he := TauCeti.Probability.map_affine_multivariateGaussian h hI.inv.posSemidef I (0:E)
  change (multivariateGaussian h I⁻¹).map (fun x ↦ I.toEuclideanLin x) = _
  simpa only [add_zero,hc] using he
/-- Covariance coordinates identify the Gaussian shift experiment with its likelihood tilt. -/
theorem map_gaussian_shift_eq_with_density
    {I : Matrix (Fin d) (Fin d) ℝ} (hI : I.PosDef) (h : E) :
    (multivariateGaussian h I⁻¹).map (Matrix.toEuclideanCLM (𝕜 := ℝ) I) =
      (multivariateGaussian (0:E) I).withDensity (fun x ↦ ENNReal.ofReal
        (Real.exp (inner ℝ h x-inner ℝ h (Matrix.toEuclideanCLM (𝕜 := ℝ) I h)/2))) := by
  have hc : Matrix.toEuclideanCLM (𝕜 := ℝ) I h = I.toEuclideanLin h := rfl
  rw [hc, map_covariance_multivariate_gaussian_inverse hI]
  exact (multivariate_gaussian_with_density_exp_inner hI h).symm
/-- The limiting Gaussian LAN likelihood ratio has expectation one. -/
theorem integral_exp_inner_sub_half_covariance
    {I : Matrix (Fin d) (Fin d) ℝ} (hI : I.PosSemidef) (h : E) :
    (∫ x, Real.exp (inner ℝ h x-inner ℝ h (Matrix.toEuclideanCLM (𝕜 := ℝ) I h)/2)
      ∂multivariateGaussian (0:E) I) = 1 := by
  have hc : Matrix.toEuclideanCLM (𝕜 := ℝ) I h = I.toEuclideanLin h := rfl
  rw [hc]
  simp_rw [sub_eq_add_neg,Real.exp_add]
  rw [integral_mul_const]
  have he := TauCeti.Probability.mgf_inner_multivariateGaussian (0:E) h hI 1
  simp only [mgf,one_mul,inner_zero_right,one_pow,mul_zero,zero_add] at he
  rw [he,← Real.exp_add]
  convert Real.exp_zero using 1
  congr 1
  ring
/-- A nonzero Gaussian LAN score has no atom at zero. -/
theorem multivariate_gaussian_affine_score_zero
    {I : Matrix (Fin d) (Fin d) ℝ} (hI : I.PosDef) (h : E) (hh : h ≠ 0) :
    multivariateGaussian (0:E) I
      {x | inner ℝ h x-inner ℝ h (Matrix.toEuclideanCLM (𝕜 := ℝ) I h)/2=0} = 0 := by
  have hc : Matrix.toEuclideanCLM (𝕜 := ℝ) I h = I.toEuclideanLin h := rfl
  rw [hc]
  have hn : h.ofLp ≠ 0 := by
    intro h0
    apply hh
    apply WithLp.ofLp_injective
    simpa using h0
  have hq : 0 < inner ℝ h (I.toEuclideanLin h) := by
    simpa [EuclideanSpace.inner_eq_star_dotProduct,Matrix.toEuclideanLin,
      Matrix.ofLp_toLpLin,Matrix.toLin'_apply,dotProduct_comm] using hI.dotProduct_mulVec_pos hn
  have hvar : (inner ℝ h (I.toEuclideanLin h)).toNNReal ≠ 0 := by
    exact (Real.toNNReal_pos.mpr hq).ne'
  let := nullSingletonClass_gaussianReal (μ := (0:ℝ)) hvar
  have hmap := TauCeti.Probability.map_inner_multivariateGaussian (0:E) h hI.posSemidef
  simp only [inner_zero_right] at hmap
  have heq : {x | inner ℝ h x-inner ℝ h (I.toEuclideanLin h)/2=0} =
      (fun x : E ↦ inner ℝ h x) ⁻¹' {inner ℝ h (I.toEuclideanLin h)/2} := by
    ext x
    simp only [Set.mem_ofPred_eq,Set.mem_preimage,Set.mem_singleton_iff,sub_eq_zero]
  rw [heq,← Measure.map_apply (by fun_prop) (measurableSet_singleton _),hmap,measure_singleton]
end CKSD
