module

public import CKSD.Bayes.Diffusion
public import TauCeti.Analysis.Calculus.Gradient
public import Mathlib.Analysis.InnerProductSpace.PiL2
/-!
# Large-step rejection for isotropic Gaussian MALA

For a Gaussian potential of precision `a`, the MALA log-acceptance ratio is
`h*a^2*(norm(x)^2-norm(y)^2)/4`. At a large effective step size, proposals from states bounded
away from zero have exponentially small acceptance on a high-probability noise event.
Simultaneous target/state rescaling reduces any physical step size to this regime.

The estimates support the quantifier order of the MALA lower-bound statement in GAPS 104.47:
the target and its curvature scale may be chosen after the physical step size. They do not by
themselves assert a fixed normalized target that is hard for every step size, or a target whose
condition number attains a prescribed upper bound. Chewi, Log-Concave Sampling (20 August 2026),
Theorem 7.6.5, printed page 210 (PDF page 222), supplies the sampling context and a stronger
normalized-curvature lower bound. The proofs here are direct Gaussian algebra and norm estimates.
-/

public section
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped NNReal ENNReal Topology RealInnerProductSpace
namespace CKSD
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
/-- The centered isotropic Gaussian potential with precision `a`. -/
@[expose] def gaussianPrecisionPotential (a : ℝ) (x : E) : ℝ := a / 2 * ‖x‖ ^ 2
/-- The potential as an explicit quadratic function. -/
theorem gaussian_precision_potential_def (a : ℝ) :
    gaussianPrecisionPotential (d := d) a = fun x ↦ a / 2 * ‖x‖ ^ 2 := rfl

/-- Evaluation of the quadratic Gaussian potential. -/
@[simp] theorem gaussian_precision_potential_apply (a : ℝ) (x : E) :
    gaussianPrecisionPotential a x = a / 2 * ‖x‖ ^ 2 := rfl

/-- The gradient of the Gaussian potential with precision `a`. -/
@[expose] def gaussianPrecisionGradient (a : ℝ) (x : E) : E := a • x
/-- The gradient as an explicit scalar linear map. -/
theorem gaussian_precision_gradient_def (a : ℝ) :
    gaussianPrecisionGradient (d := d) a = fun x ↦ a • x := rfl

/-- Evaluation of the linear Gaussian gradient. -/
@[simp] theorem gaussian_precision_gradient_apply (a : ℝ) (x : E) :
    gaussianPrecisionGradient a x = a • x := rfl

/-- The gradient identity for the isotropic Gaussian potential. -/
theorem has_gradient_at_gaussian_precision_potential (a : ℝ) (x : E) :
    HasGradientAt (gaussianPrecisionPotential a) (gaussianPrecisionGradient a x) x := by
  rw [gaussian_precision_potential_def, gaussian_precision_gradient_apply]
  simpa only [add_zero] using
    TauCeti.hasGradientAt_mul_norm_sq_add a 0 x
/-- The MALA log-acceptance ratio for an isotropic Gaussian is a difference of squared norms. -/
theorem mala_acceptance_gaussian_precision (a : ℝ) {h : ℝ} (hh : 0 < h) (x y : E) :
    malaAcceptance (gaussianPrecisionPotential a) (gaussianPrecisionGradient a) h x y =
      min 1 (Real.exp ((h * a ^ 2 / 4) * (‖x‖ ^ 2 - ‖y‖ ^ 2))) := by
  unfold malaAcceptance gaussianPrecisionPotential gaussianPrecisionGradient
  congr 2
  have hxy : y - x + h • a • x = y - (1 - h * a) • x := by module
  have hyx : x - y + h • a • y = x - (1 - h * a) • y := by module
  rw [hxy, hyx, norm_sub_sq_real, norm_sub_sq_real]
  simp only [norm_smul, Real.norm_eq_abs, real_inner_smul_right, mul_pow, sq_abs]
  rw [real_inner_comm y x]
  field_simp
  ring
/-- At large step size, typical Gaussian proposals from states away from zero have large norm. -/
theorem norm_gaussian_proposal_ge {H a : ℝ} (hH : 4 ≤ H) (ha : 0 ≤ a) (x z : E)
    (hx : a ≤ ‖x‖) (hz : ‖z‖ ≤ a * Real.sqrt H / 8) :
    H / 2 * ‖x‖ ≤ ‖(1 - H) • x + Real.sqrt (2 * H) • z‖ := by
  have hH0 : 0 ≤ H := by linarith
  have hs2 : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hn : ‖Real.sqrt (2 * H) • z‖ ≤ H * a / 4 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    calc
      _ ≤ Real.sqrt (2 * H) * (a * Real.sqrt H / 8) :=
        mul_le_mul_of_nonneg_left hz (Real.sqrt_nonneg _)
      _ = Real.sqrt 2 * H * a / 8 := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) H]
        calc
          _ = Real.sqrt 2 * a * (Real.sqrt H * Real.sqrt H) / 8 := by ring
          _ = _ := by rw [Real.mul_self_sqrt hH0]; ring
      _ ≤ H * a / 4 := by nlinarith [mul_nonneg hH0 ha]
  have ht := norm_sub_norm_le ((1 - H) • x) ((1 - H) • x + Real.sqrt (2 * H) • z)
  have he : (1 - H) • x - ((1 - H) • x + Real.sqrt (2 * H) • z) =
      - (Real.sqrt (2 * H) • z) := by abel
  rw [he, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonpos (by linarith : 1 - H ≤ 0)] at ht
  nlinarith [mul_le_mul_of_nonneg_left hx hH0]
/-- Uniformly away from zero, large Gaussian MALA steps have exponentially small acceptance
on the typical proposal-noise event. -/
theorem mala_acceptance_gaussian_one_le_exp {H a : ℝ} (hH : 4 ≤ H) (ha : 0 ≤ a) (x z : E)
    (hx : a ≤ ‖x‖) (hz : ‖z‖ ≤ a * Real.sqrt H / 8) :
    malaAcceptance (gaussianPrecisionPotential 1) (gaussianPrecisionGradient 1) H x
      ((1 - H) • x + Real.sqrt (2 * H) • z) ≤ Real.exp ( - (H ^ 3 * a ^ 2 / 32)) := by
  have hH0 : 0 < H := by linarith
  rw [mala_acceptance_gaussian_precision 1 hH0]
  apply (min_le_right _ _).trans
  apply Real.exp_le_exp.mpr
  have hn := norm_gaussian_proposal_ge hH ha x z hx hz
  have hns : (H / 2 * ‖x‖) ^ 2 ≤ ‖(1 - H) • x + Real.sqrt (2 * H) • z‖ ^ 2 :=
    pow_le_pow_left₀ (by positivity) hn 2
  have hx2 : a ^ 2 ≤ ‖x‖ ^ 2 := pow_le_pow_left₀ ha hx 2
  have hH2 : 16 ≤ H ^ 2 := by nlinarith
  norm_num only [one_pow, mul_one]
  have hb : ‖x‖ ^ 2 - ‖(1 - H) • x + Real.sqrt (2 * H) • z‖ ^ 2 ≤ - (H ^ 2 * ‖x‖ ^ 2 / 8) := by
    have hH8 : 0 ≤ H ^ 2 - 8 := by linarith
    nlinarith [mul_nonneg hH8 (sq_nonneg ‖x‖)]
  have hmul := mul_le_mul_of_nonneg_left hx2 (sq_nonneg H)
  have hb' : ‖x‖ ^ 2 - ‖(1 - H) • x + Real.sqrt (2 * H) • z‖ ^ 2 ≤ - (H ^ 2 * a ^ 2 / 8) := by
    nlinarith
  have hHquarter : 0 ≤ H / 4 := by positivity
  have hlast := mul_le_mul_of_nonneg_left hb' hHquarter
  nlinarith
/-- Rescaling a Gaussian target rescales the effective MALA step by inverse variance. -/
theorem mala_acceptance_gaussian_rescale {σ h : ℝ} (hσ : 0 < σ) (hh : 0 < h) (x y : E) :
    malaAcceptance (gaussianPrecisionPotential ((σ⁻¹) ^ 2)) (gaussianPrecisionGradient ((σ⁻¹) ^ 2))
      h (σ • x) (σ • y) =
      malaAcceptance (gaussianPrecisionPotential 1) (gaussianPrecisionGradient 1)
        (h / σ ^ 2) x y := by
  rw [mala_acceptance_gaussian_precision _ hh,
    mala_acceptance_gaussian_precision 1 (div_pos hh (sq_pos_of_pos hσ))]
  congr 2
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, one_pow, mul_one]
  field_simp

/-- The Gaussian proposal commutes with simultaneous target and state rescaling. -/
theorem gaussian_proposal_rescale {σ h : ℝ} (hσ : 0 < σ) (hh : 0 < h) (x z : E) :
    σ • x - h • gaussianPrecisionGradient ((σ⁻¹) ^ 2) (σ • x) + Real.sqrt (2 * h) • z =
      σ • ((1 - h / σ ^ 2) • x + Real.sqrt (2 * (h / σ ^ 2)) • z) := by
  have hs : σ * Real.sqrt (2 * (h / σ ^ 2)) = Real.sqrt (2 * h) := by
    have he : 2 * (h / σ ^ 2) = 2 * h / σ ^ 2 := by ring
    rw [he, Real.sqrt_div (by positivity),
      Real.sqrt_sq_eq_abs, abs_of_pos hσ]
    field_simp
  simp only [gaussianPrecisionGradient, smul_add, smul_smul]
  rw [hs, ← sub_smul]
  congr 1
  field_simp
end CKSD
