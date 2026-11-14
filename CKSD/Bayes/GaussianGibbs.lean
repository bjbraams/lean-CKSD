module

public import CKSD.Bayes.Diffusion
import CKSD.Bayes.GaussianSmoothing
import CKSD.Inference.Density
import TauCeti.Probability.Distributions.Gaussian.Quantile
/-!
# Gaussian Gibbs laws and warm initializations

The normalized Gibbs law of a positive isotropic quadratic potential is the corresponding
scaled standard Gaussian. Normalization follows from the already proved Gaussian smoothing
density, so no new Gaussian integral formula is needed. These adapters support Gaussian
examples for Metropolis-adjusted Langevin lower bounds, GAPS 104.47.
-/
public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology
namespace CKSD
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The Gibbs law of an isotropic quadratic potential is a scaled standard Gaussian. -/
theorem gibbs_measure_quadratic_eq_map_std_gaussian {σ : ℝ} (hσ : 0 < σ) :
    gibbsMeasure (fun x : E ↦ (σ⁻¹) ^ 2 / 2 * ‖x‖ ^ 2) =
      (stdGaussian E).map (fun z ↦ σ • z) := by
  let V : E → ℝ := fun x ↦ (σ⁻¹) ^ 2 / 2 * ‖x‖ ^ 2
  let c : ℝ := |σ|⁻¹ ^ Module.finrank ℝ E *
    (2 * Real.pi) ^ (-(Module.finrank ℝ E : ℝ) / 2)
  have he (x : E) : gaussianSmoothingKernel σ x = c * Real.exp (-V x) := by
    unfold gaussianSmoothingKernel
    dsimp only [c, V]
    congr 2
    field_simp
  have hmap : (stdGaussian E).map (fun z ↦ σ • z) =
      volume.withDensity (fun x ↦ ENNReal.ofReal (gaussianSmoothingKernel σ x)) := by
    simpa only [zero_add, sub_zero] using map_affine_std_gaussian_eq_with_density hσ (0 : E)
  have hd : HasDensity ((stdGaussian E).map (fun z ↦ σ • z)) volume
      (gaussianSmoothingKernel σ) :=
    ⟨(cont_diff_gaussian_smoothing_kernel hσ).continuous.measurable,
      ae_of_all _ fun x ↦ (gaussian_smoothing_kernel_pos hσ x).le, hmap⟩
  have hnorm : c * (∫ x, Real.exp (-V x)) = 1 := by
    rw [← integral_const_mul]
    simpa only [← he] using hd.integral_eq_one
  have hZ : (∫ x, Real.exp (-V x)) ≠ 0 := by
    intro h
    simp only [h, mul_zero] at hnorm
    norm_num at hnorm
  rw [hmap]
  -- Expand only the Gibbs normalization; the two density functions are then compared.
  change volume.withDensity (fun x ↦ ENNReal.ofReal (Real.exp (-V x) / (∫ y, Real.exp (-V y)))) = _
  apply withDensity_congr_ae
  refine ae_of_all _ fun x ↦ ?_
  dsimp only
  congr 1
  rw [he]
  apply (div_eq_iff hZ).2
  calc Real.exp (-V x) = Real.exp (-V x) * (c * (∫ y, Real.exp (-V y))) := by rw [hnorm, mul_one]
    _ = _ := by ring

set_option backward.isDefEq.respectTransparency.types false in
/-- A fixed positive threshold has standard Gaussian upper-tail mass exactly one quarter. -/
theorem exists_pos_gaussian_real_tail_eq_quarter :
    ∃ a : ℝ, 0 < a ∧ (gaussianReal 0 1).real (Ioi a) = 1 / 4 := by
  let a := (gaussianReal 0 1).quantile (3 / 4)
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal one_ne_zero
  have hc : cdf (gaussianReal 0 1) a = 3 / 4 :=
    Measure.cdf_quantile _ (Measure.continuous_cdf_of_noAtoms _) (by norm_num) (by norm_num)
  have ha : 0 < a := by
    by_contra h
    have hle := monotone_cdf (gaussianReal 0 1) (not_lt.mp h)
    rw [hc, TauCeti.Probability.cdf_gaussianReal_self 0 one_ne_zero] at hle
    norm_num at hle
  refine ⟨a, ha, ?_⟩
  rw [← compl_Iic, measureReal_compl measurableSet_Iic, probReal_univ, ← cdf_eq_real, hc]
  norm_num

set_option backward.isDefEq.respectTransparency.types false in
/-- Conditioning a scaled isotropic Gaussian on a fixed upper-quartile halfspace gives a
four-warm probability law supported on that halfspace. -/
theorem exists_quadratic_gibbs_halfspace_warm_start {a σ : ℝ} (hσ : 0 < σ)
    (ha : (gaussianReal 0 1).real (Ioi a) = 1 / 4) (i : Fin d) :
    let π := gibbsMeasure (fun x : E ↦ (σ⁻¹) ^ 2 / 2 * ‖x‖ ^ 2)
    let A : Set E := {x | σ * a < x i}
    ∃ μ : Measure E, IsProbabilityMeasure μ ∧ μ ≤ (4 : ℝ≥0∞) • π ∧
      μ A = 1 ∧ π.real A = 1 / 4 := by
  let π := gibbsMeasure (fun x : E ↦ (σ⁻¹) ^ 2 / 2 * ‖x‖ ^ 2)
  let A : Set E := {x | σ * a < x i}
  have hAm : MeasurableSet A := by apply measurableSet_lt <;> fun_prop
  have hπ : IsProbabilityMeasure π := by
    dsimp only [π]
    rw [gibbs_measure_quadratic_eq_map_std_gaussian hσ]
    infer_instance
  let := hπ
  have hcoord : HasLaw (fun x : E ↦ x i) (gaussianReal 0 1) (stdGaussian E) := by
    simpa only [multivariateGaussian_zero_one, PiLp.zero_apply, Matrix.one_apply_eq,
      Real.toNNReal_one] using
      (measurePreserving_eval_multivariateGaussian (μ := (0 : E))
        (S := (1 : Matrix (Fin d) (Fin d) ℝ)) Matrix.PosSemidef.one (i := i)).hasLaw
  have hmass : π.real A = 1 / 4 := by
    dsimp only [π]
    rw [gibbs_measure_quadratic_eq_map_std_gaussian hσ,
      map_measureReal_apply (by fun_prop) hAm]
    have he : (fun z : E ↦ σ • z) ⁻¹' A = (fun z : E ↦ z i) ⁻¹' Ioi a := by
      ext z
      -- Reduce coordinate evaluation of a scalar multiple to multiplication in the reals.
      change σ * a < σ * z i ↔ a < z i
      constructor <;> intro hz <;> nlinarith
    rw [he]
    exact (hcoord.measureReal_eq measurableSet_Ioi).trans ha
  have hmass' : π A = (4 : ℝ≥0∞)⁻¹ := by
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (by norm_num)).mp
    -- The real mass is the toReal value of the finite extended mass.
    change π.real A = (((4 : ℝ≥0∞)⁻¹).toReal)
    norm_num [hmass]
  let μ : Measure E := (4 : ℝ≥0∞) • π.restrict A
  have hμ : IsProbabilityMeasure μ := ⟨by
    dsimp [μ]
    rw [smul_apply, Measure.restrict_apply_univ, hmass']
    exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)⟩
  refine ⟨μ, hμ, ?_, ?_, hmass⟩
  · intro s
    -- Evaluate scalar multiplication of measures at the arbitrary test set.
    change (4 : ℝ≥0∞) * π.restrict A s ≤ 4 * π s
    gcongr
    exact Measure.restrict_le_self
  · dsimp [μ]
    rw [smul_apply, Measure.restrict_apply hAm, inter_self, hmass']
    exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)

end CKSD
