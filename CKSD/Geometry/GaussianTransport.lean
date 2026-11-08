module

public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Gaussian.Barycenter
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Moment
public import TauCeti.Probability.Distributions.Gaussian.Continuity
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric

/-!
# Quadratic transport between Gaussian laws

The Gaussian Bures formula holds for positive semidefinite covariances, including
singular laws. The proof approximates a covariance by positive definite matrices.
It uses TauCeti's positive-definite Bures formula, weak continuity of Gaussian laws,
and the weak-convergence-plus-moment criterion for Wasserstein convergence.
Continuity of the matrix square root is Mathlib's continuous functional calculus.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD
noncomputable section
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "M" => Matrix (Fin d) (Fin d) ℝ

/-- The second radial moment of a Gaussian law is the squared norm of its mean
plus the trace of its covariance. -/
lemma lintegral_edist_zero_rpow_two_multivariateGaussian (m : E) (A : M) (hA : A.PosSemidef) :
    ∫⁻ x, edist (0 : E) x ^ (2 : ℝ≥0∞).toReal ∂multivariateGaussian m A =
      ENNReal.ofReal (‖m‖ ^ 2 + Matrix.trace A) := by
  have hi : Integrable (fun x : E ↦ ‖x‖ ^ 2) (multivariateGaussian m A) :=
    IsGaussian.memLp_two_id.integrable_norm_pow two_ne_zero
  have hm := TauCeti.integral_norm_sub_sq_eq_norm_integral_sub_sq_add_trace_covMatrix
    (multivariateGaussian m A) IsGaussian.memLp_two_id 0
  simp only [sub_zero, integral_id_multivariateGaussian,
    TauCeti.Probability.covMatrix_multivariateGaussian _ hA] at hm
  have hpt : (fun x : E ↦ edist (0 : E) x ^ (2 : ℝ≥0∞).toReal) =
      fun x ↦ ENNReal.ofReal (‖x‖ ^ 2) := by
    ext x
    simp [edist_dist, dist_zero_left, ENNReal.ofReal_pow (norm_nonneg _)]
  rw [hpt, ← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun x ↦ sq_nonneg _), hm]

/-- The probability measure underlying the bundled quadratic-Wasserstein Gaussian law. -/
lemma gaussianWassersteinLaw_toProbabilityMeasure (m : E) (A : M) :
    (TauCeti.Probability.gaussianWassersteinLaw m A).toProbabilityMeasure =
      (multivariateGaussian m A).toProbabilityMeasure := by
  apply ProbabilityMeasure.toMeasure_injective
  simp [TauCeti.Probability.gaussianWassersteinLaw_coe]

/-- Gaussian laws depend continuously on their positive semidefinite covariance
in quadratic Wasserstein distance, with the mean fixed. -/
lemma continuous_gaussianWassersteinLaw (m : E) :
    Continuous (fun A : {A : M // A.PosSemidef} ↦
      TauCeti.Probability.gaussianWassersteinLaw m A.1) := by
  apply continuous_iff_continuousAt.mpr
  intro A
  apply (TauCeti.WassersteinSpace.tendsto_iff_tendsto_toProbabilityMeasure_and_lintegral
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (0 : E)).mpr
  constructor
  · simp only [gaussianWassersteinLaw_toProbabilityMeasure]
    have hc := TauCeti.Probability.continuous_multivariateGaussian (ι := Fin d)
    exact (hc.comp (continuous_const.prodMk continuous_id)).continuousAt
  · simp only [TauCeti.Probability.gaussianWassersteinLaw_coe]
    simp_rw [lintegral_edist_zero_rpow_two_multivariateGaussian _ _ (Subtype.property _)]
    exact (ENNReal.continuous_ofReal.comp
      (continuous_const.add continuous_subtype_val.matrix_trace)).continuousAt


/-- The Gaussian Bures expression is continuous up to singular source covariances. -/
lemma continuous_gaussian_bures_expression (m n : E) (B : M) (hB : B.PosSemidef) :
    Continuous (fun A : {A : M // A.PosSemidef} ↦
      ‖m - n‖ ^ 2 + Matrix.trace
        (A.1 + B - 2 • CFC.sqrt (CFC.sqrt A.1 * B * CFC.sqrt A.1))) := by
  have hs : Continuous (fun A : {A : M // A.PosSemidef} ↦ CFC.sqrt A.1) :=
    CFC.continuousOn_sqrt.comp_continuous continuous_subtype_val fun A ↦ A.2.nonneg
  have hm : Continuous (fun A : {A : M // A.PosSemidef} ↦ CFC.sqrt A.1 * B * CFC.sqrt A.1) :=
    (hs.mul_const B).mul hs
  have hm0 : ∀ A : {A : M // A.PosSemidef},
      0 ≤ CFC.sqrt A.1 * B * CFC.sqrt A.1 := by
    intro A
    have hstar : (CFC.sqrt A.1).conjTranspose = CFC.sqrt A.1 :=
      (CFC.sqrt_nonneg _).isSelfAdjoint
    simpa only [hstar] using (hB.mul_mul_conjTranspose_same (CFC.sqrt A.1)).nonneg
  have hr : Continuous (fun A : {A : M // A.PosSemidef} ↦
      CFC.sqrt (CFC.sqrt A.1 * B * CFC.sqrt A.1)) :=
    CFC.continuousOn_sqrt.comp_continuous hm hm0
  have hc : Continuous (fun A : {A : M // A.PosSemidef} ↦
      A.1 + B - (2 : ℕ) • CFC.sqrt (CFC.sqrt A.1 * B * CFC.sqrt A.1)) :=
    (continuous_subtype_val.add continuous_const).sub (hr.const_smul (2 : ℕ))
  exact continuous_const.add hc.matrix_trace

/-- GAPS 108.46: the Gaussian Bures formula, allowing both covariances to be singular. -/
theorem wasserstein_multivariateGaussian_sq_eq (m n : E) (A B : M)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (TauCeti.wassersteinEDist 2 (multivariateGaussian m A) (multivariateGaussian n B)).toReal ^ 2 =
      ‖m - n‖ ^ 2 + Matrix.trace (A + B - 2 • CFC.sqrt (CFC.sqrt A * B * CFC.sqrt A)) := by
  let As : ℕ → M := fun k ↦ A + (1 / ((k : ℝ) + 1)) • 1
  have hAs : ∀ k, (As k).PosDef := fun k ↦
    Matrix.PosDef.posSemidef_add hA (Matrix.PosDef.one.smul (by positivity))
  let Ss : ℕ → {A : M // A.PosSemidef} := fun k ↦ ⟨As k, (hAs k).posSemidef⟩
  have hAslim : Tendsto As atTop (𝓝 A) := by
    have h0 := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    simpa only [As, zero_smul, add_zero] using
      tendsto_const_nhds.add (h0.smul (tendsto_const_nhds (x := (1 : M))))
  have hSs : Tendsto Ss atTop (𝓝 ⟨A, hA⟩) := tendsto_subtype_rng.mpr hAslim
  have hW := (continuous_gaussianWassersteinLaw m).continuousAt.tendsto.comp hSs
  have hD := (hW.dist (tendsto_const_nhds
    (x := TauCeti.Probability.gaussianWassersteinLaw n B))).pow 2
  have hR := (continuous_gaussian_bures_expression m n B hB).continuousAt.tendsto.comp hSs
  have heq : ∀ k, dist (TauCeti.Probability.gaussianWassersteinLaw m (As k))
      (TauCeti.Probability.gaussianWassersteinLaw n B) ^ 2 =
        ‖m - n‖ ^ 2 + Matrix.trace
          (As k + B - 2 • CFC.sqrt (CFC.sqrt (As k) * B * CFC.sqrt (As k))) := by
    intro k
    rw [TauCeti.WassersteinSpace.dist_def,
      TauCeti.Probability.gaussianWassersteinLaw_coe,
      TauCeti.Probability.gaussianWassersteinLaw_coe]
    have he := congrArg ENNReal.toReal
      (TauCeti.wassersteinEDist_two_multivariateGaussian_rpow_two (hAs k) hB m n)
    rw [← ENNReal.toReal_rpow,
      ENNReal.toReal_ofReal (TauCeti.gaussianWassersteinSq_nonneg (hAs k) hB m n),
      Real.rpow_two, TauCeti.gaussianWassersteinSq_def] at he
    rw [he]
    simp only [Matrix.trace_sub, Matrix.trace_add, Matrix.trace_smul]
    ring
  have hresult := tendsto_nhds_unique hD (hR.congr' (Eventually.of_forall fun k ↦ (heq k).symm))
  simpa only [TauCeti.WassersteinSpace.dist_def,
    TauCeti.Probability.gaussianWassersteinLaw_coe] using hresult

end
end CKSD
