module
public import TauCeti.Geometry.Symplectic.Hamiltonian.Flow
public import TauCeti.LinearAlgebra.BilinearForm.Isometry
public import Mathlib.MeasureTheory.Function.Jacobian
public import CKSD.Bayes.HamiltonianSampling
public import CKSD.Bayes.Diffusion
public import TauCeti.Probability.Distributions.Gaussian.Density
/-!
# Hamiltonian volume and Gibbs invariance

The derivative of a C2 Hamiltonian time map is symplectic, hence has determinant
one. Change of variables proves invariance of additive Haar measure. Energy
conservation then gives invariance of any measurable density depending only on
energy, including the Gibbs-Gaussian phase law of mechanical Hamiltonian dynamics.

Pinned TauCeti supplies the Hamiltonian variational equation, the determinant
of alternating-form isometries, and Gaussian densities. Mathlib supplies the
Jacobian change-of-variables theorem. The statistical interpretation follows
Chewi, *Log-Concave Sampling*, August 20, 2026, Section 5.2 (ideal HMC).
-/
@[expose] public section
noncomputable section
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set
open scoped ENNReal NNReal
namespace CKSD
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  (ω : TauCeti.SymplecticForm V) (H : V → ℝ) {K : ℝ≥0}
/-- Hamiltonian flow derivatives have determinant one. -/
theorem det_fderiv_hamiltonianFlow (hX : LipschitzWith K (ω.hamiltonianVectorField H))
    (hH : ContDiff ℝ 2 H) (t : ℝ) (x : V) :
    (fderiv ℝ (ω.hamiltonianFlow H hX t) x).det = 1 := by
  exact TauCeti.BilinForm.IsIsometry.det_eq_one ω.isAlt ω.nondegenerate
    (TauCeti.BilinForm.isIsometry_iff.mpr (ω.apply_fderiv_hamiltonianFlow H hX hH t x))
variable [MeasurableSpace V] [BorelSpace V]
/-- Hamiltonian time maps preserve any additive Haar measure. -/
theorem measurePreserving_hamiltonianFlow (μ : Measure V) [IsAddHaarMeasure μ]
    (hX : LipschitzWith K (ω.hamiltonianVectorField H)) (hH : ContDiff ℝ 2 H) (t : ℝ) :
    MeasurePreserving (ω.hamiltonianFlow H hX t) μ μ := by
  let F := ω.hamiltonianFlow H hX
  have hc : ContDiff ℝ 1 (F t) := ω.contDiff_hamiltonianFlow_apply H 0 hX hH t
  refine ⟨hc.continuous.measurable, ?_⟩
  have he := map_withDensity_abs_det_fderiv_eq_addHaar μ (s := univ)
    (f := F t) (f' := fun x ↦ fderiv ℝ (F t) x) nullMeasurableSet_univ
    (fun x _ ↦ (hc.differentiable (by norm_num) x).hasFDerivAt.hasFDerivWithinAt)
    (F.toHomeomorph t).injective.injOn
  have hdet : (fun x ↦ ENNReal.ofReal |(fderiv ℝ (F t) x).det|) = fun _ ↦ 1 := by
    funext x
    simp [F, det_fderiv_hamiltonianFlow ω H hX hH t x]
  have hrange : range (F t) = univ := (F.toHomeomorph t).surjective.range_eq
  simpa only [hdet, Measure.restrict_univ, withDensity_const, one_smul, image_univ,
    hrange, Measure.restrict_univ] using he
/-- An invariant measurable density preserves a measure-preserving transformation. -/
theorem measurePreserving_withDensity_of_invariant {X : Type*} [MeasurableSpace X]
    {f : X → X} {μ : Measure X} (hf : MeasurePreserving f μ μ)
    (w : X → ℝ≥0∞) (hw : Measurable w) (hwi : ∀ x, w (f x) = w x) :
    MeasurePreserving f (μ.withDensity w) (μ.withDensity w) := by
  refine ⟨hf.measurable, Measure.ext fun s hs ↦ ?_⟩
  rw [Measure.map_apply hf.measurable hs, withDensity_apply _ (hf.measurable hs),
    withDensity_apply _ hs]
  calc (∫⁻ x in f ⁻¹' s, w x ∂μ) = ∫⁻ x in f ⁻¹' s, w (f x) ∂μ := by
        apply lintegral_congr
        exact fun x ↦ (hwi x).symm
    _ = _ := hf.setLIntegral_comp_preimage hs hw
/-- Any measurable density depending only on energy is invariant under Hamiltonian flow. -/
theorem measurePreserving_hamiltonianFlow_withDensity (μ : Measure V) [IsAddHaarMeasure μ]
    (hX : LipschitzWith K (ω.hamiltonianVectorField H)) (hH : ContDiff ℝ 2 H)
    (w : ℝ → ℝ≥0∞) (hw : Measurable w) (t : ℝ) :
    MeasurePreserving (ω.hamiltonianFlow H hX t) (μ.withDensity (fun x ↦ w (H x)))
      (μ.withDensity (fun x ↦ w (H x))) := by
  exact measurePreserving_withDensity_of_invariant
    (measurePreserving_hamiltonianFlow ω H μ hX hH t) _
    (hw.comp hH.continuous.measurable)
    (fun x ↦ congrArg w (ω.hamiltonianFlow_conserves H hX (hH.differentiable (by norm_num)) t x))
section Mechanical
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
/-- The Gibbs-Gaussian phase law has density depending only on mechanical energy. -/
theorem gibbsMeasure_prod_stdGaussian_eq_withDensity (V : E → ℝ) (hV : Continuous V) :
    (gibbsMeasure V).prod (stdGaussian E) = (volume.prod volume).withDensity
      (fun z : E × E ↦ ENNReal.ofReal
        (((2 * Real.pi) ^ (-(d : ℝ) / 2) / (∫ x, Real.exp (-V x))) *
          Real.exp (-mechanicalHamiltonian V z))) := by
  have hZ : 0 ≤ ∫ x, Real.exp (-V x) := integral_nonneg fun _ ↦ (Real.exp_pos _).le
  rw [gibbsMeasure, TauCeti.Probability.stdGaussian_eq_withDensity, prod_withDensity]
  · congr 1
    funext z
    rw [← ENNReal.ofReal_mul (div_nonneg (Real.exp_pos _).le hZ)]
    congr 1
    dsimp [mechanicalHamiltonian]
    rw [neg_add, Real.exp_add]
    simp only [Fintype.card_fin, neg_div]
    ring
  · exact (Real.continuous_exp.comp hV.neg |>.div_const _).measurable.ennreal_ofReal
  · fun_prop
/-- Ideal mechanical Hamiltonian flow preserves Gibbs positions and independent Gaussian momenta. -/
theorem measurePreserving_mechanicalFlow_gibbsMeasure (V : E → ℝ) (G : E → E)
    (hV : ContDiff ℝ 2 V) (hgrad : ∀ x, HasGradientAt V (G x) x)
    {L : ℝ≥0} (hG : LipschitzWith L G) (t : ℝ) :
    MeasurePreserving (mechanicalFlow G hG t)
      ((gibbsMeasure V).prod (stdGaussian E)) ((gibbsMeasure V).prod (stdGaussian E)) := by
  rw [mechanicalFlow_eq_hamiltonianFlow V G hgrad hG,
    gibbsMeasure_prod_stdGaussian_eq_withDensity V hV.continuous]
  exact measurePreserving_hamiltonianFlow_withDensity (TauCeti.stdSymplecticForm (V := E))
    (mechanicalHamiltonian V) (volume.prod volume) _ (contDiff_mechanicalHamiltonian V hV)
    (fun r ↦ ENNReal.ofReal (((2 * Real.pi) ^ (-(d : ℝ) / 2) /
      (∫ x, Real.exp (-V x))) * Real.exp (-r))) (by fun_prop) t
end Mechanical
end CKSD
