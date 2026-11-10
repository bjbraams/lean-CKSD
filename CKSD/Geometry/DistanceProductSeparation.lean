module
public import CKSD.Geometry.DistanceKernel
public import TauCeti.Probability.Density
/-!
# Separation by the product distance kernel

Distance-kernel sections determine weighted first marginals. Applying the finite-law
energy-distance criterion a second time determines the second marginals after restriction to
first-coordinate events, and hence the joint law. This proves product-kernel MMD separation
for laws with equal marginals, as needed for distance covariance.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators MatrixOrder
namespace CKSD
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

/-- A bounded distance-kernel section weights a joint law before its first marginal is taken. -/
def distanceWeightedFst (P : Measure (E × F)) (y : F) : Measure E :=
  (P.withDensity (fun z ↦ ENNReal.ofReal (distanceKernel y z.2))).map Prod.fst

/-- A distance-kernel section is integrable under every finite measure. -/
theorem integrable_distanceKernel_snd (P : Measure (E × F)) [IsFiniteMeasure P] (y : F) :
    Integrable (fun z ↦ distanceKernel y z.2) P := by
  refine Integrable.of_bound (by unfold distanceKernel; fun_prop) ‖y‖ (ae_of_all _ fun z ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (distanceKernel_nonneg_le y z.2).1]
  exact (distanceKernel_nonneg_le y z.2).2.1

/-- A bounded nonnegative section defines a finite weighted marginal. -/
instance isFiniteMeasure_distanceWeightedFst (P : Measure (E × F)) [IsFiniteMeasure P] (y : F) :
    IsFiniteMeasure (distanceWeightedFst P y) := by
  have := isFiniteMeasure_withDensity_ofReal (integrable_distanceKernel_snd P y).hasFiniteIntegral
  unfold distanceWeightedFst
  infer_instance

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]
  [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] in
/-- Integration against a weighted marginal pulls back to weighted integration. -/
theorem integral_distanceWeightedFst (P : Measure (E × F)) (y : F) (f : E → ℝ)
    (hf : Measurable f) :
    (∫ x, f x ∂distanceWeightedFst P y) = ∫ z, distanceKernel y z.2 * f z.1 ∂P := by
  rw [distanceWeightedFst, integral_map measurable_fst.aemeasurable hf.aestronglyMeasurable,
    TauCeti.Probability.integral_withDensity_ofReal (ρ := fun z : E × F ↦ distanceKernel y z.2) (by unfold distanceKernel; fun_prop)
      (ae_of_all _ fun z ↦ (distanceKernel_nonneg_le y z.2).1)]
  rfl

/-- Weighted first marginals retain finite first moments. -/
theorem integrable_norm_distanceWeightedFst (P : Measure (E × F)) [IsFiniteMeasure P]
    (hP : Integrable (fun z ↦ ‖z‖) P) (y : F) :
    Integrable (fun x ↦ ‖x‖) (distanceWeightedFst P y) := by
  rw [distanceWeightedFst, integrable_map_measure (by fun_prop) measurable_fst.aemeasurable,
    TauCeti.Probability.integrable_withDensity_ofReal_iff (ρ := fun z : E × F ↦ distanceKernel y z.2) (by unfold distanceKernel; fun_prop)
      (ae_of_all _ fun z ↦ (distanceKernel_nonneg_le y z.2).1)]
  refine (hP.const_mul ‖y‖).mono' (by unfold distanceKernel; fun_prop) (ae_of_all _ fun z ↦ ?_)
  simp only [Function.comp_apply, smul_eq_mul, Real.norm_eq_abs, abs_mul, abs_norm,
    abs_of_nonneg (distanceKernel_nonneg_le y z.2).1]
  exact mul_le_mul (distanceKernel_nonneg_le y z.2).2.1 (norm_fst_le z) (norm_nonneg _) (norm_nonneg _)

/-- The total mass of a weighted marginal depends only on the opposite marginal. -/
theorem distanceWeightedFst_univ_eq (P Q : Measure (E × F)) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (hsnd : P.map Prod.snd = Q.map Prod.snd) (y : F) :
    distanceWeightedFst P y univ = distanceWeightedFst Q y univ := by
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1
  have hP := integral_distanceWeightedFst P y (fun _ ↦ 1) measurable_const
  have hQ := integral_distanceWeightedFst Q y (fun _ ↦ 1) measurable_const
  simp only [integral_const, smul_eq_mul, mul_one] at hP hQ
  change (distanceWeightedFst P y).real univ = (distanceWeightedFst Q y).real univ
  rw [hP, hQ, ← integral_map measurable_snd.aemeasurable (by unfold distanceKernel; fun_prop),
    ← integral_map measurable_snd.aemeasurable (by unfold distanceKernel; fun_prop), hsnd]

/-- Equal second marginals and equal product-kernel sections give equal weighted first marginals. -/
theorem distanceWeightedFst_eq (P Q : Measure (E × F)) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (hP : Integrable (fun z ↦ ‖z‖) P) (hQ : Integrable (fun z ↦ ‖z‖) Q)
    (hsnd : P.map Prod.snd = Q.map Prod.snd)
    (hsec : ∀ z, (∫ w, distanceProductKernel z w ∂P) = ∫ w, distanceProductKernel z w ∂Q)
    (y : F) : distanceWeightedFst P y = distanceWeightedFst Q y := by
  refine measure_eq_of_integral_distanceKernel_eq _ _ (distanceWeightedFst_univ_eq P Q hsnd y)
    (integrable_norm_distanceWeightedFst P hP y) (integrable_norm_distanceWeightedFst Q hQ y) ?_
  intro x
  rw [integral_distanceWeightedFst P y _ (by unfold distanceKernel; fun_prop),
    integral_distanceWeightedFst Q y _ (by unfold distanceKernel; fun_prop)]
  simpa only [distanceProductKernel, mul_comm] using hsec (x, y)

/-- Evaluating a weighted marginal is a restricted weighted integral. -/
theorem real_distanceWeightedFst_apply (P : Measure (E × F)) [IsFiniteMeasure P]
    (y : F) (A : Set E) (hA : MeasurableSet A) :
    (distanceWeightedFst P y).real A = ∫ z in Prod.fst ⁻¹' A, distanceKernel y z.2 ∂P := by
  unfold distanceWeightedFst Measure.real
  rw [Measure.map_apply measurable_fst hA]
  exact TauCeti.Probability.measureReal_withDensity_ofReal
    (ae_of_all _ fun z ↦ (distanceKernel_nonneg_le y z.2).1)
    (measurable_fst hA) (integrable_distanceKernel_snd P y).integrableOn

/-- Restricting to a first-coordinate event preserves integrability of the second-coordinate norm. -/
theorem integrable_norm_map_snd_restrict (P : Measure (E × F))
    (hP : Integrable (fun z ↦ ‖z‖) P) (A : Set E) :
    Integrable (fun y ↦ ‖y‖) ((P.restrict (Prod.fst ⁻¹' A)).map Prod.snd) := by
  rw [integrable_map_measure (by fun_prop) measurable_snd.aemeasurable]
  exact hP.restrict.mono' (by fun_prop) (ae_of_all _ fun z ↦ by simpa using norm_snd_le z)

/-- Product distance-kernel sections determine finite laws once both marginals are fixed. -/
theorem measure_eq_of_integral_distanceProductKernel_eq (P Q : Measure (E × F))
    [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (hP : Integrable (fun z ↦ ‖z‖) P) (hQ : Integrable (fun z ↦ ‖z‖) Q)
    (hfst : P.map Prod.fst = Q.map Prod.fst) (hsnd : P.map Prod.snd = Q.map Prod.snd)
    (hsec : ∀ z, (∫ w, distanceProductKernel z w ∂P) = ∫ w, distanceProductKernel z w ∂Q) :
    P = Q := by
  have hw := distanceWeightedFst_eq P Q hP hQ hsnd hsec
  have hr (A : Set E) (hA : MeasurableSet A) :
      (P.restrict (Prod.fst ⁻¹' A)).map Prod.snd =
      (Q.restrict (Prod.fst ⁻¹' A)).map Prod.snd := by
    refine measure_eq_of_integral_distanceKernel_eq _ _ ?_
      (integrable_norm_map_snd_restrict P hP A) (integrable_norm_map_snd_restrict Q hQ A) ?_
    · simp only [Measure.map_apply measurable_snd MeasurableSet.univ, preimage_univ,
        Measure.restrict_apply MeasurableSet.univ, univ_inter]
      have hm := congrArg (fun μ : Measure E ↦ μ A) hfst
      simpa only [Measure.map_apply measurable_fst hA] using hm
    · intro y
      rw [integral_map measurable_snd.aemeasurable (by unfold distanceKernel; fun_prop),
        integral_map measurable_snd.aemeasurable (by unfold distanceKernel; fun_prop),
        ← real_distanceWeightedFst_apply P y A hA, ← real_distanceWeightedFst_apply Q y A hA,
        hw y]
  apply Measure.ext_prod
  intro A B hA hB
  have hm := congrArg (fun μ : Measure F ↦ μ B) (hr A hA)
  have he : Prod.snd ⁻¹' B ∩ Prod.fst ⁻¹' A = A ×ˢ B := by
    ext z
    simp only [mem_inter_iff, mem_preimage, mem_prod, and_comm]
  simpa only [Measure.map_apply measurable_snd hB, Measure.restrict_apply (measurable_snd hB),
    he] using hm

/-- The product distance-kernel discrepancy is nonnegative and separates laws with fixed marginals. -/
theorem distanceProductKernel_squaredMMD_nonneg_eq_zero_iff (P Q : Measure (E × F))
    [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (hP : Integrable (fun z ↦ ‖z‖) P) (hQ : Integrable (fun z ↦ ‖z‖) Q)
    (hfst : P.map Prod.fst = Q.map Prod.fst) (hsnd : P.map Prod.snd = Q.map Prod.snd) :
    0 ≤ squaredMMD distanceProductKernel P Q ∧
      (squaredMMD distanceProductKernel P Q = 0 ↔ P = Q) := by
  constructor
  · rw [squaredMMD_eq_norm_kernelMeanEmbedding_sub_sq
      (posSemidef_distanceProductKernel (E := E) (F := F))
      (integrable_distanceProductFeature P hP) (integrable_distanceProductFeature Q hQ)
      (integrable_distanceProductKernel_prod P P hP hP)
      (integrable_distanceProductKernel_prod Q Q hQ hQ)
      (integrable_distanceProductKernel_prod P Q hP hQ)]
    positivity
  constructor
  · intro hz
    exact measure_eq_of_integral_distanceProductKernel_eq P Q hP hQ hfst hsnd
      (integral_distanceProductKernel_eq_of_squaredMMD_eq_zero P Q hP hQ hz)
  · rintro rfl
    unfold squaredMMD
    ring

end CKSD
