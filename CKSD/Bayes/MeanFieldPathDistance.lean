module

public import CKSD.Bayes.MeanFieldPathLaws
public import Mathlib.MeasureTheory.Function.L1Space.AEEqFun


/-!
# Mean pointwise distance of random continuous paths

The expectation of the pointwise distance of two integrable continuous paths varies continuously
with time and is bounded by their `L¹` path distance. This is the scalar distance used for the
time-integral stability estimates of the nonlinear Picard operator.

Mathlib supplies dominated convergence, continuous evaluation and the integral formula for the
`L¹` norm. Continuity and comparison with the `L¹` norm do not require probability
normalization. For probability measures, almost sure integral estimates also control the mean
pointwise distance and the whole `L¹` path distance.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators

namespace CKSD

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]

/-- The mean pointwise distance of two random continuous paths, evaluated at projected time. -/
def meanPathDistance (P : Measure Ω) {T : ℝ} (hT : 0 ≤ T)
    (U V : Ω → C(Icc (0 : ℝ) T, E)) (t : ℝ) : ℝ :=
  ∫ ω, ‖(U ω).IccExtend hT t - (V ω).IccExtend hT t‖ ∂P

/-- Mean path distance is nonnegative. -/
theorem mean_path_distance_nonneg (P : Measure Ω) {T : ℝ} (hT : 0 ≤ T)
    (U V : Ω → C(Icc (0 : ℝ) T, E)) (t : ℝ) : 0 ≤ meanPathDistance P hT U V t :=
  integral_nonneg fun _ ↦ norm_nonneg _

/-- Mean path distance varies continuously with real time for integrable random paths. -/
theorem continuous_mean_path_distance_of_integrable (P : Measure Ω) {T : ℝ} (hT : 0 ≤ T)
    (U V : Ω → C(Icc (0 : ℝ) T, E)) (hUi : Integrable U P) (hVi : Integrable V P) :
    Continuous (meanPathDistance P hT U V) := by
  apply continuous_of_dominated (bound := fun ω ↦ ‖U ω‖ + ‖V ω‖)
  · intro t
    have hce : Continuous (fun f : C(Icc (0 : ℝ) T, E) ↦ f.IccExtend hT t) :=
      continuous_eval_const (Set.projIcc 0 T hT t)
    exact ((hce.comp_aestronglyMeasurable hUi.aestronglyMeasurable).sub
      (hce.comp_aestronglyMeasurable hVi.aestronglyMeasurable)).norm
  · intro t
    refine ae_of_all _ fun ω ↦ ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact (norm_sub_le _ _).trans (add_le_add
      ((U ω).norm_coe_le_norm (Set.projIcc 0 T hT t))
      ((V ω).norm_coe_le_norm (Set.projIcc 0 T hT t)))
  · exact hUi.norm.add hVi.norm
  · exact ae_of_all _ fun ω ↦ (((U ω).IccExtend hT).continuous.sub ((V ω).IccExtend hT).continuous).norm

/-- Measurable integrable random paths have a continuous mean pointwise distance. -/
theorem continuous_mean_path_distance (P : Measure Ω) {T : ℝ} (hT : 0 ≤ T)
    (U V : Ω → C(Icc (0 : ℝ) T, E)) (_hUm : Measurable U) (_hVm : Measurable V)
    (hUi : Integrable U P) (hVi : Integrable V P) : Continuous (meanPathDistance P hT U V) :=
  continuous_mean_path_distance_of_integrable P hT U V hUi hVi

/-- For two L¹ random continuous paths, mean path distance is a continuous function of time. -/
theorem continuous_mean_path_distance_l1 (P : Measure Ω) {T : ℝ} (hT : 0 ≤ T)
    (U V : Lp C(Icc (0 : ℝ) T, E) 1 P) : Continuous (meanPathDistance P hT U V) :=
  continuous_mean_path_distance_of_integrable P hT U V (L1.integrable_coeFn U) (L1.integrable_coeFn V)

/-- Mean path distance at any time is bounded by the L¹ distance of the random paths. -/
theorem mean_path_distance_le_norm_sub (P : Measure Ω) {T : ℝ} (hT : 0 ≤ T)
    (U V : Lp C(Icc (0 : ℝ) T, E) 1 P) (t : ℝ) :
    meanPathDistance P hT U V t ≤ ‖U - V‖ := by
  have hi : Integrable (fun ω ↦ U ω - V ω) P := (L1.integrable_coeFn U).sub (L1.integrable_coeFn V)
  have hpoint (ω : Ω) : ‖(U ω).IccExtend hT t - (V ω).IccExtend hT t‖ ≤ ‖U ω - V ω‖ :=
    (U ω - V ω).norm_coe_le_norm (Set.projIcc 0 T hT t)
  have hce : Continuous (fun f : C(Icc (0 : ℝ) T, E) ↦ f.IccExtend hT t) :=
    continuous_eval_const (Set.projIcc 0 T hT t)
  have hm : AEStronglyMeasurable (fun ω ↦ (U ω).IccExtend hT t - (V ω).IccExtend hT t) P :=
    (hce.comp_aestronglyMeasurable (Lp.aestronglyMeasurable U)).sub
      (hce.comp_aestronglyMeasurable (Lp.aestronglyMeasurable V))
  have hei : Integrable (fun ω ↦ (U ω).IccExtend hT t - (V ω).IccExtend hT t) P :=
    hi.norm.mono' hm (ae_of_all _ hpoint)
  calc meanPathDistance P hT U V t ≤ ∫ ω, ‖U ω - V ω‖ ∂P := integral_mono hei.norm hi.norm hpoint
    _ = ‖U - V‖ := by
      rw [L1.norm_sub_eq_lintegral, ← ofReal_integral_norm_eq_lintegral_enorm hi,
        ENNReal.toReal_ofReal (integral_nonneg fun _ ↦ norm_nonneg _)]


/-- The L¹ distance between random paths is the mean of their uniform distances. -/
theorem norm_sub_L1_eq_integral_norm (P : Measure Ω) {T : ℝ}
    (U V : Lp C(Icc (0 : ℝ) T, E) 1 P) :
    ‖U - V‖ = ∫ ω, ‖U ω - V ω‖ ∂P := by
  have hi : Integrable (fun ω ↦ U ω - V ω) P :=
    (L1.integrable_coeFn U).sub (L1.integrable_coeFn V)
  rw [L1.norm_sub_eq_lintegral, ← ofReal_integral_norm_eq_lintegral_enorm hi,
    ENNReal.toReal_ofReal (integral_nonneg fun _ ↦ norm_nonneg _)]

/-- An almost sure scalar bound on the pointwise distance also bounds its expectation. -/
theorem mean_path_distance_le_of_ae_bound (P : Measure Ω) [IsProbabilityMeasure P]
    {T : ℝ} (hT : 0 ≤ T) (U V : Lp C(Icc (0 : ℝ) T, E) 1 P) (t r : ℝ)
    (hbound : ∀ᵐ ω ∂P, ‖(U ω).IccExtend hT t - (V ω).IccExtend hT t‖ ≤ r) :
    meanPathDistance P hT U V t ≤ r := by
  have hi : Integrable (fun ω ↦ U ω - V ω) P :=
    (L1.integrable_coeFn U).sub (L1.integrable_coeFn V)
  have hce : Continuous (fun f : C(Icc (0 : ℝ) T, E) ↦ f.IccExtend hT t) :=
    continuous_eval_const (Set.projIcc 0 T hT t)
  have hm : AEStronglyMeasurable (fun ω ↦ (U ω).IccExtend hT t - (V ω).IccExtend hT t) P :=
    (hce.comp_aestronglyMeasurable (Lp.aestronglyMeasurable U)).sub
      (hce.comp_aestronglyMeasurable (Lp.aestronglyMeasurable V))
  have hei : Integrable (fun ω ↦ (U ω).IccExtend hT t - (V ω).IccExtend hT t) P :=
    hi.norm.mono' hm (ae_of_all _ fun ω ↦
      (U ω - V ω).norm_coe_le_norm (Set.projIcc 0 T hT t))
  calc meanPathDistance P hT U V t ≤ ∫ _ : Ω, r ∂P :=
      integral_mono_ae hei.norm (integrable_const _) hbound
    _ = r := by simp

/-- A uniform almost sure bound on pointwise distances bounds the L¹ path norm. -/
theorem norm_sub_L1_le_of_ae_bound (P : Measure Ω) [IsProbabilityMeasure P]
    {T : ℝ} (hT : 0 ≤ T) (U V : Lp C(Icc (0 : ℝ) T, E) 1 P) (r : ℝ) (hr : 0 ≤ r)
    (hbound : ∀ᵐ ω ∂P, ∀ t ∈ Icc (0 : ℝ) T,
      ‖(U ω).IccExtend hT t - (V ω).IccExtend hT t‖ ≤ r) :
    ‖U - V‖ ≤ r := by
  have hp : ∀ᵐ ω ∂P, ‖U ω - V ω‖ ≤ r := by
    filter_upwards [hbound] with ω hω
    apply ((U ω - V ω).norm_le hr).2
    intro t
    have hh := hω t t.2
    simpa only [ContinuousMap.coe_IccExtend,
      Set.IccExtend_of_mem (h := hT) (fun z ↦ U ω z) t.2,
      Set.IccExtend_of_mem (h := hT) (fun z ↦ V ω z) t.2,
      ContinuousMap.sub_apply] using hh
  rw [norm_sub_L1_eq_integral_norm]
  calc (∫ ω, ‖U ω - V ω‖ ∂P) ≤ ∫ _ : Ω, r ∂P :=
      integral_mono_ae ((L1.integrable_coeFn U).sub (L1.integrable_coeFn V)).norm
        (integrable_const _) hp
    _ = r := by simp

/-- An almost sure integral stability estimate implies the corresponding mean-distance bound. -/
theorem mean_path_distance_le_integral_of_ae_bound (P : Measure Ω) [IsProbabilityMeasure P]
    {T : ℝ} (hT : 0 ≤ T) (U V : Lp C(Icc (0 : ℝ) T, E) 1 P)
    (a : ℝ) (q : ℝ → ℝ)
    (hbound : ∀ᵐ ω ∂P, ∀ t ∈ Icc (0 : ℝ) T,
      ‖(U ω).IccExtend hT t - (V ω).IccExtend hT t‖ ≤ a * ∫ s in (0 : ℝ)..t, q s)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
    meanPathDistance P hT U V t ≤ a * ∫ s in (0 : ℝ)..t, q s :=
  mean_path_distance_le_of_ae_bound P hT U V t _ (hbound.mono fun _ hω ↦ hω t ht)

/-- For nonnegative continuous input, integral stability bounds the whole L¹ path distance. -/
theorem norm_sub_L1_le_integral_of_ae_bound (P : Measure Ω) [IsProbabilityMeasure P]
    {T : ℝ} (hT : 0 ≤ T) (U V : Lp C(Icc (0 : ℝ) T, E) 1 P)
    (a : ℝ) (ha : 0 ≤ a) (q : ℝ → ℝ) (hq : Continuous q)
    (hq0 : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ q t)
    (hbound : ∀ᵐ ω ∂P, ∀ t ∈ Icc (0 : ℝ) T,
      ‖(U ω).IccExtend hT t - (V ω).IccExtend hT t‖ ≤ a * ∫ s in (0 : ℝ)..t, q s) :
    ‖U - V‖ ≤ a * ∫ s in (0 : ℝ)..T, q s := by
  apply norm_sub_L1_le_of_ae_bound P hT U V _
    (mul_nonneg ha (intervalIntegral.integral_nonneg hT hq0))
  filter_upwards [hbound] with ω hω
  intro t ht
  apply (hω t ht).trans
  apply mul_le_mul_of_nonneg_left _ ha
  apply intervalIntegral.integral_mono_interval (le_refl (0 : ℝ)) ht.1 ht.2
    _ (hq.intervalIntegrable _ _)
  exact (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun s hs ↦ hq0 s ⟨hs.1.le, hs.2⟩)

/-- The integral stability estimate controls the metric distance between L¹ paths. -/
theorem dist_L1_le_integral_of_ae_bound (P : Measure Ω) [IsProbabilityMeasure P]
    {T : ℝ} (hT : 0 ≤ T) (U V : Lp C(Icc (0 : ℝ) T, E) 1 P)
    (a : ℝ) (ha : 0 ≤ a) (q : ℝ → ℝ) (hq : Continuous q)
    (hq0 : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ q t)
    (hbound : ∀ᵐ ω ∂P, ∀ t ∈ Icc (0 : ℝ) T,
      ‖(U ω).IccExtend hT t - (V ω).IccExtend hT t‖ ≤ a * ∫ s in (0 : ℝ)..t, q s) :
    dist U V ≤ a * ∫ s in (0 : ℝ)..T, q s := by
  rw [dist_eq_norm]
  exact norm_sub_L1_le_integral_of_ae_bound P hT U V a ha q hq hq0 hbound

end CKSD
