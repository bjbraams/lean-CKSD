module

public import CKSD.Bayes.MeanFieldPicardLaw
public import CKSD.Bayes.MeanFieldPathDistance
public import CKSD.Bayes.MeanFieldStability


/-!
# Mean-distance comparison of frozen-law Picard solutions

Common-source coupling bounds the first-Wasserstein difference of frozen marginal laws. The
deterministic stability estimate then controls Picard output paths by the time integral of the
mean pointwise distance between their inputs. The estimate is preserved by the `L¹` path
representatives, uniformly in time on the interval.

These estimates support the factorial-iterate contraction construction for GAPS 104.51.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators
namespace CKSD
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- A common-source coupling bounds the distance between random-path marginal laws. -/
theorem dist_path_marginal_law_le_mean_path_distance (P : Measure Ω) [IsProbabilityMeasure P]
    {T : ℝ} (hT : 0 ≤ T) (U V : Ω → C(Icc (0 : ℝ) T, E))
    (hUm : Measurable U) (hVm : Measurable V) (hUi : Integrable U P) (hVi : Integrable V P) (t : ℝ) :
    dist (pathMarginalLaw P hT U hUm hUi t) (pathMarginalLaw P hT V hVm hVi t) ≤ meanPathDistance P hT U V t := by
  rw [TauCeti.WassersteinSpace.dist_def, path_marginal_law_to_measure, path_marginal_law_to_measure]
  exact wasserstein_e_dist_one_map_to_real_le_integral_norm_sub P
    ((ContinuousMap.measurable_eval (Set.projIcc 0 T hT t)).comp hUm).aestronglyMeasurable
    ((ContinuousMap.measurable_eval (Set.projIcc 0 T hT t)).comp hVm).aestronglyMeasurable
    ((integrable_icc_extend_eval P hT U hUm hUi t).sub (integrable_icc_extend_eval P hT V hVm hVi t))

/-- Frozen drifts differ by the mean distance between the underlying path marginals. -/
theorem norm_sub_nonlinear_frozen_drift_le (P : Measure Ω) [IsProbabilityMeasure P]
    {T : ℝ} (hT : 0 ≤ T) (b : E → Measure E → E) {L : ℝ}
    (hb : IsWassersteinLipschitzDrift b L) (U V : Ω → C(Icc (0 : ℝ) T, E))
    (hUm : Measurable U) (hVm : Measurable V) (hUi : Integrable U P) (hVi : Integrable V P) (t : ℝ) (x : E) :
    ‖nonlinearFrozenDrift P hT b U hUm hUi t x - nonlinearFrozenDrift P hT b V hVm hVi t x‖ ≤
      (Real.toNNReal L : ℝ) * meanPathDistance P hT U V t := by
  let μ := pathMarginalLaw P hT U hUm hUi t
  let ν := pathMarginalLaw P hT V hVm hVi t
  have hm (σ : TauCeti.WassersteinSpace 1 E) : Integrable (fun z ↦ ‖z‖) ((σ : ProbabilityMeasure E) : Measure E) := by
    simpa only [id_eq] using (TauCeti.WassersteinSpace.hasFiniteMoment σ).memLp_id.integrable (by norm_num) |>.norm
  have hh := hb x x ((μ : ProbabilityMeasure E) : Measure E) ((ν : ProbabilityMeasure E) : Measure E)
    inferInstance inferInstance (hm μ) (hm ν)
  have h : ‖nonlinearFrozenDrift P hT b U hUm hUi t x - nonlinearFrozenDrift P hT b V hVm hVi t x‖ ≤
      L * dist μ ν := by
    simpa only [nonlinearFrozenDrift, TauCeti.WassersteinSpace.dist_def, sub_self, norm_zero, zero_add] using hh
  exact h.trans ((mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal L) dist_nonneg).trans
    (mul_le_mul_of_nonneg_left (dist_path_marginal_law_le_mean_path_distance P hT U V hUm hVm hUi hVi t) (Real.toNNReal L).coe_nonneg))

/-- With the same additive forcing, frozen-law solutions are controlled by the integrated mean
pointwise distance between their input random paths. -/
theorem norm_sub_frozen_path_solution_map_le (P : Measure Ω) [IsProbabilityMeasure P]
    {T : ℝ} (hT : 0 ≤ T) (b : E → Measure E → E) {L : ℝ}
    (hb : IsWassersteinLipschitzDrift b L) (U V : Ω → C(Icc (0 : ℝ) T, E))
    (hUm : Measurable U) (hVm : Measurable V) (hUi : Integrable U P) (hVi : Integrable V P)
    (f : C(Icc (0 : ℝ) T, E)) :
    ∀ t ∈ Icc (0 : ℝ) T,
      ‖(frozenPathSolutionMap P hT b hb U hUm hUi f).IccExtend hT t -
        (frozenPathSolutionMap P hT b hb V hVm hVi f).IccExtend hT t‖ ≤
      ((Real.toNNReal L : ℝ) * Real.exp ((Real.toNNReal L : ℝ) * T)) *
        ∫ s in (0 : ℝ)..t, meanPathDistance P hT U V s := by
  let v := nonlinearFrozenDrift P hT b U hUm hUi
  let w := nonlinearFrozenDrift P hT b V hVm hVi
  let x := (frozenPathSolutionMap P hT b hb U hUm hUi f).IccExtend hT
  let y := (frozenPathSolutionMap P hT b hb V hVm hVi f).IccExtend hT
  let F := f.IccExtend hT
  have hxe (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : x t = F t + ∫ s in (0 : ℝ)..t, v s (x s) := by
    have heq := frozen_path_solution_map_apply_eq P hT b hb U hUm hUi f ⟨t, ht⟩
    simpa only [x, F, ContinuousMap.coe_IccExtend, Set.IccExtend_of_mem (h := hT) _ ht] using heq
  have hye (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : y t = F t + ∫ s in (0 : ℝ)..t, w s (y s) := by
    have heq := frozen_path_solution_map_apply_eq P hT b hb V hVm hVi f ⟨t, ht⟩
    simpa only [y, F, ContinuousMap.coe_IccExtend, Set.IccExtend_of_mem (h := hT) _ ht] using heq
  have h := norm_sub_le_exp_mul_integral_of_forced_eq v w
    (continuous_nonlinear_frozen_drift P hT b hb U hUm hUi)
    (continuous_nonlinear_frozen_drift P hT b hb V hVm hVi)
    (lipschitz_with_nonlinear_frozen_drift P hT b hb U hUm hUi)
    (fun s ↦ (Real.toNNReal L : ℝ) * meanPathDistance P hT U V s)
    ((continuous_mean_path_distance_of_integrable P hT U V hUi hVi).const_mul _)
    (fun s _ ↦ mul_nonneg (Real.toNNReal L).coe_nonneg (mean_path_distance_nonneg P hT U V s))
    (fun s _ z ↦ norm_sub_nonlinear_frozen_drift_le P hT b hb U V hUm hVm hUi hVi s z)
    x y F x.continuous y.continuous hxe hye
  intro t ht
  convert h t ht using 1
  rw [intervalIntegral.integral_const_mul]
  ring

/-- Picard representatives obey the same pointwise comparison almost surely for whole paths. -/
theorem nonlinear_path_picard_ae_norm_sub_le (P : Measure Ω) [IsProbabilityMeasure P]
    {T : ℝ} (hT : 0 ≤ T) (b : E → Measure E → E) {L : ℝ}
    (hb : IsWassersteinLipschitzDrift b L) (F : Ω → C(Icc (0 : ℝ) T, E))
    (hFm : Measurable F) (hFi : Integrable F P) (U V : Lp C(Icc (0 : ℝ) T, E) 1 P) :
    ∀ᵐ ω ∂P, ∀ t ∈ Icc (0 : ℝ) T,
      ‖(nonlinearPathPicard P hT b hb F hFm hFi U ω).IccExtend hT t -
        (nonlinearPathPicard P hT b hb F hFm hFi V ω).IccExtend hT t‖ ≤
      ((Real.toNNReal L : ℝ) * Real.exp ((Real.toNNReal L : ℝ) * T)) *
        ∫ s in (0 : ℝ)..t, meanPathDistance P hT U V s := by
  filter_upwards [nonlinear_path_picard_ae_eq P hT b hb F hFm hFi U,
    nonlinear_path_picard_ae_eq P hT b hb F hFm hFi V] with ω hU hV
  rw [hU, hV]
  exact norm_sub_frozen_path_solution_map_le P hT b hb U V (Lp.stronglyMeasurable U).measurable
    (Lp.stronglyMeasurable V).measurable (L1.integrable_coeFn U) (L1.integrable_coeFn V) (F ω)
end CKSD
