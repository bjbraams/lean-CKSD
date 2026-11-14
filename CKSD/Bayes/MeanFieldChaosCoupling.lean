module
public import CKSD.Bayes.MeanFieldEmpirical
public import CKSD.Bayes.MeanFieldPicardLaw
/-!
# Whole-path synchronous coupling for mean-field particles

First-Wasserstein distance between the reference empirical path law and the common reference
path law controls every synchronously coupled particle path. Evaluation of continuous paths is
nonexpansive, so the empirical marginal discrepancy at all times is bounded by the same path
law discrepancy. The resulting constant depends only on the drift Lipschitz constant and the
time horizon, and is independent of the number of particles.

The estimate combines local particle stability with pinned TauCeti's Wasserstein pushforward
contraction and Mathlib's uniform norm on continuous paths.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped NNReal ENNReal Topology BigOperators
namespace CKSD
variable {Ω : Type*} [MeasurableSpace Ω] {d N : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
/-- A whole-path empirical Wasserstein discrepancy controls every particle path in a synchronous
coupling, with a constant independent of the particle count. -/
theorem norm_particle_path_sub_le_empirical_wasserstein
    (P : Measure Ω) [IsProbabilityMeasure P] {T : ℝ} (hT : 0 ≤ T) (hN : 0 < N)
    (b : E → Measure E → E) {L : ℝ} (hb : IsWassersteinLipschitzDrift b L)
    (Z : Ω → C(Icc (0 : ℝ) T, E)) (hZm : Measurable Z) (hZi : Integrable Z P)
    (z : Fin N → C(Icc (0 : ℝ) T, E)) (x f : ℝ → Fin N → E) (hx : Continuous x)
    (hxe : ∀ t ∈ Icc (0 : ℝ) T, x t = f t + ∫ s in (0 : ℝ)..t,
      fun j ↦ b (x s j) (empiricalMeasure N (x s)))
    (hze : ∀ t ∈ Icc (0 : ℝ) T,
      (fun j ↦ (z j).IccExtend hT t) = f t + ∫ s in (0 : ℝ)..t,
        fun j ↦ b ((z j).IccExtend hT s) (P.map (fun ω ↦ (Z ω).IccExtend hT s)))
    (i : Fin N) :
    ‖pathOn T (fun t ↦ x t i) - z i‖ ≤
      ((Real.toNNReal L : ℝ) * T * Real.exp (2 * (Real.toNNReal L : ℝ) * T)) *
        (TauCeti.wassersteinEDist 1 (empiricalMeasure N z) (P.map Z)).toReal := by
  let μ : ℝ → Measure E := fun t ↦ P.map (fun ω ↦ (Z ω).IccExtend hT t)
  have hμp (t : ℝ) : IsProbabilityMeasure (μ t) := inferInstance
  have hμi (t : ℝ) : Integrable (fun v ↦ ‖v‖) (μ t) := by
    exact (integrable_map_measure continuous_norm.aestronglyMeasurable
      (((ContinuousMap.measurable_eval (Set.projIcc 0 T hT t)).comp hZm).aemeasurable)).2
      (integrable_IccExtend_eval P hT Z hZm hZi t).norm
  have hμb : Continuous (Function.uncurry (fun t v ↦ b v (μ t))) := by
    have hbeq : (fun t v ↦ b v (μ t)) = nonlinearFrozenDrift P hT b Z hZm hZi := by
      funext t v
      rw [nonlinearFrozenDrift, pathMarginalLaw_toMeasure]
    rw [hbeq]
    exact continuous_nonlinearFrozenDrift P hT b hb Z hZm hZi
  let y : ℝ → Fin N → E := fun t j ↦ (z j).IccExtend hT t
  have hy : Continuous y := continuous_pi fun j ↦ ((z j).IccExtend hT).continuous
  let r := (TauCeti.wassersteinEDist 1 (empiricalMeasure N z) (P.map Z)).toReal
  have hW (t : ℝ) (_ht : t ∈ Icc (0 : ℝ) T) :
      (TauCeti.wassersteinEDist 1 (empiricalMeasure N (y t)) (μ t)).toReal ≤ r := by
    have hh := wassersteinEDist_one_empirical_IccExtend_toReal_le hN hT z (P.map Z)
      (wassersteinEDist_one_empirical_map_ne_top P hN z Z hZm hZi) t
    have hEval : Measurable (fun f : C(Icc (0 : ℝ) T, E) ↦ f.IccExtend hT t) :=
      ContinuousMap.measurable_eval (Set.projIcc 0 T hT t)
    rw [hEval.aemeasurable.map_map_of_aemeasurable hZm.aemeasurable] at hh
    have hcomp : (fun f : C(Icc (0 : ℝ) T, E) ↦ f.IccExtend hT t) ∘ Z =
        (fun ω ↦ (Z ω).IccExtend hT t) := rfl
    rw [hcomp] at hh
    exact hh
  have hg := norm_sub_le_of_particle_integral_eq hT hN b hb μ hμp hμi hμb
    x y f hx hy hxe hze r ENNReal.toReal_nonneg hW
  have hc : 0 ≤ (Real.toNNReal L : ℝ) * T * Real.exp (2 * (Real.toNNReal L : ℝ) * T) * r :=
    mul_nonneg (mul_nonneg (mul_nonneg (Real.toNNReal L).coe_nonneg hT) (Real.exp_pos _).le) ENNReal.toReal_nonneg
  apply (ContinuousMap.norm_le _ hc).2
  intro t
  have hh := (norm_le_pi_norm (x t - y t) i).trans (hg t t.2)
  have hxi : Continuous (fun s ↦ x s i) := (continuous_apply i).comp hx
  rw [ContinuousMap.sub_apply, pathOn_apply_of_continuousOn T (fun s ↦ x s i) hxi.continuousOn t]
  simpa only [y, Pi.sub_apply,
    ContinuousMap.coe_IccExtend, Set.IccExtend_of_mem (h := hT) (fun u ↦ z i u) t.2] using hh
end CKSD
