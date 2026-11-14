module

public import CKSD.Bayes.MeanFieldLaw
public import CKSD.Bayes.MeanFieldWasserstein
public import Mathlib.MeasureTheory.Function.L1Space.AEEqFun

/-!
# First-Wasserstein continuity of random path marginals

An integrable random continuous path has integrable evaluation at each time. Dominated
convergence and the common-source coupling estimate then show that its marginal law varies
continuously in first Wasserstein distance. This gives the continuous frozen-law drifts used
in the path-space Picard construction of McKean–Vlasov solutions.

Mathlib supplies continuous path norms and dominated convergence; pinned TauCeti supplies the
first-Wasserstein space and coupling estimates through the local adapters.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators
namespace CKSD
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- Integrable random continuous paths have integrable evaluation at every projected time. -/
theorem integrable_IccExtend_eval (P : Measure Ω) {T : ℝ} (hT : 0 ≤ T)
    (U : Ω → C(Icc (0 : ℝ) T, E)) (hUm : Measurable U) (hUi : Integrable U P) (t : ℝ) :
    Integrable (fun ω ↦ (U ω).IccExtend hT t) P := by
  have hm : Measurable (fun f : C(Icc (0 : ℝ) T, E) ↦ f.IccExtend hT t) :=
    ContinuousMap.measurable_eval (Set.projIcc 0 T hT t)
  apply hUi.norm.mono' (hm.comp hUm).aestronglyMeasurable
  exact ae_of_all _ fun ω ↦ (U ω).norm_coe_le_norm (Set.projIcc 0 T hT t)

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- The law of an integrable random variable has finite first moment. -/
theorem hasFiniteMoment_one_map_of_integrable (P : Measure Ω) (U : Ω → E)
    (hUm : Measurable U) (hUi : Integrable U P) : TauCeti.HasFiniteMoment 1 (P.map U) := by
  have hm : Integrable (id : E → E) (P.map U) :=
    (integrable_map_measure aestronglyMeasurable_id hUm.aemeasurable).mpr hUi
  rw [TauCeti.hasFiniteMoment_def]
  refine ⟨0, ?_⟩
  simpa only [edist_eq_enorm_sub, zero_sub, enorm_neg, id_eq] using
    (memLp_one_iff_integrable.mpr hm).enorm

/-- First-Wasserstein marginal law of an integrable random continuous path. -/
def pathMarginalLaw (P : Measure Ω) [IsProbabilityMeasure P] {T : ℝ} (hT : 0 ≤ T)
    (U : Ω → C(Icc (0 : ℝ) T, E)) (hUm : Measurable U) (hUi : Integrable U P) (t : ℝ) :
    TauCeti.WassersteinSpace 1 E :=
  TauCeti.WassersteinSpace.mk
    (ProbabilityMeasure.map (⟨P, inferInstance⟩ : ProbabilityMeasure Ω) (fun ω ↦ (U ω).IccExtend hT t))
    (hasFiniteMoment_one_map_of_integrable P _ ((ContinuousMap.measurable_eval (Set.projIcc 0 T hT t)).comp hUm)
      (integrable_IccExtend_eval P hT U hUm hUi t))

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- The underlying marginal measure is the pushforward under projected evaluation. -/
theorem pathMarginalLaw_toMeasure (P : Measure Ω) [IsProbabilityMeasure P] {T : ℝ} (hT : 0 ≤ T)
    (U : Ω → C(Icc (0 : ℝ) T, E)) (hUm : Measurable U) (hUi : Integrable U P) (t : ℝ) :
    ((pathMarginalLaw P hT U hUm hUi t : ProbabilityMeasure E) : Measure E) =
      P.map (fun ω ↦ (U ω).IccExtend hT t) := by
  exact (congrArg ProbabilityMeasure.toMeasure (TauCeti.WassersteinSpace.coe_mk _ _)).trans rfl

/-- Integrability of the uniform path norm makes the marginal laws continuous in first
Wasserstein distance. -/
theorem continuous_pathMarginalLaw (P : Measure Ω) [IsProbabilityMeasure P] {T : ℝ} (hT : 0 ≤ T)
    (U : Ω → C(Icc (0 : ℝ) T, E)) (hUm : Measurable U) (hUi : Integrable U P) :
    Continuous (pathMarginalLaw P hT U hUm hUi) := by
  let Y : ℝ → Ω → E := fun t ω ↦ (U ω).IccExtend hT t
  have hYm (t : ℝ) : Measurable (Y t) :=
    (ContinuousMap.measurable_eval (Set.projIcc 0 T hT t)).comp hUm
  have hYb (t : ℝ) (ω : Ω) : ‖Y t ω‖ ≤ ‖U ω‖ :=
    (U ω).norm_coe_le_norm (Set.projIcc 0 T hT t)
  let D : ℝ × ℝ → ℝ := fun p ↦ ∫ ω, ‖Y p.1 ω - Y p.2 ω‖ ∂P
  have hDc : Continuous D := by
    apply continuous_of_dominated (bound := fun ω ↦ 2 * ‖U ω‖)
    · intro p
      exact ((hYm p.1).sub (hYm p.2)).norm.aestronglyMeasurable
    · intro p
      refine ae_of_all _ fun ω ↦ ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      exact (norm_sub_le _ _).trans (by linarith [hYb p.1 ω, hYb p.2 ω])
    · exact hUi.norm.const_mul 2
    · exact ae_of_all _ fun ω ↦ (((U ω).IccExtend hT).continuous.comp continuous_fst |>.sub
        (((U ω).IccExtend hT).continuous.comp continuous_snd)).norm
  have hW (s t : ℝ) : dist (pathMarginalLaw P hT U hUm hUi s) (pathMarginalLaw P hT U hUm hUi t) ≤ D (s, t) := by
    rw [TauCeti.WassersteinSpace.dist_def, pathMarginalLaw_toMeasure, pathMarginalLaw_toMeasure]
    exact wassersteinEDist_one_map_toReal_le_integral_norm_sub P (hYm s).aestronglyMeasurable
      (hYm t).aestronglyMeasurable ((integrable_IccExtend_eval P hT U hUm hUi s).sub
        (integrable_IccExtend_eval P hT U hUm hUi t))
  apply continuous_iff_continuousAt.mpr
  intro t
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hlim : Tendsto (fun s ↦ D (s, t)) (𝓝 t) (𝓝 0) := by
    simpa only [Function.comp_def, id_eq, D, sub_self, norm_zero, integral_zero] using
      (hDc.comp (continuous_id.prodMk (continuous_const : Continuous (fun _ : ℝ ↦ t)))).continuousAt.tendsto (x := t)
  filter_upwards [hlim.eventually (gt_mem_nhds hε)] with s hs
  exact (hW s t).trans_lt hs
end CKSD
