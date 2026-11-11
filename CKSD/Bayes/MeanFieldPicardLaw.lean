module

public import CKSD.Bayes.MeanFieldPathLaws
public import CKSD.Bayes.MeanFieldPicard

/-!
# The frozen-law Picard operator on integrable random paths

Freezing the marginal laws of an integrable random continuous path gives a continuous drift.
Solving its additive-forcing integral equation defines a new integrable random path, hence an
operator on the complete space `L¹(P; C([0,T],E))`. Fixed points solve the nonlinear
McKean–Vlasov equation on the time interval.

The construction uses the local continuous forcing solution map and first-Wasserstein marginal
continuity. Mathlib supplies Bochner `L¹` spaces and measurable representatives.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators
namespace CKSD
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The drift obtained by freezing the marginal laws of an integrable random path. -/
def nonlinearFrozenDrift (P : Measure Ω) [IsProbabilityMeasure P] {T : ℝ} (hT : 0 ≤ T)
    (b : E → Measure E → E) (U : Ω → C(Icc (0 : ℝ) T, E))
    (hUm : Measurable U) (hUi : Integrable U P) (t : ℝ) (x : E) : E :=
  b x ((pathMarginalLaw P hT U hUm hUi t : ProbabilityMeasure E) : Measure E)

/-- Frozen marginal laws give a jointly continuous drift. -/
theorem continuous_nonlinearFrozenDrift (P : Measure Ω) [IsProbabilityMeasure P]
    {T : ℝ} (hT : 0 ≤ T) (b : E → Measure E → E) {L : ℝ}
    (hb : IsWassersteinLipschitzDrift b L) (U : Ω → C(Icc (0 : ℝ) T, E))
    (hUm : Measurable U) (hUi : Integrable U P) :
    Continuous (Function.uncurry (nonlinearFrozenDrift P hT b U hUm hUi)) :=
  (hb.lipschitzWith_lift b).continuous.comp
    (continuous_snd.prodMk ((continuous_pathMarginalLaw P hT U hUm hUi).comp continuous_fst))

/-- Freezing a path law retains the spatial Lipschitz constant. -/
theorem lipschitzWith_nonlinearFrozenDrift (P : Measure Ω) [IsProbabilityMeasure P]
    {T : ℝ} (hT : 0 ≤ T) (b : E → Measure E → E) {L : ℝ}
    (hb : IsWassersteinLipschitzDrift b L) (U : Ω → C(Icc (0 : ℝ) T, E))
    (hUm : Measurable U) (hUi : Integrable U P) (t : ℝ) :
    LipschitzWith (Real.toNNReal L) (nonlinearFrozenDrift P hT b U hUm hUi t) := by
  let μ := pathMarginalLaw P hT U hUm hUi t
  have hi : Integrable (fun z ↦ ‖z‖) ((μ : ProbabilityMeasure E) : Measure E) := by
    simpa only [id_eq] using (TauCeti.WassersteinSpace.hasFiniteMoment μ).memLp_id.integrable (by norm_num) |>.norm
  exact hb.lipschitzWith_position b _ hi

/-- Solve the pathwise equation with the marginal laws of a prescribed random path. -/
def frozenPathSolutionMap (P : Measure Ω) [IsProbabilityMeasure P] {T : ℝ} (hT : 0 ≤ T)
    (b : E → Measure E → E) {L : ℝ} (hb : IsWassersteinLipschitzDrift b L)
    (U : Ω → C(Icc (0 : ℝ) T, E)) (hUm : Measurable U) (hUi : Integrable U P) :
    C(Icc (0 : ℝ) T, E) → C(Icc (0 : ℝ) T, E) :=
  (pathForcingEquiv hT (nonlinearFrozenDrift P hT b U hUm hUi)
    (continuous_nonlinearFrozenDrift P hT b hb U hUm hUi)
    (lipschitzWith_nonlinearFrozenDrift P hT b hb U hUm hUi)).symm

/-- Frozen-law solutions depend Lipschitz continuously on their additive forcing. -/
theorem lipschitzWith_frozenPathSolutionMap (P : Measure Ω) [IsProbabilityMeasure P]
    {T : ℝ} (hT : 0 ≤ T) (b : E → Measure E → E) {L : ℝ}
    (hb : IsWassersteinLipschitzDrift b L) (U : Ω → C(Icc (0 : ℝ) T, E))
    (hUm : Measurable U) (hUi : Integrable U P) :
    LipschitzWith (Real.toNNReal (Real.exp ((Real.toNNReal L : ℝ) * T)))
      (frozenPathSolutionMap P hT b hb U hUm hUi) :=
  lipschitzWith_pathForcingEquiv_symm hT _ _ _

set_option maxHeartbeats 800000 in
/-- Integrable random forcings give integrable frozen-law solution paths. -/
theorem integrable_frozenPathSolutionMap_comp (P : Measure Ω) [IsProbabilityMeasure P]
    {T : ℝ} (hT : 0 ≤ T) (b : E → Measure E → E) {L : ℝ}
    (hb : IsWassersteinLipschitzDrift b L) (U F : Ω → C(Icc (0 : ℝ) T, E))
    (hUm : Measurable U) (hUi : Integrable U P) (hFm : Measurable F) (hFi : Integrable F P) :
    Integrable (fun ω ↦ frozenPathSolutionMap P hT b hb U hUm hUi (F ω)) P := by
  let G := frozenPathSolutionMap P hT b hb U hUm hUi
  have hG := lipschitzWith_frozenPathSolutionMap P hT b hb U hUm hUi
  let c := Real.toNNReal (Real.exp ((Real.toNNReal L : ℝ) * T))
  apply ((hFi.norm.const_mul (c : ℝ)).add (integrable_const ‖G 0‖)).mono'
    (hG.continuous.measurable.comp hFm).aestronglyMeasurable
  refine ae_of_all _ fun ω ↦ ?_
  have h := hG.norm_sub_le (F ω) 0
  simp only [sub_zero] at h
  change ‖G (F ω) - G 0‖ ≤ (c : ℝ) * ‖F ω‖ at h
  change ‖G (F ω)‖ ≤ (c : ℝ) * ‖F ω‖ + ‖G 0‖
  calc _ = ‖(G (F ω) - G 0) + G 0‖ := by rw [sub_add_cancel]
    _ ≤ ‖G (F ω) - G 0‖ + ‖G 0‖ := norm_add_le _ _
    _ ≤ _ := by linarith only [h]

/-- The frozen-law Picard operator on integrable random continuous paths. -/
def nonlinearPathPicard (P : Measure Ω) [IsProbabilityMeasure P] {T : ℝ} (hT : 0 ≤ T)
    (b : E → Measure E → E) {L : ℝ} (hb : IsWassersteinLipschitzDrift b L)
    (F : Ω → C(Icc (0 : ℝ) T, E)) (hFm : Measurable F) (hFi : Integrable F P)
    (U : Lp C(Icc (0 : ℝ) T, E) 1 P) : Lp C(Icc (0 : ℝ) T, E) 1 P :=
  (integrable_frozenPathSolutionMap_comp P hT b hb U F (Lp.stronglyMeasurable U).measurable
    (L1.integrable_coeFn U) hFm hFi).toL1
      (fun ω ↦ frozenPathSolutionMap P hT b hb U (Lp.stronglyMeasurable U).measurable (L1.integrable_coeFn U) (F ω))
/-- Frozen-law solutions satisfy their pathwise integral equation at every time. -/
theorem frozenPathSolutionMap_apply_eq (P : Measure Ω) [IsProbabilityMeasure P]
    {T : ℝ} (hT : 0 ≤ T) (b : E → Measure E → E) {L : ℝ}
    (hb : IsWassersteinLipschitzDrift b L) (U : Ω → C(Icc (0 : ℝ) T, E))
    (hUm : Measurable U) (hUi : Integrable U P) (f : C(Icc (0 : ℝ) T, E)) (t : Icc (0 : ℝ) T) :
    frozenPathSolutionMap P hT b hb U hUm hUi f t = f t + ∫ s in (0 : ℝ)..t,
      nonlinearFrozenDrift P hT b U hUm hUi s ((frozenPathSolutionMap P hT b hb U hUm hUi f).IccExtend hT s) :=
  pathForcingEquiv_symm_apply_eq hT _ _ _ f t

/-- The integrable path representative of the Picard operator is its pathwise frozen-law solution
almost everywhere, as an equality of whole continuous paths. -/
theorem nonlinearPathPicard_ae_eq (P : Measure Ω) [IsProbabilityMeasure P]
    {T : ℝ} (hT : 0 ≤ T) (b : E → Measure E → E) {L : ℝ}
    (hb : IsWassersteinLipschitzDrift b L) (F : Ω → C(Icc (0 : ℝ) T, E))
    (hFm : Measurable F) (hFi : Integrable F P) (U : Lp C(Icc (0 : ℝ) T, E) 1 P) :
    (nonlinearPathPicard P hT b hb F hFm hFi U : Ω → C(Icc (0 : ℝ) T, E)) =ᵐ[P]
      fun ω ↦ frozenPathSolutionMap P hT b hb U (Lp.stronglyMeasurable U).measurable
        (L1.integrable_coeFn U) (F ω) := by
  exact (integrable_frozenPathSolutionMap_comp P hT b hb U F (Lp.stronglyMeasurable U).measurable
    (L1.integrable_coeFn U) hFm hFi).coeFn_toL1
end CKSD
