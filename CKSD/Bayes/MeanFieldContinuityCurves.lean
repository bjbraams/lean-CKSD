module
public import CKSD.Bayes.MeanFieldContinuityMoments
public import CKSD.Bayes.MeanFieldCore
/-!
# First-Wasserstein time bounds for weak nonlinear continuity equations

Bounded velocity makes any narrowly continuous probability solution Lipschitz in first
Wasserstein distance. A Wasserstein-Lipschitz nonlinear drift therefore becomes globally
Lipschitz in space and projected nonnegative time along that solution. Initial first moments
are propagated by the continuity-equation action bound; none are assumed for comparison
solutions at later times.

The estimate uses pinned TauCeti's Benamou–Brenier lower bound through the local moment and
finite-measure adapters, and supports GAPS 104.53.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped ENNReal NNReal Topology
namespace CKSD
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
/-- Bounded velocity makes a narrowly continuous probability solution Lipschitz in first
Wasserstein distance on nonnegative time, even before any moment condition is known. -/
theorem wassersteinEDist_one_nonneg_le_of_isContinuityEquation_of_bound
    (μ : ℝ → Measure E) (hp : ∀ t ≥ 0, IsProbabilityMeasure (μ t))
    (hc : ∀ g : BoundedContinuousFunction E ℝ, ContinuousOn (fun t ↦ ∫ x, g x ∂μ t) (Ici 0))
    (v : ℝ → E → E) (hce : ∀ T > 0, TauCeti.IsContinuityEquation μ v 0 T)
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ t ≥ 0, ∀ x, ‖v t x‖ ≤ B)
    (s : ℝ) (hs : 0 ≤ s) (t : ℝ) (ht : 0 ≤ t) :
    TauCeti.wassersteinEDist 1 (μ s) (μ t) ≤ ENNReal.ofReal (B * |t - s|) := by
  let ν := finiteMeasureNonnegExtension μ hp
  have hν : Continuous ν := continuous_finiteMeasure_nonneg_extension μ hp hc
  have hνeq (r : ℝ) (hr : 0 ≤ r) : (ν r : Measure E) = μ r := by
    simp only [ν, finiteMeasureNonnegExtension_toMeasure, max_eq_right hr]
  have hνce (R : ℝ) (hR : 0 < R) :
      TauCeti.IsContinuityEquation (fun r ↦ (ν r : Measure E)) v 0 R := by
    apply isContinuityEquation_congr_measure_on_Ioo (hce R hR)
      ((hce R hR).measurable.comp (continuous_const.max continuous_id).measurable)
    intro r hr
    exact hνeq r hr.1.le
  have hfor (a : ℝ) (ha : 0 ≤ a) (b : ℝ) (hab : a ≤ b) :
      TauCeti.wassersteinEDist 1 (μ a) (μ b) ≤ ENNReal.ofReal (B * (b - a)) := by
    have hb0 : 0 ≤ b := ha.trans hab
    have hh := wassersteinEDist_one_le_of_isContinuityEquation_of_bound
      ((hνce (b + 1) (by linarith)).mono ha (by linarith : b ≤ b + 1))
      (hν.continuousOn) hab (fun r hr ↦ by rw [hνeq r (ha.trans hr.1)]; exact hp r (ha.trans hr.1))
      B hB (fun r hr x ↦ hb r (ha.trans hr.1.le) x)
    simpa only [hνeq a ha, hνeq b hb0] using hh
  rcases le_total s t with hst | hts
  · simpa only [abs_of_nonneg (sub_nonneg.2 hst)] using hfor s hs t hst
  · have hh := hfor t ht s hts
    rw [TauCeti.wassersteinEDist_comm measurable_edist 1 (μ t) (μ s)] at hh
    simpa only [abs_of_nonpos (sub_nonpos.2 hts), neg_sub] using hh

/-- Wasserstein-Lipschitz marginal curves give globally Lipschitz nonlinear drifts after
projecting time to the nonnegative half-line. -/
theorem IsWassersteinLipschitzDrift.lipschitzWith_nonneg_marginalDrift_of_wasserstein_bound {d : ℕ}
    (b : EuclideanSpace ℝ (Fin d) → Measure (EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d))
    {L : ℝ} (hb : IsWassersteinLipschitzDrift b L) (hL : 0 ≤ L)
    (μ : ℝ → Measure (EuclideanSpace ℝ (Fin d))) (hp : ∀ t ≥ 0, IsProbabilityMeasure (μ t))
    (hi' : ∀ t ≥ 0, Integrable (fun x ↦ ‖x‖) (μ t)) (B : ℝ) (hB : 0 ≤ B)
    (hWbound : ∀ s ≥ 0, ∀ t ≥ 0,
      (TauCeti.wassersteinEDist 1 (μ s) (μ t)).toReal ≤ B * |t - s|) :
    LipschitzWith (Real.toNNReal (L * (B + 1)))
      (fun q : ℝ × EuclideanSpace ℝ (Fin d) ↦ b q.2 (μ (max 0 q.1))) := by
  apply LipschitzWith.of_dist_le_mul
  intro q q'
  rw [dist_eq_norm]
  have hWr := hWbound (max 0 q.1) (le_max_left _ _) (max 0 q'.1) (le_max_left _ _)
  have ht : |max 0 q'.1 - max 0 q.1| ≤ dist q q' := by
    have hh : |max 0 q'.1 - max 0 q.1| ≤ |q'.1 - q.1| := by
      simpa only [max_comm] using abs_max_sub_max_le_abs q'.1 q.1 0
    apply hh.trans
    simpa only [NNReal.coe_one, one_mul, Real.dist_eq, abs_sub_comm] using
      LipschitzWith.prod_fst.dist_le_mul q q'
  have hx : ‖q.2 - q'.2‖ ≤ dist q q' := by
    simpa only [NNReal.coe_one, one_mul, dist_eq_norm] using
      LipschitzWith.prod_snd.dist_le_mul q q'
  have hh := hb q.2 q'.2 (μ (max 0 q.1)) (μ (max 0 q'.1))
    (hp _ (le_max_left _ _)) (hp _ (le_max_left _ _))
    (hi' _ (le_max_left _ _)) (hi' _ (le_max_left _ _))
  calc
    _ ≤ L * (‖q.2 - q'.2‖ + (TauCeti.wassersteinEDist 1 (μ (max 0 q.1)) (μ (max 0 q'.1))).toReal) := hh
    _ ≤ L * (dist q q' + B * dist q q') := mul_le_mul_of_nonneg_left
      (add_le_add hx (hWr.trans (mul_le_mul_of_nonneg_left ht hB))) hL
    _ = (L * (B + 1)) * dist q q' := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal _) dist_nonneg

/-- Along a bounded-velocity nonlinear continuity-equation solution, a Wasserstein-Lipschitz
drift is globally Lipschitz in space and projected nonnegative time. -/
theorem IsWassersteinLipschitzDrift.lipschitzWith_nonneg_marginalDrift {d : ℕ}
    (b : EuclideanSpace ℝ (Fin d) → Measure (EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d))
    {L : ℝ} (hb : IsWassersteinLipschitzDrift b L) (hL : 0 ≤ L)
    (μ : ℝ → Measure (EuclideanSpace ℝ (Fin d))) (hp : ∀ t ≥ 0, IsProbabilityMeasure (μ t))
    (hc : ∀ g : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ,
      ContinuousOn (fun t ↦ ∫ x, g x ∂μ t) (Ici 0))
    (hce : ∀ T > 0, TauCeti.IsContinuityEquation μ (fun t x ↦ b x (μ t)) 0 T)
    (hi : Integrable (fun x ↦ ‖x‖) (μ 0)) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ t ≥ 0, ∀ x, ‖b x (μ t)‖ ≤ B) :
    LipschitzWith (Real.toNNReal (L * (B + 1)))
      (fun q : ℝ × EuclideanSpace ℝ (Fin d) ↦ b q.2 (μ (max 0 q.1))) := by
  apply hb.lipschitzWith_nonneg_marginalDrift_of_wasserstein_bound b hL μ hp
    (fun t ht ↦ integrable_norm_of_isContinuityEquation_on_nonneg μ hp hc _ hce hi t ht) B hB
  intro s hs t ht
  have hW := wassersteinEDist_one_nonneg_le_of_isContinuityEquation_of_bound μ hp hc _ hce
    B hB hbound s hs t ht
  simpa only [ENNReal.toReal_ofReal (mul_nonneg hB (abs_nonneg _))] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top hW
end CKSD
