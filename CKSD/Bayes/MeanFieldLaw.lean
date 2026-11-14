module

public import CKSD.Bayes.MeanFieldCore
public import CKSD.Bayes.MeanFieldCoupling
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Borel


/-!
# Marginal laws and time-measurable nonlinear drifts

Almost sure path continuity gives weak continuity of marginal probability laws. Pointwise finite
first moments then lift their measurable dependence into first-Wasserstein space. Consequently
a Wasserstein-Lipschitz drift is time-measurable along continuous paths without assuming any
locally uniform moment bound.

Mathlib supplies the bounded-continuous-test characterization and dominated convergence;
pinned TauCeti identifies the Giry measurable structure with the finite-exponent Wasserstein
Borel structure. These lemmas support the well-posedness assertion of GAPS 104.51.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators
namespace CKSD
/-- Almost sure path continuity implies weak continuity of the marginal laws, without moment
bounds. -/
theorem continuous_probability_measure_map_of_ae_continuous {Ω E : Type*} [MeasurableSpace Ω]
    [MetricSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℝ → Ω → E)
    (hY : ∀ t, Measurable (Y t)) (hc : ∀ᵐ ω ∂P, Continuous (fun t ↦ Y t ω)) :
    Continuous (fun t ↦ ProbabilityMeasure.map (⟨P, inferInstance⟩ : ProbabilityMeasure Ω) (Y t)) := by
  apply ProbabilityMeasure.continuous_iff_forall_continuous_integral.mpr
  intro f
  change Continuous (fun t ↦ ∫ x, f x ∂P.map (Y t))
  have heq : (fun t ↦ ∫ x, f x ∂P.map (Y t)) = (fun t ↦ ∫ ω, f (Y t ω) ∂P) := by
    funext t
    exact integral_map (hY t).aemeasurable f.continuous.aestronglyMeasurable
  rw [heq]
  apply continuous_of_dominated (bound := fun _ ↦ ‖f‖)
  · intro t
    exact (f.continuous.measurable.comp (hY t)).aestronglyMeasurable
  · intro t
    exact ae_of_all _ fun ω ↦ f.norm_coe_le_norm _
  · exact integrable_const _
  · exact hc.mono fun ω hω ↦ f.continuous.comp hω
/-- Fixing a finite-first-moment probability law preserves the spatial Lipschitz bound of a
Wasserstein-Lipschitz drift. -/
theorem IsWassersteinLipschitzDrift.lipschitz_with_position {d : ℕ}
    (b : EuclideanSpace ℝ (Fin d) → Measure (EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d))
    {L : ℝ} (hb : IsWassersteinLipschitzDrift b L)
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun z ↦ ‖z‖) μ) :
    LipschitzWith (Real.toNNReal L) (fun x ↦ b x μ) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, dist_eq_norm]
  have h := hb x y μ μ inferInstance inferInstance hμ hμ
  simp only [TauCeti.wassersteinEDist_self, ENNReal.toReal_zero, add_zero] at h
  exact h.trans (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal L) (norm_nonneg _))

/-- A Wasserstein-Lipschitz drift is a globally Lipschitz function of position and its
finite-first-moment law, with the product metric. -/
theorem IsWassersteinLipschitzDrift.lipschitz_with_lift {d : ℕ}
    (b : EuclideanSpace ℝ (Fin d) → Measure (EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d))
    {L : ℝ} (hb : IsWassersteinLipschitzDrift b L) :
    LipschitzWith (2 * Real.toNNReal L)
      (fun p : EuclideanSpace ℝ (Fin d) × TauCeti.WassersteinSpace 1 (EuclideanSpace ℝ (Fin d)) ↦
        b p.1 ((p.2 : ProbabilityMeasure (EuclideanSpace ℝ (Fin d))) : Measure (EuclideanSpace ℝ (Fin d)))) := by
  let E := EuclideanSpace ℝ (Fin d)
  let B : E × TauCeti.WassersteinSpace 1 E → E := fun p ↦ b p.1 ((p.2 : ProbabilityMeasure E) : Measure E)
  change LipschitzWith (2 * Real.toNNReal L) B
  apply LipschitzWith.of_dist_le_mul
  intro p r
  have hfirst (μ : TauCeti.WassersteinSpace 1 E) : Integrable (fun z ↦ ‖z‖) ((μ : ProbabilityMeasure E) : Measure E) := by
    simpa only [id_eq] using (TauCeti.WassersteinSpace.hasFiniteMoment μ).memLp_id.integrable (by norm_num) |>.norm
  have hh := hb p.1 r.1 ((p.2 : ProbabilityMeasure E) : Measure E) ((r.2 : ProbabilityMeasure E) : Measure E)
    inferInstance inferInstance (hfirst p.2) (hfirst r.2)
  have hnn : 0 ≤ ‖p.1 - r.1‖ + (TauCeti.wassersteinEDist 1 ((p.2 : ProbabilityMeasure E) : Measure E) ((r.2 : ProbabilityMeasure E) : Measure E)).toReal := by positivity
  calc dist (B p) (B r) ≤ (Real.toNNReal L : ℝ) *
        (dist p.1 r.1 + dist p.2 r.2) := by
          rw [dist_eq_norm, TauCeti.WassersteinSpace.dist_def]
          exact hh.trans (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal L) hnn)
    _ ≤ (Real.toNNReal L : ℝ) * (2 * dist p r) := by
      apply mul_le_mul_of_nonneg_left _ (Real.toNNReal L).coe_nonneg
      rw [Prod.dist_eq]
      nlinarith [le_max_left (dist p.1 r.1) (dist p.2 r.2), le_max_right (dist p.1 r.1) (dist p.2 r.2)]
    _ = _ := by simp only [NNReal.coe_mul, NNReal.coe_ofNat]; ring
/-- A Wasserstein-Lipschitz drift is measurable in time along continuous paths and marginal
laws with finite first moments, even when no locally uniform moment bound has been assumed. -/
theorem IsWassersteinLipschitzDrift.aestrongly_measurable_drift_of_ae_continuous
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (b : EuclideanSpace ℝ (Fin d) → Measure (EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d))
    {L : ℝ} (hb : IsWassersteinLipschitzDrift b L)
    (Y : ℝ → Ω → EuclideanSpace ℝ (Fin d)) (hY : ∀ t, Measurable (Y t))
    (hYc : ∀ᵐ ω ∂P, Continuous (fun t ↦ Y t ω))
    (hYint : ∀ t ≥ 0, Integrable (fun ω ↦ ‖Y t ω‖) P)
    (x : ℝ → EuclideanSpace ℝ (Fin d)) (hx : Continuous x) :
    AEStronglyMeasurable (fun t ↦ b (x t) (P.map (Y t))) (volume.restrict (Ici (0 : ℝ))) := by
  let E := EuclideanSpace ℝ (Fin d)
  have : Fact ((1 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  have : BorelSpace (TauCeti.WassersteinSpace 1 E) := TauCeti.WassersteinSpace.borelSpace (by norm_num)
  let pm : ℝ → ProbabilityMeasure E := fun t ↦ ProbabilityMeasure.map (⟨P, inferInstance⟩ : ProbabilityMeasure Ω) (Y t)
  have hpm : Continuous pm := continuous_probability_measure_map_of_ae_continuous P Y hY hYc
  have hmem (t : ℝ≥0) : TauCeti.HasFiniteMoment 1 (pm t : Measure E) := by
    have hi : Integrable (Y t) P := (integrable_norm_iff (hY t).aestronglyMeasurable).mp (hYint t t.coe_nonneg)
    have hm : Integrable (id : E → E) (P.map (Y t)) :=
      (integrable_map_measure aestronglyMeasurable_id (hY t).aemeasurable).mpr hi
    rw [TauCeti.hasFiniteMoment_def]
    refine ⟨0, ?_⟩
    change MemLp (fun y ↦ edist (0 : E) y) 1 (P.map (Y t))
    simpa only [edist_eq_enorm_sub, zero_sub, enorm_neg, id_eq] using (memLp_one_iff_integrable.mpr hm).enorm
  let q : ℝ≥0 → TauCeti.WassersteinSpace 1 E := fun t ↦ .mk (pm t) (hmem t)
  have hq : Measurable q := TauCeti.WassersteinSpace.measurable_mk
    (hpm.measurable_probabilityMeasure.comp measurable_subtype_coe) hmem
  let B : E × TauCeti.WassersteinSpace 1 E → E := fun p ↦ b p.1 ((p.2 : ProbabilityMeasure E) : Measure E)
  have hB : LipschitzWith (2 * Real.toNNReal L) B := hb.lipschitz_with_lift b
  have hm : Measurable (fun t : ℝ ↦ B (x t, q t.toNNReal)) :=
    hB.continuous.measurable.comp (hx.measurable.prodMk (hq.comp continuous_real_toNNReal.measurable))
  apply hm.aestronglyMeasurable.restrict.congr
  filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
  simp only [B, q, TauCeti.WassersteinSpace.coe_mk, pm, Real.coe_toNNReal t ht]
  rfl
end CKSD
