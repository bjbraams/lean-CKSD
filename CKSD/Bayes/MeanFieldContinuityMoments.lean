module
public import CKSD.Bayes.MeanFieldPathLaws
public import TauCeti.MeasureTheory.OptimalTransport.ContinuityEquation.BenamouBrenier
/-!
# First moments of weak continuity-equation solutions

Narrowly continuous solutions at finite velocity action have finite first-Wasserstein distance
between their endpoints. Consequently an initial first moment propagates to every subsequent
time without a moment assumption on comparison solutions. Bounded velocity gives the usual
linear displacement bound. This removes a potential restriction in the weak comparison class
of the mean-field training limit, GAPS 104.53.

Pinned TauCeti supplies the Benamou–Brenier lower bound and the finite-moment characterization
by finite Wasserstein distance. Mathlib supplies finite-measure weak topology and integration.
The local adapters permit probability curves specified only on nonnegative time.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped ENNReal NNReal Topology
namespace CKSD
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
/-- A narrowly continuous finite-measure continuity-equation solution is at finite first
Wasserstein distance between its endpoint laws. No moment of the second endpoint is assumed. -/
theorem wassersteinEDist_one_ne_top_of_isContinuityEquation
    {ν : ℝ → FiniteMeasure E} {v : ℝ → E → E} {a b : ℝ}
    (h : TauCeti.IsContinuityEquation (fun t ↦ (ν t : Measure E)) v a b)
    (hν : ContinuousOn ν (Icc a b)) (hab : a ≤ b)
    [IsProbabilityMeasure (ν a : Measure E)] :
    TauCeti.wassersteinEDist 1 (ν a : Measure E) (ν b) ≠ ∞ := by
  have hh := h.wassersteinEDist_rpow_le hν hab (p := 1) le_rfl ENNReal.one_ne_top
  simp only [ENNReal.toReal_one, ENNReal.rpow_one, sub_self, Real.rpow_zero,
    ENNReal.ofReal_one, one_mul] at hh
  exact (lt_of_le_of_lt hh h.lintegral_lintegral_enorm_lt_top).ne

/-- Finite first moments propagate along narrowly continuous solutions of the continuity
equation solely from the action integrability built into its definition. -/
theorem integrable_norm_end_of_isContinuityEquation
    {ν : ℝ → FiniteMeasure E} {v : ℝ → E → E} {a b : ℝ}
    (h : TauCeti.IsContinuityEquation (fun t ↦ (ν t : Measure E)) v a b)
    (hν : ContinuousOn ν (Icc a b)) (hab : a ≤ b)
    [IsProbabilityMeasure (ν a : Measure E)] [IsProbabilityMeasure (ν b : Measure E)]
    (hi : Integrable (fun x ↦ ‖x‖) (ν a : Measure E)) :
    Integrable (fun x ↦ ‖x‖) (ν b : Measure E) := by
  have hiid : Integrable (id : E → E) (ν a : Measure E) :=
    hi.mono' aestronglyMeasurable_id (ae_of_all _ fun x ↦ le_rfl)
  have hm : TauCeti.HasFiniteMoment 1 (ν a : Measure E) := by
    rw [TauCeti.hasFiniteMoment_def]
    refine ⟨0, ?_⟩
    simpa only [edist_eq_enorm_sub, zero_sub, enorm_neg, id_eq] using
      (memLp_one_iff_integrable.mpr hiid).enorm
  have hm' := (TauCeti.hasFiniteMoment_iff_wassersteinEDist_ne_top_of_hasFiniteMoment
    measurable_edist hm).2 (wassersteinEDist_one_ne_top_of_isContinuityEquation h hν hab)
  have him := hm'.memLp_id.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 1)
  simpa only [id_eq] using him.norm

/-- Replacing time marginals only outside the equation interval preserves its weak identity. -/
theorem isContinuityEquation_congr_measure_on_Ioo
    {μ η : ℝ → Measure E} {v : ℝ → E → E} {a b : ℝ}
    (h : TauCeti.IsContinuityEquation μ v a b) (hη : Measurable η)
    (heq : ∀ t ∈ Ioo a b, η t = μ t) : TauCeti.IsContinuityEquation η v a b := by
  refine ⟨hη, h.measurable_velocity, ?_, ?_, fun φ hφ hφc hφs ↦ ?_⟩
  · convert h.lintegral_measure_univ_lt_top using 1
    apply setLIntegral_congr_fun measurableSet_Ioo
    intro t ht
    dsimp only
    rw [heq t ht]
  · convert h.lintegral_lintegral_enorm_lt_top using 1
    apply setLIntegral_congr_fun measurableSet_Ioo
    intro t ht
    dsimp only
    rw [heq t ht]
  · convert h.integral_integral_fderiv_eq_zero hφ hφc hφs using 1
    apply setIntegral_congr_fun measurableSet_Ioo
    intro t ht
    dsimp only
    rw [heq t ht]

/-- Continue a nonnegative-time probability marginal family constantly to negative times. -/
def finiteMeasureNonnegExtension (μ : ℝ → Measure E)
    (hp : ∀ t ≥ 0, IsProbabilityMeasure (μ t)) (t : ℝ) : FiniteMeasure E :=
  ⟨μ (max 0 t), by have := hp (max 0 t) (le_max_left _ _); infer_instance⟩

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- The extended finite measure has the prescribed nonnegative-time marginal. -/
theorem finiteMeasureNonnegExtension_toMeasure (μ : ℝ → Measure E)
    (hp : ∀ t ≥ 0, IsProbabilityMeasure (μ t)) (t : ℝ) :
    (finiteMeasureNonnegExtension μ hp t : Measure E) = μ (max 0 t) := rfl

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The nonnegative-time marginal family, continued constantly to negative times, is narrowly
continuous whenever its bounded continuous tests are continuous on the nonnegative half-line. -/
theorem continuous_finiteMeasure_nonneg_extension
    (μ : ℝ → Measure E) (hp : ∀ t ≥ 0, IsProbabilityMeasure (μ t))
    (hc : ∀ g : BoundedContinuousFunction E ℝ, ContinuousOn (fun t ↦ ∫ x, g x ∂μ t) (Ici 0)) :
    Continuous (finiteMeasureNonnegExtension μ hp) := by
  apply FiniteMeasure.continuous_iff_forall_continuous_integral.2
  intro g
  change Continuous (fun t ↦ ∫ x, g x ∂μ (max 0 t))
  exact (hc g).comp_continuous (continuous_const.max continuous_id) fun t ↦ le_max_left _ _

/-- A narrowly continuous probability solution on nonnegative time has integrable norm at
every time, provided the initial law has integrable norm. -/
theorem integrable_norm_of_isContinuityEquation_on_nonneg
    (μ : ℝ → Measure E) (hp : ∀ t ≥ 0, IsProbabilityMeasure (μ t))
    (hc : ∀ g : BoundedContinuousFunction E ℝ, ContinuousOn (fun t ↦ ∫ x, g x ∂μ t) (Ici 0))
    (v : ℝ → E → E)
    (hce : ∀ T > 0, TauCeti.IsContinuityEquation μ v 0 T)
    (hi : Integrable (fun x ↦ ‖x‖) (μ 0)) (t : ℝ) (ht : 0 ≤ t) :
    Integrable (fun x ↦ ‖x‖) (μ t) := by
  obtain rfl | ht := ht.eq_or_lt
  · exact hi
  let ν : ℝ → FiniteMeasure E := finiteMeasureNonnegExtension μ hp
  have hν : Continuous ν := continuous_finiteMeasure_nonneg_extension μ hp hc
  have hmeas : Measurable (fun s ↦ (ν s : Measure E)) :=
    (hce t ht).measurable.comp (continuous_const.max continuous_id).measurable
  have heq (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) t) : (ν s : Measure E) = μ s := by
    simp only [ν, finiteMeasureNonnegExtension_toMeasure, max_eq_right hs.1.le]
  have hνce := isContinuityEquation_congr_measure_on_Ioo (hce t ht) hmeas heq
  let : IsProbabilityMeasure (ν 0 : Measure E) := by simpa only [ν, finiteMeasureNonnegExtension_toMeasure, max_self] using hp 0 le_rfl
  let : IsProbabilityMeasure (ν t : Measure E) := by simpa only [ν, finiteMeasureNonnegExtension_toMeasure, max_eq_right ht.le] using hp t ht.le
  have hi' : Integrable (fun x ↦ ‖x‖) (ν 0 : Measure E) := by simpa only [ν, finiteMeasureNonnegExtension_toMeasure, max_self] using hi
  have hh := integrable_norm_end_of_isContinuityEquation hνce hν.continuousOn ht.le hi'
  simpa only [ν, finiteMeasureNonnegExtension_toMeasure, max_eq_right ht.le] using hh

/-- Bounded velocity controls first-Wasserstein displacement without any endpoint moment
hypotheses. -/
theorem wassersteinEDist_one_le_of_isContinuityEquation_of_bound
    {ν : ℝ → FiniteMeasure E} {v : ℝ → E → E} {a b : ℝ}
    (h : TauCeti.IsContinuityEquation (fun t ↦ (ν t : Measure E)) v a b)
    (hν : ContinuousOn ν (Icc a b)) (hab : a ≤ b)
    (hp : ∀ t ∈ Icc a b, IsProbabilityMeasure (ν t : Measure E))
    (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ t ∈ Ioo a b, ∀ x, ‖v t x‖ ≤ M) :
    TauCeti.wassersteinEDist 1 (ν a : Measure E) (ν b) ≤ ENNReal.ofReal (M * (b - a)) := by
  let := hp a ⟨le_rfl, hab⟩
  have hh := h.wassersteinEDist_rpow_le hν hab (p := 1) le_rfl ENNReal.one_ne_top
  simp only [ENNReal.toReal_one, ENNReal.rpow_one, sub_self, Real.rpow_zero,
    ENNReal.ofReal_one, one_mul] at hh
  have hstep : (∫⁻ t in Ioo a b, ∫⁻ x, ‖v t x‖ₑ ∂(ν t : Measure E)) ≤
      ∫⁻ _t in Ioo a b, ENNReal.ofReal M := by
    apply setLIntegral_mono' measurableSet_Ioo
    intro t ht
    let := hp t ⟨ht.1.le, ht.2.le⟩
    calc
      (∫⁻ x, ‖v t x‖ₑ ∂(ν t : Measure E)) ≤
          (∫⁻ _x, ENNReal.ofReal M ∂(ν t : Measure E)) := by
        apply lintegral_mono
        intro x
        dsimp only
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (hbound t ht x)
      _ = ENNReal.ofReal M := by simp
  apply hh.trans (hstep.trans_eq _)
  rw [setLIntegral_const, Real.volume_Ioo, ← ENNReal.ofReal_mul hM]
end CKSD
