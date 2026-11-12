module
public import CKSD.Bayes.MeanFieldBackwardTest
public import CKSD.Bayes.MeanFieldContinuityUniqueness
public import CKSD.Bayes.MeanFieldContinuityMoments
public import TauCeti.MeasureTheory.OptimalTransport.ContinuityEquation.Basic
/-!
# Characteristic representation of bounded Lipschitz continuity equations

A globally Lipschitz space-time velocity has a canonical characteristic family obtained from
the augmented autonomous flow. Under a uniform velocity bound, its marginal laws solve the
continuity equation for every initial probability law. Dominated convergence gives narrow
continuity without moment assumptions. Weak continuity-equation uniqueness identifies every
narrowly continuous nonnegative-time probability solution with those characteristic laws.

Pinned TauCeti supplies globally Lipschitz ODE flows and the Lagrangian continuity-equation
construction. Mathlib supplies dominated convergence and finite-measure weak topology. Local
backward transport tests supply uniqueness. This is the characteristic representation step
for the mean-field training limit, GAPS 104.53.
-/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped ENNReal NNReal Topology ContDiff
namespace CKSD
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [NormedSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- Jointly continuous trajectories have narrowly continuous marginal laws under any probability
initial measure; no moment assumption is needed. -/
theorem continuous_integral_map_of_continuous_curves (P : Measure E) [IsProbabilityMeasure P]
    (γ : E → ℝ → E) (hγ : Continuous (uncurry γ)) (g : BoundedContinuousFunction E ℝ) :
    Continuous (fun t ↦ ∫ x, g x ∂P.map (fun x ↦ γ x t)) := by
  have hm (t : ℝ) : Measurable (fun x ↦ γ x t) :=
    (hγ.comp (continuous_id.prodMk continuous_const)).measurable
  have heq (t : ℝ) : (∫ x, g x ∂P.map (fun x ↦ γ x t)) = ∫ x, g (γ x t) ∂P :=
    integral_map (hm t).aemeasurable g.continuous.aestronglyMeasurable
  simp_rw [heq]
  apply continuous_of_dominated (bound := fun _ ↦ ‖g‖)
  · intro t
    exact (g.continuous.comp (hγ.comp (continuous_id.prodMk continuous_const))).aestronglyMeasurable
  · intro t
    exact ae_of_all _ fun x ↦ g.norm_coe_le_norm _
  · exact integrable_const _
  · exact ae_of_all _ fun x ↦ g.continuous.comp (hγ.comp (continuous_const.prodMk continuous_id))

/-- A bounded globally Lipschitz space-time velocity has a canonical family of characteristics
whose marginal laws solve the continuity equation for arbitrary initial probability laws. -/
theorem exists_flow_law_of_bounded_lipschitz (v : ℝ × E → E) {K M : ℝ≥0}
    (hv : LipschitzWith K v) (hM : ∀ q, ‖v q‖₊ ≤ M)
    (P : Measure E) [IsProbabilityMeasure P] :
    ∃ γ : E → ℝ → E, Continuous (uncurry γ) ∧ (∀ x, γ x 0 = x) ∧
      (∀ x t, HasDerivAt (γ x) (v (t, γ x t)) t) ∧
      (∀ T > 0, TauCeti.IsContinuityEquation
        (fun t ↦ P.map (fun x ↦ γ x t)) (fun t x ↦ v (t, x)) 0 T) ∧
      (∀ g : BoundedContinuousFunction E ℝ,
        Continuous (fun t ↦ ∫ x, g x ∂P.map (fun x ↦ γ x t))) := by
  let w : ℝ × E → ℝ × E := fun q ↦ (1, v q)
  have hc : LipschitzWith K (fun _ : ℝ × E ↦ (1 : ℝ)) :=
    (LipschitzWith.const 1).weaken (bot_le)
  have hw : LipschitzWith K w := by simpa only [w, max_self] using hc.prodMk hv
  let γ : E → ℝ → E := fun x t ↦ (ODE.globalSolution w hw (0, x) t).2
  have hγ : Continuous (uncurry γ) :=
    ((ODE.continuous_globalSolution w hw).comp
      (continuous_snd.prodMk (continuous_const.prodMk continuous_fst))).snd
  have hzero (x : E) : γ x 0 = x := by simp only [γ, ODE.globalSolution_zero]
  have hd (x : E) (t : ℝ) : HasDerivAt (γ x) (v (t, γ x t)) t := by
    have hh := (ContinuousLinearMap.snd ℝ ℝ E).hasFDerivAt.comp_hasDerivAt t
      (ODE.hasDerivAt_globalSolution w hw (0,x) t)
    change HasDerivAt (γ x)
      (v ((ODE.globalSolution w hw (0,x) t).1, γ x t)) t at hh
    have ht := globalSolution_fst_eq_add w hw (fun _ ↦ rfl) (0,x) t
    simp only [zero_add] at ht
    rwa [ht] at hh
  have hγL (x : E) : LipschitzWith M (γ x) := by
    apply lipschitzWith_of_nnnorm_deriv_le
    · exact fun t ↦ (hd x t).differentiableAt
    · intro t
      rw [(hd x t).deriv]
      exact hM _
  refine ⟨γ, hγ, hzero, hd, ?_, continuous_integral_map_of_continuous_curves P γ hγ⟩
  intro T _hT
  apply TauCeti.isContinuityEquation_map P (v := fun t x ↦ v (t,x)) hγ.measurable hv.continuous.measurable
    (ae_of_all _ fun x ↦ (hγL x).lipschitzOnWith.absolutelyContinuousOnInterval)
    (ae_of_all _ fun x ↦ ae_of_all _ fun t _ ↦ hd x t)
  have hbound : (∫⁻ x, ∫⁻ t in Ioo (0 : ℝ) T, ‖v (t, γ x t)‖ₑ ∂volume ∂P) ≤
      ∫⁻ _x, ∫⁻ _t in Ioo (0 : ℝ) T, (M : ℝ≥0∞) ∂volume ∂P := by
    apply lintegral_mono
    intro x
    apply lintegral_mono
    intro t
    change (‖v (t, γ x t)‖₊ : ℝ≥0∞) ≤ (M : ℝ≥0∞)
    exact ENNReal.coe_le_coe.mpr (hM _)
  apply lt_of_le_of_lt hbound
  simp only [lintegral_const, Measure.restrict_apply_univ, measure_univ, mul_one]
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top measure_Ioo_lt_top
section InnerProduct
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H] [CompleteSpace H]
/-- Narrowly continuous probability solutions with a common initial law agree at every
nonnegative time for a bounded globally Lipschitz space-time velocity. -/
theorem eq_on_nonneg_of_isContinuityEquation_of_bounded_lipschitz
    (v : ℝ × H → H) {K M : ℝ≥0} (hv : LipschitzWith K v) (hM : ∀ q, ‖v q‖₊ ≤ M)
    (μ ν : ℝ → Measure H)
    (hμp : ∀ t ≥ 0, IsProbabilityMeasure (μ t))
    (hνp : ∀ t ≥ 0, IsProbabilityMeasure (ν t))
    (hμc : ∀ g : BoundedContinuousFunction H ℝ,
      ContinuousOn (fun t ↦ ∫ x, g x ∂μ t) (Ici 0))
    (hνc : ∀ g : BoundedContinuousFunction H ℝ,
      ContinuousOn (fun t ↦ ∫ x, g x ∂ν t) (Ici 0))
    (hμce : ∀ T > 0, TauCeti.IsContinuityEquation μ (fun t x ↦ v (t,x)) 0 T)
    (hνce : ∀ T > 0, TauCeti.IsContinuityEquation ν (fun t x ↦ v (t,x)) 0 T)
    (hinit : μ 0 = ν 0) (t : ℝ) (ht : 0 ≤ t) : μ t = ν t := by
  obtain rfl | ht := ht.eq_or_lt
  · exact hinit
  let μ' := finiteMeasureNonnegExtension μ hμp
  let ν' := finiteMeasureNonnegExtension ν hνp
  have hμc' : Continuous μ' := continuous_finiteMeasure_nonneg_extension μ hμp hμc
  have hνc' : Continuous ν' := continuous_finiteMeasure_nonneg_extension ν hνp hνc
  have hμce' : TauCeti.IsContinuityEquation (fun s ↦ (μ' s : Measure H)) (fun s x ↦ v (s,x)) 0 t := by
    apply isContinuityEquation_congr_measure_on_Ioo (hμce t ht)
      ((hμce t ht).measurable.comp (continuous_const.max continuous_id).measurable)
    intro s hs
    change μ (max 0 s) = μ s
    rw [max_eq_right hs.1.le]
  have hνce' : TauCeti.IsContinuityEquation (fun s ↦ (ν' s : Measure H)) (fun s x ↦ v (s,x)) 0 t := by
    apply isContinuityEquation_congr_measure_on_Ioo (hνce t ht)
      ((hνce t ht).measurable.comp (continuous_const.max continuous_id).measurable)
    intro s hs
    change ν (max 0 s) = ν s
    rw [max_eq_right hs.1.le]
  have hpμ (s : ℝ) (_hs : s ∈ Icc (0 : ℝ) t) : IsProbabilityMeasure (μ' s : Measure H) :=
    hμp (max 0 s) (le_max_left _ _)
  have hpν (s : ℝ) (_hs : s ∈ Icc (0 : ℝ) t) : IsProbabilityMeasure (ν' s : Measure H) :=
    hνp (max 0 s) (le_max_left _ _)
  have hinit' : μ' 0 = ν' 0 := by
    apply Subtype.ext
    change μ (max 0 0) = ν (max 0 0)
    simpa only [max_self] using hinit
  have heq := eq_of_isContinuityEquation_of_bounded_lipschitz ht.le v hv hM μ' ν'
    hμc'.continuousOn hνc'.continuousOn hpμ hpν hμce' hνce' hinit'
  have hh := congrArg (fun κ : FiniteMeasure H ↦ (κ : Measure H)) heq
  simpa only [μ', ν', finiteMeasureNonnegExtension_toMeasure, max_eq_right ht.le] using hh
/-- Bounded globally Lipschitz space-time velocities represent every narrowly continuous
probability solution by the canonical characteristic flow, with no moment hypothesis. -/
theorem exists_flow_representation_of_bounded_lipschitz
    (v : ℝ × H → H) {K M : ℝ≥0} (hv : LipschitzWith K v) (hM : ∀ q, ‖v q‖₊ ≤ M)
    (P : Measure H) [IsProbabilityMeasure P] :
    ∃ γ : H → ℝ → H, Continuous (uncurry γ) ∧ (∀ x, γ x 0 = x) ∧
      (∀ x t, HasDerivAt (γ x) (v (t, γ x t)) t) ∧
      (∀ T > 0, TauCeti.IsContinuityEquation
        (fun t ↦ P.map (fun x ↦ γ x t)) (fun t x ↦ v (t, x)) 0 T) ∧
      (∀ g : BoundedContinuousFunction H ℝ,
        Continuous (fun t ↦ ∫ x, g x ∂P.map (fun x ↦ γ x t))) ∧
      ∀ σ : ℝ → Measure H,
        (∀ t ≥ 0, IsProbabilityMeasure (σ t)) →
        (∀ g : BoundedContinuousFunction H ℝ,
          ContinuousOn (fun t ↦ ∫ x, g x ∂σ t) (Ici 0)) →
        (∀ T > 0, TauCeti.IsContinuityEquation σ (fun t x ↦ v (t,x)) 0 T) →
        σ 0 = P → ∀ t ≥ 0, σ t = P.map (fun x ↦ γ x t) := by
  obtain ⟨γ, hγ, hzero, hd, hce, hc⟩ := exists_flow_law_of_bounded_lipschitz v hv hM P
  refine ⟨γ, hγ, hzero, hd, hce, hc, ?_⟩
  intro σ hσp hσc hσce hinit t ht
  have hp : ∀ s ≥ 0, IsProbabilityMeasure (P.map (fun x ↦ γ x s)) := by
    intro s _
    infer_instance
  have hzero' : P.map (fun x ↦ γ x 0) = P := by
    simp only [hzero, Measure.map_id']
  exact eq_on_nonneg_of_isContinuityEquation_of_bounded_lipschitz v hv hM σ
    (fun s ↦ P.map (fun x ↦ γ x s)) hσp hp hσc (fun g ↦ (hc g).continuousOn)
    hσce hce (hinit.trans hzero'.symm) t ht
end InnerProduct
end CKSD
