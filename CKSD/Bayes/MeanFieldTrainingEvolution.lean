module
public import CKSD.Bayes.MeanFieldZeroNoise
public import CKSD.Bayes.MeanFieldFlowRepresentation
/-!
# Bounded nonlinear continuity equations and characteristic evolution

A bounded Wasserstein-Lipschitz drift admits a unique narrowly continuous probability
solution of its nonlinear continuity equation from any finite-first-moment initial law.
The comparison class has no moment assumptions: continuity-equation action bounds propagate
those moments, and characteristic representation identifies comparison solutions with
zero-forcing nonlinear integral solutions. Picard existence and nonlinear integral uniqueness
then provide the nonlinear evolution and its characteristic family.

Mathlib supplies the fundamental theorem of calculus and measurable trajectory bounds;
pinned TauCeti supplies continuity-equation and Wasserstein interfaces through the imported
local bridges. The characteristic interpretation is consistent with Carmona–Delarue, volume I,
Theorem 6.49 (printed pages 608–609), although the imported flow representation is proved by
backward transport tests rather than a general superposition principle. This supports GAPS 104.53.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped NNReal ENNReal Topology
namespace CKSD
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
/-- Bounded continuous characteristics with their own marginal drift are nonlinear integral solutions. -/
theorem isMcKeanVlasovSolution_of_bounded_characteristics
    (P : Measure E) [IsProbabilityMeasure P] (hi : Integrable (fun x ↦ ‖x‖) P)
    (b : E → Measure E → E) (v : ℝ × E → E) (hv : Continuous v)
    (M : ℝ≥0) (hM : ∀ q, ‖v q‖₊ ≤ M)
    (γ : E → ℝ → E) (hγ : Continuous (uncurry γ)) (hγ0 : ∀ x, γ x 0 = x)
    (hγd : ∀ x t, HasDerivAt (γ x) (v (t, γ x t)) t)
    (heq : ∀ t ≥ 0, ∀ x, v (t,x) = b x (P.map (fun z ↦ γ z t))) :
    IsMcKeanVlasovSolution b id (fun _ _ ↦ 0) (fun t x ↦ γ x t) P := by
  have hm (t : ℝ) : Measurable (fun x ↦ γ x t) :=
    (hγ.comp (continuous_id.prodMk continuous_const)).measurable
  have hc (x : E) : Continuous (γ x) := hγ.comp (continuous_const.prodMk continuous_id)
  have hl (x : E) : LipschitzWith M (γ x) := by
    apply lipschitzWith_of_nnnorm_deriv_le (fun t ↦ (hγd x t).differentiableAt)
    intro t
    rw [(hγd x t).deriv]
    exact hM _
  refine ⟨hm, ?_, ae_of_all _ fun x ↦ ⟨hc x, ?_⟩⟩
  · intro t _
    apply (hi.add (integrable_const ((M : ℝ) * |t|))).mono' (hm t).norm.aestronglyMeasurable
    exact ae_of_all _ fun x ↦ by
      have hh := (hl x).norm_sub_le t 0
      rw [hγ0, sub_zero, Real.norm_eq_abs] at hh
      rw [norm_norm]
      exact (norm_le_norm_add_norm_sub x (γ x t)).trans
        (add_le_add le_rfl (by simpa only [norm_sub_rev] using hh))
  · intro t ht
    have hvc : Continuous (fun s ↦ v (s,γ x s)) := hv.comp (continuous_id.prodMk (hc x))
    have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _ ↦ hγd x s) (hvc.intervalIntegrable 0 t)
    have he : (∫ s in (0 : ℝ)..t, v (s,γ x s)) =
        ∫ s in (0 : ℝ)..t, b (γ x s) (P.map (fun z ↦ γ z s)) := by
      apply intervalIntegral.integral_congr
      intro s hs
      exact heq s (by simpa only [min_eq_left ht] using hs.1) _
    rw [he, hγ0] at hf
    change γ x t = x + _ + 0
    rw [hf]
    abel

/-- A nonlinear zero-noise integral solution follows the characteristics of its frozen law drift. -/
theorem IsMcKeanVlasovSolution.ae_eq_characteristics
    (P : Measure E) [IsProbabilityMeasure P] (b : E → Measure E → E)
    (Y : ℝ → E → E) (hY : IsMcKeanVlasovSolution b id (fun _ _ ↦ 0) Y P)
    (v : ℝ × E → E) {K : ℝ≥0} (hv : LipschitzWith K v)
    (γ : E → ℝ → E) (hγ : Continuous (uncurry γ)) (hγ0 : ∀ x, γ x 0 = x)
    (hγd : ∀ x t, HasDerivAt (γ x) (v (t, γ x t)) t)
    (heq : ∀ t ≥ 0, ∀ x, v (t,x) = b x (P.map (Y t))) :
    ∀ᵐ x ∂P, ∀ t ≥ 0, Y t x = γ x t := by
  filter_upwards [hY.2.2] with x hx
  have hgc : Continuous (γ x) := hγ.comp (continuous_const.prodMk continuous_id)
  have hcY := hv.continuous.comp (continuous_id.prodMk hx.1)
  have hcγ := hv.continuous.comp (continuous_id.prodMk hgc)
  intro t ht
  have hLip (s : ℝ) (_hs : s ∈ Icc (0 : ℝ) t) : LipschitzWith K (fun z ↦ v (s,z)) := by
    simpa only [zero_le_one, max_eq_right, mul_one, Function.comp_def, id_eq] using hv.comp ((LipschitzWith.const s).prodMk LipschitzWith.id)
  have hbound := norm_sub_le_of_spatially_lipschitz_integral_eq (fun s z ↦ v (s,z)) K ht
    (T := t) (R := 0) le_rfl hLip (fun s ↦ Y s x) (γ x) (fun _ ↦ x) (fun _ ↦ x)
    hx.1 hgc hcY.aestronglyMeasurable hcγ.aestronglyMeasurable
    (fun _ _ ↦ by simp) ?_ ?_ t ⟨ht,le_rfl⟩
  · have hz : ‖Y t x - γ x t‖ = 0 := le_antisymm (by simpa using hbound) (norm_nonneg _)
    exact sub_eq_zero.mp (norm_eq_zero.mp hz)
  · intro r hr
    rw [hx.2 r hr.1, add_zero]
    apply congrArg (x + ·)
    apply intervalIntegral.integral_congr
    intro s hs
    exact (heq s (by simpa only [min_eq_left hr.1] using hs.1) _).symm
  · intro r hr
    have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _ ↦ hγd x s) (hcγ.intervalIntegrable 0 r)
    rw [hγ0] at hf
    rw [hf]
    abel
/-- Narrowly continuous probability solutions of a nonlinear continuity equation on nonnegative time. -/
def IsNonlinearContinuitySolution (b : E → Measure E → E) (P : Measure E)
    (ρ : ℝ → Measure E) : Prop :=
  (∀ t ≥ 0, IsProbabilityMeasure (ρ t)) ∧ ρ 0 = P ∧
    (∀ g : BoundedContinuousFunction E ℝ,
      ContinuousOn (fun t ↦ ∫ x, g x ∂ρ t) (Ici 0)) ∧
    ∀ T > 0, TauCeti.IsContinuityEquation ρ (fun t x ↦ b x (ρ t)) 0 T

/-- Bounded Wasserstein-Lipschitz nonlinear drifts have a unique weak evolution, represented
by a jointly continuous globally defined family of characteristics. -/
theorem exists_unique_nonlinear_continuity_solution_of_bound
    (P : Measure E) [IsProbabilityMeasure P] (hi : Integrable (fun x ↦ ‖x‖) P)
    (b : E → Measure E → E) {L : ℝ} (hb : IsWassersteinLipschitzDrift b L) (hL : 0 ≤ L)
    (M : ℝ≥0) (hM : ∀ μ, IsProbabilityMeasure μ → ∀ x, ‖b x μ‖ ≤ M) :
    ∃ (ρ : ℝ → Measure E) (v : ℝ × E → E) (K : ℝ≥0) (γ : E → ℝ → E),
      IsNonlinearContinuitySolution b P ρ ∧
      (∀ σ, IsNonlinearContinuitySolution b P σ → ∀ t ≥ 0, σ t = ρ t) ∧
      LipschitzWith K v ∧ (∀ q, ‖v q‖₊ ≤ M) ∧ Continuous (uncurry γ) ∧
      (∀ x, γ x 0 = x) ∧ (∀ x t, HasDerivAt (γ x) (v (t,γ x t)) t) ∧
      (∀ t ≥ 0, ρ t = P.map (fun x ↦ γ x t)) ∧
      (∀ t ≥ 0, ∀ x, v (t,x) = b x (ρ t)) := by
  have hid : Integrable (id : E → E) P := (integrable_norm_iff aestronglyMeasurable_id).1 hi
  obtain ⟨Y,hY⟩ := exists_mcKeanVlasovSolution_zero_forcing P b hb id measurable_id hid
  let μ : ℝ → Measure E := fun t ↦ P.map (Y t)
  have hμp (t : ℝ) (_ht : 0 ≤ t) : IsProbabilityMeasure (μ t) := inferInstance
  have hμi (t : ℝ) (ht : 0 ≤ t) : Integrable (fun x ↦ ‖x‖) (μ t) :=
    (integrable_map_measure continuous_norm.aestronglyMeasurable (hY.1 t).aemeasurable).2 (hY.2.1 t ht)
  let v : ℝ × E → E := fun q ↦ b q.2 (μ (max 0 q.1))
  have hv := hb.lipschitzWith_nonneg_marginalDrift_of_wasserstein_bound b hL μ hμp hμi
    M M.coe_nonneg (fun s hs t ht ↦
      hY.wassersteinEDist_toReal_le_of_zero_forcing_of_bound P b hb id Y M hM s hs t ht)
  have hvM (q : ℝ × E) : ‖v q‖₊ ≤ M := by
    exact_mod_cast hM (μ (max 0 q.1)) inferInstance q.2
  obtain ⟨γ,hγ,hγ0,hγd,hγce,hγc,_⟩ :=
    exists_flow_representation_of_bounded_lipschitz v hv hvM P
  have hvμ (t : ℝ) (ht : 0 ≤ t) (x : E) : v (t,x) = b x (μ t) := by
    simp only [v,max_eq_right ht]
  have hYγ := hY.ae_eq_characteristics P b Y v hv γ hγ hγ0 hγd hvμ
  have hμγ (t : ℝ) (ht : 0 ≤ t) : μ t = P.map (fun x ↦ γ x t) :=
    Measure.map_congr (hYγ.mono fun x hx ↦ hx t ht)
  let ρ : ℝ → Measure E := fun t ↦ P.map (fun x ↦ γ x (max 0 t))
  have hρlaw (t : ℝ) (ht : 0 ≤ t) : ρ t = P.map (fun x ↦ γ x t) := by
    simp only [ρ,max_eq_right ht]
  have hvρall (t : ℝ) (x : E) : v (t,x) = b x (ρ t) := by
    change b x (μ (max 0 t)) = b x (P.map (fun z ↦ γ z (max 0 t)))
    rw [hμγ _ (le_max_left _ _)]
  have hvγ (t : ℝ) (ht : 0 ≤ t) (x : E) : v (t,x) = b x (P.map (fun z ↦ γ z t)) := by
    rw [hvμ t ht x,hμγ t ht]
  have hγMV := isMcKeanVlasovSolution_of_bounded_characteristics P hi b v hv.continuous M hvM
    γ hγ hγ0 hγd hvγ
  have hρm : Measurable ρ :=
    (hγce 1 zero_lt_one).measurable.comp (continuous_const.max continuous_id).measurable
  have hρce (T : ℝ) (hT : 0 < T) :
      TauCeti.IsContinuityEquation ρ (fun t x ↦ b x (ρ t)) 0 T := by
    have hh := isContinuityEquation_congr_measure_on_Ioo (hγce T hT) hρm
      (fun t ht ↦ hρlaw t ht.1.le)
    simpa only [hvρall] using hh
  have hρc (g : BoundedContinuousFunction E ℝ) :
      Continuous (fun t ↦ ∫ x, g x ∂ρ t) :=
    (hγc g).comp (continuous_const.max continuous_id)
  refine ⟨ρ,v,_,γ,⟨(fun _ _ ↦ inferInstance),?_,(fun g ↦ (hρc g).continuousOn),hρce⟩,
    ?_,hv,hvM,hγ,hγ0,hγd,hρlaw,(fun t _ x ↦ hvρall t x)⟩
  · simp only [ρ,max_self,hγ0,Measure.map_id']
  · intro σ hσ t ht
    have hσi0 : Integrable (fun x ↦ ‖x‖) (σ 0) := by rw [hσ.2.1]; exact hi
    let w : ℝ × E → E := fun q ↦ b q.2 (σ (max 0 q.1))
    have hw := hb.lipschitzWith_nonneg_marginalDrift b hL σ hσ.1 hσ.2.2.1 hσ.2.2.2
      hσi0 M M.coe_nonneg (fun t ht x ↦ hM (σ t) (hσ.1 t ht) x)
    have hwM (q : ℝ × E) : ‖w q‖₊ ≤ M := by
      exact_mod_cast hM (σ (max 0 q.1)) (hσ.1 _ (le_max_left _ _)) q.2
    have hwσ (s : ℝ) (hs : 0 ≤ s) (x : E) : w (s,x) = b x (σ s) := by
      simp only [w,max_eq_right hs]
    have hσce (T : ℝ) (hT : 0 < T) :
        TauCeti.IsContinuityEquation σ (fun s x ↦ w (s,x)) 0 T :=
      (hσ.2.2.2 T hT).congr hw.continuous.measurable
        (ae_of_all _ fun s hs ↦ ae_of_all _ fun x ↦ (hwσ s hs.1.le x).symm)
    obtain ⟨η,hη,hη0,hηd,_,_,hησ⟩ :=
      exists_flow_representation_of_bounded_lipschitz w hw hwM P
    have hσlaw := hησ σ hσ.1 hσ.2.2.1 hσce hσ.2.1
    have hwη (s : ℝ) (hs : 0 ≤ s) (x : E) : w (s,x) = b x (P.map (fun z ↦ η z s)) := by
      rw [hwσ s hs x,hσlaw s hs]
    have hηMV := isMcKeanVlasovSolution_of_bounded_characteristics P hi b w hw.continuous M hwM
      η hη hη0 hηd hwη
    have he := hγMV.ae_eq_of_zero_forcing_of_bound P b hb id hid
      (fun t x ↦ γ x t) (fun t x ↦ η x t) hηMV M hM
    rw [hσlaw t ht,hρlaw t ht]
    exact Measure.map_congr (he.mono fun x hx ↦ (hx t ht).symm)
end CKSD
