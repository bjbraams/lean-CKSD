module
public import CKSD.Bayes.MeanFieldCore
public import CKSD.Bayes.MeanFieldEmpirical
/-!
# Iid compact characteristic paths for mean-field training

A jointly continuous characteristic family gives a continuous map from initial states to
paths on a compact time interval. Bounded speed controls the path norm by the initial norm
plus speed times elapsed time. Consequently iid initial states with finite first moment give
iid integrable paths, whose evaluation laws are exactly the characteristic pushforwards.

Mathlib supplies compact-open continuity, iid composition and Bochner integrability. The
local compact-path constructor and projected evaluation conventions agree with the empirical
Wasserstein consistency and synchronous coupling helpers for GAPS 104.53.
-/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped ENNReal NNReal Topology BigOperators
namespace CKSD
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- Restricting a jointly continuous characteristic family to a compact time interval gives a
continuous map from initial states to compact paths. -/
theorem continuous_pathOn_parameter (γ : E → ℝ → E) (hγ : Continuous (uncurry γ)) (T : ℝ) :
    Continuous (fun x ↦ pathOn T (γ x)) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  have hc (x : E) : Continuous (γ x) := hγ.comp (continuous_const.prodMk continuous_id)
  have heq : (fun z : E × Icc (0 : ℝ) T ↦ pathOn T (γ z.1) z.2) =
      fun z ↦ γ z.1 z.2 := by
    funext z
    exact pathOn_apply_of_continuousOn T (γ z.1) (hc _).continuousOn z.2
  change Continuous (fun z : E × Icc (0 : ℝ) T ↦ pathOn T (γ z.1) z.2)
  rw [heq]
  exact hγ.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))

omit [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] in
/-- Uniform bounded speed controls the norm of a characteristic path by its initial norm. -/
theorem norm_pathOn_le_initial_add_time {T : ℝ} (hT : 0 ≤ T)
    (γ : E → ℝ → E) {M : ℝ≥0} (hγL : ∀ x, LipschitzWith M (γ x))
    (hzero : ∀ x, γ x 0 = x) (x : E) :
    ‖pathOn T (γ x)‖ ≤ ‖x‖ + (M : ℝ)*T := by
  apply (ContinuousMap.norm_le _ (by positivity : 0 ≤ ‖x‖+(M : ℝ)*T)).2
  intro t
  rw [pathOn_apply_of_continuousOn T (γ x) (hγL x).continuous.continuousOn]
  have hl := (hγL x).norm_sub_le (t : ℝ) 0
  rw [hzero, sub_zero, Real.norm_of_nonneg t.2.1] at hl
  have hn := norm_le_norm_sub_add (γ x t) x
  have hm := mul_le_mul_of_nonneg_left t.2.2 M.coe_nonneg
  linarith

/-- Integrable initial norm and bounded characteristic speed yield an integrable compact path. -/
theorem integrable_pathOn_comp (P : Measure Ω) [IsProbabilityMeasure P]
    {T : ℝ} (hT : 0 ≤ T) (γ : E → ℝ → E) (hγ : Continuous (uncurry γ))
    {M : ℝ≥0} (hγL : ∀ x, LipschitzWith M (γ x)) (hzero : ∀ x, γ x 0 = x)
    (ξ : Ω → E) (hξm : Measurable ξ) (hξi : Integrable (fun ω ↦ ‖ξ ω‖) P) :
    Integrable (fun ω ↦ pathOn T (γ (ξ ω))) P := by
  have hm : AEStronglyMeasurable (fun ω ↦ pathOn T (γ (ξ ω))) P :=
    ((continuous_pathOn_parameter γ hγ T).measurable.comp hξm).aestronglyMeasurable
  apply (hξi.add (integrable_const ((M : ℝ)*T))).mono' hm
  exact ae_of_all _ fun ω ↦ norm_pathOn_le_initial_add_time hT γ hγL hzero (ξ ω)

/-- Iid initial states generate iid integrable compact characteristic paths, with the exact
prescribed time-marginal law. -/
theorem exists_iid_training_paths_on_Icc (P : Measure Ω) [IsProbabilityMeasure P]
    (ρ₀ : Measure E) (hρ : Integrable (fun x : E ↦ ‖x‖) ρ₀)
    (ξ : ℕ → Ω → E) (hξm : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ P)
    (hlaw : ∀ i, P.map (ξ i) = ρ₀) {T : ℝ} (hT : 0 ≤ T)
    (γ : E → ℝ → E) (hγ : Continuous (uncurry γ)) {M : ℝ≥0}
    (hγL : ∀ x, LipschitzWith M (γ x)) (hzero : ∀ x, γ x 0 = x) :
    ∃ Z : ℕ → Ω → C(Icc (0 : ℝ) T, E),
      (∀ i ω, Z i ω = pathOn T (γ (ξ i ω))) ∧
      (∀ i, Measurable (Z i)) ∧ (∀ i, Integrable (Z i) P) ∧ iIndepFun Z P ∧
      (∀ i, IdentDistrib (Z i) (Z 0) P P) ∧
      (∀ i t, t ∈ Icc (0 : ℝ) T →
        P.map (fun ω ↦ (Z i ω).IccExtend hT t) = ρ₀.map (fun x ↦ γ x t)) ∧
      (∀ i ω t, t ∈ Icc (0 : ℝ) T → (Z i ω).IccExtend hT t = γ (ξ i ω) t) := by
  let F : E → C(Icc (0 : ℝ) T, E) := fun x ↦ pathOn T (γ x)
  have hFm : Measurable F := (continuous_pathOn_parameter γ hγ T).measurable
  let Z : ℕ → Ω → C(Icc (0 : ℝ) T, E) := fun i ω ↦ F (ξ i ω)
  have hZm (i : ℕ) : Measurable (Z i) := hFm.comp (hξm i)
  have hZi (i : ℕ) : Integrable (Z i) P := by
    have hi : Integrable (fun ω ↦ ‖ξ i ω‖) P := by
      apply (integrable_map_measure continuous_norm.aestronglyMeasurable (hξm i).aemeasurable).mp
      rwa [hlaw i]
    exact integrable_pathOn_comp P hT γ hγ hγL hzero (ξ i) (hξm i) hi
  have hid (i : ℕ) : IdentDistrib (ξ i) (ξ 0) P P :=
    ⟨(hξm i).aemeasurable, (hξm 0).aemeasurable, (hlaw i).trans (hlaw 0).symm⟩
  have heval (i : ℕ) (ω : Ω) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      (Z i ω).IccExtend hT t = γ (ξ i ω) t := by
    exact pathOn_IccExtend_of_continuousOn hT (γ (ξ i ω))
      (hγL _).continuous.continuousOn t ht
  refine ⟨Z, fun _ _ ↦ rfl, hZm, hZi, ?_, fun i ↦ (hid i).comp hFm, ?_, heval⟩
  · exact hind.comp (fun _ ↦ F) (fun _ ↦ hFm)
  · intro i t ht
    have hm : Measurable (fun x ↦ γ x t) :=
      (hγ.comp (continuous_id.prodMk continuous_const)).measurable
    simp_rw [heval i _ t ht]
    change P.map ((fun x ↦ γ x t) ∘ ξ i) = _
    rw [← Measure.map_map hm (hξm i), hlaw i]
section IntegralEquation
variable [NormedSpace ℝ E] [CompleteSpace E]
omit [BorelSpace E] [SecondCountableTopology E] in
/-- Characteristic compact paths satisfy the reference mean-field integral equation with their
own common marginal law, including the endpoints of the time interval. -/
theorem training_path_integral_eq
    (P : Measure Ω) (ρ₀ : Measure E) (ξ : ℕ → Ω → E)
    {T : ℝ} (hT : 0 ≤ T) (γ : E → ℝ → E)
    (v : ℝ × E → E) (hv : Continuous v)
    (hd : ∀ x t, HasDerivAt (γ x) (v (t, γ x t)) t)
    (hzero : ∀ x, γ x 0 = x) (b : E → Measure E → E)
    (hvEq : ∀ t ≥ 0, ∀ x, v (t,x) = b x (ρ₀.map (fun y ↦ γ y t)))
    (Z : ℕ → Ω → C(Icc (0 : ℝ) T, E))
    (hZeval : ∀ i ω t, t ∈ Icc (0 : ℝ) T → (Z i ω).IccExtend hT t = γ (ξ i ω) t)
    (hZmap : ∀ t, t ∈ Icc (0 : ℝ) T →
      P.map (fun ω ↦ (Z 0 ω).IccExtend hT t) = ρ₀.map (fun x ↦ γ x t))
    (i : ℕ) (ω : Ω) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
    (Z i ω).IccExtend hT t = ξ i ω + ∫ s in (0 : ℝ)..t,
      b ((Z i ω).IccExtend hT s) (P.map (fun z ↦ (Z 0 z).IccExtend hT s)) := by
  have hc : Continuous (γ (ξ i ω)) := continuous_iff_continuousAt.2
    (fun s ↦ (hd (ξ i ω) s).continuousAt)
  have hvc : Continuous (fun s ↦ v (s, γ (ξ i ω) s)) :=
    hv.comp (continuous_id.prodMk hc)
  have hInt : (∫ s in (0 : ℝ)..t, v (s, γ (ξ i ω) s)) = γ (ξ i ω) t-γ (ξ i ω) 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _ ↦ hd (ξ i ω) s) (hvc.intervalIntegrable 0 t)
  have heq : (∫ s in (0 : ℝ)..t,
      b ((Z i ω).IccExtend hT s) (P.map (fun z ↦ (Z 0 z).IccExtend hT s))) =
      ∫ s in (0 : ℝ)..t, v (s, γ (ξ i ω) s) := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht.1] at hs
    have hsT : s ∈ Icc (0 : ℝ) T := ⟨hs.1, hs.2.trans ht.2⟩
    change b ((Z i ω).IccExtend hT s) (P.map (fun z ↦ (Z 0 z).IccExtend hT s)) =
      v (s, γ (ξ i ω) s)
    rw [hZeval i ω s hsT, hZmap s hsT, hvEq s hs.1]
  rw [heq, hInt, hzero, hZeval i ω t ht]
  abel
end IntegralEquation
end CKSD
