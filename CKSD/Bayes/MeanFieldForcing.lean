module
public import CKSD.Bayes.MeanFieldGlobal
public import CKSD.Bayes.MeanFieldBrownianBound
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace
/-!
# Integrable continuous-path versions of Brownian forcing

The measurable path reconstruction from rational evaluations retains an integrable uniform
bound. In particular an integrable initial vector plus Euclidean Brownian motion determines an
integrable random continuous path on every compact time interval, with no independence needed.
Mathlib supplies compact-path norms and integrability; local Brownian maximum bounds use pinned
TauCeti.
-/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped NNReal ENNReal Topology
namespace CKSD
/-- Integrably bounded continuous forcing admits an integrable measurable continuous-path version. -/
theorem exists_integrable_measurable_continuousPath_version
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) (F : ℝ → Ω → E)
    (hFm : ∀ t, AEMeasurable (F t) P) (hFc : ∀ᵐ ω ∂P, Continuous (fun t ↦ F t ω))
    {T : ℝ} (hT : 0 ≤ T) (D : Ω → ℝ) (hDi : Integrable D P)
    (hD : ∀ᵐ ω ∂P, ∀ t ∈ Icc (0 : ℝ) T, ‖F t ω‖ ≤ D ω) :
    ∃ G : Ω → C(Icc (0 : ℝ) T, E), Measurable G ∧ Integrable G P ∧
      ∀ᵐ ω ∂P, ∀ t : Icc (0 : ℝ) T, G ω t = F t ω := by
  obtain ⟨G, hGm, hG⟩ := exists_measurable_continuousPath_version P F hFm hFc hT
  refine ⟨G, hGm, hDi.mono' hGm.aestronglyMeasurable ?_, hG⟩
  filter_upwards [hG, hD] with ω heq hb
  apply (ContinuousMap.norm_le _ ((norm_nonneg (F 0 ω)).trans (hb 0 ⟨le_rfl, hT⟩))).2
  intro t
  rw [heq t]
  exact hb t t.2
/-- An integrable initial vector and Euclidean Brownian driver give a measurable integrable
forcing path on every compact nonnegative time interval. -/
theorem exists_integrable_brownian_forcing_path
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : Ω → EuclideanSpace ℝ (Fin d)) (hξ : Integrable ξ P)
    (W : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) (hW : IsBrownianEuclidean W P)
    {T : ℝ} (hT : 0 ≤ T) :
    ∃ F : Ω → C(Icc (0 : ℝ) T, EuclideanSpace ℝ (Fin d)),
      Measurable F ∧ Integrable F P ∧
        ∀ᵐ ω ∂P, ∀ t : Icc (0 : ℝ) T, F ω t = ξ ω + W (t:ℝ).toNNReal ω := by
  have hWm (t : ℝ≥0) : AEMeasurable (W t) P := by
    have hc : AEMeasurable (fun ω (j : Fin d) ↦ W t ω j) P :=
      AEMeasurable.of_eval fun j ↦ (hW.1 j).toIsPreBrownianReal.aemeasurable t
    convert (PiLp.continuous_toLp 2 _).measurable.comp_aemeasurable hc using 1
    funext ω
    ext j
    rfl
  obtain ⟨D, hDi, hD⟩ := exists_integrable_uniform_bound_add_brownianEuclidean P ξ hξ W hW.1 T
  exact exists_integrable_measurable_continuousPath_version P
    (fun t ω ↦ ξ ω + W t.toNNReal ω)
    (fun t ↦ hξ.aemeasurable.add (hWm t.toNNReal))
    (hW.ae_continuous_toNNReal.mono fun ω hc ↦ continuous_const.add hc) hT D hDi hD
end CKSD
