module

public import CKSD.Inference.Basic
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Basic

/-!
# Common-source and empirical first-Wasserstein bounds

Pairing two random variables on the same probability space bounds the first Wasserstein distance
of their laws by their mean pointwise distance. Equal-index pairing of empirical atoms gives
the corresponding bound by the uniform configuration norm. These estimates connect a
Wasserstein-Lipschitz mean-field drift to ordinary finite-dimensional Lipschitz vector fields.

The coupling and transport-cost bound are from pinned TauCeti's
`MeasureTheory.OptimalTransport.Coupling` and `Wasserstein.Basic`; pushforwards of empirical laws
use TauCeti's `TauCeti.Probability.map_empiricalFiniteMeasure`. Mathlib supplies pushforward
integration and the first-moment identities.
-/

public section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace CKSD
/-- Pushforward of an empirical law is the empirical law of the mapped atoms, from TauCeti's
`TauCeti.Probability.map_empiricalFiniteMeasure` through
`CKSD.empiricalMeasure_eq_empiricalFiniteMeasure`; for `N = 0` both sides are zero. -/
theorem map_empiricalMeasure {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (N : ℕ) (x : Fin N → A) (f : A → B) (hf : Measurable f) :
    (empiricalMeasure N x).map f = empiricalMeasure N (fun j ↦ f (x j)) := by
  rw [empiricalMeasure_eq_empiricalFiniteMeasure, empiricalMeasure_eq_empiricalFiniteMeasure,
    ← FiniteMeasure.toMeasure_map, TauCeti.Probability.map_empiricalFiniteMeasure hf]
  rfl

/-- The common-source coupling bounds first Wasserstein distance by mean pointwise distance. -/
theorem wassersteinEDist_one_map_toReal_le_integral_norm_sub {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (P : Measure Ω) {f g : Ω → E}
    (hf : AEStronglyMeasurable f P) (hg : AEStronglyMeasurable g P)
    (hfg : Integrable (fun ω ↦ f ω - g ω) P) :
    (TauCeti.wassersteinEDist 1 (P.map f) (P.map g)).toReal ≤ ∫ ω, ‖f ω - g ω‖ ∂P := by
  have hc := TauCeti.isCoupling_map_prodMk_of_aemeasurable (γ := P) hf.aemeasurable
    hg.aemeasurable rfl rfl
  have hW := TauCeti.wassersteinEDist_le hc 1
  rw [eLpNorm_map_measure continuous_edist.aestronglyMeasurable (hf.prodMk hg).aemeasurable] at hW
  have he : eLpNorm ((fun z : E × E ↦ edist z.1 z.2) ∘ fun ω ↦ (f ω, g ω)) 1 P =
      ENNReal.ofReal (∫ ω, ‖f ω - g ω‖ ∂P) := by
    simp only [Function.comp_def]
    rw [eLpNorm_one_eq_lintegral_enorm (continuous_edist.comp_aestronglyMeasurable₂ hf hg),
      ofReal_integral_norm_eq_lintegral_enorm hfg]
    apply lintegral_congr
    intro ω
    simp [edist_eq_enorm_sub]
  rw [he] at hW
  simpa only [ENNReal.toReal_ofReal (integral_nonneg fun _ ↦ norm_nonneg _)] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top hW
/-- Pairing equal-index atoms controls empirical first Wasserstein distance in the uniform
configuration norm. -/
theorem wassersteinEDist_one_empirical_toReal_le_norm_sub {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {N : ℕ} (hN : 0 < N) (x y : Fin N → E) :
    (TauCeti.wassersteinEDist 1 (empiricalMeasure N x) (empiricalMeasure N y)).toReal ≤
      ‖x - y‖ := by
  let P : Measure (Fin N) := empiricalMeasure N id
  have : IsProbabilityMeasure P := isProbabilityMeasure_empiricalMeasure hN id
  have hmap (z : Fin N → E) : P.map z = empiricalMeasure N z :=
    map_empiricalMeasure N id z (measurable_of_finite z)
  have hi : Integrable (fun j ↦ x j - y j) P :=
    Integrable.of_bound (measurable_of_finite _).aestronglyMeasurable ‖x - y‖
      (ae_of_all _ fun j ↦ norm_le_pi_norm (x - y) j)
  rw [← hmap x, ← hmap y]
  calc _ ≤ ∫ j, ‖x j - y j‖ ∂P := by
          exact wassersteinEDist_one_map_toReal_le_integral_norm_sub P
            (measurable_of_finite _).aestronglyMeasurable
            (measurable_of_finite _).aestronglyMeasurable hi
    _ ≤ ∫ _ : Fin N, ‖x - y‖ ∂P :=
      integral_mono hi.norm (integrable_const _) (fun j ↦ norm_le_pi_norm (x - y) j)
    _ = _ := by simp
end CKSD
