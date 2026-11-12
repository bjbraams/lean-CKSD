module
public import CKSD.Bayes.Diffusion
public import TauCeti.Probability.Distributions.Uniform.Basic
public import CKSD.Nonparametric.Basic
/-!
# The lazy MALA law and rejection-event bounds

The half-lazy Metropolis-adjusted Langevin update is an explicit measurable accept-reject map.
Measurable potentials and gradients give probability-preserving updates. A uniform acceptance
bound on a proposal-noise event supplies a lower bound for the mass retained inside an event.

Mathlib supplies measurable maps and product-measure probabilities; pinned TauCeti supplies
uniform laws and their tail probabilities. These definitions and estimates support GAPS 104.47.
-/

public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology
namespace CKSD
/-- One step of the `1/2`-lazy Metropolis-adjusted Langevin algorithm acting on laws: the image
of `μ ⊗ N(0, I) ⊗ U(0,1) ⊗ U(0,1)` under the lazy accept–reject map. -/
@[expose] def malaStepLaw {d : ℕ} (V : EuclideanSpace ℝ (Fin d) → ℝ)
    (gradV : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (h : ℝ)
    (μ : Measure (EuclideanSpace ℝ (Fin d))) : Measure (EuclideanSpace ℝ (Fin d)) :=
  (((μ.prod (stdGaussian (EuclideanSpace ℝ (Fin d)))).prod
      (TauCeti.Probability.uniformMeasure 0 1)).prod (TauCeti.Probability.uniformMeasure 0 1)).map
    fun w ↦
      let x := w.1.1.1
      let y := x - h • gradV x + Real.sqrt (2 * h) • w.1.1.2
      if w.2 ≤ 1 / 2 then x else if w.1.2 ≤ malaAcceptance V gradV h x y then y else x

/-- The explicit sampling representation of a lazy MALA step. -/
theorem malaStepLaw_def {d : ℕ} (V : EuclideanSpace ℝ (Fin d) → ℝ)
    (gradV : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (h : ℝ)
    (μ : Measure (EuclideanSpace ℝ (Fin d))) :
    malaStepLaw V gradV h μ =
  (((μ.prod (stdGaussian (EuclideanSpace ℝ (Fin d)))).prod
      (TauCeti.Probability.uniformMeasure 0 1)).prod (TauCeti.Probability.uniformMeasure 0 1)).map
    fun w ↦
      let x := w.1.1.1
      let y := x - h • gradV x + Real.sqrt (2 * h) • w.1.1.2
      if w.2 ≤ 1 / 2 then x else if w.1.2 ≤ malaAcceptance V gradV h x y then y else x := rfl

/-- The lazy MALA accept-reject update is measurable for measurable potential and gradient. -/
theorem measurable_malaStepMap {d : ℕ}
    (V : EuclideanSpace ℝ (Fin d) → ℝ)
    (G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (h : ℝ) (hV : Measurable V) (hG : Measurable G) :
    Measurable (fun w : ((EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) × ℝ) × ℝ ↦
      let x := w.1.1.1
      let y := x - h • G x + Real.sqrt (2 * h) • w.1.1.2
      if w.2 ≤ 1 / 2 then x else if w.1.2 ≤ malaAcceptance V G h x y then y else x) := by
  let X := fun w : ((EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) × ℝ) × ℝ ↦ w.1.1.1
  let Y := fun w : ((EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) × ℝ) × ℝ ↦
    X w - h • G (X w) + Real.sqrt (2 * h) • w.1.1.2
  have hX : Measurable X := by fun_prop
  have hY : Measurable Y := by dsimp [Y]; fun_prop
  have hAcc : Measurable (fun w ↦ malaAcceptance V G h (X w) (Y w)) := by
    unfold malaAcceptance
    fun_prop
  -- Name the sampled state and proposal before applying the measurable conditional rule.
  change Measurable (fun w ↦ if w.2 ≤ 1 / 2 then X w else
    if w.1.2 ≤ malaAcceptance V G h (X w) (Y w) then Y w else X w)
  exact Measurable.ite (measurableSet_le measurable_snd measurable_const) hX
    (Measurable.ite (measurableSet_le (measurable_snd.comp measurable_fst) hAcc) hY hX)

/-- Lazy MALA maps probability laws to probability laws. -/
theorem isProbabilityMeasure_malaStepLaw {d : ℕ}
    (V : EuclideanSpace ℝ (Fin d) → ℝ)
    (G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (h : ℝ) (hV : Measurable V) (hG : Measurable G)
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (malaStepLaw V G h μ) := by
  have := TauCeti.Probability.isProbabilityMeasure_uniformMeasure zero_lt_one
  constructor
  rw [malaStepLaw_def, Measure.map_apply (measurable_malaStepMap V G h hV hG) MeasurableSet.univ,
    Set.preimage_univ]
  simp

/-- If proposals from an event have small acceptance on a noise event, the accept-reject
update retains at least the corresponding rejected mass inside the original event. -/
theorem malaStepLaw_apply_ge_of_acceptance_lt {d : ℕ}
    (V : EuclideanSpace ℝ (Fin d) → ℝ)
    (G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (h : ℝ) (hV : Measurable V) (hG : Measurable G)
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (A B : Set (EuclideanSpace ℝ (Fin d))) (hA : MeasurableSet A)
    (r : ℝ) (hr : 0 ≤ r)
    (hacc : ∀ x ∈ A, ∀ z ∈ B,
      malaAcceptance V G h x (x - h • G x + Real.sqrt (2 * h) • z) < r) :
    μ A * stdGaussian _ B * ENNReal.ofReal (1 - r) ≤ malaStepLaw V G h μ A := by
  rw [malaStepLaw_def, Measure.map_apply (measurable_malaStepMap V G h hV hG) hA]
  have hsub : ((A ×ˢ B) ×ˢ Ici r) ×ˢ (univ : Set ℝ) ⊆
      (fun w : ((EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) × ℝ) × ℝ ↦
        let x := w.1.1.1
        let y := x - h • G x + Real.sqrt (2 * h) • w.1.1.2
        if w.2 ≤ 1 / 2 then x else if w.1.2 ≤ malaAcceptance V G h x y then y else x) ⁻¹' A := by
    rintro ⟨⟨⟨x, z⟩, u⟩, v⟩ ⟨⟨⟨hx, hz⟩, hu⟩, _⟩
    -- Reduce the sampled tuple, keeping the acceptance expression symbolic.
    change (if v ≤ 1 / 2 then x else if u ≤ _ then _ else x) ∈ A
    split_ifs with hv hu'
    · exact hx
    · exact False.elim ((hacc x hx z hz).not_ge (hu.trans hu'))
    · exact hx
  have := TauCeti.Probability.isProbabilityMeasure_uniformMeasure zero_lt_one
  have hm : (((μ.prod (stdGaussian (EuclideanSpace ℝ (Fin d)))).prod
      (TauCeti.Probability.uniformMeasure 0 1)).prod (TauCeti.Probability.uniformMeasure 0 1))
      (((A ×ˢ B) ×ˢ Ici r) ×ˢ (univ : Set ℝ)) ≤ _ := measure_mono hsub
  simpa only [Measure.prod_prod, measure_univ, mul_one,
    TauCeti.Probability.uniformMeasure_Ici zero_lt_one hr, sub_zero, div_one] using hm
end CKSD
