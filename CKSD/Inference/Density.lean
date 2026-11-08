module

public import CKSD.Inference.Basic

/-!
# Inference: integrals against laws with a density

For a law `P = f μ` given by a real density in the sense of `CKSD.HasDensity`, integrals under
`P` are integrals of `f · g` under `μ`, and `f` is `μ`-integrable when `P` is finite. These are
adapters to Mathlib's `withDensity` integration lemmas, used by the Neyman–Pearson arguments.

Sources: `GAPS.md` and `SYNOPSIS101.md`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace CKSD

variable {X : Type*} [MeasurableSpace X]

/-- Pushing forward a measure with a density that factors through `φ`. -/
theorem map_withDensity_comp {Y : Type*} [MeasurableSpace Y] (ν : Measure X) {φ : X → Y}
    (hφ : Measurable φ) {k : Y → ℝ≥0∞} (hk : Measurable k) :
    (ν.withDensity (k ∘ φ)).map φ = (ν.map φ).withDensity k := by
  ext s hs
  rw [Measure.map_apply hφ hs, withDensity_apply _ (hφ hs), withDensity_apply _ hs,
    setLIntegral_map hs hk hφ]
  rfl

/-- Integrals against a law with a density are density-weighted integrals. -/
theorem HasDensity.integral_eq {P μ : Measure X} {f : X → ℝ} (h : HasDensity P μ f)
    (g : X → ℝ) : ∫ x, g x ∂P = ∫ x, f x * g x ∂μ := by
  rw [h.2.2, integral_withDensity_eq_integral_toReal_smul h.1.ennreal_ofReal
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top) g]
  refine integral_congr_ae (h.2.1.mono fun x hx ↦ ?_)
  simp only [smul_eq_mul, ENNReal.toReal_ofReal hx]

/-- The density of a finite law is integrable. -/
theorem HasDensity.integrable {P μ : Measure X} {f : X → ℝ} (h : HasDensity P μ f)
    [IsFiniteMeasure P] : Integrable f μ := by
  have huniv : P univ = ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
    rw [h.2.2, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hi := integrable_toReal_of_lintegral_ne_top h.1.ennreal_ofReal.aemeasurable
    (huniv ▸ measure_ne_top P univ)
  exact hi.congr (h.2.1.mono fun x hx ↦ ENNReal.toReal_ofReal hx)

end CKSD
