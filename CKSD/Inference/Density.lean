module

public import CKSD.Inference.Basic


/-!
# Integrals against laws with a real density

For a law `P = f · μ` with a real density `f` in the sense of `CKSD.HasDensity`, integrals and
integrability under `P` are those of `f · g` under `μ`. These are adapters to Mathlib's
`withDensity` integration lemmas.

## Main results

* `CKSD.HasDensity.integral_eq`, `CKSD.HasDensity.integrable_iff`: `∫ g dP = ∫ f g dμ`, and `g`
  is `P`-integrable iff `f g` is `μ`-integrable.
* `CKSD.HasDensity.integrable`, `CKSD.HasDensity.integral_eq_one`: the density of a finite
  (probability) law is integrable (with integral one).
* `CKSD.integral_with_density_of_real`, `CKSD.integral_map_with_density_of_real` and their
  integrability counterparts, for everywhere nonnegative densities.
-/
@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace CKSD

variable {X : Type*} [MeasurableSpace X]

/-- Pushing forward a measure with a density that factors through `φ`. -/
theorem map_with_density_comp {Y : Type*} [MeasurableSpace Y] (ν : Measure X) {φ : X → Y}
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

/-- For a law with a density, integrability of `g` is integrability of `f · g` for the
reference measure. -/
theorem HasDensity.integrable_iff {P μ : Measure X} {f : X → ℝ} (h : HasDensity P μ f)
    (g : X → ℝ) : Integrable g P ↔ Integrable (fun x ↦ f x * g x) μ := by
  rw [h.2.2, integrable_withDensity_iff_integrable_smul' h.1.ennreal_ofReal
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  refine integrable_congr (h.2.1.mono fun x hx ↦ ?_)
  simp only [smul_eq_mul, ENNReal.toReal_ofReal hx]

/-- The density of a probability law has integral one. -/
theorem HasDensity.integral_eq_one {P μ : Measure X} {f : X → ℝ} (h : HasDensity P μ f)
    [IsProbabilityMeasure P] : ∫ x, f x ∂μ = 1 := by
  have := h.integral_eq (fun _ ↦ 1)
  simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at this
  exact this.symm

/-- A measurable everywhere nonnegative `h` is a density of `ν.withDensity (ofReal ∘ h)`. -/
theorem has_density_with_density_of_real (ν : Measure X) {h : X → ℝ} (hh : Measurable h)
    (hh0 : ∀ x, 0 ≤ h x) : HasDensity (ν.withDensity fun x ↦ ENNReal.ofReal (h x)) ν h :=
  ⟨hh, ae_of_all _ hh0, rfl⟩

/-- Integrals against a measure with a nonnegative real density `h`. -/
theorem integral_with_density_of_real (ν : Measure X) {h : X → ℝ} (hh : Measurable h)
    (hh0 : ∀ x, 0 ≤ h x) (F : X → ℝ) :
    ∫ x, F x ∂(ν.withDensity fun x ↦ ENNReal.ofReal (h x)) = ∫ x, h x * F x ∂ν :=
  (has_density_with_density_of_real ν hh hh0).integral_eq F

/-- Integrability against a measure with a nonnegative real density `h`. -/
theorem integrable_with_density_of_real_iff (ν : Measure X) {h : X → ℝ} (hh : Measurable h)
    (hh0 : ∀ x, 0 ≤ h x) (F : X → ℝ) :
    Integrable F (ν.withDensity fun x ↦ ENNReal.ofReal (h x)) ↔
      Integrable (fun x ↦ h x * F x) ν :=
  (has_density_with_density_of_real ν hh hh0).integrable_iff F

/-- Integrals against the image under `T` of a measure with a nonnegative real density `h`. -/
theorem integral_map_with_density_of_real {E : Type*} [MeasurableSpace E] (ν : Measure X)
    {T : X → E} (hT : Measurable T) {h : X → ℝ} (hh : Measurable h) (hh0 : ∀ x, 0 ≤ h x)
    {F : E → ℝ} (hF : Measurable F) :
    ∫ t, F t ∂(ν.withDensity fun x ↦ ENNReal.ofReal (h x)).map T = ∫ x, h x * F (T x) ∂ν := by
  rw [integral_map hT.aemeasurable hF.aestronglyMeasurable]
  exact integral_with_density_of_real ν hh hh0 _

/-- Integrability against the image under `T` of a measure with a nonnegative real density. -/
theorem integrable_map_with_density_of_real_iff {E : Type*} [MeasurableSpace E] (ν : Measure X)
    {T : X → E} (hT : Measurable T) {h : X → ℝ} (hh : Measurable h) (hh0 : ∀ x, 0 ≤ h x)
    {F : E → ℝ} (hF : Measurable F) :
    Integrable F ((ν.withDensity fun x ↦ ENNReal.ofReal (h x)).map T) ↔
      Integrable (fun x ↦ h x * F (T x)) ν := by
  rw [integrable_map_measure hF.aestronglyMeasurable hT.aemeasurable]
  exact integrable_with_density_of_real_iff ν hh hh0 _

end CKSD
