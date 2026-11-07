module

public import CKSD.Inference.Basic
public import TauCeti.Probability.Moments.Determinacy

/-!
# Inference: Laplace determinacy and densities

* `Measure.ext_of_integral_exp_inner_eq`: two finite measures on a finite-dimensional real inner
  product space whose Laplace transforms are finite and agree on a ball around the origin are
  equal. Each one-dimensional projection is determined by its moment-generating function near
  the origin (TauCeti's `TauCeti.Measure.ext_of_mgf`), and the characteristic function of the
  measure is that of its projections (Mathlib's `Measure.ext_of_charFun`).
* Integral and integrability transfer for measures `ν.withDensity (ofReal ∘ h)` and their images.

These are the analytic steps in completeness of full-rank exponential families (GAPS 101.5).

Sources: `GAPS.md` and `SYNOPSIS101.md`.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace CKSD


/-- Multivariate Laplace determinacy: two finite measures on a finite-dimensional real inner
product space whose Laplace transforms `u ↦ ∫ exp ⟪u, t⟫` are finite and agree on a ball around
the origin are equal. -/
theorem Measure.ext_of_integral_exp_inner_eq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ₁ μ₂ : Measure (E)) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] {r : ℝ} (hr : 0 < r)
    (hint : ∀ u : E, ‖u‖ < r → Integrable (fun t ↦ Real.exp (inner ℝ u t)) μ₁)
    (heq : ∀ u : E, ‖u‖ < r →
      ∫ t, Real.exp (inner ℝ u t) ∂μ₁ = ∫ t, Real.exp (inner ℝ u t) ∂μ₂) :
    μ₁ = μ₂ := by
  refine Measure.ext_of_charFun (funext fun w ↦ ?_)
  have hw : Measurable fun t : E ↦ inner ℝ t w := by fun_prop
  rw [← Measure.map_id (μ := μ₁), ← Measure.map_id (μ := μ₂),
    charFun_map_eq_charFun_map_inner_one aemeasurable_id,
    charFun_map_eq_charFun_map_inner_one aemeasurable_id]
  simp only [id]
  congr 1
  set c : ℝ := r / (‖w‖ + 1)
  have hc : 0 < c := div_pos hr (by positivity)
  have hsmall : ∀ s : ℝ, s ∈ Metric.ball (0 : ℝ) c → ‖s • w‖ < r := fun s hs ↦ by
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hs
    rw [norm_smul, Real.norm_eq_abs]
    calc |s| * ‖w‖ ≤ |s| * (‖w‖ + 1) := by gcongr; linarith
      _ < c * (‖w‖ + 1) := by gcongr
      _ = r := div_mul_cancel₀ r (by positivity)
  have hexp : ∀ s : ℝ, ∀ t : E, Real.exp (s * inner ℝ t w) = Real.exp (inner ℝ (s • w) t) :=
    fun s t ↦ by rw [real_inner_smul_left, real_inner_comm]
  have hball : Metric.ball (0 : ℝ) c ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds 0 hc
  refine TauCeti.Measure.ext_of_mgf ?_ ?_
  · refine mem_interior_iff_mem_nhds.2 (Filter.mem_of_superset hball fun s hs ↦ ?_)
    change Integrable (fun y ↦ Real.exp (s * id y)) (μ₁.map fun t ↦ inner ℝ t w)
    rw [integrable_map_measure (by fun_prop) hw.aemeasurable]
    simpa [Function.comp_def, hexp] using hint _ (hsmall s hs)
  · filter_upwards [hball] with s hs
    simp only [mgf, id]
    rw [integral_map hw.aemeasurable (by fun_prop), integral_map hw.aemeasurable (by fun_prop)]
    simpa [hexp] using heq _ (hsmall s hs)

variable {X : Type*} [MeasurableSpace X]

/-- Integrals against a measure with a nonnegative real density `h`. -/
theorem integral_withDensity_ofReal (ν : Measure X) {h : X → ℝ} (hh : Measurable h)
    (hh0 : ∀ x, 0 ≤ h x) (F : X → ℝ) :
    ∫ x, F x ∂(ν.withDensity fun x ↦ ENNReal.ofReal (h x)) = ∫ x, h x * F x ∂ν := by
  refine (integral_withDensity_eq_integral_smul (f := fun x ↦ (h x).toNNReal)
    (measurable_real_toNNReal.comp hh) F).trans ?_
  congr 1
  funext x
  rw [NNReal.smul_def, Real.coe_toNNReal _ (hh0 x), smul_eq_mul]

/-- Integrability against a measure with a nonnegative real density `h`. -/
theorem integrable_withDensity_ofReal_iff (ν : Measure X) {h : X → ℝ} (hh : Measurable h)
    (hh0 : ∀ x, 0 ≤ h x) (F : X → ℝ) :
    Integrable F (ν.withDensity fun x ↦ ENNReal.ofReal (h x)) ↔
      Integrable (fun x ↦ h x * F x) ν := by
  refine (integrable_withDensity_iff_integrable_smul (f := fun x ↦ (h x).toNNReal)
    (measurable_real_toNNReal.comp hh) (g := F)).trans ?_
  have : (fun x ↦ (h x).toNNReal • F x) = fun x ↦ h x * F x :=
    funext fun x ↦ by rw [NNReal.smul_def, Real.coe_toNNReal _ (hh0 x), smul_eq_mul]
  rw [this]

/-- Integrals against the image under `T` of a measure with a nonnegative real density `h`. -/
theorem integral_map_withDensity_ofReal {E : Type*} [MeasurableSpace E] (ν : Measure X)
    {T : X → E} (hT : Measurable T) {h : X → ℝ} (hh : Measurable h) (hh0 : ∀ x, 0 ≤ h x)
    {F : E → ℝ} (hF : Measurable F) :
    ∫ t, F t ∂(ν.withDensity fun x ↦ ENNReal.ofReal (h x)).map T = ∫ x, h x * F (T x) ∂ν := by
  rw [integral_map hT.aemeasurable hF.aestronglyMeasurable]
  exact integral_withDensity_ofReal ν hh hh0 _

/-- Integrability against the image under `T` of a measure with a nonnegative real density. -/
theorem integrable_map_withDensity_ofReal_iff {E : Type*} [MeasurableSpace E] (ν : Measure X)
    {T : X → E} (hT : Measurable T) {h : X → ℝ} (hh : Measurable h) (hh0 : ∀ x, 0 ≤ h x)
    {F : E → ℝ} (hF : Measurable F) :
    Integrable F ((ν.withDensity fun x ↦ ENNReal.ofReal (h x)).map T) ↔
      Integrable (fun x ↦ h x * F (T x)) ν := by
  rw [integrable_map_measure hF.aestronglyMeasurable hT.aemeasurable]
  exact integrable_withDensity_ofReal_iff ν hh hh0 _

end CKSD
