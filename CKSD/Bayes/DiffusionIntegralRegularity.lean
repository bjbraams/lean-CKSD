module
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
/-!
# Time-measurability guards for pathwise drift integrals

A time coefficient that is not almost-everywhere strongly measurable can be recovered from
a nonconstant affine scalar component of a vector-valued integrand. That integrand is then
not Bochner integrable, and its totalized interval integral is zero. The planar example
isolates this mechanism for a translating/rotating drift.

These are path-integral obstruction lemmas only. They do not formally construct a coefficient
nonmeasurable on every initial interval, a Gaussian Fokker–Planck solution, or an entire
stochastic counterexample. They make explicit why jointly measurable drift and integrable
pathwise drift are required in the marginal-preserving diffusion formulation, GAPS 104.76.

The proofs use Mathlib's continuous-linear-map integration, almost-everywhere measurability,
and the undefined-integral convention.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped NNReal ENNReal Topology
namespace CKSD
/-- A nonmeasurable time coefficient forces a vector-valued integral to vanish under the
Bochner convention whenever one fixed scalar component recovers that coefficient. -/
theorem intervalIntegral_eq_zero_of_nonmeasurable_component
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ℝ → ℝ) {t : ℝ} (ht : 0 ≤ t)
    (ha : ¬ AEStronglyMeasurable a (volume.restrict (Ioc (0 : ℝ) t)))
    (F : ℝ → E) (l : E →L[ℝ] ℝ) (c k : ℝ) (hk : k ≠ 0)
    (hl : ∀ s, l (F s) = c + a s * k) :
    (∫ s in (0 : ℝ)..t, F s) = 0 := by
  apply intervalIntegral.integral_undef
  intro hi
  have hi' := (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).1 hi
  have hm := (l.integrable_comp hi').aestronglyMeasurable.aemeasurable
  have ha' : AEMeasurable a (volume.restrict (Ioc (0 : ℝ) t)) := by
    have hh := (hm.sub (aemeasurable_const (b := c))).div_const k
    convert hh using 1
    funext s
    simp only [Pi.sub_apply]
    rw [hl]
    field_simp
    ring
  exact ha ha'.aestronglyMeasurable
/-- The planar translating/rotating drift has a scalar component that recovers its time
coefficient whenever the second coordinate of the frozen state is nonzero. -/
theorem intervalIntegral_translating_rotation_eq_zero
    (a : ℝ → ℝ) {t : ℝ} (ht : 0 ≤ t)
    (ha : ¬ AEStronglyMeasurable a (volume.restrict (Ioc (0 : ℝ) t)))
    (x : EuclideanSpace ℝ (Fin 2)) (hx : x 1 ≠ 0) :
    (∫ s in (0 : ℝ)..t, (WithLp.toLp 2 ![1 - a s * x 1, a s * (x 0 - s)] :
      EuclideanSpace ℝ (Fin 2))) = 0 := by
  apply intervalIntegral_eq_zero_of_nonmeasurable_component a ht ha _
    (PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) (0 : Fin 2)) 1 (-x 1) (neg_ne_zero.mpr hx)
  intro s
  change 1 - a s * x 1 = 1 + a s * -x 1
  ring
end CKSD
