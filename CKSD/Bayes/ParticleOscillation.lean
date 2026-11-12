module
public import CKSD.Bayes.ParticleFilter
public import Mathlib.MeasureTheory.Measure.Sub
/-!
# Oscillation contraction of positively weighted probability means

Mutual minorization by `ε` implies contraction by `1-ε²` after any common bounded positive
weighting. The proof separates the nonnegative measure remainder and integrates a centered
function bounded by its oscillation. This is the one-step mechanism underlying the normalized
Feynman–Kac contraction in Del Moral, *Feynman–Kac Formulae*, Proposition 4.3.3 and
Corollary 4.3.3, printed pages 140–142 (PDF pages 154–156 of the local 2004 copy).

Mathlib supplies measure subtraction, Bochner integration against sums and scalings, and
integral norm bounds. No normalized-kernel or Dobrushin theorem is assumed.
-/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace CKSD
/-- Integrating over the nonnegative remainder of a dominated scalar measure. -/
theorem integral_sub_smul_measure_of_le {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {c : ℝ} (hc : 0 ≤ c) (hle : ENNReal.ofReal c • ν ≤ μ)
    {f : X → ℝ} (hμ : Integrable f μ) (hν : Integrable f ν) :
    (∫ x, f x ∂(μ - ENNReal.ofReal c • ν)) = (∫ x, f x ∂μ) - c * ∫ x, f x ∂ν := by
  let : IsFiniteMeasure (ENNReal.ofReal c • ν) := isFiniteMeasure_of_le μ hle
  have hsub : Integrable f (μ - ENNReal.ofReal c • ν) := hμ.mono_measure Measure.sub_le
  have hscalar : Integrable f (ENNReal.ofReal c • ν) := hν.smul_measure ENNReal.ofReal_ne_top
  have heq := integral_add_measure hsub hscalar
  rw [Measure.sub_add_cancel_of_le hle, integral_smul_measure,
    ENNReal.toReal_ofReal hc, smul_eq_mul] at heq
  linarith

/-- A weighted probability mean differs from any function value by at most its oscillation. -/
theorem abs_sub_weighted_mean_le_of_oscillation {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] {g f : X → ℝ}
    (hg : Measurable g) (hf : Measurable f) {a b C D : ℝ}
    (ha : 0 < a) (hgb : ∀ x, g x ∈ Icc a b) (hfb : ∀ x, |f x| ≤ C)
    (hosc : ∀ x y, |f x - f y| ≤ D) (x : X) :
    |f x - (∫ y, g y * f y ∂μ) / (∫ y, g y ∂μ)| ≤ D := by
  have hg0 : ∀ y, 0 ≤ g y := fun y ↦ (ha.trans_le (hgb y).1).le
  have hgi : Integrable g μ := Integrable.of_bound hg.aestronglyMeasurable b
    (ae_of_all _ fun y ↦ by simpa only [Real.norm_eq_abs, abs_of_nonneg (hg0 y)] using (hgb y).2)
  have hgfi : Integrable (fun y ↦ g y * f y) μ := Integrable.of_bound
    (hg.mul hf).aestronglyMeasurable (b*C) (ae_of_all _ fun y ↦ by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hg0 y)]
      exact mul_le_mul (hgb y).2 (hfb y) (abs_nonneg _) ((hg0 y).trans (hgb y).2))
  have hI : 0 < ∫ y, g y ∂μ := ha.trans_le (by
    simpa only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] using
      integral_mono_ae (integrable_const a) hgi (ae_of_all _ fun y ↦ (hgb y).1))
  have hId : (∫ y, g y * (f x - f y) ∂μ) = f x * (∫ y, g y ∂μ) - ∫ y, g y * f y ∂μ := by
    simp_rw [mul_sub]
    rw [integral_sub (hgi.mul_const _) hgfi, integral_mul_const, mul_comm]
  have hEq : f x - (∫ y, g y*f y ∂μ)/(∫ y, g y ∂μ) =
      (∫ y, g y*(f x-f y) ∂μ)/(∫ y, g y ∂μ) := by
    rw [hId]
    field_simp
  rw [hEq, abs_div, abs_of_pos hI, div_le_iff₀ hI]
  calc
    |(∫ y, g y*(f x-f y) ∂μ)| ≤ (∫ y, D*g y ∂μ) := by
      rw [← Real.norm_eq_abs]
      apply norm_integral_le_of_norm_le (hgi.const_mul D)
      exact ae_of_all _ fun y ↦ by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hg0 y)]
        simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hosc x y) (hg0 y)
    _ = D * ∫ y, g y ∂μ := integral_const_mul _ _
/-- Mutual minorization contracts oscillation after any common positive weighting. -/
theorem abs_weighted_mean_sub_weighted_mean_le_of_minorization
    {X : Type*} [MeasurableSpace X] [Nonempty X]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {ε : ℝ} (hε : ε ∈ Ioc 0 1)
    (hμν : ENNReal.ofReal ε • ν ≤ μ) (hνμ : ENNReal.ofReal ε • μ ≤ ν)
    {g f : X → ℝ} (hg : Measurable g) (hf : Measurable f) {a b C D : ℝ}
    (ha : 0 < a) (hgb : ∀ x, g x ∈ Icc a b) (hfb : ∀ x, |f x| ≤ C)
    (hosc : ∀ x y, |f x - f y| ≤ D) :
    |(∫ x, g x * f x ∂μ) / (∫ x, g x ∂μ) -
      (∫ x, g x * f x ∂ν) / (∫ x, g x ∂ν)| ≤ (1 - ε^2) * D := by
  have hg0 : ∀ x, 0 ≤ g x := fun x ↦ (ha.trans_le (hgb x).1).le
  have hb0 : 0 ≤ b := (hg0 (Classical.arbitrary X)).trans (hgb _).2
  have hD0 : 0 ≤ D := by simpa using hosc (Classical.arbitrary X) (Classical.arbitrary X)
  have hgi (π : Measure X) [IsProbabilityMeasure π] : Integrable g π :=
    Integrable.of_bound hg.aestronglyMeasurable b (ae_of_all _ fun x ↦ by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hg0 x)] using (hgb x).2)
  have hI (π : Measure X) [IsProbabilityMeasure π] : 0 < ∫ x, g x ∂π := by
    apply ha.trans_le
    simpa only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] using
      integral_mono_ae (integrable_const a) (hgi π) (ae_of_all _ fun x ↦ (hgb x).1)
  have hgfi (π : Measure X) [IsProbabilityMeasure π] : Integrable (fun x ↦ g x * f x) π :=
    Integrable.of_bound (hg.mul hf).aestronglyMeasurable (b*C) (ae_of_all _ fun x ↦ by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hg0 x)]
      exact mul_le_mul (hgb x).2 (hfb x) (abs_nonneg _) hb0)
  let c := (∫ x, g x * f x ∂ν) / (∫ x, g x ∂ν)
  let rem :=  μ - ENNReal.ofReal ε • ν
  have hcent (x : X) : |f x - c| ≤ D :=
    abs_sub_weighted_mean_le_of_oscillation ν hg hf ha hgb hfb hosc x
  have hcenti (π : Measure X) [IsProbabilityMeasure π] :
      Integrable (fun x ↦ g x * (f x - c)) π := by
    have heq : (fun x ↦ g x * (f x-c)) = fun x ↦ g x*f x - g x*c := by
      funext x
      ring
    rw [heq]
    exact (hgfi π).sub ((hgi π).mul_const c)
  have hcentInt (π : Measure X) [IsProbabilityMeasure π] :
      (∫ x, g x * (f x-c) ∂π) = (∫ x, g x*f x ∂π) - c * ∫ x, g x ∂π := by
    simp_rw [mul_sub]
    rw [integral_sub (hgfi π) ((hgi π).mul_const c), integral_mul_const, mul_comm]
  have hzero : (∫ x, g x * (f x-c) ∂ν) = 0 := by
    rw [hcentInt]
    dsimp [c]
    field_simp [(hI ν).ne']
    ring
  have hnum : (∫ x, g x * (f x-c) ∂rem) =
      (∫ x, g x*f x ∂μ) - c * ∫ x, g x ∂μ := by
    rw [integral_sub_smul_measure_of_le μ ν hε.1.le hμν (hcenti μ) (hcenti ν),
      hzero, mul_zero, sub_zero, hcentInt]
  have hcomp : ε * (∫ x, g x ∂μ) ≤ (∫ x, g x ∂ν) := by
    have h := integral_mono_measure hνμ (ae_of_all _ hg0) (hgi ν)
    rw [integral_smul_measure, ENNReal.toReal_ofReal hε.1.le, smul_eq_mul] at h
    exact h
  have hloss : (∫ x, g x ∂rem) ≤ (1-ε^2) * ∫ x, g x ∂μ := by
    rw [integral_sub_smul_measure_of_le μ ν hε.1.le hμν (hgi μ) (hgi ν)]
    nlinarith [mul_le_mul_of_nonneg_left hcomp hε.1.le]
  have hnorm : |∫ x, g x * (f x-c) ∂rem| ≤ D * ∫ x, g x ∂rem := by
    rw [← integral_const_mul]
    rw [← Real.norm_eq_abs]
    apply norm_integral_le_of_norm_le (((hgi μ).mono_measure Measure.sub_le).const_mul D)
    exact ae_of_all _ fun x ↦ by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hg0 x)]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hcent x) (hg0 x)
  change |(∫ x, g x*f x ∂μ)/(∫ x, g x ∂μ) - c| ≤ _
  have hEq : (∫ x, g x*f x ∂μ)/(∫ x, g x ∂μ) - c =
      (∫ x, g x*(f x-c) ∂rem)/(∫ x, g x ∂μ) := by
    rw [hnum]
    field_simp [(hI μ).ne']
  rw [hEq, abs_div, abs_of_pos (hI μ), div_le_iff₀ (hI μ)]
  exact hnorm.trans (by nlinarith [mul_le_mul_of_nonneg_left hloss hD0])

end CKSD
