module

public import CKSD.Asymptotics.Basic
public import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv
/-!
# The singular part in likelihood transfer

The Lebesgue decomposition bounds the error made by integrating only against
the Radon–Nikodym density. This keeps the change-of-law argument applicable
to alternatives that need not be absolutely continuous at finite sample sizes.
-/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology
namespace CKSD
/-- The discrepancy between integration under an alternative law and its absolutely continuous
likelihood contribution is controlled by the missing likelihood mass. -/
theorem abs_integral_sub_integral_rn_deriv_mul_le
    {Ω : Type*} [MeasurableSpace Ω] (P Q : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (f : Ω → ℝ) (hf : Measurable f) (B : ℝ) (hB : ∀ x, ‖f x‖ ≤ B) :
    |(∫ x, f x ∂Q) - ∫ x, (Q.rnDeriv P x).toReal * f x ∂P| ≤
      B * (1 - ∫ x, (Q.rnDeriv P x).toReal ∂P) := by
  have hac : Integrable f (P.withDensity (Q.rnDeriv P)) :=
    Integrable.of_bound hf.aestronglyMeasurable B (ae_of_all _ hB)
  have hsing : Integrable f (Q.singularPart P) :=
    Integrable.of_bound hf.aestronglyMeasurable B (ae_of_all _ hB)
  have heq : (∫ x, f x ∂Q) =
      (∫ x, (Q.rnDeriv P x).toReal * f x ∂P) + ∫ x, f x ∂Q.singularPart P := by
    calc
      _ = ∫ x, f x ∂(P.withDensity (Q.rnDeriv P) + Q.singularPart P) := by
        rw [Measure.rnDeriv_add_singularPart]
      _ = _ := by
        rw [integral_add_measure hac hsing,
          integral_withDensity_eq_integral_toReal_smul (Measure.measurable_rnDeriv _ _)
            (Measure.rnDeriv_lt_top _ _)]
        rfl
  rw [heq, add_sub_cancel_left, ← Real.norm_eq_abs]
  have hmass : 1 - ∫ x, (Q.rnDeriv P x).toReal ∂P = (Q.singularPart P).real univ := by
    rw [Measure.integral_toReal_rnDeriv', probReal_univ]
    ring
  rw [hmass]
  exact norm_integral_le_of_norm_le_const (ae_of_all _ hB)
end CKSD
