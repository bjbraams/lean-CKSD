module

public import CKSD.Nonparametric.Basic
public import TauCeti.InformationTheory.KullbackLeibler.Pinsker

/-!
# Endpoint total variation from path relative entropy

This is the data-processing and Pinsker step of GAPS 104.68. The stochastic-calculus bound on
path relative entropy is a separate statement. Pinsker's event inequality is imported from TauCeti.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal

namespace CKSD

/-- GAPS 104.68: endpoint total variation is at most the square root of half the path entropy. -/
theorem totalVariationDistance_map_le_sqrt_klDiv
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (e : Ω → X) (he : Measurable e) (hfin : klDiv P Q ≠ ∞) :
    totalVariationDistance (P.map e) (Q.map e) ≤ Real.sqrt ((klDiv P Q).toReal / 2) := by
  have : IsProbabilityMeasure (P.map e) := inferInstance
  have : IsProbabilityMeasure (Q.map e) := inferInstance
  apply csSup_le
  · exact ⟨0, ∅, MeasurableSet.empty, by simp⟩
  · rintro r ⟨A, hA, rfl⟩
    have h := (TauCeti.two_mul_sq_measureReal_sub_le_klDiv (μ := P.map e)
      (ν := Q.map e) hA).trans (InformationTheory.klDiv_map_le P Q he)
    have hr := ENNReal.toReal_mono hfin h
    rw [ENNReal.toReal_ofReal (by positivity)] at hr
    apply Real.le_sqrt_of_sq_le
    rw [sq_abs]
    linarith

end CKSD
