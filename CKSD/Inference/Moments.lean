module

public import CKSD.Inference.Basic
public import Mathlib.Probability.CDF
public import Mathlib.Probability.Moments.Variance

/-!
# Statistical moment adapters

The section interfaces take a measure first. These equalities connect their distribution and
second-moment conventions to the existing Mathlib API. No statistical result is proved anew here.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace CKSD

/-- The CDF adapter agrees with Mathlib for probability measures. -/
theorem cdf_eq_mathlib (P : Measure ℝ) [IsProbabilityMeasure P] (x : ℝ) :
    cdf P x = ProbabilityTheory.cdf P x :=
  (ProbabilityTheory.cdf_eq_real P x).symm

/-- The centred-integral variance agrees with Mathlib for almost everywhere measurable variables. -/
theorem variance_eq_mathlib {X : Type*} [MeasurableSpace X]
    (P : Measure X) (f : X → ℝ) (hf : AEMeasurable f P) :
    variance P f = ProbabilityTheory.variance f P :=
  (ProbabilityTheory.variance_eq_integral hf).symm

end CKSD
