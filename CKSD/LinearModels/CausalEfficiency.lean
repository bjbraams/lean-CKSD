module

public import CKSD.LinearModels.Causal

/-!
# Treatment-effect influence functions in finite strata

Conditional means, variances, and propensities are defined by integrals on observed strata.
The results cover the variance identity and bounded-score path derivatives of the observed-data
functional. They do not assert the full convolution bound or cross-fitting central limit theorem.
Source: GAPS 105.56.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators

namespace CKSD

/-- Joint covariate-stratum and treatment event. -/
def treatmentStratum {Ω : Type*} {k : ℕ} (X : Ω → Fin k) (A : Ω → Bool)
    (x : Fin k) (a : Bool) : Set Ω := {ω | X ω = x ∧ A ω = a}

/-- Observed conditional outcome mean in a treatment stratum. -/
def stratumOutcomeMean {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (P : Measure Ω) (X : Ω → Fin k) (A : Ω → Bool) (Y : Ω → ℝ)
    (x : Fin k) (a : Bool) : ℝ :=
  (∫ ω in treatmentStratum X A x a, Y ω ∂P) / P.real (treatmentStratum X A x a)

/-- Observed conditional outcome variance in a treatment stratum. -/
def stratumOutcomeVariance {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (P : Measure Ω) (X : Ω → Fin k) (A : Ω → Bool) (Y : Ω → ℝ)
    (x : Fin k) (a : Bool) : ℝ :=
  (∫ ω in treatmentStratum X A x a, (Y ω - stratumOutcomeMean P X A Y x a) ^ 2 ∂P) /
    P.real (treatmentStratum X A x a)

/-- Propensity in a finite observed covariate stratum. -/
def stratumPropensity {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (P : Measure Ω) (X : Ω → Fin k) (A : Ω → Bool) (x : Fin k) : ℝ :=
  P.real (treatmentStratum X A x true) / P.real {ω | X ω = x}

/-- Identified treatment-effect functional of an observed law with finite covariate strata. -/
def finiteStrataTreatmentEffect {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (P : Measure Ω) (X : Ω → Fin k) (A : Ω → Bool) (Y : Ω → ℝ) : ℝ :=
  ∫ ω, stratumOutcomeMean P X A Y (X ω) true - stratumOutcomeMean P X A Y (X ω) false ∂P

/-- Treatment-effect influence function at the true finite-stratum nuisances. -/
def finiteStrataTreatmentInfluence {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (P : Measure Ω) (X : Ω → Fin k) (A : Ω → Bool) (Y : Ω → ℝ) (ω : Ω) : ℝ :=
  treatmentEffectInfluence (fun x ↦ stratumOutcomeMean P X A Y x false)
    (fun x ↦ stratumOutcomeMean P X A Y x true) (stratumPropensity P X A)
    (finiteStrataTreatmentEffect P X A Y) (X ω) (A ω) (Y ω)

/-- GAPS 105.56: mean zero and the variance formula for the treatment-effect influence function
in finite strata. Positive joint stratum masses express overlap explicitly. -/
theorem finiteStrataTreatmentInfluence_mean_and_variance
    {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → Fin k) (A : Ω → Bool)
    (hX : Measurable X) (hA : Measurable A) (Y : Ω → ℝ) (hY : MemLp Y 2 P)
    (hpos : ∀ x a, 0 < P.real (treatmentStratum X A x a)) :
    (∫ ω, finiteStrataTreatmentInfluence P X A Y ω ∂P) = 0 ∧
      variance P (finiteStrataTreatmentInfluence P X A Y) =
        variance P (fun ω ↦ stratumOutcomeMean P X A Y (X ω) true -
          stratumOutcomeMean P X A Y (X ω) false) +
          ∫ ω, stratumOutcomeVariance P X A Y (X ω) true / stratumPropensity P X A (X ω) +
            stratumOutcomeVariance P X A Y (X ω) false /
              (1 - stratumPropensity P X A (X ω)) ∂P := by
  sorry

/-- GAPS 105.56: the treatment-effect influence function represents derivatives along bounded
mean-zero score tilts of the observed law. The semiparametric convolution bound is not included. -/
theorem hasDerivAt_finiteStrataTreatmentEffect_score_tilt
    {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → Fin k) (A : Ω → Bool)
    (hX : Measurable X) (hA : Measurable A) (Y : Ω → ℝ) (hY : MemLp Y 2 P)
    (hpos : ∀ x a, 0 < P.real (treatmentStratum X A x a))
    (s : Ω → ℝ) (hs : Measurable s) (hbound : ∃ C, ∀ ω, |s ω| ≤ C)
    (hmean : (∫ ω, s ω ∂P) = 0) :
    HasDerivAt (fun t : ℝ ↦ finiteStrataTreatmentEffect
      (P.withDensity (fun ω ↦ ENNReal.ofReal (1 + t * s ω))) X A Y)
      (∫ ω, finiteStrataTreatmentInfluence P X A Y ω * s ω ∂P) 0 := by
  sorry

end CKSD
