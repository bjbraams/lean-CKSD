module

public import CKSD.Bayes.Nonparametric

/-!
# Pólya urn predictive laws and distinct values

The urn is specified by its conditional next-observation law given the complete finite past.
For an atomless base measure, the distinct-count theorems describe the Chinese restaurant
counting process. Sources: GAPS 104.16.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- Pólya urn protocol, with predictive law conditional on the first `n` observations. -/
def IsPolyaUrnProcess {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [StandardBorelSpace X] [Nonempty X] (P : Measure Ω) [IsProbabilityMeasure P] (α : Measure X)
    (Xn : ℕ → Ω → X) : Prop :=
  (∀ n, Measurable (Xn n)) ∧ ∀ n, ∀ᵐ ω ∂P,
    condDistrib (Xn n) (fun (ω : Ω) (i : Fin n) ↦ Xn i.val ω) P
      (fun i : Fin n ↦ Xn i.val ω) = polyaPredictiveLaw α (fun i : Fin n ↦ Xn i.val ω)

/-- Number of distinct values among the first `n` observations. -/
def distinctObservationCount {Ω X : Type*} (Xn : ℕ → Ω → X) (n : ℕ) (ω : Ω) : ℕ :=
  ((Finset.range n).image fun i ↦ Xn i ω).card

/-- GAPS 104.16: expected number of distinct observations under an atomless Pólya base. -/
theorem integral_distinctObservationCount_polya {Ω X : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
    (P : Measure Ω) [IsProbabilityMeasure P] (α : Measure X) [IsFiniteMeasure α]
    [NullSingletonClass α] (hα : α ≠ 0) (Xn : ℕ → Ω → X)
    (hurn : IsPolyaUrnProcess P α Xn) (n : ℕ) :
    (∫ ω, (distinctObservationCount Xn n ω : ℝ) ∂P) =
      ∑ i ∈ Finset.range n, α.real univ / (α.real univ + i) := by
  sorry

/-- GAPS 104.16: logarithmic almost-sure growth of the number of distinct values.
The logarithm uses `n+1`, which has the same asymptotics and avoids its initial zero argument. -/
theorem ae_tendsto_distinctObservationCount_div_log_polya
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
    (P : Measure Ω) [IsProbabilityMeasure P] (α : Measure X) [IsFiniteMeasure α]
    [NullSingletonClass α] (hα : α ≠ 0) (Xn : ℕ → Ω → X)
    (hurn : IsPolyaUrnProcess P α Xn) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ ↦ (distinctObservationCount Xn n ω : ℝ) /
      Real.log (n + 1)) atTop (𝓝 (α.real univ)) := by
  sorry

/-- No values have been observed before the first sample. -/
@[simp] theorem distinctObservationCount_zero {Ω X : Type*} (Xn : ℕ → Ω → X) (ω : Ω) :
    distinctObservationCount Xn 0 ω = 0 := by simp [distinctObservationCount]

end CKSD
