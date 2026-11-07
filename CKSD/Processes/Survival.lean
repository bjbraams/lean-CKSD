module

public import CKSD.Processes.Basic
public import CKSD.Asymptotics.Basic
public import CKSD.Nonparametric.Basic

/-!
# Processes: Survival

Sources: `GAPS.md`, `SYNOPSIS106.md`, and `STRUCTURE106.md`.
Declarations adapted from this project's section drafts.
The docstrings specify the scope of each result; `sorry` marks unfinished proofs.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- GAPS 106.28, fixed-time Nelson–Aalen CLT for absolutely continuous failure times. -/
theorem tendstoInDistribution_nelsonAalenEstimator {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F C₀ : Measure ℝ)
    [IsProbabilityMeasure F] [IsProbabilityMeasure C₀]
    (T C : ℕ → Ω → ℝ) (hiid : IsIndependentIdenticallyDistributed μ (fun i ω ↦ (T i ω, C i ω))
      (F.prod C₀))
    (f : ℝ → ℝ) (hf : HasDensity F volume f)
    (hF : F (Ici 0) = 1) (hC : C₀ (Ici 0) = 1)
    (t : ℝ) (ht : 0 ≤ t) (hrisk : 0 < F (Ici t) * C₀ (Ici t)) :
    let Λ := ∫ s in (0 : ℝ)..t, f s / (1 - cdf F s);
    let v := ∫ s in (0 : ℝ)..t, f s / ((1 - cdf F s) ^ 2 * C₀.real (Ici s));
    TendstoInDistribution μ (fun n ω ↦ Real.sqrt n * (nelsonAalenEstimator T C n ω t - Λ))
      (gaussianReal 0 (Real.toNNReal v)) := by
  sorry

/-- GAPS 106.29, fixed-time Kaplan–Meier CLT under independent censoring. -/
theorem tendstoInDistribution_kaplanMeierEstimator {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F C₀ : Measure ℝ)
    [IsProbabilityMeasure F] [IsProbabilityMeasure C₀]
    (T C : ℕ → Ω → ℝ) (hiid : IsIndependentIdenticallyDistributed μ (fun i ω ↦ (T i ω, C i ω))
      (F.prod C₀))
    (f : ℝ → ℝ) (hf : HasDensity F volume f)
    (hF : F (Ici 0) = 1) (hC : C₀ (Ici 0) = 1)
    (t : ℝ) (ht : 0 ≤ t) (hrisk : 0 < F (Ici t) * C₀ (Ici t)) :
    let S := 1 - cdf F t;
    let v := S ^ 2 * ∫ s in (0 : ℝ)..t, f s / ((1 - cdf F s) ^ 2 * C₀.real (Ici s));
    TendstoInDistribution μ (fun n ω ↦ Real.sqrt n * (kaplanMeierEstimator T C n ω t - S))
      (gaussianReal 0 (Real.toNNReal v)) := by
  sorry


end CKSD
