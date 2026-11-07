module

public import CKSD.Processes.Basic
public import CKSD.Asymptotics.Basic
public import CKSD.Nonparametric.Basic

/-!
# Processes: Extremes

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

/-- GAPS 106.46, the regularly varying positive-tail sufficient condition for a Fréchet limit. -/
theorem tendsto_maximum_of_regularly_varying_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure ℝ) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hiid : IsIndependentIdenticallyDistributed μ X P) (γ : ℝ) (hγ : 0 < γ)
    (hpos : ∀ t : ℝ, cdf P t < 1)
    (hrv : ∀ x > 0, Tendsto (fun t ↦ (1 - cdf P (t * x)) / (1 - cdf P t))
      atTop (𝓝 (Real.rpow x (-1 / γ)))) :
    let a := fun n : ℕ ↦ sInf {t | 1 - (n : ℝ)⁻¹ ≤ cdf P t};
    ∀ x > 0, Tendsto (fun n ↦ μ.real {ω | ∀ i < n, X i ω ≤ a n * x}) atTop
      (𝓝 (Real.exp (-Real.rpow x (-1 / γ)))) := by
  sorry

/-- GAPS 106.48 (independent scope) and GAPS 106.50, finite-intensity exceedance limit; also the
independent part of 106.48. -/
theorem tendsto_maximum_and_exceedance_count_of_tail_limit {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure ℝ) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hiid : IsIndependentIdenticallyDistributed μ X P) (u : ℕ → ℝ) (τ : ℝ≥0)
    (htail : Tendsto (fun n : ℕ ↦ (n : ℝ) * (1 - cdf P (u n))) atTop (𝓝 (τ : ℝ))) :
    Tendsto (fun n ↦ μ.real {ω | ∀ i < n, X i ω ≤ u n}) atTop (𝓝 (Real.exp (-τ))) ∧
      TendstoInDistribution μ (fun n ω ↦ ((Finset.range n).filter (fun i ↦ u n < X i ω)).card)
        (poissonMeasure τ) := by
  sorry


end CKSD
