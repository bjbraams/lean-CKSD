module

public import CKSD.Asymptotics.Basic

/-!
# Processes: definitions

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

/-- Sample autocovariance using the sample mean and divisor `n`. -/
def sampleAutocovariance {Ω : Type*} (X : ℕ → Ω → ℝ) (lag n : ℕ) (ω : Ω) : ℝ :=
  (∑ i ∈ Finset.range (n - lag),
    (X (i + lag) ω - sampleAverage X n ω) * (X i ω - sampleAverage X n ω)) / n

/-- The risk-set cardinality at the `i`th observed time. -/
def riskSetSize {Ω : Type*} (T C : ℕ → Ω → ℝ) (n i : ℕ) (ω : Ω) : ℕ :=
  ((Finset.range n).filter fun j ↦ min (T i ω) (C i ω) ≤ min (T j ω) (C j ω)).card

/-- Nelson–Aalen estimator, expressed as a sum over individual observed failures. -/
def nelsonAalenEstimator {Ω : Type*} (T C : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) (t : ℝ) : ℝ :=
  ∑ i ∈ Finset.range n, if T i ω ≤ C i ω ∧ T i ω ≤ t then
    (riskSetSize T C n i ω : ℝ)⁻¹ else 0

/-- Kaplan–Meier product, with one factor for each individual observed failure. -/
def kaplanMeierEstimator {Ω : Type*} (T C : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) (t : ℝ) : ℝ :=
  ∏ i ∈ Finset.range n, if T i ω ≤ C i ω ∧ T i ω ≤ t then
    1 - (riskSetSize T C n i ω : ℝ)⁻¹ else 1


end CKSD
