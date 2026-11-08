module

public import CKSD.Inference.Basic

/-!
# Empirical statistics and asymptotic distances

Empirical distribution functions and their left quantiles, ordered-injection U-statistics,
sequence contiguity, Kolmogorov distance and the clipped Huber score. The empirical quantile
and U-statistic are total definitions; their statistical theorems specify admissible sample
sizes and parameters.
Sources: Section 102 of `GAPS.md`, `SYNOPSIS102.md`, and `STRUCTURE102.md`.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- Empirical distribution function of the first `n` real observations. -/
def empiricalCDF {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) (t : ℝ) : ℝ :=
  ((Finset.range n).filter (fun i ↦ X i ω ≤ t)).card / (n : ℝ)

/-- Left empirical quantile; only used for nonempty samples and probabilities in `(0,1)`. -/
def sampleQuantile {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) (p : ℝ) : ℝ :=
  sInf {t | p ≤ empiricalCDF X n ω t}

/-- The ordered-injection formula for a symmetric U-statistic of order `m`. -/
def uStatistic {E : Type*} (m n : ℕ) (h : (Fin m → E) → ℝ) (x : Fin n → E) : ℝ :=
  ((n.descFactorial m : ℕ) : ℝ)⁻¹ *
    ∑ f ∈ (Finset.univ : Finset (Fin m → Fin n)).filter Function.Injective,
      h (x ∘ f)

/-- Contiguity of sequences of laws on a common measurable space. -/
def IsContiguous {Ω : Type*} [MeasurableSpace Ω]
    (P Q : ℕ → Measure Ω) : Prop :=
  ∀ A : ℕ → Set Ω, (∀ n, MeasurableSet (A n)) →
    Tendsto (fun n ↦ (P n).real (A n)) atTop (𝓝 0) →
    Tendsto (fun n ↦ (Q n).real (A n)) atTop (𝓝 0)

/-- The Kolmogorov distance, with the CDF normalization for probability laws. -/
def kolmogorovDistance (P Q : Measure ℝ) : ℝ := sSup (range fun t ↦ |cdf P t - cdf Q t|)

/-- The clipped Huber score. -/
def huberScore (k x : ℝ) : ℝ := max (-k) (min k x)


end CKSD
