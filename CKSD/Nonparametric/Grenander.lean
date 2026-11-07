module

public import CKSD.Nonparametric.Basic
public import Mathlib.Probability.BrownianMotion.Basic

/-!
# The Grenander estimator of a decreasing density

The least concave majorant is taken on `[0, ∞)`, as the pointwise infimum of all concave
majorants there. The Grenander estimator at `x` is the left derivative at `x` of the least
concave majorant of the empirical distribution function. Two-sided Brownian motion is built
from two independent Brownian motions of Mathlib (`ProbabilityTheory.IsBrownianReal`) on
`[0, ∞)`, and Chernoff's random variable is specified as a measurable almost-sure maximizer of
`W(t) - t ^ 2`; its law, being that of the almost surely unique maximizer, does not depend
on the realization.
Source: GAPS 103.11.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace CKSD

/-- Least concave majorant on `[0, ∞)` of a real function, as the infimum of the values of
its concave majorants; the empty-set convention `sInf ∅ = 0` is never used for bounded
functions such as distribution functions. -/
def leastConcaveMajorant (F : ℝ → ℝ) (t : ℝ) : ℝ :=
  sInf {r : ℝ | ∃ g : ℝ → ℝ, ConcaveOn ℝ (Ici 0) g ∧ (∀ s ∈ Ici (0 : ℝ), F s ≤ g s) ∧
    r = g t}

/-- The Grenander estimator at `x`: the left slope of the least concave majorant of the
empirical distribution function of the first `n` observations. -/
def grenanderEstimator {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) (x : ℝ) : ℝ :=
  derivWithin (leastConcaveMajorant (empiricalCDF X n ω)) (Iio x) x

/-- A nonincreasing probability density on `[0, ∞)`, vanishing on the negative half-line. -/
def IsNonincreasingDensity (g : ℝ → ℝ) : Prop :=
  Measurable g ∧ (∀ t, 0 ≤ g t) ∧ (∀ t < 0, g t = 0) ∧ AntitoneOn g (Ioi 0) ∧
    ∫ t, g t = 1

/-- The path of two-sided Brownian motion built from two one-sided paths: `B₁` on the
nonnegative half-line and `B₂` reflected on the negative half-line. -/
def twoSidedBrownianPath {Ω : Type*} (B₁ B₂ : ℝ≥0 → Ω → ℝ) (ω : Ω) (t : ℝ) : ℝ :=
  if 0 ≤ t then B₁ t.toNNReal ω else B₂ (-t).toNNReal ω

/-- `Z` is a realization of Chernoff's random variable `argmax (W(t) - t ^ 2)` for the
two-sided Brownian motion `W` built from independent Brownian motions `B₁` and `B₂`. -/
def IsChernoffArgmax {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    (B₁ B₂ : ℝ≥0 → Ω → ℝ) (Z : Ω → ℝ) : Prop :=
  IsBrownianReal B₁ ν ∧ IsBrownianReal B₂ ν ∧
    IndepFun (fun ω t ↦ B₁ t ω) (fun ω t ↦ B₂ t ω) ν ∧ Measurable Z ∧
    ∀ᵐ ω ∂ν, ∀ t : ℝ, twoSidedBrownianPath B₁ B₂ ω t - t ^ 2 ≤
      twoSidedBrownianPath B₁ B₂ ω (Z ω) - Z ω ^ 2

/-- GAPS 103.11: the Grenander estimator is a nonparametric maximum likelihood estimator
among nonincreasing densities on `[0, ∞)`. Scope: a fixed sample of `n ≥ 1` positive
observations; the estimator is extended by zero to the nonpositive half-line, and the
likelihood is the product of density values at the observations. -/
theorem grenanderEstimator_isMaximumLikelihood {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ)
    (hn : 0 < n) (ω : Ω) (hpos : ∀ i < n, 0 < X i ω) :
    let ĝ := fun t ↦ if 0 < t then grenanderEstimator X n ω t else 0;
    IsNonincreasingDensity ĝ ∧ ∀ g : ℝ → ℝ, IsNonincreasingDensity g →
      ∏ i ∈ Finset.range n, g (X i ω) ≤ ∏ i ∈ Finset.range n, ĝ (X i ω) := by
  sorry

/-- GAPS 103.11: the cube-root limit law of the Grenander estimator at an interior point.
The density `f` is a version vanishing on the negative half-line, positive and nonincreasing
on `[0, ∞)`, and differentiable at `x₀ > 0` with negative derivative (which gives continuity
at `x₀`); the limit is the law of `|4 f(x₀) f'(x₀)| ^ (1/3) Z` for Chernoff's `Z`. -/
theorem tendstoInDistribution_grenanderEstimator {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure ℝ) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hiid : IsIndependentIdenticallyDistributed μ X P) (f : ℝ → ℝ)
    (hf : HasDensity P volume f) (hneg : ∀ t < 0, f t = 0) (hfpos : ∀ t, 0 ≤ t → 0 < f t)
    (hanti : AntitoneOn f (Ici 0)) (x₀ f' : ℝ) (hx₀ : 0 < x₀) (hderiv : HasDerivAt f f' x₀)
    (hf' : f' < 0) {Ω' : Type*} [MeasurableSpace Ω'] (ν : Measure Ω') [IsProbabilityMeasure ν]
    (B₁ B₂ : ℝ≥0 → Ω' → ℝ) (Z : Ω' → ℝ) (hZ : IsChernoffArgmax ν B₁ B₂ Z) :
    TendstoInDistribution μ
      (fun n ω ↦ (n : ℝ) ^ (1 / 3 : ℝ) * (grenanderEstimator X n ω x₀ - f x₀))
      (ν.map fun ω ↦ |4 * f x₀ * f'| ^ (1 / 3 : ℝ) * Z ω) := by
  sorry

end CKSD
