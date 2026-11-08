module

public import CKSD.Processes.Basic

/-!
# Nelson–Aalen and Kaplan–Meier estimators under random censoring

Central limit theorems at a fixed time for the Nelson–Aalen estimator of the cumulative hazard
and the Kaplan–Meier estimator of the survival function, from independent copies of a failure
time `T` with law `F` and an independent censoring time `C` with law `C₀`, both nonnegative.
The failure law has a Lebesgue density `f`, so that `Λ(t) = ∫_0^t f / (1 - F)` and the at-risk
probability is `y(s) = P(min(T, C) ≥ s) = (1 - F(s)) C₀[s, ∞)`.

## Main definitions

* `CKSD.IsRandomCensoringModel`: the observations `(T i, C i)` are iid with law `F ⊗ C₀`, and
  `F`, `C₀` are concentrated on `[0, ∞)`.

## Main results

* `CKSD.tendstoInDistribution_nelsonAalenEstimator` (GAPS 106.28):
  `√n (Λ̂_n(t) - Λ(t)) ⇒ N(0, ∫_0^t dΛ / y)`.
* `CKSD.tendstoInDistribution_kaplanMeierEstimator` (GAPS 106.29):
  `√n (Ŝ_n(t) - S(t)) ⇒ N(0, S(t)² ∫_0^t dΛ / y)`.

The process-level convergence in the Skorokhod space `D[0, τ]` and Greenwood's variance
estimator are not stated.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace CKSD

/-- The random censoring model: the pairs `(T i, C i)` of failure and censoring times are
independent copies with law `F ⊗ C₀` (so failure and censoring are independent), and both laws
are concentrated on `[0, ∞)`. -/
structure IsRandomCensoringModel {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (F C₀ : Measure ℝ) (T C : ℕ → Ω → ℝ) : Prop where
  /-- The pairs `(T i, C i)` are iid with the product law `F ⊗ C₀`. -/
  iid : IsIndependentIdenticallyDistributed μ (fun i ω ↦ (T i ω, C i ω)) (F.prod C₀)
  /-- Failure times are nonnegative. -/
  failure_nonneg : F (Ici 0) = 1
  /-- Censoring times are nonnegative. -/
  censoring_nonneg : C₀ (Ici 0) = 1

/-- GAPS 106.28, fixed-time Nelson–Aalen central limit theorem: in the random censoring model
with a failure law `F` of density `f` and `P(min(T, C) ≥ t) > 0`,
`√n (Λ̂_n(t) - Λ(t)) ⇒ N(0, v)` with `Λ(t) = ∫_0^t f / (1 - F)` and
`v = ∫_0^t f / ((1 - F)² C₀[s, ∞))`. -/
theorem tendstoInDistribution_nelsonAalenEstimator {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F C₀ : Measure ℝ)
    [IsProbabilityMeasure F] [IsProbabilityMeasure C₀]
    (T C : ℕ → Ω → ℝ) (hcens : IsRandomCensoringModel μ F C₀ T C)
    (f : ℝ → ℝ) (hf : HasDensity F volume f)
    (t : ℝ) (ht : 0 ≤ t) (hrisk : 0 < F (Ici t) * C₀ (Ici t)) :
    let Λ := ∫ s in (0 : ℝ)..t, f s / (1 - cdf F s);
    let v := ∫ s in (0 : ℝ)..t, f s / ((1 - cdf F s) ^ 2 * C₀.real (Ici s));
    TendstoInDistribution μ (fun n ω ↦ Real.sqrt n * (nelsonAalenEstimator T C n ω t - Λ))
      (gaussianReal 0 (Real.toNNReal v)) := by
  sorry

/-- GAPS 106.29, fixed-time Kaplan–Meier central limit theorem: under the assumptions of
`tendstoInDistribution_nelsonAalenEstimator`, `√n (Ŝ_n(t) - S(t)) ⇒ N(0, S(t)² v)` with
`S(t) = 1 - F(t)` and `v` the Nelson–Aalen asymptotic variance (Greenwood's formula). -/
theorem tendstoInDistribution_kaplanMeierEstimator {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F C₀ : Measure ℝ)
    [IsProbabilityMeasure F] [IsProbabilityMeasure C₀]
    (T C : ℕ → Ω → ℝ) (hcens : IsRandomCensoringModel μ F C₀ T C)
    (f : ℝ → ℝ) (hf : HasDensity F volume f)
    (t : ℝ) (ht : 0 ≤ t) (hrisk : 0 < F (Ici t) * C₀ (Ici t)) :
    let S := 1 - cdf F t;
    let v := S ^ 2 * ∫ s in (0 : ℝ)..t, f s / ((1 - cdf F s) ^ 2 * C₀.real (Ici s));
    TendstoInDistribution μ (fun n ω ↦ Real.sqrt n * (kaplanMeierEstimator T C n ω t - S))
      (gaussianReal 0 (Real.toNNReal v)) := by
  sorry

end CKSD
