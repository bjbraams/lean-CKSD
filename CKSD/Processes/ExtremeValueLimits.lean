module

public import CKSD.Processes.Extremes
public import TauCeti.Probability.Distributions.OrderStatistic.Basic
public import TauCeti.Probability.Distributions.GeneralizedExtremeValue.Cdf
public import TauCeti.Probability.Distributions.GeneralizedPareto.Cdf
public import TauCeti.Probability.Distributions.GeneralizedPareto.Threshold

/-!
# Threshold excesses and the Hill estimator

The Pickands–Balkema–de Haan theorem characterizes the extreme-value domain of attraction by
generalized Pareto approximation of the excesses over high thresholds, and the Hill estimator of
a positive extreme-value index is asymptotically normal under second-order regular variation.

The generalized extreme-value and Pareto laws and the finite-sample order statistic are TauCeti
constructions. The upper endpoint is extended-real, so both finite and infinite endpoints are
allowed.

## Main definitions

* `CKSD.distributionUpperEndpoint`: the right endpoint `sup {t | F(t) < 1}` in `EReal`.
* `CKSD.thresholdExcessLaw`: the law of `X - u` given `X > u`.
* `CKSD.HasExtremeValueDomainOfAttraction`: `F^n(a_n x + b_n) → G_γ(x)` for the unit-scale
  generalized extreme-value law `G_γ`.
* `CKSD.thresholdParetoDiscrepancy`: the uniform distance between the excess law and a
  generalized Pareto law.
* `CKSD.HasSecondOrderTailQuantile`: second-order regular variation of the tail quantile.
* `CKSD.hillEstimator`: `k⁻¹ ∑_{i<k} log X_{(n-i)} - log X_{(n-k)}`.

## Main results

* `CKSD.hasExtremeValueDomainOfAttraction_iff_pareto_excesses` (GAPS 106.47).
* `CKSD.tendstoInDistribution_hillEstimator` (GAPS 106.49):
  `√k (γ̂ - γ) ⇒ N(b / (1 - ρ), γ²)`, `b = lim √k A(n/k)`.
* `CKSD.thresholdExcessLaw_generalizedPareto`: threshold stability of the generalized Pareto
  laws, from TauCeti.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- Right endpoint of a real distribution, allowed to be infinite. -/
def distributionUpperEndpoint (P : Measure ℝ) : EReal :=
  sSup {x : EReal | ∃ t : ℝ, x = t ∧ cdf P t < 1}

/-- The conditional law of the excess over a threshold. -/
def thresholdExcessLaw (P : Measure ℝ) (u : ℝ) : Measure ℝ :=
  (ProbabilityTheory.cond P (Ioi u)).map (fun x ↦ x - u)

/-- Membership in the domain of attraction of the unit-scale generalized extreme-value law. -/
def HasExtremeValueDomainOfAttraction (P : Measure ℝ) (γ : ℝ) : Prop :=
  ∃ a b : ℕ → ℝ, (∀ n, 0 < a n) ∧ ∀ x : ℝ,
    Tendsto (fun n ↦ cdf P (a n * x + b n) ^ n) atTop
      (𝓝 (cdf (TauCeti.Probability.generalizedExtremeValueMeasure 0 1 γ) x))

/-- Uniform discrepancy over all nonnegative excesses, including the terminal jump, against a
fitted generalized Pareto law. -/
def thresholdParetoDiscrepancy (P : Measure ℝ) (γ scale threshold : ℝ) : ℝ :=
  sSup {r : ℝ | ∃ y : ℝ, 0 ≤ y ∧
    r = |cdf (thresholdExcessLaw P threshold) y -
      cdf (TauCeti.Probability.generalizedParetoMeasure scale γ) y|}

/-- GAPS 106.47: Pickands–Balkema–de Haan theorem. `F` lies in the domain of attraction of the
generalized extreme-value law with index `γ` if and only if there is a positive scale function
`σ(u)` such that the excess law over `u` is uniformly approximated by the generalized Pareto law
with scale `σ(u)` and shape `γ` as `u` increases to the upper endpoint, finite or infinite. -/
theorem hasExtremeValueDomainOfAttraction_iff_pareto_excesses
    (P : Measure ℝ) [IsProbabilityMeasure P] (γ : ℝ) :
    HasExtremeValueDomainOfAttraction P γ ↔
      ∃ scale : ℝ → ℝ, (∀ u : ℝ, (u : EReal) < distributionUpperEndpoint P → 0 < scale u) ∧
        Tendsto (fun u ↦ thresholdParetoDiscrepancy P γ (scale u) u)
          (Filter.comap (fun u : ℝ ↦ (u : EReal)) (𝓝[<] distributionUpperEndpoint P)) (𝓝 0) := by
  sorry

/-- Second-order regular variation of the tail quantile `U` with index `γ`, second-order
parameter `ρ` and auxiliary function `A`: `A(t) → 0` with eventually constant sign, and
`(U(tx)/U(t) - x^γ) / A(t) → x^γ (x^ρ - 1) / ρ` for every `x > 0`. -/
def HasSecondOrderTailQuantile (P : Measure ℝ) (γ ρ : ℝ) (A : ℝ → ℝ) : Prop :=
  Tendsto A atTop (𝓝 0) ∧
    ((∀ᶠ t in atTop, 0 < A t) ∨ (∀ᶠ t in atTop, A t < 0)) ∧
    ∀ x > 0, Tendsto (fun t ↦ (tailQuantile P (t * x) / tailQuantile P t - Real.rpow x γ) / A t)
      atTop (𝓝 (Real.rpow x γ * (Real.rpow x ρ - 1) / ρ))

/-- The Hill estimator `k⁻¹ ∑_{i<k} log X_{(n-i)} - log X_{(n-k)}` from the `k + 1` largest
order statistics of `x`; it is defined to be zero unless `1 ≤ k < n`. -/
def hillEstimator {n : ℕ} (k : ℕ) (x : Fin n → ℝ) : ℝ :=
  if h : 0 < k ∧ k < n then
    (∑ i : Fin k, Real.log (TauCeti.orderStatistic ⟨n - i.val - 1, by omega⟩ x)) / k -
      Real.log (TauCeti.orderStatistic ⟨n - k - 1, by omega⟩ x)
  else 0

/-- GAPS 106.49: Hill central limit theorem. For iid positive observations whose tail quantile
is second-order regularly varying with index `γ > 0` and parameter `ρ < 0`, and intermediate
sequences `k_n → ∞`, `k_n / n → 0` with `√k_n A(n / k_n) → b`,
`√k_n (γ̂_n - γ) ⇒ N(b / (1 - ρ), γ²)`. Regular variation of the tail `1 - F` with index
`-1/γ` follows from the second-order condition and is not assumed separately. -/
theorem tendstoInDistribution_hillEstimator {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure ℝ) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hiid : IsIndependentIdenticallyDistributed μ X P)
    (hpositive : P (Ioi 0) = 1) (γ ρ : ℝ) (hγ : 0 < γ) (hρ : ρ < 0) (A : ℝ → ℝ)
    (hsecond : HasSecondOrderTailQuantile P γ ρ A) (k : ℕ → ℕ)
    (hklim : Tendsto k atTop atTop) (hkn : Tendsto (fun n ↦ (k n : ℝ) / n) atTop (𝓝 0))
    (b : ℝ) (hA : Tendsto (fun n ↦ Real.sqrt (k n) * A ((n : ℝ) / k n)) atTop (𝓝 b)) :
    TendstoInDistribution (fun (n : ℕ) ω ↦ Real.sqrt (k n) *
      (hillEstimator (k n) (fun i : Fin n ↦ X i.val ω) - γ)) atTop id (fun _ ↦ μ)
      (gaussianReal (b / (1 - ρ)) (Real.toNNReal (γ ^ 2))) := by
  sorry

/-- The Hill estimator of order zero uses the explicitly specified zero convention. -/
@[simp] theorem hillEstimator_zero {n : ℕ} (x : Fin n → ℝ) : hillEstimator 0 x = 0 := by
  simp [hillEstimator]

/-- Threshold stability of the generalized Pareto laws: the excess law over `u ≥ 0` of the
generalized Pareto law with scale `s` and shape `γ` is generalized Pareto with scale `s + γ u`
and the same shape (TauCeti's `map_sub_cond_generalizedParetoMeasure`). -/
theorem thresholdExcessLaw_generalizedPareto (s γ u : ℝ) (hs : 0 < s) (hu : 0 ≤ u)
    (hscale : 0 < s + γ * u) :
    thresholdExcessLaw (TauCeti.Probability.generalizedParetoMeasure s γ) u =
      TauCeti.Probability.generalizedParetoMeasure (s + γ * u) γ :=
  TauCeti.Probability.map_sub_cond_generalizedParetoMeasure hs hu hscale

end CKSD
