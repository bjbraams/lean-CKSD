module

public import CKSD.Processes.Extremes
public import TauCeti.Probability.Distributions.OrderStatistic.Basic
public import TauCeti.Probability.Distributions.GeneralizedExtremeValue.Cdf
public import TauCeti.Probability.Distributions.GeneralizedPareto.Cdf
public import TauCeti.Probability.Distributions.GeneralizedPareto.Threshold

/-!
# Threshold excesses and the Hill estimator

The generalized extreme-value and Pareto laws and the finite-sample order statistic are TauCeti
constructions. The domain-of-attraction and second-order tail conditions below are new statistical
interfaces. The upper endpoint is extended-real, so both finite and infinite endpoints are allowed.
Sources: GAPS 106.47 and GAPS 106.49.
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

/-- Uniform discrepancy between threshold excesses and a fitted generalized Pareto law. -/
def thresholdParetoDiscrepancy (P : Measure ℝ) (γ scale threshold : ℝ) : ℝ :=
  sSup {r : ℝ | ∃ y : ℝ, 0 ≤ y ∧ (threshold + y : EReal) < distributionUpperEndpoint P ∧
    r = |cdf (thresholdExcessLaw P threshold) y -
      cdf (TauCeti.Probability.generalizedParetoMeasure scale γ) y|}

/-- GAPS 106.47: Pickands–Balkema–de Haan equivalence, allowing finite upper endpoints. -/
theorem hasExtremeValueDomainOfAttraction_iff_pareto_excesses
    (P : Measure ℝ) [IsProbabilityMeasure P] (γ : ℝ) :
    HasExtremeValueDomainOfAttraction P γ ↔
      ∃ scale : ℝ → ℝ, (∀ u : ℝ, (u : EReal) < distributionUpperEndpoint P → 0 < scale u) ∧
        Tendsto (fun u ↦ thresholdParetoDiscrepancy P γ (scale u) u)
          (Filter.comap (fun u : ℝ ↦ (u : EReal)) (𝓝[<] distributionUpperEndpoint P)) (𝓝 0) := by
  sorry

/-- Tail quantile of order `1-1/t`, used for `t>1`. -/
def tailQuantile (P : Measure ℝ) (t : ℝ) : ℝ :=
  sInf {x : ℝ | 1 - 1 / t ≤ cdf P x}

/-- Positive regularly varying tail of index `-1/γ`. -/
def HasRegularlyVaryingTail (P : Measure ℝ) (γ : ℝ) : Prop :=
  (∀ t : ℝ, cdf P t < 1) ∧ ∀ x > 0,
    Tendsto (fun t ↦ (1 - cdf P (t * x)) / (1 - cdf P t)) atTop
      (𝓝 (Real.rpow x (-1 / γ)))

/-- Second-order regular variation of the tail quantile, with an eventually constant-sign remainder. -/
def HasSecondOrderTailQuantile (P : Measure ℝ) (γ ρ : ℝ) (A : ℝ → ℝ) : Prop :=
  Tendsto A atTop (𝓝 0) ∧
    ((∀ᶠ t in atTop, 0 < A t) ∨ (∀ᶠ t in atTop, A t < 0)) ∧
    ∀ x > 0, Tendsto (fun t ↦ (tailQuantile P (t * x) / tailQuantile P t - Real.rpow x γ) / A t)
      atTop (𝓝 (Real.rpow x γ * (Real.rpow x ρ - 1) / ρ))

/-- Hill estimator from the largest `k` observations. It is zero outside `1≤k<n`. -/
def hillEstimator {n : ℕ} (k : ℕ) (x : Fin n → ℝ) : ℝ :=
  if h : 0 < k ∧ k < n then
    (∑ i : Fin k, Real.log (TauCeti.orderStatistic ⟨n - i.val - 1, by omega⟩ x)) / k -
      Real.log (TauCeti.orderStatistic ⟨n - k - 1, by omega⟩ x)
  else 0

/-- GAPS 106.49: Hill central limit theorem under second-order regular variation. -/
theorem tendstoInDistribution_hillEstimator {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure ℝ) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hiid : IsIndependentIdenticallyDistributed μ X P)
    (hpositive : P (Ioi 0) = 1) (γ ρ : ℝ) (hγ : 0 < γ) (hρ : ρ < 0)
    (htail : HasRegularlyVaryingTail P γ) (A : ℝ → ℝ)
    (hsecond : HasSecondOrderTailQuantile P γ ρ A) (k : ℕ → ℕ)
    (hklim : Tendsto k atTop atTop) (hkn : Tendsto (fun n ↦ (k n : ℝ) / n) atTop (𝓝 0))
    (lambda : ℝ) (hA : Tendsto (fun n ↦ Real.sqrt (k n) * A ((n : ℝ) / k n)) atTop (𝓝 lambda)) :
    TendstoInDistribution μ (fun n ω ↦ Real.sqrt (k n) *
      (hillEstimator (k n) (fun i : Fin n ↦ X i.val ω) - γ))
      (gaussianReal (lambda / (1 - ρ)) (Real.toNNReal (γ ^ 2))) := by
  sorry

/-- The Hill estimator of order zero uses the explicitly specified zero convention. -/
@[simp] theorem hillEstimator_zero {n : ℕ} (x : Fin n → ℝ) : hillEstimator 0 x = 0 := by
  simp [hillEstimator]

/-- TauCeti's exact Pareto threshold stability in the excess-law interface. -/
theorem thresholdExcessLaw_generalizedPareto (s γ u : ℝ) (hs : 0 < s) (hu : 0 ≤ u)
    (hscale : 0 < s + γ * u) :
    thresholdExcessLaw (TauCeti.Probability.generalizedParetoMeasure s γ) u =
      TauCeti.Probability.generalizedParetoMeasure (s + γ * u) γ :=
  TauCeti.Probability.map_sub_cond_generalizedParetoMeasure hs hu hscale

end CKSD
