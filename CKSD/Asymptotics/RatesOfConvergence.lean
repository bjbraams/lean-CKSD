module

public import CKSD.Asymptotics.Statistics

/-!
# Rate of convergence of M-estimators

The rate theorem for approximate maximizers of random criterion functions on a pseudometric
parameter space, with the modulus of continuity of the centred criterion process controlled by
an outer expectation (`outerExpectation`). Probabilities of events defined by the estimator are
outer probabilities, since `Measure` applied to an arbitrary set is the outer measure; no
measurability of the estimator or of the suprema is assumed. Source: GAPS 102.25.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace CKSD

/-- Local modulus of the centred criterion process `Mₙ - M` on the ball of radius `δ` about
`θ₀`, as a nonnegative extended-real random quantity. -/
def centredCriterionModulus {Ω Θ : Type*} [PseudoMetricSpace Θ] (M : Θ → ℝ)
    (Mn : Ω → Θ → ℝ) (θ₀ : Θ) (δ : ℝ) (ω : Ω) : ℝ≥0∞ :=
  ⨆ (θ : Θ) (_ : dist θ θ₀ < δ),
    ENNReal.ofReal |(Mn ω θ - M θ) - (Mn ω θ₀ - M θ₀)|

/-- GAPS 102.25: the rate theorem for `M`-estimators. Suppose the deterministic criterion has
quadratic separation `M θ - M θ₀ ≤ -c d(θ,θ₀)²` near `θ₀`, and that for every `n ≥ 1` and all
`δ` in a fixed interval `(0, δ₀)`, the outer expectation of the local modulus of `Mₙ - M` is at
most `C φₙ(δ)/√n`, where `δ ↦ φₙ(δ)/δ^a` is decreasing on `(0,∞)` for a fixed `a < 2`.
If `rₙ² φₙ(1/rₙ) ≤ √n`, the estimator maximizes `Mₙ` up to `O_P(rₙ⁻²)`, and it is consistent
in outer probability, then `rₙ d(Tₙ, θ₀) = O_P(1)`. -/
theorem isBoundedInProbability_rate_m_estimator {Ω Θ : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace Θ] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (M : Θ → ℝ) (Mn : ℕ → Ω → Θ → ℝ) (θ₀ : Θ)
    (c η : ℝ) (hc : 0 < c) (hη : 0 < η)
    (hcurv : ∀ θ, dist θ θ₀ < η → M θ - M θ₀ ≤ -(c * dist θ θ₀ ^ 2))
    (φ : ℕ → ℝ → ℝ) (a : ℝ) (ha : a < 2)
    (hφ : ∀ n, AntitoneOn (fun δ ↦ φ n δ / δ ^ a) (Ioi 0))
    (C δ₀ : ℝ) (hδ₀ : 0 < δ₀)
    (hmod : ∀ n : ℕ, 1 ≤ n → ∀ δ, 0 < δ → δ < δ₀ →
      outerExpectation μ (centredCriterionModulus M (Mn n) θ₀ δ) ≤
        ENNReal.ofReal (C * φ n δ / Real.sqrt n))
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    (hrate : ∀ n : ℕ, 1 ≤ n → r n ^ 2 * φ n (1 / r n) ≤ Real.sqrt n)
    (T : ℕ → Ω → Θ) (R : ℕ → Ω → ℝ)
    (hR : IsBoundedInProbability μ (fun n ω ↦ r n ^ 2 * R n ω))
    (hopt : ∀ n ω, Mn n ω θ₀ - R n ω ≤ Mn n ω (T n ω))
    (hcons : TendstoInProbabilityConst μ T θ₀) :
    IsBoundedInProbability μ (fun n ω ↦ r n * dist (T n ω) θ₀) := by
  sorry

end CKSD
