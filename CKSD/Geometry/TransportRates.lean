module

public import CKSD.Geometry.Basic
public import CKSD.Bayes.Basic
public import TauCeti.Probability.Quantile
public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# Limits and rates for empirical transport

The one-dimensional limit uses Mathlib's Brownian motion `W`, with Brownian bridge
`B⁰(u) = W(u) - u W(1)`, and TauCeti's quantile function `μ.quantile`.

For transport maps, potentials are real functions on `ℝ^d`; Legendre conjugates are taken over
the closed unit ball, which carries both laws, and covering numbers of a class of potentials are
taken in the supremum norm over that ball. A semidual estimator is any minimizer over the class of
the empirical semidual functional.

## Main definitions

* `CKSD.ballLegendreConjugate`, `CKSD.semidualFunctional`, `CKSD.ballSupCoveringNumber`.
* `CKSD.IsRegularPotentialClass`: the regularity class of potentials for map estimation.
* `CKSD.IsSemidualEstimator`, `CKSD.transportMapRisk`.

## Main results

* `CKSD.tendstoInDistribution_mul_wasserstein_sq_empiricalMeasure`: the one-dimensional limit law
  of `n W₂²(μ_n, μ)` (GAPS 108.47).
* `CKSD.lintegral_transportMapRisk_semidualEstimator_le` and
  `CKSD.lintegral_transportMapRisk_semidualEstimator_le_of_poincare`: risk bounds for semidual
  transport-map estimators (GAPS 108.53).
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators InnerProductSpace

namespace CKSD

/-- GAPS 108.47: let `μ` be concentrated on `[a, b]` with a density `f` continuous on `[a, b]`
and bounded there between positive constants (the upper bound is automatic by continuity on the
compact interval, and `a < b` follows because `μ` has a density and total mass one). For an
i.i.d. sample of law `μ`, `n W₂²(μ_n, μ)` converges in distribution to
`∫₀¹ B⁰(u)² / f(F⁻¹(u))² du`, where `B⁰(u) = W(u) - u W(1)` is the Brownian bridge built from any Brownian motion `W`; consequently
`√n W₂(μ_n, μ)` is bounded in probability. -/
theorem tendstoInDistribution_mul_wasserstein_sq_empiricalMeasure
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (a b : ℝ) (f : ℝ → ℝ)
    (hμ : HasDensity μ volume f) (hsupp : μ (Icc a b)ᶜ = 0) (hf : ContinuousOn f (Icc a b))
    (c : ℝ) (hc : 0 < c) (hfb : ∀ x ∈ Icc a b, c ≤ f x)
    (X : ℕ → Ω → ℝ) (hX : IsIndependentIdenticallyDistributed P X μ)
    (P' : Measure Ω') [IsProbabilityMeasure P'] (W : ℝ≥0 → Ω' → ℝ) (hW : IsBrownianReal W P') :
    TendstoInDistribution
      (fun (n : ℕ) ω ↦ (n : ℝ) *
        (TauCeti.wassersteinEDist 2 (empiricalMeasure n fun i : Fin n ↦ X i ω) μ).toReal ^ 2)
      atTop id (fun _ ↦ P)
      (P'.map fun ω' ↦ ∫ u in (0 : ℝ)..1,
        (W u.toNNReal ω' - u * W 1 ω') ^ 2 / f (μ.quantile u) ^ 2) ∧
    IsBoundedInProbability P (fun n ω ↦ Real.sqrt n *
      (TauCeti.wassersteinEDist 2 (empiricalMeasure n fun i : Fin n ↦ X i ω) μ).toReal) := by
  sorry

section TransportMaps

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Legendre conjugate of a potential, with the supremum over the closed unit ball. -/
def ballLegendreConjugate (φ : E → ℝ) (y : E) : ℝ :=
  ⨆ x : Metric.closedBall (0 : E) 1, (⟪(x : E), y⟫_ℝ - φ x)

/-- Semidual functional `∫ φ dμ + ∫ φ* dν`. -/
def semidualFunctional (μ ν : Measure E) (φ : E → ℝ) : ℝ :=
  (∫ x, φ x ∂μ) + ∫ y, ballLegendreConjugate φ y ∂ν

/-- Covering number of a class of potentials in the supremum norm over the closed unit ball. -/
def ballSupCoveringNumber (Φ : Set (E → ℝ)) (ε : ℝ) : ℕ∞ :=
  ⨅ (G : Finset (E → ℝ)) (_ : ∀ φ ∈ Φ, ∃ g ∈ G, ∀ x ∈ Metric.closedBall (0 : E) 1,
    |φ x - g x| ≤ ε), (G.card : ℕ∞)

/-- Regularity class for transport-map estimation (Section 108.53): potentials bounded by `B` on
the closed unit ball, ambient twice continuously differentiable at each point of that ball,
with `½ I ≤ ∇²φ ≤ 2 I` there, and with sup-norm metric entropy
`log N(ε, Φ) ≤ A ε^{-γ} log(1 + 1/ε)` for `0 < ε ≤ 1`. -/
structure IsRegularPotentialClass (Φ : Set (E → ℝ)) (B A γ : ℝ) : Prop where
  /-- Uniform bound on the ball. -/
  bounded : ∀ φ ∈ Φ, ∀ x ∈ Metric.closedBall (0 : E) 1, |φ x| ≤ B
  /-- Ambient twice continuous differentiability at every point of the closed ball. -/
  contDiffAt : ∀ φ ∈ Φ, ∀ x ∈ Metric.closedBall (0 : E) 1, ContDiffAt ℝ 2 φ x
  /-- Hessian bounds `½ I ≤ ∇²φ ≤ 2 I`. -/
  hessian_bounds : ∀ φ ∈ Φ, ∀ x ∈ Metric.closedBall (0 : E) 1, ∀ v : E,
    ‖v‖ ^ 2 / 2 ≤ fderiv ℝ (fderiv ℝ φ) x v v ∧ fderiv ℝ (fderiv ℝ φ) x v v ≤ 2 * ‖v‖ ^ 2
  /-- Metric entropy bound. -/
  entropy : ∀ ε ∈ Ioc (0 : ℝ) 1, ∃ N : ℕ, ballSupCoveringNumber Φ ε ≤ N ∧
    Real.log N ≤ A * ε ^ (-γ) * Real.log (1 + 1 / ε)

/-- A semidual estimator: a map from paired samples to potentials in `Φ` minimizing the
empirical semidual functional. -/
def IsSemidualEstimator (Φ : Set (E → ℝ)) (n : ℕ) (est : (Fin n → E × E) → (E → ℝ)) : Prop :=
  ∀ z, est z ∈ Φ ∧ ∀ φ ∈ Φ,
    semidualFunctional (empiricalMeasure n fun i ↦ (z i).1) (empiricalMeasure n fun i ↦ (z i).2)
      (est z) ≤
    semidualFunctional (empiricalMeasure n fun i ↦ (z i).1) (empiricalMeasure n fun i ↦ (z i).2) φ

/-- Squared `L²(μ)` error of the estimated transport map `∇φ̂`. -/
def transportMapRisk (μ : Measure E) (φ₀ φ : E → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (‖gradient φ x - gradient φ₀ x‖ ^ 2) ∂μ

/-- GAPS 108.53, the parametric-rate bound for semidual estimators. Let `μ` be carried by a closed
ball of radius `r ∈ [0, 1)` and `ν` by the closed unit ball, with `ν = (∇φ₀)_# μ` for `φ₀ ∈ Φ`.
The regular class `Φ` has entropy exponent `γ ∈ [0, 1)`. Every semidual estimator from `n`
independent pairs satisfies `E ‖∇φ̂ - ∇φ₀‖²_{L²(μ)} ≤ K n^{-1/2}`, where `K` is independent of `n`
and may depend on `r`. The expectation is the lower Lebesgue integral of the measurable risk. -/
theorem lintegral_transportMapRisk_semidualEstimator_le (Φ : Set (E → ℝ)) (B A γ : ℝ)
    (hΦ : IsRegularPotentialClass Φ B A γ) (hγ : γ ∈ Ico (0 : ℝ) 1)
    (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (r : ℝ) (hr : r ∈ Ico (0 : ℝ) 1)
    (hμ : μ (Metric.closedBall 0 r)ᶜ = 0) (hν : ν (Metric.closedBall 0 1)ᶜ = 0)
    (φ₀ : E → ℝ) (hφ₀ : φ₀ ∈ Φ) (hpush : ν = μ.map (gradient φ₀)) :
    ∃ K : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ est : (Fin n → E × E) → (E → ℝ),
      IsSemidualEstimator Φ n est → Measurable (fun z ↦ transportMapRisk μ φ₀ (est z)) →
      ∫⁻ z, transportMapRisk μ φ₀ (est z) ∂(Measure.pi fun _ : Fin n ↦ μ.prod ν) ≤
        ENNReal.ofReal (K / Real.sqrt n) := by
  sorry

/-- GAPS 108.53, the fast rate: if moreover `Φ` is convex and `μ` satisfies the Poincaré
inequality `Var_μ(h) ≤ C_P ∫ ‖∇h‖² dμ` for continuously differentiable `h`, the risk of every
semidual estimator is at most `K (log n / n)^{2/(2+γ)}`. The source is carried by a closed ball of
radius `r ∈ [0, 1)`; the constant may depend on this interior margin. The minimax rate for Hölder
maps and its wavelet estimator are not formalized. -/
theorem lintegral_transportMapRisk_semidualEstimator_le_of_poincare (Φ : Set (E → ℝ))
    (B A γ : ℝ) (hΦ : IsRegularPotentialClass Φ B A γ) (hγ : γ ∈ Ico (0 : ℝ) 1)
    (hconv : Convex ℝ Φ) (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (r : ℝ) (hr : r ∈ Ico (0 : ℝ) 1)
    (hμ : μ (Metric.closedBall 0 r)ᶜ = 0) (hν : ν (Metric.closedBall 0 1)ᶜ = 0)
    (CP : ℝ) (hpoincare : ∀ h : E → ℝ, ContDiff ℝ 1 h →
      Var[h; μ] ≤ CP * ∫ x, ‖gradient h x‖ ^ 2 ∂μ)
    (φ₀ : E → ℝ) (hφ₀ : φ₀ ∈ Φ) (hpush : ν = μ.map (gradient φ₀)) :
    ∃ K : ℝ, ∀ n : ℕ, 2 ≤ n → ∀ est : (Fin n → E × E) → (E → ℝ),
      IsSemidualEstimator Φ n est → Measurable (fun z ↦ transportMapRisk μ φ₀ (est z)) →
      ∫⁻ z, transportMapRisk μ φ₀ (est z) ∂(Measure.pi fun _ : Fin n ↦ μ.prod ν) ≤
        ENNReal.ofReal (K * (Real.log n / n) ^ (2 / (2 + γ))) := by
  sorry

end TransportMaps

end CKSD
