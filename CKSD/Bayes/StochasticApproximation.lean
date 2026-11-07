module

public import CKSD.Bayes.Basic
public import Mathlib.Probability.Martingale.Basic

/-!
# The ordinary differential equation method of stochastic approximation

For the recursion `θₙ₊₁ = θₙ - aₙ(h(θₙ) + Mₙ₊₁)` the limiting equation is `θ' = -h(θ)`. Its flow
is specified by its defining differential equation (`IsFlowOf`), which determines it uniquely for
Lipschitz `h`. Invariant and internally chain transitive sets follow Benaïm, the limit set of a
sequence is the set of its cluster points, and the interpolated process is piecewise linear
between the times `tₙ = ∑_{k<n} aₖ`. The noise is a martingale difference sequence for a
filtration to which the iterates and the noise are adapted. Sources: GAPS 104.49.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace CKSD

/-- `Φ` is the flow of `θ' = -h(θ)`. -/
def IsFlowOf {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (h : E → E)
    (Φ : ℝ → E → E) : Prop :=
  ∀ x, Φ 0 x = x ∧ ∀ t, HasDerivAt (fun s ↦ Φ s x) (-h (Φ t x)) t

/-- A set invariant under the flow for all real times, `Φₜ(A) = A`. -/
def IsInvariantSet {E : Type*} (Φ : ℝ → E → E) (A : Set E) : Prop :=
  ∀ t, Φ t '' A = A

/-- Internally chain transitive invariant set: any two points of `A` are joined by `(ε, T)`-chains
of points of `A`, each flowing for time at least `T` to within `ε` of the next. -/
def IsInternallyChainTransitive {E : Type*} [NormedAddCommGroup E] (Φ : ℝ → E → E)
    (A : Set E) : Prop :=
  IsInvariantSet Φ A ∧ ∀ x ∈ A, ∀ y ∈ A, ∀ ε > 0, ∀ T > 0, ∃ n : ℕ, 0 < n ∧
    ∃ z : ℕ → E, (∀ i ≤ n, z i ∈ A) ∧ ‖z 0 - x‖ < ε ∧ z n = y ∧
      ∀ i < n, ∃ t ≥ T, ‖Φ t (z i) - z (i + 1)‖ < ε

/-- Limit set of a sequence: the set of its cluster points. -/
def limitSet {E : Type*} [TopologicalSpace E] (u : ℕ → E) : Set E :=
  ⋂ n, closure (u '' Ici n)

/-- Interpolation times `tₙ = ∑_{k<n} aₖ`. -/
def stochasticApproxTime (a : ℕ → ℝ) (n : ℕ) : ℝ := ∑ k ∈ Finset.range n, a k

/-- Piecewise-linear interpolation of the iterates, linear on each `[tₙ, tₙ₊₁]`. -/
def stochasticApproxInterp {E : Type*} [AddCommGroup E] [Module ℝ E] (a : ℕ → ℝ)
    (θ : ℕ → E) (s : ℝ) : E :=
  let n := sSup {n : ℕ | stochasticApproxTime a n ≤ s}
  θ n + ((s - stochasticApproxTime a n) / a n) • (θ (n + 1) - θ n)

/-- GAPS 104.49: Benaïm's limit-set theorem. Under Robbins–Monro steps, martingale-difference noise
with conditional second moment at most `K(1 + ‖θₙ‖²)`, a Lipschitz field, and a.s. bounded iterates,
the limit set is a.s. a compact connected internally chain transitive invariant set. -/
theorem ae_isInternallyChainTransitive_limitSet {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (θ M : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (hθm : ∀ n, Measurable[F n] (θ n)) (hMm : ∀ n, Measurable[F n] (M n))
    (hM2 : ∀ n, MemLp (M n) 2 μ)
    (hzero : ∀ n, μ[M (n + 1) | F n] =ᵐ[μ] fun _ ↦ 0)
    (K : ℝ) (hnoise : ∀ n, μ[(fun ω ↦ ‖M (n + 1) ω‖ ^ 2) | F n] ≤ᵐ[μ]
      fun ω ↦ K * (1 + ‖θ n ω‖ ^ 2))
    (h : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (L : ℝ≥0)
    (hL : LipschitzWith L h) (Φ : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hΦ : IsFlowOf h Φ)
    (a : ℕ → ℝ) (hapos : ∀ n, 0 < a n) (ha2 : Summable (fun n ↦ a n ^ 2))
    (haDiverges : Tendsto (fun n ↦ ∑ k ∈ Finset.range n, a k) atTop atTop)
    (hrec : ∀ n, ∀ᵐ ω ∂μ, θ (n + 1) ω = θ n ω - a n • (h (θ n ω) + M (n + 1) ω))
    (hbdd : ∀ᵐ ω ∂μ, BddAbove (range fun n ↦ ‖θ n ω‖)) :
    ∀ᵐ ω ∂μ, IsCompact (limitSet (θ · ω)) ∧ IsConnected (limitSet (θ · ω)) ∧
      IsInternallyChainTransitive Φ (limitSet (θ · ω)) := by
  sorry

/-- GAPS 104.49: if the only compact connected internally chain transitive invariant sets are
equilibria, the iterates converge almost surely to a possibly random equilibrium. -/
theorem ae_tendsto_equilibrium_of_chainTransitive {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (θ M : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (hθm : ∀ n, Measurable[F n] (θ n)) (hMm : ∀ n, Measurable[F n] (M n))
    (hM2 : ∀ n, MemLp (M n) 2 μ)
    (hzero : ∀ n, μ[M (n + 1) | F n] =ᵐ[μ] fun _ ↦ 0)
    (K : ℝ) (hnoise : ∀ n, μ[(fun ω ↦ ‖M (n + 1) ω‖ ^ 2) | F n] ≤ᵐ[μ]
      fun ω ↦ K * (1 + ‖θ n ω‖ ^ 2))
    (h : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (L : ℝ≥0)
    (hL : LipschitzWith L h) (Φ : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hΦ : IsFlowOf h Φ)
    (a : ℕ → ℝ) (hapos : ∀ n, 0 < a n) (ha2 : Summable (fun n ↦ a n ^ 2))
    (haDiverges : Tendsto (fun n ↦ ∑ k ∈ Finset.range n, a k) atTop atTop)
    (hrec : ∀ n, ∀ᵐ ω ∂μ, θ (n + 1) ω = θ n ω - a n • (h (θ n ω) + M (n + 1) ω))
    (hbdd : ∀ᵐ ω ∂μ, BddAbove (range fun n ↦ ‖θ n ω‖))
    (hequil : ∀ A : Set (EuclideanSpace ℝ (Fin d)), IsCompact A → IsConnected A →
      IsInternallyChainTransitive Φ A → ∃ x, A = {x} ∧ h x = 0) :
    ∀ᵐ ω ∂μ, ∃ x, h x = 0 ∧ Tendsto (θ · ω) atTop (𝓝 x) := by
  sorry

/-- GAPS 104.49: the interpolated process is almost surely an asymptotic pseudotrajectory of the
flow, uniformly on time windows of length `T`. -/
theorem ae_asymptotic_pseudotrajectory {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (θ M : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (hθm : ∀ n, Measurable[F n] (θ n)) (hMm : ∀ n, Measurable[F n] (M n))
    (hM2 : ∀ n, MemLp (M n) 2 μ)
    (hzero : ∀ n, μ[M (n + 1) | F n] =ᵐ[μ] fun _ ↦ 0)
    (K : ℝ) (hnoise : ∀ n, μ[(fun ω ↦ ‖M (n + 1) ω‖ ^ 2) | F n] ≤ᵐ[μ]
      fun ω ↦ K * (1 + ‖θ n ω‖ ^ 2))
    (h : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (L : ℝ≥0)
    (hL : LipschitzWith L h) (Φ : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hΦ : IsFlowOf h Φ)
    (a : ℕ → ℝ) (hapos : ∀ n, 0 < a n) (ha2 : Summable (fun n ↦ a n ^ 2))
    (haDiverges : Tendsto (fun n ↦ ∑ k ∈ Finset.range n, a k) atTop atTop)
    (hrec : ∀ n, ∀ᵐ ω ∂μ, θ (n + 1) ω = θ n ω - a n • (h (θ n ω) + M (n + 1) ω))
    (hbdd : ∀ᵐ ω ∂μ, BddAbove (range fun n ↦ ‖θ n ω‖)) (T : ℝ) (hT : 0 < T) :
    ∀ᵐ ω ∂μ, ∀ ε > 0, ∀ᶠ s in atTop, ∀ u ∈ Icc 0 T,
      ‖stochasticApproxInterp a (θ · ω) (s + u) -
        Φ u (stochasticApproxInterp a (θ · ω) s)‖ ≤ ε := by
  sorry

/-- The interpolation times start at zero. -/
@[simp] theorem stochasticApproxTime_zero (a : ℕ → ℝ) : stochasticApproxTime a 0 = 0 := by
  simp [stochasticApproxTime]

end CKSD
