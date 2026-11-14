module

public import CKSD.Bayes.Basic
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic


/-!
# Flows, limit sets, and Robbins–Monro schemes

This module specifies autonomous flows, internally chain transitive sets, stochastic
approximation interpolation, and martingale-difference noise hypotheses. The interpolation uses
positive step sizes and is affine on the intervals between successive cumulative step sums.
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

/-- A bounded sequence in a proper metric space converges if its limit set is a singleton. -/
theorem tendsto_of_limit_set_eq_singleton {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    (u : ℕ → E) (hbdd : BddAbove (range fun n ↦ ‖u n‖)) (x : E)
    (hlim : limitSet u = {x}) : Tendsto u atTop (𝓝 x) := by
  obtain ⟨R, hR⟩ := hbdd
  apply (isCompact_closedBall (0 : E) R).tendsto_nhds_of_unique_mapClusterPt
    (Eventually.of_forall fun n ↦ ?_)
  · intro y _ hy
    have hymem : y ∈ limitSet u :=
      mem_iInter.2 (mapClusterPt_atTop_iff_forall_mem_closure.1 hy)
    simpa only [hlim, mem_singleton_iff] using hymem
  · simpa only [Metric.mem_closedBall, dist_zero_right] using hR (mem_range_self n)

/-- Interpolation times `tₙ = ∑_{k<n} aₖ`. -/
def stochasticApproxTime (a : ℕ → ℝ) (n : ℕ) : ℝ := ∑ k ∈ Finset.range n, a k

/-- Piecewise-linear interpolation of the iterates, linear on each `[tₙ, tₙ₊₁]`. -/
def stochasticApproxInterp {E : Type*} [AddCommGroup E] [Module ℝ E] (a : ℕ → ℝ)
    (θ : ℕ → E) (s : ℝ) : E :=
  let n := sSup {n : ℕ | stochasticApproxTime a n ≤ s}
  θ n + ((s - stochasticApproxTime a n) / a n) • (θ (n + 1) - θ n)

/-- Standing hypotheses of the Robbins–Monro recursion `θₙ₊₁ = θₙ - aₙ(h(θₙ) + Mₙ₊₁)`: the iterates
and the noise are adapted to the filtration `F`, the noise is a square-integrable martingale
difference sequence whose conditional second moment given `Fₙ` is at most `σ²(θₙ)`, and the steps
satisfy the Robbins–Monro conditions. -/
structure IsRobbinsMonroScheme {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E]
    (μ : Measure Ω) (F : Filtration ℕ (inferInstance : MeasurableSpace Ω)) (h : E → E)
    (a : ℕ → ℝ) (σ2 : E → ℝ) (θ M : ℕ → Ω → E) : Prop where
  /-- The iterates are adapted. -/
  measurable_iterate : ∀ n, Measurable[F n] (θ n)
  /-- The noise is adapted. -/
  measurable_noise : ∀ n, Measurable[F n] (M n)
  /-- The noise is square integrable. -/
  memLp_noise : ∀ n, MemLp (M n) 2 μ
  /-- The noise is a martingale difference sequence. -/
  condExp_noise : ∀ n, μ[M (n + 1) | F n] =ᵐ[μ] fun _ ↦ 0
  /-- Conditional second-moment bound `𝔼[‖Mₙ₊₁‖² | Fₙ] ≤ σ²(θₙ)`. -/
  condExp_sq_noise_le : ∀ n, μ[(fun ω ↦ ‖M (n + 1) ω‖ ^ 2) | F n] ≤ᵐ[μ] fun ω ↦ σ2 (θ n ω)
  /-- The steps are positive. -/
  step_pos : ∀ n, 0 < a n
  /-- The squared steps are summable. -/
  summable_sq_step : Summable fun n ↦ a n ^ 2
  /-- The steps are not summable. -/
  tendsto_sum_step : Tendsto (fun n ↦ ∑ k ∈ Finset.range n, a k) atTop atTop
  /-- The recursion holds almost surely. -/
  recursion : ∀ n, ∀ᵐ ω ∂μ, θ (n + 1) ω = θ n ω - a n • (h (θ n ω) + M (n + 1) ω)

end CKSD
