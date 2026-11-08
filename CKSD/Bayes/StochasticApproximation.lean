module

public import CKSD.Bayes.Basic
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Stochastic approximation: Robbins–Monro and the ODE method

For the recursion `θₙ₊₁ = θₙ - aₙ(h(θₙ) + Mₙ₊₁)` in a finite-dimensional real inner product space
the limiting equation is `θ' = -h(θ)`. Its flow is specified by its defining differential equation
(`IsFlowOf`), which determines it uniquely for Lipschitz `h`. Invariant and internally chain
transitive sets follow Benaïm, the limit set of a sequence is the set of its cluster points, and
the interpolated process is piecewise linear between the times `tₙ = ∑_{k<n} aₖ`.

## Main definitions

* `CKSD.IsRobbinsMonroScheme`: the standing hypotheses on the recursion — adapted iterates and
  martingale-difference noise with a conditional second-moment bound, and Robbins–Monro steps
  `aₙ > 0`, `∑ aₙ = ∞`, `∑ aₙ² < ∞`.
* `CKSD.IsFlowOf`, `CKSD.IsInvariantSet`, `CKSD.IsInternallyChainTransitive`, `CKSD.limitSet`:
  flows, invariant and internally chain transitive sets, and limit sets.
* `CKSD.stochasticApproxTime`, `CKSD.stochasticApproxInterp`: interpolation times and the
  piecewise-linear interpolated process.

## Main results

* `CKSD.ae_tendsto_robbins_monro`: almost-sure convergence of Robbins–Monro under a strongly
  monotone Lipschitz field and bounded conditional noise variance (GAPS 104.40).
* `CKSD.ae_isInternallyChainTransitive_limitSet`: Benaïm's limit-set theorem (GAPS 104.49).
* `CKSD.ae_tendsto_equilibrium_of_chainTransitive`: convergence to an equilibrium when the only
  internally chain transitive sets are equilibria (GAPS 104.49).
* `CKSD.ae_asymptotic_pseudotrajectory`: the interpolated process is an asymptotic
  pseudotrajectory of the flow (GAPS 104.49).
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
theorem tendsto_of_limitSet_eq_singleton {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
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

section Robbins

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- GAPS 104.40: almost-sure convergence of the Robbins–Monro recursion. If `h` is Lipschitz with
`h θ⋆ = 0` and `⟪θ - θ⋆, h θ⟫ ≥ m ‖θ - θ⋆‖²` for some `m > 0`, the initial state is square
integrable, and the conditional noise variance is bounded by a constant `K`, then `θₙ → θ⋆`
almost surely. -/
theorem ae_tendsto_robbins_monro (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Filtration ℕ (inferInstance : MeasurableSpace Ω)) (h : E → E) (a : ℕ → ℝ) (K : ℝ)
    (θ M : ℕ → Ω → E) (hRM : IsRobbinsMonroScheme μ F h a (fun _ ↦ K) θ M)
    (hθ2 : MemLp (θ 0) 2 μ) (L : ℝ≥0) (hL : LipschitzWith L h) (θ₀ : E)
    (hz : h θ₀ = 0) (m : ℝ) (hm : 0 < m)
    (hdrift : ∀ x, m * ‖x - θ₀‖ ^ 2 ≤ inner ℝ (x - θ₀) (h x)) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ θ n ω) atTop (𝓝 θ₀) := by
  sorry

/-- GAPS 104.49: Benaïm's limit-set theorem. Under Robbins–Monro steps, martingale-difference noise
with conditional second moment at most `K(1 + ‖θₙ‖²)`, a Lipschitz field, and a.s. bounded iterates,
the limit set is a.s. a compact connected internally chain transitive invariant set of the flow
of `θ' = -h(θ)`. -/
theorem ae_isInternallyChainTransitive_limitSet (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Filtration ℕ (inferInstance : MeasurableSpace Ω)) (h : E → E) (a : ℕ → ℝ) (K : ℝ)
    (θ M : ℕ → Ω → E) (hRM : IsRobbinsMonroScheme μ F h a (fun x ↦ K * (1 + ‖x‖ ^ 2)) θ M)
    (L : ℝ≥0) (hL : LipschitzWith L h) (Φ : ℝ → E → E) (hΦ : IsFlowOf h Φ)
    (hbdd : ∀ᵐ ω ∂μ, BddAbove (range fun n ↦ ‖θ n ω‖)) :
    ∀ᵐ ω ∂μ, IsCompact (limitSet (θ · ω)) ∧ IsConnected (limitSet (θ · ω)) ∧
      IsInternallyChainTransitive Φ (limitSet (θ · ω)) := by
  sorry

/-- GAPS 104.49: if the only compact connected internally chain transitive invariant sets are
equilibria, the iterates converge almost surely to a possibly random equilibrium. -/
theorem ae_tendsto_equilibrium_of_chainTransitive (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Filtration ℕ (inferInstance : MeasurableSpace Ω)) (h : E → E) (a : ℕ → ℝ) (K : ℝ)
    (θ M : ℕ → Ω → E) (hRM : IsRobbinsMonroScheme μ F h a (fun x ↦ K * (1 + ‖x‖ ^ 2)) θ M)
    (L : ℝ≥0) (hL : LipschitzWith L h) (Φ : ℝ → E → E) (hΦ : IsFlowOf h Φ)
    (hbdd : ∀ᵐ ω ∂μ, BddAbove (range fun n ↦ ‖θ n ω‖))
    (hequil : ∀ A : Set E, IsCompact A → IsConnected A →
      IsInternallyChainTransitive Φ A → ∃ x, A = {x} ∧ h x = 0) :
    ∀ᵐ ω ∂μ, ∃ x, h x = 0 ∧ Tendsto (θ · ω) atTop (𝓝 x) := by
  have hlimit := ae_isInternallyChainTransitive_limitSet μ F h a K θ M hRM L hL Φ hΦ hbdd
  filter_upwards [hlimit, hbdd] with ω hω hbω
  obtain ⟨x, hx, heq⟩ := hequil _ hω.1 hω.2.1 hω.2.2
  exact ⟨x, heq, tendsto_of_limitSet_eq_singleton _ hbω x hx⟩

/-- GAPS 104.49: the interpolated process is almost surely an asymptotic pseudotrajectory of the
flow: `sup_{0 ≤ u ≤ T} ‖θ̄(s + u) - Φᵤ(θ̄(s))‖ → 0` as `s → ∞`, for every `T > 0`. -/
theorem ae_asymptotic_pseudotrajectory (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Filtration ℕ (inferInstance : MeasurableSpace Ω)) (h : E → E) (a : ℕ → ℝ) (K : ℝ)
    (θ M : ℕ → Ω → E) (hRM : IsRobbinsMonroScheme μ F h a (fun x ↦ K * (1 + ‖x‖ ^ 2)) θ M)
    (L : ℝ≥0) (hL : LipschitzWith L h) (Φ : ℝ → E → E) (hΦ : IsFlowOf h Φ)
    (hbdd : ∀ᵐ ω ∂μ, BddAbove (range fun n ↦ ‖θ n ω‖)) (T : ℝ) (hT : 0 < T) :
    ∀ᵐ ω ∂μ, ∀ ε > 0, ∀ᶠ s in atTop, ∀ u ∈ Icc 0 T,
      ‖stochasticApproxInterp a (θ · ω) (s + u) -
        Φ u (stochasticApproxInterp a (θ · ω) s)‖ ≤ ε := by
  sorry

end Robbins

/-- The interpolation times start at zero. -/
@[simp] theorem stochasticApproxTime_zero (a : ℕ → ℝ) : stochasticApproxTime a 0 = 0 := by
  simp [stochasticApproxTime]

end CKSD
