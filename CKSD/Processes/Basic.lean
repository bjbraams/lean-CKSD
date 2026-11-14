module

public import CKSD.Asymptotics.Basic


/-!
# Processes: basic definitions

Common notions for Section 106 (dependent data and stochastic models).

* Weak stationarity of a sequence in an inner-product space, in the Hilbert-space form
  `⟪X s, X t⟫ = ⟪X 0, X (t - s)⟫`; for centred square-integrable random variables this is
  weak stationarity of the process in `L²`.
* Independent identically distributed centred noise on `ℤ` with a prescribed variance, the
  innovation sequence of linear, ARMA and GARCH models.
* The sample autocovariance, and the Nelson–Aalen and Kaplan–Meier estimators of right-censored
  survival data.

## Main definitions

* `CKSD.IsWeaklyStationary`: shift-invariance of the Gram matrix of a sequence on `ℤ`.
* `CKSD.IsIIDNoise`: an iid sequence on `ℤ` with mean `0` and variance `σ² > 0`.
* `CKSD.sampleAutocovariance`: `γ̂(h) = n⁻¹ ∑_{i < n - h} (X_{i+h} - X̄)(X_i - X̄)`.
* `CKSD.riskSetSize`, `CKSD.nelsonAalenEstimator`, `CKSD.kaplanMeierEstimator`.

## Main results

* `CKSD.IsWeaklyStationary.inner_eq_inner_sub_zero`: the equivalent form
  `⟪X s, X t⟫ = ⟪X (s - t), X 0⟫`.
* `CKSD.IsIIDNoise.mem_lp_two`, `CKSD.IsIIDNoise.integral_eq_zero'`,
  `CKSD.IsIIDNoise.integral_sq'`: the moments of every term, not only of `Z 0`.
* `CKSD.mem_lp_id_two_of_variance_pos`: a law with positive variance is square integrable.

## Conventions

Observations of a time series are `X 0, …, X (n - 1)`. In the survival estimators the `i`th
subject has failure time `T i` and censoring time `C i`, and one observes `min (T i) (C i)` and
whether `T i ≤ C i`.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- A sequence `X : ℤ → H` in an inner-product space is weakly stationary when its Gram matrix
is shift invariant: `⟪X s, X t⟫ = ⟪X 0, X (t - s)⟫` for all `s, t`. Applied to centred
square-integrable random variables in `L²`, this is weak (second-order) stationarity of the
process. -/
def IsWeaklyStationary (𝕜 : Type*) {H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] (X : ℤ → H) : Prop :=
  ∀ s t, inner 𝕜 (X s) (X t) = inner 𝕜 (X 0) (X (t - s))

/-- For a weakly stationary sequence, `⟪X s, X t⟫ = ⟪X (s - t), X 0⟫`. -/
theorem IsWeaklyStationary.inner_eq_inner_sub_zero {𝕜 H : Type*} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] {X : ℤ → H} (hX : IsWeaklyStationary 𝕜 X)
    (s t : ℤ) : inner 𝕜 (X s) (X t) = inner 𝕜 (X (s - t)) (X 0) := by
  rw [hX s t, hX (s - t) 0]
  congr 2
  ring

/-- An iid centred noise sequence on `ℤ` with variance `σ² > 0`: the `Z t` are measurable,
mutually independent and identically distributed, `𝔼 Z_0 = 0` and `𝔼 Z_0² = σ²`. Square
integrability is not a separate condition: it follows from `𝔼 Z_0² = σ² ≠ 0`
(`IsIIDNoise.mem_lp_two`). -/
structure IsIIDNoise {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (Z : ℤ → Ω → ℝ)
    (σsq : ℝ) : Prop where
  /-- Each `Z t` is measurable. -/
  measurable : ∀ t, Measurable (Z t)
  /-- The `Z t` are mutually independent. -/
  iIndepFun : iIndepFun Z μ
  /-- All `Z t` have the law of `Z 0`. -/
  map_eq : ∀ t, μ.map (Z t) = μ.map (Z 0)
  /-- The noise is centred. -/
  integral_eq_zero : ∫ ω, Z 0 ω ∂μ = 0
  /-- The noise has variance `σ²`. -/
  integral_sq : ∫ ω, Z 0 ω ^ 2 ∂μ = σsq
  /-- The variance is positive. -/
  pos : 0 < σsq

namespace IsIIDNoise

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {Z : ℤ → Ω → ℝ} {σsq : ℝ}

/-- Each term of an iid noise sequence has the law of `Z 0`. -/
theorem ident_distrib (hZ : IsIIDNoise μ Z σsq) (t : ℤ) : IdentDistrib (Z t) (Z 0) μ μ :=
  ⟨(hZ.measurable t).aemeasurable, (hZ.measurable 0).aemeasurable, hZ.map_eq t⟩

/-- Every term of an iid noise sequence is square integrable. -/
theorem mem_lp_two (hZ : IsIIDNoise μ Z σsq) (t : ℤ) : MemLp (Z t) 2 μ := by
  have h0 : MemLp (Z 0) 2 μ := by
    refine (memLp_two_iff_integrable_sq (hZ.measurable 0).aestronglyMeasurable).2 ?_
    exact Integrable.of_integral_ne_zero (by rw [hZ.integral_sq]; exact hZ.pos.ne')
  exact (hZ.ident_distrib t).memLp_iff.2 h0

/-- Every term of an iid noise sequence is centred. -/
theorem integral_eq_zero' (hZ : IsIIDNoise μ Z σsq) (t : ℤ) : ∫ ω, Z t ω ∂μ = 0 := by
  rw [(hZ.ident_distrib t).integral_eq, hZ.integral_eq_zero]

/-- Every term of an iid noise sequence has second moment `σ²`. -/
theorem integral_sq' (hZ : IsIIDNoise μ Z σsq) (t : ℤ) : ∫ ω, Z t ω ^ 2 ∂μ = σsq := by
  rw [← hZ.integral_sq]
  exact ((hZ.ident_distrib t).comp (measurable_id.pow_const 2)).integral_eq

end IsIIDNoise

/-- A real law with positive variance has a finite second moment: `0 < Var(P)` forces the
integrand `(x - 𝔼x)²` to be integrable, since a Bochner integral of a non-integrable function
is `0`. -/
theorem mem_lp_id_two_of_variance_pos {P : Measure ℝ} [IsProbabilityMeasure P]
    (hv : 0 < Var[id; P]) : MemLp id 2 P := by
  rw [variance_eq_integral aemeasurable_id] at hv
  have hint : Integrable (fun x : ℝ ↦ (x - ∫ y, id y ∂P) ^ 2) P :=
    Integrable.of_integral_ne_zero hv.ne'
  have h : MemLp (fun x : ℝ ↦ x - ∫ y, id y ∂P) 2 P :=
    (memLp_two_iff_integrable_sq (by fun_prop)).2 hint
  refine (h.add (memLp_const (∫ y, id y ∂P))).congr_norm (by fun_prop) (ae_of_all _ fun x ↦ ?_)
  simp

/-- The sample autocovariance `γ̂(h) = n⁻¹ ∑_{i < n - h} (X_{i+h} - X̄_n)(X_i - X̄_n)` at lag
`h` of `X 0, …, X (n - 1)`, with the sample mean `X̄_n` and divisor `n`. -/
def sampleAutocovariance {Ω : Type*} (X : ℕ → Ω → ℝ) (lag n : ℕ) (ω : Ω) : ℝ :=
  (∑ i ∈ Finset.range (n - lag),
    (X (i + lag) ω - sampleAverage X n ω) * (X i ω - sampleAverage X n ω)) / n

/-- The size `#{j < n : min (T j) (C j) ≥ min (T i) (C i)}` of the risk set at the observed time
of subject `i`. -/
def riskSetSize {Ω : Type*} (T C : ℕ → Ω → ℝ) (n i : ℕ) (ω : Ω) : ℕ :=
  ((Finset.range n).filter fun j ↦ min (T i ω) (C i ω) ≤ min (T j ω) (C j ω)).card

/-- The Nelson–Aalen estimator `Λ̂(t) = ∑ 1 / #(risk set)` of the cumulative hazard, with one
term for each subject `i < n` whose failure `T i ≤ C i` is observed by time `t`. -/
def nelsonAalenEstimator {Ω : Type*} (T C : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) (t : ℝ) : ℝ :=
  ∑ i ∈ Finset.range n, if T i ω ≤ C i ω ∧ T i ω ≤ t then
    (riskSetSize T C n i ω : ℝ)⁻¹ else 0

/-- The Kaplan–Meier estimator `Ŝ(t) = ∏ (1 - 1 / #(risk set))` of the survival function, with
one factor for each subject `i < n` whose failure `T i ≤ C i` is observed by time `t`. -/
def kaplanMeierEstimator {Ω : Type*} (T C : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) (t : ℝ) : ℝ :=
  ∏ i ∈ Finset.range n, if T i ω ≤ C i ω ∧ T i ω ≤ t then
    1 - (riskSetSize T C n i ω : ℝ)⁻¹ else 1

end CKSD
