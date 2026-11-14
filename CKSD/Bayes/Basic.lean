module

public import CKSD.Inference.Basic
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Basic


/-!
# Basic objects for Bayesian computation

This file collects the elementary objects shared by the Bayesian and Monte Carlo files of
Section 104: the Poisson likelihood used in empirical Bayes, the finite-state Metropolis–Hastings
kernel, the leapfrog integrator of Hamiltonian Monte Carlo, and the normal-location posterior.
It also contains two general probabilistic lemmas used by several strong-law arguments.

## Main definitions

* `CKSD.poissonMass θ x`: the Poisson mass `e^{-θ} θ^x / x!`, for an arbitrary real `θ`.
* `CKSD.metropolisAcceptance`, `CKSD.metropolisTransition`: the Metropolis–Hastings acceptance
  probability and transition matrix of a proposal matrix `q` and positive target weights `π` on
  a finite state space.
* `CKSD.leapfrogStep`, `CKSD.momentumFlip`: one leapfrog step with identity mass matrix, and the
  momentum reversal `(x, p) ↦ (x, -p)`.
* `CKSD.normalPosterior`: the posterior of a normal location with known variance under a prior
  density, as a function of the sample size and the sample mean.

## Main results

* `CKSD.poisson_mass_coe`: `poissonMass` agrees with Mathlib's `poissonMeasure` on singletons.
* `CKSD.integral_comp_eq_sum_measure_real`: the integral of a function of a finitely-valued random
  variable is the sum of its values weighted by their probabilities.
* `CKSD.ae_tendsto_div_of_summable_integral_sq_div`: if `∑ₖ 𝔼[Zₖ²] / bₖ² < ∞`, then
  `Zₖ / bₖ → 0` almost surely (Chebyshev and Borel–Cantelli).
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace CKSD

/-- Poisson likelihood `e^{-θ} θ^x / x!` as a real number. For `θ ≥ 0` it is the Poisson mass of
`x` (`poisson_mass_coe`); it is defined for every real `θ`, so that it can be integrated against an
arbitrary prior on `ℝ`. -/
def poissonMass (θ : ℝ) (x : ℕ) : ℝ := Real.exp (-θ) * θ ^ x / Nat.factorial x

/-- For a nonnegative intensity, `poissonMass` is the mass of Mathlib's Poisson law. -/
theorem poisson_mass_coe (r : ℝ≥0) (x : ℕ) :
    poissonMass r x = (poissonMeasure r).real {x} :=
  (poissonMeasure_real_singleton r x).symm

/-- Metropolis–Hastings acceptance probability `min (1, π(y) q(y,x) / (π(x) q(x,y)))` of a move
from `x` to `y`, with the convention that it is one when `π(x) q(x,y) = 0`. -/
def metropolisAcceptance {ι : Type*} (π : ι → ℝ) (q : Matrix ι ι ℝ) (x y : ι) : ℝ :=
  if π x * q x y = 0 then 1 else min 1 (π y * q y x / (π x * q x y))

/-- Metropolis–Hastings transition matrix of a proposal matrix `q` and target weights `π`: the
off-diagonal entries are `q(x,y)` times the acceptance probability, and the diagonal also
carries the total probability of rejected proposals. -/
def metropolisTransition {ι : Type*} [Fintype ι] [DecidableEq ι] (π : ι → ℝ)
    (q : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  fun x y ↦ q x y * metropolisAcceptance π q x y +
    if x = y then 1 - ∑ z, q x z * metropolisAcceptance π q x z else 0

/-- One leapfrog step `p ↦ p - (h/2) g(x)`, `x ↦ x + h p`, `p ↦ p - (h/2) g(x)` with identity mass
matrix, step size `h` and force `g` (the gradient of the potential). -/
def leapfrogStep {d : ℕ} (g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (h : ℝ) (z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) :=
  let p := z.2 - (h / 2) • g z.1
  let x := z.1 + h • p
  (x, p - (h / 2) • g x)

/-- Momentum reversal `(x, p) ↦ (x, -p)` on phase space. -/
def momentumFlip {E : Type*} [Neg E] (z : E × E) : E × E := (z.1, -z.2)

/-- Posterior of a normal location with known variance `v` under a prior density `prior`, after
`n` observations with sample mean `mean`: the prior density times `exp(-n (θ - mean)² / (2v))`,
normalized. Likelihood factors that do not depend on the parameter cancel in the normalization. -/
def normalPosterior (prior : ℝ → ℝ) (v : ℝ≥0) (n : ℕ) (mean : ℝ) : Measure ℝ :=
  let density := fun θ ↦ prior θ * Real.exp (-(n : ℝ) * (θ - mean) ^ 2 / (2 * v))
  (ENNReal.ofReal (∫ θ, density θ))⁻¹ • volume.withDensity (fun θ ↦ ENNReal.ofReal (density θ))

/-- The integral of a function of a random variable with finitely many values is the sum of the
values weighted by their probabilities. -/
theorem integral_comp_eq_sum_measure_real {Ω β : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]
    (Y : Ω → β) (hY : Measurable Y) (F : β → ℝ) :
    ∫ ω, F (Y ω) ∂μ = ∑ b, μ.real (Y ⁻¹' {b}) * F b := by
  rw [← integral_map hY.aemeasurable
    (measurable_of_finite F).aestronglyMeasurable, integral_fintype Integrable.of_finite]
  simp [map_measureReal_apply hY (measurableSet_singleton _)]

/-- A function of a random variable with finitely many values is integrable under a finite
measure. -/
theorem integrable_comp_of_finite {Ω β : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] [Finite β] [MeasurableSpace β] [MeasurableSingletonClass β]
    (Y : Ω → β) (hY : Measurable Y) (F : β → ℝ) : Integrable (fun ω ↦ F (Y ω)) μ :=
  (Integrable.of_finite (μ := μ.map Y)).comp_measurable hY

/-- If `∑ₖ 𝔼[Zₖ²] / bₖ² < ∞`, then `Zₖ / bₖ → 0` almost surely, by Chebyshev's inequality and the
Borel–Cantelli lemma. -/
theorem ae_tendsto_div_of_summable_integral_sq_div {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : ℕ → Ω → ℝ) (b : ℕ → ℝ) (hb : ∀ k, 0 < b k)
    (hint : ∀ k, Integrable (fun ω ↦ Z k ω ^ 2) μ)
    (hsum : Summable fun k ↦ (∫ ω, Z k ω ^ 2 ∂μ) / b k ^ 2) :
    ∀ᵐ ω ∂μ, Tendsto (fun k ↦ Z k ω / b k) atTop (𝓝 0) := by
  have key (j : ℕ) : ∀ᵐ ω ∂μ, ∀ᶠ k in atTop, |Z k ω / b k| < 1 / ((j : ℝ) + 1) := by
    set δ : ℝ := 1 / ((j : ℝ) + 1) with hδ
    have hδ0 : 0 < δ := by positivity
    set A : ℕ → Set Ω := fun k ↦ {ω | δ ^ 2 * b k ^ 2 ≤ Z k ω ^ 2} with hA
    set v : ℕ → ℝ := fun k ↦ (∫ ω, Z k ω ^ 2 ∂μ) / b k ^ 2 with hv
    have hv0 (k : ℕ) : 0 ≤ v k :=
      div_nonneg (integral_nonneg fun ω ↦ sq_nonneg _) (sq_nonneg _)
    have hAb (k : ℕ) : μ (A k) ≤ ENNReal.ofReal (v k / δ ^ 2) := by
      rw [← ofReal_measureReal]
      refine ENNReal.ofReal_le_ofReal ?_
      have hε : 0 < δ ^ 2 * b k ^ 2 := by have := hb k; positivity
      have hm := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ fun ω ↦ sq_nonneg _)
        (hint k) (δ ^ 2 * b k ^ 2)
      rw [show v k / δ ^ 2 = (∫ ω, Z k ω ^ 2 ∂μ) / (δ ^ 2 * b k ^ 2) by
        simp only [hv]; field_simp, le_div_iff₀ hε, mul_comm]
      exact hm
    have htsum : ∑' k, μ (A k) ≠ ∞ := by
      refine ne_top_of_le_ne_top ?_
        (CompleteLattice.summable.tsum_le_tsum hAb CompleteLattice.summable)
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun k ↦ div_nonneg (hv0 k) (sq_nonneg _))
        (hsum.div_const _)]
      exact ENNReal.ofReal_ne_top
    filter_upwards [ae_eventually_notMem htsum] with ω hω
    filter_upwards [hω] with k hk
    simp only [hA, mem_ofPred_eq, not_le] at hk
    have hbk := hb k
    rw [abs_div, abs_of_pos hbk, div_lt_iff₀ hbk]
    have : |Z k ω| ^ 2 < (δ * b k) ^ 2 := by rw [sq_abs, mul_pow]; exact hk
    exact (pow_lt_pow_iff_left₀ (abs_nonneg _) (by positivity) two_ne_zero).1 this
  rw [← ae_all_iff] at key
  filter_upwards [key] with ω hω
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt hε
  obtain ⟨K, hK⟩ := (hω j).exists_forall_of_atTop
  exact ⟨K, fun k hk ↦ by rw [Real.dist_eq, sub_zero]; exact (hK k hk).trans hj⟩

/-- Integration of a vector-valued function against the empirical measure. -/
theorem integral_empirical_measure_vector {E F : Type*} [MeasurableSpace E]
    [MeasurableSingletonClass E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {N : ℕ} (x : Fin N → E) (f : E → F) :
    (∫ y, f y ∂empiricalMeasure N x) = (N : ℝ)⁻¹ • ∑ j, f (x j) := by
  rw [empiricalMeasure, integral_smul_measure, integral_finsetSum_measure]
  · simp
  · intro j _
    exact integrable_dirac (by finiteness)

end CKSD
