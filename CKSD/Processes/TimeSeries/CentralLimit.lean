module

public import CKSD.Processes.Basic
public import Mathlib.Probability.Martingale.Basic

/-!
# Central limit theorems for dependent data and sample autocorrelations

## Main results

* `CKSD.tendstoInDistribution_martingale_array_sum` (GAPS 106.1): the martingale central limit
  theorem for triangular arrays of square-integrable martingale differences under convergence
  of the conditional variances and the conditional Lindeberg condition.
* `CKSD.tendstoInDistribution_sample_autocorrelations` (GAPS 106.4, independent case of
  Bartlett's theorem): for iid observations with finite positive variance,
  `√n (ρ̂(1), …, ρ̂(m)) ⇒ N(0, I_m)`.

The general linear-process form of Bartlett's theorem is not covered.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace CKSD

/-- GAPS 106.1: triangular-array martingale central limit theorem. For each `n`, let
`X n 0, …, X n (k n - 1)` be square-integrable martingale differences for the filtration `F n`
(`X n j` is `F n (j + 1)`-measurable with `𝔼[X n j | F n j] = 0`). If
`∑_j 𝔼[X_{n,j}² | F n j] → v` and `∑_j 𝔼[X_{n,j}² 1{|X_{n,j}| > ε} | F n j] → 0` in probability
for every `ε > 0`, then `∑_j X_{n,j} ⇒ N(0, v)`. The limit `v` is automatically nonnegative. -/
theorem tendstoInDistribution_martingale_array_sum {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : ℕ → Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (X : ℕ → ℕ → Ω → ℝ) (k : ℕ → ℕ)
    (ha : ∀ n j, Measurable[F n (j + 1)] (X n j))
    (h2 : ∀ n j, MemLp (X n j) 2 μ)
    (h0 : ∀ n j, μ[X n j | F n j] =ᵐ[μ] fun _ ↦ 0) (v : ℝ)
    (hvar : TendstoInMeasure μ (fun (n : ℕ) ω ↦
      ∑ j ∈ Finset.range (k n), μ[(fun ω ↦ X n j ω ^ 2) | F n j] ω) atTop (fun _ ↦ v))
    (hlin : ∀ ε > 0, TendstoInMeasure μ (fun (n : ℕ) ω ↦
      ∑ j ∈ Finset.range (k n),
        μ[(fun ω ↦ if ε < |X n j ω| then X n j ω ^ 2 else 0) | F n j] ω) atTop (fun _ ↦ 0)) :
    TendstoInDistribution (fun (n : ℕ) ω ↦ ∑ j ∈ Finset.range (k n), X n j ω) atTop id (fun _ ↦ μ)
      (gaussianReal 0 (Real.toNNReal v)) := by
  sorry

/-- GAPS 106.4, independent-observation case of Bartlett's theorem: for iid observations with
finite positive variance, the normalized sample autocorrelations
`√n ρ̂(h) = √n γ̂(h) / γ̂(0)` at lags `h = 1, …, m` converge jointly in law to independent
standard normal variables. Finite variance follows from `0 < Var`
(`memLp_id_two_of_variance_pos`). -/
theorem tendstoInDistribution_sample_autocorrelations {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure ℝ) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hiid : IsIndependentIdenticallyDistributed μ X P)
    (hv : 0 < Var[id; P]) (m : ℕ) :
    TendstoInDistribution (fun (n : ℕ) ω ↦ (WithLp.toLp 2 fun i : Fin m ↦
      Real.sqrt n * sampleAutocovariance X (i.val + 1) n ω / sampleAutocovariance X 0 n ω))
      atTop id (fun _ ↦ μ)
      (stdGaussian (EuclideanSpace ℝ (Fin m))) := by
  sorry

end CKSD
