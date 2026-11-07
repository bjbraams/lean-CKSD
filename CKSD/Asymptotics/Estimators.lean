module

public import CKSD.Asymptotics.Basic
public import TauCeti.Probability.Distributions.ChiSquared.Basic
public import TauCeti.Probability.Distributions.StudentT.Basic
public import TauCeti.Probability.Distributions.FisherSnedecor.Basic

/-!
# Asymptotics: Estimators

Sources: `GAPS.md`, `SYNOPSIS102.md`, and `STRUCTURE102.md`.
Declarations adapted from this project's section drafts.
The docstrings specify the scope of each result; `sorry` marks unfinished proofs.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- GAPS 102.1: the delta method and its stochastic linearization in Banach spaces. -/
theorem tendstoInDistribution_delta_method {Ω E F : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ℕ → Ω → E)
    (hT : ∀ n, Measurable (T n)) (θ : E) (ν : Measure E) [IsProbabilityMeasure ν]
    (g : E → F) (hg : Measurable g) (D : E →L[ℝ] F) (hd : HasFDerivAt g D θ)
    (hlim : TendstoInDistribution μ (fun n ω ↦ Real.sqrt n • (T n ω - θ)) ν) :
    TendstoInDistribution μ (fun n ω ↦ Real.sqrt n • (g (T n ω) - g θ)) (ν.map D) ∧
      TendstoInProbabilityConst μ (fun n ω ↦
        Real.sqrt n • (g (T n ω) - g θ) - D (Real.sqrt n • (T n ω - θ))) 0 := by
  sorry

/-- GAPS 102.6: asymptotic normality of a sample quantile. -/
theorem tendstoInDistribution_sampleQuantile {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure ℝ) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hiid : IsIndependentIdenticallyDistributed μ X P) (p q f : ℝ)
    (hp : p ∈ Ioo 0 1) (hq : cdf P q = p) (hf : 0 < f)
    (hd : HasDerivAt (cdf P) f q) :
    TendstoInDistribution μ (fun n ω ↦ Real.sqrt n * (sampleQuantile X n ω p - q))
      (gaussianReal 0 (Real.toNNReal (p * (1 - p) / f ^ 2))) := by
  sorry

/-- GAPS 102.7: the first-order Bahadur representation. -/
theorem tendstoInProbabilityConst_bahadur_remainder {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure ℝ) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hiid : IsIndependentIdenticallyDistributed μ X P) (p q f : ℝ)
    (hp : p ∈ Ioo 0 1) (hq : cdf P q = p) (hf : 0 < f)
    (hd : HasDerivAt (cdf P) f q) :
    TendstoInProbabilityConst μ (fun n ω ↦ Real.sqrt n *
      (sampleQuantile X n ω p - q - (p - empiricalCDF X n ω q) / f)) 0 := by
  sorry

/-- GAPS 102.8: the nondegenerate U-statistic CLT, with its first projection. -/
theorem tendstoInDistribution_uStatistic_of_nondegenerate
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure E) [IsProbabilityMeasure P]
    (X : ℕ → Ω → E) (hiid : IsIndependentIdenticallyDistributed μ X P) (m : ℕ)
    (h : (Fin (m + 1) → E) → ℝ) (hmeas : Measurable h)
    (hsym : ∀ (σ : Equiv.Perm (Fin (m + 1))) x, h (x ∘ σ) = h x)
    (h2 : MemLp h 2 (Measure.pi fun _ : Fin (m + 1) ↦ P)) :
    let θ := ∫ x, h x ∂(Measure.pi fun _ : Fin (m + 1) ↦ P);
    let g := fun x ↦ (∫ y, h (Fin.cases x y) ∂(Measure.pi fun _ : Fin m ↦ P)) - θ;
    ∀ (hv : 0 < variance P g),
    TendstoInDistribution μ (fun n ω ↦ Real.sqrt n *
      (uStatistic (m + 1) n h (fun i ↦ X i.val ω) - θ))
      (gaussianReal 0 (Real.toNNReal (((m + 1 : ℕ) : ℝ) ^ 2 * variance P g))) := by
  sorry

/-- GAPS 102.3, scalar smooth likelihood-score roots and their efficient expansion.
`ell` is the per-observation log likelihood; the score/information moment
identities and the local third-derivative envelope are explicit hypotheses. -/
theorem mle_asymptotic_linearization_and_normality
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (mu : Measure Ω) [IsProbabilityMeasure mu] (P : Measure E) [IsProbabilityMeasure P]
    (X : ℕ → Ω → E) (hiid : IsIndependentIdenticallyDistributed mu X P) (ell : ℝ → E → ℝ)
    (hm : ∀ theta, Measurable (ell theta)) (hsmooth : ∀ x, ContDiff ℝ 3 (fun theta ↦ ell theta x))
    (theta₀ I : ℝ) (hI : 0 < I) (r : ℝ) (hr : 0 < r) (M : E → ℝ)
    (hM : Integrable M P)
    (henv : ∀ x theta, |theta - theta₀| < r →
      |deriv (deriv (deriv (fun t ↦ ell t x))) theta| ≤ M x)
    (hscore : MemLp (fun x ↦ deriv (fun t ↦ ell t x) theta₀) 2 P)
    (hmean : (∫ x, deriv (fun t ↦ ell t x) theta₀ ∂P) = 0)
    (hvar : (∫ x, deriv (fun t ↦ ell t x) theta₀ ^ 2 ∂P) = I)
    (hhess : Integrable (fun x ↦ deriv (deriv (fun t ↦ ell t x)) theta₀) P)
    (hinfo : (∫ x, deriv (deriv (fun t ↦ ell t x)) theta₀ ∂P) = -I)
    (T : ℕ → Ω → ℝ) (hT : ∀ n, Measurable (T n)) (hcons : TendstoInProbabilityConst mu T theta₀)
    (hroot : ∀ n : ℕ, 1 ≤ n → ∀ᵐ w ∂mu,
      (∑ i ∈ Finset.range n, deriv (fun t ↦ ell t (X i w)) (T n w)) = 0) :
    TendstoInProbabilityConst mu (fun n w ↦ Real.sqrt n * (T n w - theta₀) -
      (I * Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n,
        deriv (fun t ↦ ell t (X i w)) theta₀) 0 ∧
      TendstoInDistribution mu (fun n w ↦ Real.sqrt n * (T n w - theta₀))
        (gaussianReal 0 (Real.toNNReal I⁻¹)) := by
  sorry

/-- GAPS 102.4, the scalar Z-estimator theorem under a square-integrable Lipschitz envelope. -/
theorem z_estimator_asymptotic_linearization_and_normality
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (mu : Measure Ω) [IsProbabilityMeasure mu] (P : Measure E) [IsProbabilityMeasure P]
    (X : ℕ → Ω → E) (hiid : IsIndependentIdenticallyDistributed mu X P) (psi : ℝ → E → ℝ)
    (hm : Measurable (Function.uncurry psi)) (theta₀ D : ℝ) (hD : D ≠ 0)
    (hpsi : MemLp (psi theta₀) 2 P) (h0 : (∫ x, psi theta₀ x ∂P) = 0)
    (hd : HasDerivAt (fun theta ↦ ∫ x, psi theta x ∂P) D theta₀)
    (r : ℝ) (hr : 0 < r) (M : E → ℝ) (hM : MemLp M 2 P)
    (hlip : ∀ x a b, |a - theta₀| < r → |b - theta₀| < r →
      |psi a x - psi b x| ≤ M x * |a - b|)
    (T : ℕ → Ω → ℝ) (hT : ∀ n, Measurable (T n)) (hcons : TendstoInProbabilityConst mu T theta₀)
    (hroot : TendstoInProbabilityConst mu (fun n w ↦ (Real.sqrt n)⁻¹ *
      ∑ i ∈ Finset.range n, psi (T n w) (X i w)) 0) :
    TendstoInProbabilityConst mu (fun n w ↦ Real.sqrt n * (T n w - theta₀) +
      (D * Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, psi theta₀ (X i w)) 0 ∧
      TendstoInDistribution mu (fun n w ↦ Real.sqrt n * (T n w - theta₀))
        (gaussianReal 0 (Real.toNNReal (variance P (psi theta₀) / D ^ 2))) := by
  sorry


end CKSD
