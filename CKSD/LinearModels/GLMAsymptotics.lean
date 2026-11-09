module

public import CKSD.Inference.Basic
public import TauCeti.Probability.Distributions.ChiSquared.Basic

/-!
# Asymptotics of the generalised linear model with canonical link

An exponential dispersion law with cumulant function `b` and dispersion `φ > 0` has density
`exp((yθ - b θ) / φ)` with respect to a dominating measure `ν` on `ℝ` (the factor `exp c(y, φ)`
is absorbed into `ν`). In the canonical-link model the natural parameter of the response is the
linear predictor `θ = ⟪x, β⟫`, so the mean is `b'(⟪x, β⟫)`, the variance is `φ b''(⟪x, β⟫)`,
the weight is `w(x) = b''(⟪x, β⟫)`, and the likelihood equations are
`∑ᵢ xᵢ (Yᵢ - b'(⟪xᵢ, β⟫)) = 0`.

The pairs `(xᵢ, Yᵢ)` are independent and identically distributed; the conditional law of the
response given the covariate is supplied by a Markov kernel.

## Main definitions

* `CKSD.exponentialDispersionLaw`: the law `exp((yθ - b θ) / φ) ν(dy)`.
* `CKSD.canonicalGLMInformation`: `J = E[x xᵀ b''(⟪x, β⟫)]`.
* `CKSD.canonicalGLMLogLikelihood`, `CKSD.IsCanonicalGLMRoot`: the log likelihood and the
  likelihood equations of the first `n` observations.

## Main results

* `CKSD.tendstoInDistribution_canonicalGLM_root`: asymptotic normality
  `√n (β̂ - β) ⇒ N(0, φ J⁻¹)` of consistent roots, and its studentized form.
* `CKSD.tendstoInDistribution_canonicalGLM_deviance`: the deviance difference of nested
  models is asymptotically chi-squared.

## References

* P. McCullagh and J. A. Nelder, *Generalized Linear Models*, 2nd ed., Chapman and Hall, 1989.
* L. Fahrmeir and H. Kaufmann, *Consistency and asymptotic normality of the maximum likelihood
  estimator in generalized linear models*, Ann. Statist. 13 (1985).
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators MatrixOrder

namespace CKSD

variable {p : ℕ}

/-- The exponential dispersion law with cumulant `b`, dispersion `φ`, and natural parameter
`θ`, relative to the dominating measure `ν`. -/
def exponentialDispersionLaw (ν : Measure ℝ) (b : ℝ → ℝ) (φ θ : ℝ) : Measure ℝ :=
  ν.withDensity fun y ↦ ENNReal.ofReal (Real.exp ((y * θ - b θ) / φ))

/-- The canonical-link information matrix `J = E[x xᵀ b''(⟪x, β⟫)]` of one covariate draw. -/
def canonicalGLMInformation (Px : Measure (EuclideanSpace ℝ (Fin p))) (b : ℝ → ℝ)
    (β : EuclideanSpace ℝ (Fin p)) : Matrix (Fin p) (Fin p) ℝ :=
  fun i j ↦ ∫ x, x i * x j * iteratedDeriv 2 b (inner ℝ x β) ∂Px

/-- The canonical-link log likelihood of the first `n` observations, up to terms free of `β`,
with the dispersion kept. -/
def canonicalGLMLogLikelihood (b : ℝ → ℝ) (φ : ℝ) (n : ℕ)
    (x : ℕ → EuclideanSpace ℝ (Fin p)) (y : ℕ → ℝ) (β : EuclideanSpace ℝ (Fin p)) : ℝ :=
  ∑ i ∈ Finset.range n, (y i * inner ℝ (x i) β - b (inner ℝ (x i) β)) / φ

/-- `β` solves the canonical-link likelihood equations for the first `n` observations. -/
def IsCanonicalGLMRoot (b : ℝ → ℝ) (n : ℕ) (x : ℕ → EuclideanSpace ℝ (Fin p)) (y : ℕ → ℝ)
    (β : EuclideanSpace ℝ (Fin p)) : Prop :=
  ∑ i ∈ Finset.range n, (y i - deriv b (inner ℝ (x i) β)) • x i = 0

/-- GAPS 105.3, canonical-link form: for independent and identically distributed pairs
`(xᵢ, Yᵢ)` whose response given the covariate is exponential-dispersion with natural parameter
`⟪x, β⟫`, with covariates bounded by `R`, smooth cumulant function, natural parameter space all
of `ℝ`, and nonsingular `J = E[x xᵀ b''(⟪x, β⟫)]`, every consistent root `β̂` of the likelihood
equations satisfies `√n (β̂ - β) ⇒ N(0, φ J⁻¹)`, and
`φ̂^{-1/2} J^{1/2} √n (β̂ - β) ⇒ N(0, I_p)` for every consistent `φ̂`. Restrictions of scope:
canonical link (`g = (b')⁻¹`), bounded covariates, and natural parameter space `ℝ`; the
general twice-differentiable link is not covered. -/
theorem tendstoInDistribution_canonicalGLM_root {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Measure ℝ) (b : ℝ → ℝ) (hb : ContDiff ℝ 3 b)
    (φ : ℝ) (hφ : 0 < φ)
    (hlaw : ∀ θ, IsProbabilityMeasure (exponentialDispersionLaw ν b φ θ))
    (Px : Measure (EuclideanSpace ℝ (Fin p))) [IsProbabilityMeasure Px]
    (κ : Kernel (EuclideanSpace ℝ (Fin p)) ℝ) [IsMarkovKernel κ]
    (β : EuclideanSpace ℝ (Fin p))
    (hκ : ∀ x, κ x = exponentialDispersionLaw ν b φ (inner ℝ x β))
    (R : ℝ) (hR : ∀ᵐ x ∂Px, ‖x‖ ≤ R)
    (X : ℕ → Ω → EuclideanSpace ℝ (Fin p)) (Y : ℕ → Ω → ℝ)
    (hiid : IsIndependentIdenticallyDistributed P (fun i ω ↦ (X i ω, Y i ω)) (Px ⊗ₘ κ))
    (hJ : (canonicalGLMInformation Px b β).PosDef)
    (βhat : ℕ → Ω → EuclideanSpace ℝ (Fin p)) (hβm : ∀ n, Measurable (βhat n))
    (hcons : TendstoInMeasure P βhat atTop (fun _ ↦ β))
    (hroot : ∀ n, 1 ≤ n → ∀ᵐ ω ∂P,
      IsCanonicalGLMRoot b n (fun i ↦ X i ω) (fun i ↦ Y i ω) (βhat n ω))
    (φhat : ℕ → Ω → ℝ) (hφm : ∀ n, Measurable (φhat n))
    (hφcons : TendstoInMeasure P φhat atTop (fun _ ↦ φ)) :
    TendstoInDistribution (fun (n : ℕ) ω ↦ Real.sqrt n • (βhat n ω - β)) atTop id (fun _ ↦ P)
        (multivariateGaussian 0 (φ • (canonicalGLMInformation Px b β)⁻¹)) ∧
      TendstoInDistribution (fun (n : ℕ) ω ↦ (Real.sqrt (φhat n ω))⁻¹ •
          Matrix.toEuclideanLin (CFC.sqrt (canonicalGLMInformation Px b β))
            (Real.sqrt n • (βhat n ω - β))) atTop id (fun _ ↦ P)
        (multivariateGaussian 0 1) := by
  sorry

/-- GAPS 105.3, deviance test for nested canonical-link models with known dispersion: if the
true coefficient lies in a subspace `L`, `β̂` is a consistent root of the full likelihood
equations and `β̃` a consistent maximizer of the likelihood over `L`, then the scaled deviance
difference `2 (ℓₙ(β̂) - ℓₙ(β̃))` converges in distribution to chi-squared on
`p - dim L` degrees of freedom. Hypotheses as in `tendstoInDistribution_canonicalGLM_root`. -/
theorem tendstoInDistribution_canonicalGLM_deviance {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Measure ℝ) (b : ℝ → ℝ) (hb : ContDiff ℝ 3 b)
    (φ : ℝ) (hφ : 0 < φ)
    (hlaw : ∀ θ, IsProbabilityMeasure (exponentialDispersionLaw ν b φ θ))
    (Px : Measure (EuclideanSpace ℝ (Fin p))) [IsProbabilityMeasure Px]
    (κ : Kernel (EuclideanSpace ℝ (Fin p)) ℝ) [IsMarkovKernel κ]
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin p))) (β : EuclideanSpace ℝ (Fin p)) (hβL : β ∈ L)
    (hκ : ∀ x, κ x = exponentialDispersionLaw ν b φ (inner ℝ x β))
    (R : ℝ) (hR : ∀ᵐ x ∂Px, ‖x‖ ≤ R)
    (X : ℕ → Ω → EuclideanSpace ℝ (Fin p)) (Y : ℕ → Ω → ℝ)
    (hiid : IsIndependentIdenticallyDistributed P (fun i ω ↦ (X i ω, Y i ω)) (Px ⊗ₘ κ))
    (hJ : (canonicalGLMInformation Px b β).PosDef)
    (βhat βtilde : ℕ → Ω → EuclideanSpace ℝ (Fin p))
    (hβm : ∀ n, Measurable (βhat n)) (hβm' : ∀ n, Measurable (βtilde n))
    (hcons : TendstoInMeasure P βhat atTop (fun _ ↦ β))
    (hcons' : TendstoInMeasure P βtilde atTop (fun _ ↦ β))
    (hroot : ∀ n, 1 ≤ n → ∀ᵐ ω ∂P,
      IsCanonicalGLMRoot b n (fun i ↦ X i ω) (fun i ↦ Y i ω) (βhat n ω))
    (hmax : ∀ n, ∀ᵐ ω ∂P, βtilde n ω ∈ L ∧ ∀ γ ∈ L,
      canonicalGLMLogLikelihood b φ n (fun i ↦ X i ω) (fun i ↦ Y i ω) γ ≤
        canonicalGLMLogLikelihood b φ n (fun i ↦ X i ω) (fun i ↦ Y i ω) (βtilde n ω)) :
    TendstoInDistribution (fun (n : ℕ) ω ↦
        2 * (canonicalGLMLogLikelihood b φ n (fun i ↦ X i ω) (fun i ↦ Y i ω) (βhat n ω) -
          canonicalGLMLogLikelihood b φ n (fun i ↦ X i ω) (fun i ↦ Y i ω) (βtilde n ω)))
      atTop id (fun _ ↦ P)
      (TauCeti.Probability.chiSquaredMeasure (p - Module.finrank ℝ L : ℕ)) := by
  sorry

end CKSD
