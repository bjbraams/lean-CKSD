module

import Mathlib.Probability.Moments.MGFAnalytic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Convex.Deriv
public import CKSD.Inference.Basic

/-!
# The generalised linear model with canonical link: definitions and the response law

An exponential dispersion law with cumulant function `b` and dispersion `φ > 0` has density
`exp((yθ - b θ) / φ)` with respect to a dominating measure `ν` on `ℝ` (the factor `exp c(y, φ)`
is absorbed into `ν`). In the canonical-link model the natural parameter of the response is the
linear predictor `θ = ⟪x, β⟫`, so the mean is `b'(⟪x, β⟫)`, the variance is `φ b''(⟪x, β⟫)`,
the weight is `w(x) = b''(⟪x, β⟫)`, and the likelihood equations are
`∑ᵢ xᵢ (Yᵢ - b'(⟪xᵢ, β⟫)) = 0`.

The moments of the exponential dispersion law are read off from the cumulant generating
function of the dominating measure, using Mathlib's analytic moment generating functions.

## Main definitions

* `CKSD.exponentialDispersionLaw`: the law `exp((yθ - b θ) / φ) ν(dy)`.
* `CKSD.canonicalGLMInformation`: `J = E[x xᵀ b''(⟪x, β⟫)]`.
* `CKSD.canonicalGLMLogLikelihood`, `CKSD.IsCanonicalGLMRoot`: the log likelihood and the
  likelihood equations of the first `n` observations.

## Main results

* `CKSD.integrable_pow_exponentialDispersionLaw`: polynomial moments of the exponential
  dispersion law are finite.
* `CKSD.integral_id_exponentialDispersionLaw`, `CKSD.integral_sq_sub_exponentialDispersionLaw`:
  its mean is `b'(θ)` and its variance is `φ b''(θ)`.
* `CKSD.convexOn_univ_cumulant`: a `C³` cumulant function is convex on `ℝ`.

## References

* P. McCullagh and J. A. Nelder, *Generalized Linear Models*, 2nd ed., Chapman and Hall, 1989.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators MatrixOrder InnerProductSpace RealInnerProductSpace

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

/-- Entries of `canonicalGLMInformation`. -/
theorem canonicalGLMInformation_apply (Px : Measure (EuclideanSpace ℝ (Fin p))) (b : ℝ → ℝ)
    (β : EuclideanSpace ℝ (Fin p)) (i j : Fin p) :
    canonicalGLMInformation Px b β i j = ∫ x, x i * x j * iteratedDeriv 2 b (inner ℝ x β) ∂Px := by
  rw [canonicalGLMInformation]

/-- The canonical-link log likelihood of the first `n` observations, up to terms free of `β`,
with the dispersion kept. -/
def canonicalGLMLogLikelihood (b : ℝ → ℝ) (φ : ℝ) (n : ℕ)
    (x : ℕ → EuclideanSpace ℝ (Fin p)) (y : ℕ → ℝ) (β : EuclideanSpace ℝ (Fin p)) : ℝ :=
  ∑ i ∈ Finset.range n, (y i * inner ℝ (x i) β - b (inner ℝ (x i) β)) / φ

/-- Defining equation of `canonicalGLMLogLikelihood`. -/
theorem canonicalGLMLogLikelihood_def (b : ℝ → ℝ) (φ : ℝ) (n : ℕ)
    (x : ℕ → EuclideanSpace ℝ (Fin p)) (y : ℕ → ℝ) (β : EuclideanSpace ℝ (Fin p)) :
    canonicalGLMLogLikelihood b φ n x y β =
      ∑ i ∈ Finset.range n, (y i * inner ℝ (x i) β - b (inner ℝ (x i) β)) / φ := by
  rw [canonicalGLMLogLikelihood]

/-- `β` solves the canonical-link likelihood equations for the first `n` observations. -/
def IsCanonicalGLMRoot (b : ℝ → ℝ) (n : ℕ) (x : ℕ → EuclideanSpace ℝ (Fin p)) (y : ℕ → ℝ)
    (β : EuclideanSpace ℝ (Fin p)) : Prop :=
  ∑ i ∈ Finset.range n, (y i - deriv b (inner ℝ (x i) β)) • x i = 0

/-- Characterization of `IsCanonicalGLMRoot`. -/
theorem isCanonicalGLMRoot_iff (b : ℝ → ℝ) (n : ℕ) (x : ℕ → EuclideanSpace ℝ (Fin p))
    (y : ℕ → ℝ) (β : EuclideanSpace ℝ (Fin p)) :
    IsCanonicalGLMRoot b n x y β ↔
      ∑ i ∈ Finset.range n, (y i - deriv b (inner ℝ (x i) β)) • x i = 0 := by
  rw [IsCanonicalGLMRoot]

section ExponentialDispersion

variable {ν : Measure ℝ} {b : ℝ → ℝ} {φ : ℝ}

/-- Integrals against the exponential dispersion law. -/
private lemma integral_exponentialDispersionLaw (g : ℝ → ℝ) (θ : ℝ) :
    ∫ y, g y ∂(exponentialDispersionLaw ν b φ θ) =
      ∫ y, Real.exp ((y * θ - b θ) / φ) * g y ∂ν := by
  rw [exponentialDispersionLaw]
  have := integral_withDensity_eq_integral_smul (μ := ν)
    (f := fun y ↦ (Real.exp ((y * θ - b θ) / φ)).toNNReal) (by fun_prop) g
  simp only [ENNReal.ofReal] at this ⊢
  rw [this]
  refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
  simp [NNReal.smul_def, Real.coe_toNNReal _ (Real.exp_pos _).le]

/-- Integrability against the exponential dispersion law is integrability of the function
weighted by the density `exp((yθ - b θ) / φ)` against the dominating measure. -/
private lemma integrable_exponentialDispersionLaw_iff {g : ℝ → ℝ} (θ : ℝ) :
    Integrable g (exponentialDispersionLaw ν b φ θ) ↔
      Integrable (fun y ↦ Real.exp ((y * θ - b θ) / φ) * g y) ν := by
  rw [exponentialDispersionLaw]
  have := integrable_withDensity_iff_integrable_smul (μ := ν)
    (f := fun y ↦ (Real.exp ((y * θ - b θ) / φ)).toNNReal) (by fun_prop) (g := g)
  simp only [ENNReal.ofReal] at this ⊢
  rw [this]
  refine integrable_congr (ae_of_all _ fun y ↦ ?_)
  simp [NNReal.smul_def, Real.coe_toNNReal _ (Real.exp_pos _).le]

variable (hφ : 0 < φ) (hlaw : ∀ θ, IsProbabilityMeasure (exponentialDispersionLaw ν b φ θ))
include hφ hlaw

/-- The Laplace transform of the dominating measure: `∫ e^{s y} ν(dy) = exp (b(φ s) / φ)`. -/
private lemma lintegral_exp_mul_eq (s : ℝ) :
    ∫⁻ y, ENNReal.ofReal (Real.exp (s * y)) ∂ν = ENNReal.ofReal (Real.exp (b (φ * s) / φ)) := by
  have h := (hlaw (φ * s)).measure_univ
  rw [exponentialDispersionLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h
  have hpt : ∀ y, ENNReal.ofReal (Real.exp (s * y)) =
      ENNReal.ofReal (Real.exp ((y * (φ * s) - b (φ * s)) / φ)) *
        ENNReal.ofReal (Real.exp (b (φ * s) / φ)) := fun y ↦ by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2
    field_simp
    ring
  simp_rw [hpt]
  rw [lintegral_mul_const _ (by fun_prop), h, one_mul]

/-- The exponential moments of the dominating measure are all finite. -/
private lemma integrable_exp_mul (s : ℝ) :
    Integrable (fun y ↦ Real.exp (s * y)) ν :=
  ⟨(by fun_prop : Measurable fun y : ℝ ↦ Real.exp (s * y)).aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ ↦ (Real.exp_pos _).le)).2
      (by rw [lintegral_exp_mul_eq hφ hlaw]; exact ENNReal.ofReal_lt_top)⟩

/-- Every real `s` lies in the interior of the set where `exp (s y)` is `ν`-integrable, since
that set is all of `ℝ`. -/
private lemma mem_interior_integrableExpSet (s : ℝ) :
    s ∈ interior (integrableExpSet id ν) := by
  have : integrableExpSet id ν = univ :=
    eq_univ_of_forall fun t ↦ by simpa [integrableExpSet] using integrable_exp_mul hφ hlaw t
  rw [this, interior_univ]; trivial

/-- `mgf ν (s) = exp (b(φ s) / φ)`. -/
private lemma mgf_id_eq (s : ℝ) :
    mgf id ν s = Real.exp (b (φ * s) / φ) := by
  rw [mgf, integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ ↦ (Real.exp_pos _).le)
    (by fun_prop : Measurable fun y : ℝ ↦ Real.exp (s * id y)).aestronglyMeasurable]
  simp only [id]
  rw [lintegral_exp_mul_eq hφ hlaw, ENNReal.toReal_ofReal (Real.exp_pos _).le]

/-- The cumulant function is a rescaled cumulant generating function:
`b θ = φ · cgf_ν (θ / φ)`. -/
private lemma eq_mul_cgf :
    b = fun θ ↦ φ * cgf id ν (φ⁻¹ * θ) := by
  funext θ
  rw [cgf, mgf_id_eq hφ hlaw, Real.log_exp, mul_inv_cancel_left₀ hφ.ne']
  field_simp

/-- The cumulant generating function of the dominating measure is smooth of every order. -/
private lemma contDiff_cgf {n : WithTop ℕ∞} :
    ContDiff ℝ n (cgf id ν) :=
  AnalyticOnNhd.contDiff fun s _ ↦ analyticOnNhd_cgf s (mem_interior_integrableExpSet hφ hlaw s)

/-- The first derivative of the cumulant function in terms of the cumulant generating function:
`b'(θ) = cgf_ν'(θ / φ)`. -/
private lemma deriv_eq_deriv_cgf (θ : ℝ) :
    deriv b θ = deriv (cgf id ν) (φ⁻¹ * θ) := by
  have hd : DifferentiableAt ℝ (cgf id ν) (φ⁻¹ * θ) :=
    (contDiff_cgf hφ hlaw (n := 1)).differentiable one_ne_zero _
  have h := (hd.hasDerivAt.comp θ ((hasDerivAt_id θ).const_mul φ⁻¹)).const_mul φ
  have h' : HasDerivAt (fun θ ↦ φ * cgf id ν (φ⁻¹ * θ)) (deriv (cgf id ν) (φ⁻¹ * θ)) θ := by
    simp only [Function.comp_def, mul_one] at h
    rwa [← mul_assoc, mul_comm φ, mul_assoc, mul_inv_cancel₀ hφ.ne', mul_one] at h
  rw [eq_mul_cgf hφ hlaw, h'.deriv]

/-- The second derivative of the cumulant function in terms of the cumulant generating function:
`b''(θ) = φ⁻¹ cgf_ν''(θ / φ)`. -/
private lemma iteratedDeriv_two_eq (θ : ℝ) :
    iteratedDeriv 2 b θ = φ⁻¹ * iteratedDeriv 2 (cgf id ν) (φ⁻¹ * θ) := by
  rw [eq_mul_cgf hφ hlaw, iteratedDeriv_const_mul_field,
    iteratedDeriv_comp_const_mul (contDiff_cgf hφ hlaw) φ⁻¹]
  field_simp

/-- The density factorizes as `exp(s y) / mgf(s)` with `s = θ / φ`. -/
private lemma exp_div_eq (θ y : ℝ) :
    Real.exp ((y * θ - b θ) / φ) = Real.exp (φ⁻¹ * θ * id y) / mgf id ν (φ⁻¹ * θ) := by
  rw [mgf_id_eq hφ hlaw, mul_inv_cancel_left₀ hφ.ne', ← Real.exp_sub]
  congr 1
  simp only [id]
  field_simp

/-- Polynomial moments of the exponential dispersion law are finite. -/
lemma integrable_pow_exponentialDispersionLaw (θ : ℝ) (k : ℕ) :
    Integrable (fun y ↦ y ^ k) (exponentialDispersionLaw ν b φ θ) := by
  rw [integrable_exponentialDispersionLaw_iff]
  have h := (integrable_pow_mul_exp_of_mem_interior_integrableExpSet
    (mem_interior_integrableExpSet hφ hlaw (φ⁻¹ * θ)) k).div_const (mgf id ν (φ⁻¹ * θ))
  refine h.congr (ae_of_all _ fun y ↦ ?_)
  simp only [exp_div_eq hφ hlaw, id]
  ring

/-- The mean of the exponential dispersion law is `b'(θ)`. -/
lemma integral_id_exponentialDispersionLaw (θ : ℝ) :
    ∫ y, y ∂(exponentialDispersionLaw ν b φ θ) = deriv b θ := by
  rw [integral_exponentialDispersionLaw, deriv_eq_deriv_cgf hφ hlaw,
    deriv_cgf (mem_interior_integrableExpSet hφ hlaw _), ← integral_div]
  refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
  simp only [exp_div_eq hφ hlaw, id]
  ring

/-- The variance of the exponential dispersion law is `φ b''(θ)`. -/
lemma integral_sq_sub_exponentialDispersionLaw (θ : ℝ) :
    ∫ y, (y - deriv b θ) ^ 2 ∂(exponentialDispersionLaw ν b φ θ) =
      φ * iteratedDeriv 2 b θ := by
  rw [integral_exponentialDispersionLaw, iteratedDeriv_two_eq hφ hlaw,
    iteratedDeriv_two_cgf_eq_integral (mem_interior_integrableExpSet hφ hlaw _),
    deriv_eq_deriv_cgf hφ hlaw, mul_inv_cancel_left₀ hφ.ne', ← integral_div]
  refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
  simp only [exp_div_eq hφ hlaw, id]
  ring

/-- The cumulant function is convex: `b'' ≥ 0`. -/
private lemma iteratedDeriv_two_nonneg (θ : ℝ) :
    0 ≤ iteratedDeriv 2 b θ := by
  have h := integral_sq_sub_exponentialDispersionLaw hφ hlaw θ
  have h0 : 0 ≤ ∫ y, (y - deriv b θ) ^ 2 ∂(exponentialDispersionLaw ν b φ θ) :=
    integral_nonneg fun _ ↦ sq_nonneg _
  rw [h] at h0
  exact nonneg_of_mul_nonneg_right (by linarith) hφ

/-- A `C³` cumulant function of an exponential dispersion family is convex on `ℝ`. -/
lemma convexOn_univ_cumulant (hb : ContDiff ℝ 3 b) : ConvexOn ℝ univ b := by
  refine convexOn_univ_of_deriv2_nonneg (hb.differentiable (by norm_num)) ?_ fun x ↦ ?_
  · have := hb.differentiable_iteratedDeriv 1 (by norm_num)
    rwa [iteratedDeriv_one] at this
  · rw [← iteratedDeriv_eq_iterate]
    exact iteratedDeriv_two_nonneg hφ hlaw x

end ExponentialDispersion

end CKSD
