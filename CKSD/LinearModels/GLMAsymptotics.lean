module

public import CKSD.Inference.Basic
public import CKSD.LinearModels.ConvexLikelihood
public import TauCeti.Probability.Distributions.ChiSquared.Basic
import CKSD.Asymptotics.ConvexRegression.Basic
import Mathlib.Probability.CentralLimitTheorem
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Probability.StrongLaw
import Mathlib.Analysis.Matrix.Order

/-!
# Asymptotics of the generalised linear model with canonical link

An exponential dispersion law with cumulant function `b` and dispersion `φ > 0` has density
`exp((yθ - b θ) / φ)` with respect to a dominating measure `ν` on `ℝ` (the factor `exp c(y, φ)`
is absorbed into `ν`). In the canonical-link model the natural parameter of the response is the
linear predictor `θ = ⟪x, β⟫`, so the mean is `b'(⟪x, β⟫)`, the variance is `φ b''(⟪x, β⟫)`,
the weight is `w(x) = b''(⟪x, β⟫)`, and the likelihood equations are
`∑ᵢ xᵢ (Yᵢ - b'(⟪xᵢ, β⟫)) = 0`.

The deviance proof whitens the information matrix and applies the convex minimum-value
and Gaussian projection results in `CKSD.LinearModels.ConvexLikelihood`.

The pairs `(xᵢ, Yᵢ)` are independent and identically distributed; the conditional law of the
response given the covariate is supplied by a Markov kernel.

## Main definitions

* `CKSD.exponentialDispersionLaw`: the law `exp((yθ - b θ) / φ) ν(dy)`.
* `CKSD.canonicalGLMInformation`: `J = E[x xᵀ b''(⟪x, β⟫)]`.
* `CKSD.canonicalGLMLogLikelihood`, `CKSD.IsCanonicalGLMRoot`: the log likelihood and the
  likelihood equations of the first `n` observations.

## Main results

* `CKSD.tendstoInDistribution_canonicalGLM_root`: asymptotic normality
  `√n (β̂ - β) ⇒ N(0, φ J⁻¹)` of roots of the likelihood equations, and its studentized form.
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

/-- The canonical-link log likelihood of the first `n` observations, up to terms free of `β`,
with the dispersion kept. -/
def canonicalGLMLogLikelihood (b : ℝ → ℝ) (φ : ℝ) (n : ℕ)
    (x : ℕ → EuclideanSpace ℝ (Fin p)) (y : ℕ → ℝ) (β : EuclideanSpace ℝ (Fin p)) : ℝ :=
  ∑ i ∈ Finset.range n, (y i * inner ℝ (x i) β - b (inner ℝ (x i) β)) / φ

/-- `β` solves the canonical-link likelihood equations for the first `n` observations. -/
def IsCanonicalGLMRoot (b : ℝ → ℝ) (n : ℕ) (x : ℕ → EuclideanSpace ℝ (Fin p)) (y : ℕ → ℝ)
    (β : EuclideanSpace ℝ (Fin p)) : Prop :=
  ∑ i ∈ Finset.range n, (y i - deriv b (inner ℝ (x i) β)) • x i = 0

section ExponentialDispersion

variable {ν : Measure ℝ} {b : ℝ → ℝ} {φ : ℝ}

/-- The Laplace transform of the dominating measure: `∫ e^{s y} ν(dy) = exp (b(φ s) / φ)`. -/
private lemma lintegral_exp_mul_eq (hφ : 0 < φ)
    (hlaw : ∀ θ, IsProbabilityMeasure (exponentialDispersionLaw ν b φ θ)) (s : ℝ) :
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
private lemma integrable_exp_mul (hφ : 0 < φ)
    (hlaw : ∀ θ, IsProbabilityMeasure (exponentialDispersionLaw ν b φ θ)) (s : ℝ) :
    Integrable (fun y ↦ Real.exp (s * y)) ν :=
  ⟨(by fun_prop : Measurable fun y : ℝ ↦ Real.exp (s * y)).aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ ↦ (Real.exp_pos _).le)).2
      (by rw [lintegral_exp_mul_eq hφ hlaw]; exact ENNReal.ofReal_lt_top)⟩

private lemma mem_interior_integrableExpSet (hφ : 0 < φ)
    (hlaw : ∀ θ, IsProbabilityMeasure (exponentialDispersionLaw ν b φ θ)) (s : ℝ) :
    s ∈ interior (integrableExpSet id ν) := by
  have : integrableExpSet id ν = univ :=
    eq_univ_of_forall fun t ↦ by simpa [integrableExpSet] using integrable_exp_mul hφ hlaw t
  rw [this, interior_univ]; trivial

/-- `mgf ν (s) = exp (b(φ s) / φ)`. -/
private lemma mgf_id_eq (hφ : 0 < φ)
    (hlaw : ∀ θ, IsProbabilityMeasure (exponentialDispersionLaw ν b φ θ)) (s : ℝ) :
    mgf id ν s = Real.exp (b (φ * s) / φ) := by
  rw [mgf, integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ ↦ (Real.exp_pos _).le)
    (by fun_prop : Measurable fun y : ℝ ↦ Real.exp (s * id y)).aestronglyMeasurable]
  simp only [id]
  rw [lintegral_exp_mul_eq hφ hlaw, ENNReal.toReal_ofReal (Real.exp_pos _).le]

/-- The cumulant function is a rescaled cumulant generating function:
`b θ = φ · cgf_ν (θ / φ)`. -/
private lemma eq_mul_cgf (hφ : 0 < φ)
    (hlaw : ∀ θ, IsProbabilityMeasure (exponentialDispersionLaw ν b φ θ)) :
    b = fun θ ↦ φ * cgf id ν (φ⁻¹ * θ) := by
  funext θ
  rw [cgf, mgf_id_eq hφ hlaw, Real.log_exp, mul_inv_cancel_left₀ hφ.ne']
  field_simp

private lemma contDiff_cgf (hφ : 0 < φ)
    (hlaw : ∀ θ, IsProbabilityMeasure (exponentialDispersionLaw ν b φ θ)) {n : WithTop ℕ∞} :
    ContDiff ℝ n (cgf id ν) :=
  AnalyticOnNhd.contDiff fun s _ ↦ analyticOnNhd_cgf s (mem_interior_integrableExpSet hφ hlaw s)

private lemma deriv_eq_deriv_cgf (hφ : 0 < φ)
    (hlaw : ∀ θ, IsProbabilityMeasure (exponentialDispersionLaw ν b φ θ)) (θ : ℝ) :
    deriv b θ = deriv (cgf id ν) (φ⁻¹ * θ) := by
  have hd : DifferentiableAt ℝ (cgf id ν) (φ⁻¹ * θ) :=
    (contDiff_cgf hφ hlaw (n := 1)).differentiable one_ne_zero _
  have h := (hd.hasDerivAt.comp θ ((hasDerivAt_id θ).const_mul φ⁻¹)).const_mul φ
  have h' : HasDerivAt (fun θ ↦ φ * cgf id ν (φ⁻¹ * θ)) (deriv (cgf id ν) (φ⁻¹ * θ)) θ := by
    simp only [Function.comp_def, mul_one] at h
    rwa [← mul_assoc, mul_comm φ, mul_assoc, mul_inv_cancel₀ hφ.ne', mul_one] at h
  rw [eq_mul_cgf hφ hlaw, h'.deriv]

private lemma iteratedDeriv_two_eq (hφ : 0 < φ)
    (hlaw : ∀ θ, IsProbabilityMeasure (exponentialDispersionLaw ν b φ θ)) (θ : ℝ) :
    iteratedDeriv 2 b θ = φ⁻¹ * iteratedDeriv 2 (cgf id ν) (φ⁻¹ * θ) := by
  rw [eq_mul_cgf hφ hlaw, iteratedDeriv_const_mul_field,
    iteratedDeriv_comp_const_mul (contDiff_cgf hφ hlaw) φ⁻¹]
  field_simp

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

/-- The density factorizes as `exp(s y) / mgf(s)` with `s = θ / φ`. -/
private lemma exp_div_eq (hφ : 0 < φ)
    (hlaw : ∀ θ, IsProbabilityMeasure (exponentialDispersionLaw ν b φ θ)) (θ y : ℝ) :
    Real.exp ((y * θ - b θ) / φ) = Real.exp (φ⁻¹ * θ * id y) / mgf id ν (φ⁻¹ * θ) := by
  rw [mgf_id_eq hφ hlaw, mul_inv_cancel_left₀ hφ.ne', ← Real.exp_sub]
  congr 1
  simp only [id]
  field_simp

/-- Polynomial moments of the exponential dispersion law are finite. -/
private lemma integrable_pow_exponentialDispersionLaw (hφ : 0 < φ)
    (hlaw : ∀ θ, IsProbabilityMeasure (exponentialDispersionLaw ν b φ θ)) (θ : ℝ) (k : ℕ) :
    Integrable (fun y ↦ y ^ k) (exponentialDispersionLaw ν b φ θ) := by
  rw [integrable_exponentialDispersionLaw_iff]
  have h := (integrable_pow_mul_exp_of_mem_interior_integrableExpSet
    (mem_interior_integrableExpSet hφ hlaw (φ⁻¹ * θ)) k).div_const (mgf id ν (φ⁻¹ * θ))
  refine h.congr (ae_of_all _ fun y ↦ ?_)
  simp only [exp_div_eq hφ hlaw, id]
  ring

/-- The mean of the exponential dispersion law is `b'(θ)`. -/
private lemma integral_id_exponentialDispersionLaw (hφ : 0 < φ)
    (hlaw : ∀ θ, IsProbabilityMeasure (exponentialDispersionLaw ν b φ θ)) (θ : ℝ) :
    ∫ y, y ∂(exponentialDispersionLaw ν b φ θ) = deriv b θ := by
  rw [integral_exponentialDispersionLaw, deriv_eq_deriv_cgf hφ hlaw,
    deriv_cgf (mem_interior_integrableExpSet hφ hlaw _), ← integral_div]
  refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
  simp only [exp_div_eq hφ hlaw, id]
  ring

/-- The variance of the exponential dispersion law is `φ b''(θ)`. -/
private lemma integral_sq_sub_exponentialDispersionLaw (hφ : 0 < φ)
    (hlaw : ∀ θ, IsProbabilityMeasure (exponentialDispersionLaw ν b φ θ)) (θ : ℝ) :
    ∫ y, (y - deriv b θ) ^ 2 ∂(exponentialDispersionLaw ν b φ θ) =
      φ * iteratedDeriv 2 b θ := by
  rw [integral_exponentialDispersionLaw, iteratedDeriv_two_eq hφ hlaw,
    iteratedDeriv_two_cgf_eq_integral (mem_interior_integrableExpSet hφ hlaw _),
    deriv_eq_deriv_cgf hφ hlaw, mul_inv_cancel_left₀ hφ.ne', ← integral_div]
  refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
  simp only [exp_div_eq hφ hlaw, id]
  ring

/-- The cumulant function is convex: `b'' ≥ 0`. -/
private lemma iteratedDeriv_two_nonneg (hφ : 0 < φ)
    (hlaw : ∀ θ, IsProbabilityMeasure (exponentialDispersionLaw ν b φ θ)) (θ : ℝ) :
    0 ≤ iteratedDeriv 2 b θ := by
  have h := integral_sq_sub_exponentialDispersionLaw hφ hlaw θ
  have h0 : 0 ≤ ∫ y, (y - deriv b θ) ^ 2 ∂(exponentialDispersionLaw ν b φ θ) :=
    integral_nonneg fun _ ↦ sq_nonneg _
  rw [h] at h0
  exact nonneg_of_mul_nonneg_right (by linarith) hφ

end ExponentialDispersion

section RandomDesign

/-- Second-order Taylor bound for a `C³` function on a bounded set:
`|b(θ + t) - b θ - b'(θ) t - b''(θ) t² / 2| ≤ M |t|³` for `|θ| ≤ K`, `|t| ≤ 1`. -/
private lemma exists_abs_taylor_two_le {b : ℝ → ℝ} (hb : ContDiff ℝ 3 b) (K : ℝ) :
    ∃ M, ∀ θ t, |θ| ≤ K → |t| ≤ 1 →
      |b (θ + t) - b θ - deriv b θ * t - iteratedDeriv 2 b θ * t ^ 2 / 2| ≤ M * |t| ^ 3 := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc (-(K + 1)) (K + 1))
    (hb.continuous_iteratedDeriv 3 le_rfl).continuousOn
  have h0 : ∀ r, HasDerivAt b (deriv b r) r := fun r ↦
    ((hb.differentiable (by norm_num)) r).hasDerivAt
  have h1 : ∀ r, HasDerivAt (deriv b) (iteratedDeriv 2 b r) r := fun r ↦ by
    have := (hb.differentiable_iteratedDeriv 1 (by norm_num)) r
    rw [iteratedDeriv_one] at this
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    exact this.hasDerivAt
  have h2 : ∀ r, HasDerivAt (iteratedDeriv 2 b) (iteratedDeriv 3 b r) r := fun r ↦ by
    have e : iteratedDeriv 3 b = deriv (iteratedDeriv 2 b) := iteratedDeriv_succ
    rw [e]
    exact ((hb.differentiable_iteratedDeriv 2 (by norm_num)) r).hasDerivAt
  refine ⟨M, fun θ t hθ ht ↦ ?_⟩
  have hsub : uIcc 0 t ⊆ Icc (-1) 1 := uIcc_subset_Icc (by simp) (abs_le.1 ht)
  have hr : ∀ r ∈ uIcc 0 t, |r| ≤ |t| := fun r hr ↦ by
    simpa using abs_sub_left_of_mem_uIcc hr
  have hmem : ∀ r ∈ uIcc 0 t, θ + r ∈ Icc (-(K + 1)) (K + 1) := fun r hr' ↦ by
    have := abs_le.1 hθ; have := hsub hr'
    constructor <;> linarith [this.1, this.2]
  have hz : (0 : ℝ) ∈ uIcc 0 t := left_mem_uIcc
  -- step 1: `|b''(θ + r) - b''(θ)| ≤ M |t|`
  have s1 : ∀ r ∈ uIcc 0 t, |iteratedDeriv 2 b (θ + r) - iteratedDeriv 2 b θ| ≤ M * |t| := by
    intro r hr'
    have := convex_uIcc 0 t |>.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun r ↦ iteratedDeriv 2 b (θ + r))
      (fun r _ ↦ ((h2 (θ + r)).comp_const_add θ r).hasDerivWithinAt)
      (fun r hr ↦ hM _ (hmem r hr)) hz hr'
    simp only [add_zero, sub_zero, Real.norm_eq_abs] at this
    exact this.trans (mul_le_mul_of_nonneg_left (hr r hr')
      ((norm_nonneg _).trans (hM _ (hmem 0 hz))))
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM _ (hmem 0 hz))
  -- step 2: `|b'(θ + r) - b'(θ) - r b''(θ)| ≤ M t²`
  have s2 : ∀ r ∈ uIcc 0 t,
      |deriv b (θ + r) - deriv b θ - r * iteratedDeriv 2 b θ| ≤ M * |t| ^ 2 := by
    intro r hr'
    have hd : ∀ r, HasDerivAt (fun r ↦ deriv b (θ + r) - r * iteratedDeriv 2 b θ)
        (iteratedDeriv 2 b (θ + r) - iteratedDeriv 2 b θ) r := fun r ↦ by
      convert ((h1 (θ + r)).comp_const_add θ r).sub
        ((hasDerivAt_id r).mul_const (iteratedDeriv 2 b θ)) using 1
      · rfl
      · ring
    have := convex_uIcc 0 t |>.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun r _ ↦ (hd r).hasDerivWithinAt) (fun r hr ↦ s1 r hr) hz hr'
    simp only [add_zero, sub_zero, zero_mul, Real.norm_eq_abs] at this
    calc _ = |deriv b (θ + r) - r * iteratedDeriv 2 b θ - deriv b θ| := by ring_nf
      _ ≤ M * |t| * |r| := this
      _ ≤ M * |t| * |t| := mul_le_mul_of_nonneg_left (hr r hr') (by positivity)
      _ = M * |t| ^ 2 := by ring
  -- step 3
  have hd : ∀ r, HasDerivAt
      (fun r ↦ b (θ + r) - r * deriv b θ - r ^ 2 / 2 * iteratedDeriv 2 b θ)
      (deriv b (θ + r) - deriv b θ - r * iteratedDeriv 2 b θ) r := fun r ↦ by
    have := (((h0 (θ + r)).comp_const_add θ r).sub ((hasDerivAt_id r).mul_const (deriv b θ))).sub
      (((hasDerivAt_pow 2 r).div_const 2).mul_const (iteratedDeriv 2 b θ))
    convert this using 1
    · funext r; simp only [Pi.sub_apply, id]
    · simp only [Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl, pow_one]; ring
  have := convex_uIcc 0 t |>.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun r _ ↦ (hd r).hasDerivWithinAt) (fun r hr ↦ s2 r hr) hz right_mem_uIcc
  simp only [add_zero, sub_zero, zero_mul, Real.norm_eq_abs] at this
  calc _ = |b (θ + t) - t * deriv b θ - t ^ 2 / 2 * iteratedDeriv 2 b θ - b θ| := by ring_nf
    _ ≤ M * |t| ^ 2 * |t| := by simpa using this
    _ = M * |t| ^ 3 := by ring

/-- The second-order Taylor remainders of the GLM log likelihood summed over the sample: with
bounded covariates `‖xᵢ‖ ≤ R` and a step `s h` with `R s ‖h‖ ≤ 1`, the sum is at most
`n M (R s ‖h‖)³`. -/
private lemma exists_abs_sum_taylor_le {b : ℝ → ℝ} (hb : ContDiff ℝ 3 b) {R : ℝ}
    (β : EuclideanSpace ℝ (Fin p)) :
    ∃ M ≥ 0, ∀ (n : ℕ) (x : ℕ → EuclideanSpace ℝ (Fin p)) (s : ℝ) (h : EuclideanSpace ℝ (Fin p)),
      0 ≤ s → (∀ i, ‖x i‖ ≤ R) → R * (s * ‖h‖) ≤ 1 →
      |∑ i ∈ Finset.range n, (b (inner ℝ (x i) (β + s • h)) - b (inner ℝ (x i) β) -
          deriv b (inner ℝ (x i) β) * inner ℝ (x i) (s • h) -
          iteratedDeriv 2 b (inner ℝ (x i) β) * inner ℝ (x i) (s • h) ^ 2 / 2)| ≤
        n * (M * (R * (s * ‖h‖)) ^ 3) := by
  obtain ⟨M, hM⟩ := exists_abs_taylor_two_le hb (R * ‖β‖)
  refine ⟨max M 0, le_max_right _ _, fun n x s h hs hx hRs ↦ ?_⟩
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ i, |b (inner ℝ (x i) (β + s • h)) - b (inner ℝ (x i) β) -
      deriv b (inner ℝ (x i) β) * inner ℝ (x i) (s • h) -
      iteratedDeriv 2 b (inner ℝ (x i) β) * inner ℝ (x i) (s • h) ^ 2 / 2| ≤
        max M 0 * (R * (s * ‖h‖)) ^ 3 := by
    intro i
    have ht : |inner ℝ (x i) (s • h)| ≤ R * (s * ‖h‖) := by
      refine (abs_real_inner_le_norm _ _).trans ?_
      rw [norm_smul, Real.norm_of_nonneg hs]
      exact mul_le_mul_of_nonneg_right (hx i) (by positivity)
    have hθ : |inner ℝ (x i) β| ≤ R * ‖β‖ :=
      (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hx i) (norm_nonneg _))
    have h1 := hM _ _ hθ (ht.trans hRs)
    rw [inner_add_right]
    calc _ ≤ M * |inner ℝ (x i) (s • h)| ^ 3 := h1
      _ ≤ max M 0 * |inner ℝ (x i) (s • h)| ^ 3 :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ max M 0 * (R * (s * ‖h‖)) ^ 3 := by gcongr
  refine (Finset.sum_le_sum fun i _ ↦ hterm i).trans ?_
  simp

variable {Px : Measure (EuclideanSpace ℝ (Fin p))} [IsProbabilityMeasure Px] {R : ℝ}

/-- A continuous function is integrable for a law supported in a ball. -/
private lemma integrable_of_continuous (hR : ∀ᵐ x ∂Px, ‖x‖ ≤ R) {E : Type*}
    [NormedAddCommGroup E] {f : EuclideanSpace ℝ (Fin p) → E} (hf : Continuous f) :
    Integrable f Px := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin p)) R)
    |>.exists_bound_of_continuousOn hf.continuousOn
  exact Integrable.of_bound hf.aestronglyMeasurable C
    (hR.mono fun x hx ↦ hC x (mem_closedBall_zero_iff.2 hx))

variable {κ : Kernel (EuclideanSpace ℝ (Fin p)) ℝ} [IsMarkovKernel κ]

/-- The covariate marginal of `Px ⊗ κ` is `Px`. -/
private lemma map_fst_compProd : (Px ⊗ₘ κ).map Prod.fst = Px := Measure.fst_compProd Px κ

/-- Integrals of functions of the covariate alone against `Px ⊗ κ`. -/
private lemma integral_comp_fst_compProd {g : EuclideanSpace ℝ (Fin p) → ℝ} (hg : Continuous g) :
    ∫ z, g z.1 ∂(Px ⊗ₘ κ) = ∫ x, g x ∂Px := by
  conv_rhs => rw [← map_fst_compProd (Px := Px) (κ := κ)]
  exact (integral_map measurable_fst.aemeasurable hg.aestronglyMeasurable).symm

open Matrix in
/-- `∫ b''(⟪x, β⟫) ⟪x, h⟫² dPx = hᵀ J h`. -/
private lemma integral_iteratedDeriv_mul_inner_sq (hR : ∀ᵐ x ∂Px, ‖x‖ ≤ R) {b : ℝ → ℝ}
    (hb2 : Continuous (iteratedDeriv 2 b)) (β h : EuclideanSpace ℝ (Fin p)) :
    ∫ x, iteratedDeriv 2 b (inner ℝ x β) * inner ℝ x h ^ 2 ∂Px =
      WithLp.ofLp h ⬝ᵥ canonicalGLMInformation Px b β *ᵥ WithLp.ofLp h := by
  have hexp : ∀ x : EuclideanSpace ℝ (Fin p), iteratedDeriv 2 b (inner ℝ x β) * inner ℝ x h ^ 2 =
      ∑ j, ∑ k, h j * h k * (x j * x k * iteratedDeriv 2 b (inner ℝ x β)) := by
    intro x
    simp only [PiLp.inner_apply]
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    simp only [RCLike.inner_apply, conj_trivial]
    ring
  have hint : ∀ j k, Integrable (fun x : EuclideanSpace ℝ (Fin p) ↦
      h j * h k * (x j * x k * iteratedDeriv 2 b (inner ℝ x β))) Px := fun j k ↦
    integrable_of_continuous hR (by fun_prop)
  simp_rw [hexp]
  rw [integral_finsetSum _ fun j _ ↦ integrable_finsetSum _ fun k _ ↦ hint j k]
  simp only [dotProduct, mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [integral_finsetSum _ fun k _ ↦ hint j k]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [integral_const_mul, canonicalGLMInformation]
  ring

open Matrix in
/-- Moments of the projected score `s_v(x, y) = (y - b'(⟪x, β⟫)) ⟪x, v⟫` under `Px ⊗ κ`: it is
square integrable, centred, and `E s_v² = φ vᵀ J v`. -/
private lemma memLp_score_and_integral {ν : Measure ℝ} {b : ℝ → ℝ} (hb : ContDiff ℝ 3 b)
    {φ : ℝ} (hφ : 0 < φ) (hlaw : ∀ θ, IsProbabilityMeasure (exponentialDispersionLaw ν b φ θ))
    (hR : ∀ᵐ x ∂Px, ‖x‖ ≤ R) {β : EuclideanSpace ℝ (Fin p)}
    (hκ : ∀ x, κ x = exponentialDispersionLaw ν b φ (inner ℝ x β))
    (v : EuclideanSpace ℝ (Fin p)) :
    MemLp (fun z : EuclideanSpace ℝ (Fin p) × ℝ ↦ (z.2 - deriv b (inner ℝ z.1 β)) *
        inner ℝ z.1 v) 2 (Px ⊗ₘ κ) ∧
      ∫ z, (z.2 - deriv b (inner ℝ z.1 β)) * inner ℝ z.1 v ∂(Px ⊗ₘ κ) = 0 ∧
      ∫ z, ((z.2 - deriv b (inner ℝ z.1 β)) * inner ℝ z.1 v) ^ 2 ∂(Px ⊗ₘ κ) =
        φ * (WithLp.ofLp v ⬝ᵥ canonicalGLMInformation Px b β *ᵥ WithLp.ofLp v) := by
  set g : EuclideanSpace ℝ (Fin p) × ℝ → ℝ :=
    fun z ↦ (z.2 - deriv b (inner ℝ z.1 β)) * inner ℝ z.1 v with hg_def
  have hd1 : Continuous (deriv b) := hb.continuous_deriv (by norm_num)
  have hb2 : Continuous (iteratedDeriv 2 b) := hb.continuous_iteratedDeriv 2 (by norm_num)
  have hg : Continuous g := by fun_prop
  have hpoly : ∀ x (c a : ℝ), Integrable (fun y ↦ (y - c) ^ 2 * a) (κ x) := fun x c a ↦ by
    rw [hκ]
    have h2 := integrable_pow_exponentialDispersionLaw hφ hlaw (inner ℝ x β) 2
    have h1 := integrable_pow_exponentialDispersionLaw hφ hlaw (inner ℝ x β) 1
    exact (((h2.sub (h1.const_mul (2 * c))).add (integrable_const (c ^ 2))).mul_const a).congr
      (ae_of_all _ fun y ↦ by simp only [Pi.add_apply, Pi.sub_apply]; ring)
  have hsq : ∀ x, ∫ y, g (x, y) ^ 2 ∂(κ x) =
      φ * (iteratedDeriv 2 b (inner ℝ x β) * inner ℝ x v ^ 2) := fun x ↦ by
    simp only [hg_def, mul_pow]
    rw [hκ, integral_mul_const, integral_sq_sub_exponentialDispersionLaw hφ hlaw]
    ring
  have hint2 : Integrable (fun z ↦ g z ^ 2) (Px ⊗ₘ κ) := by
    rw [Measure.integrable_compProd_iff
      (by fun_prop : Continuous fun z ↦ g z ^ 2).aestronglyMeasurable]
    refine ⟨ae_of_all _ fun x ↦ ?_, ?_⟩
    · exact (hpoly x (deriv b (inner ℝ x β)) (inner ℝ x v ^ 2)).congr
        (ae_of_all _ fun y ↦ by simp only [hg_def]; ring)
    · have : (fun x ↦ ∫ y, ‖g (x, y) ^ 2‖ ∂(κ x)) =
          fun x ↦ φ * (iteratedDeriv 2 b (inner ℝ x β) * inner ℝ x v ^ 2) := funext fun x ↦ by
        simp only [Real.norm_eq_abs, abs_pow, sq_abs]
        exact hsq x
      rw [this]
      exact integrable_of_continuous hR (by fun_prop)
  have hmem : MemLp g 2 (Px ⊗ₘ κ) := (memLp_two_iff_integrable_sq hg.aestronglyMeasurable).2 hint2
  refine ⟨hmem, ?_, ?_⟩
  · rw [Measure.integral_compProd (hmem.integrable one_le_two)]
    have : ∀ x, ∫ y, g (x, y) ∂(κ x) = 0 := fun x ↦ by
      simp only [hg_def]
      have h1 := integrable_pow_exponentialDispersionLaw hφ hlaw (inner ℝ x β) 1
      simp only [pow_one] at h1
      rw [integral_mul_const, hκ, integral_sub h1 (integrable_const _),
        integral_id_exponentialDispersionLaw hφ hlaw, integral_const, probReal_univ, one_smul,
        sub_self, zero_mul]
    simp only [this, integral_zero]
  · rw [Measure.integral_compProd hint2]
    simp only [hsq]
    rw [integral_const_mul, integral_iteratedDeriv_mul_inner_sq hR hb2]

/-- Slutsky's lemma for scalar factors: if `cₙ → 0` in probability and `Vₙ` converges in
distribution, then `cₙ Vₙ → 0` in probability. -/
private lemma tendstoInMeasure_smul_zero {Ω Ω' E : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [OpensMeasurableSpace E] (μ : Measure Ω) [IsProbabilityMeasure μ] {μ' : Measure Ω'}
    [IsProbabilityMeasure μ'] (c : ℕ → Ω → ℝ) (V : ℕ → Ω → E) {W : Ω' → E}
    (hc : TendstoInMeasure μ c atTop (fun _ ↦ 0))
    (hV : TendstoInDistribution V atTop W (fun _ ↦ μ) μ') :
    TendstoInMeasure μ (fun (n : ℕ) ω ↦ c n ω • V n ω) atTop (fun _ ↦ 0) := by
  have hb := isBoundedInProbability_of_tendstoInDistribution μ (fun n ω ↦ ‖V n ω‖)
    (hV.continuous_comp continuous_norm)
  have h := tendstoInMeasure_mul_zero_of_isBoundedInProbability μ _ c hb hc
  intro ε hε
  refine (h ε hε).congr fun n ↦ ?_
  congr 1
  ext ω
  simp [enorm_smul, mul_comm]

/-- Pointwise convergence in probability of the centred GLM log-likelihood process:
`Zₙ(h) + ⟪Uₙ, h⟫ → ⟪h, J h⟫ / 2`, where `Zₙ(h) = ∑ [b(⟪xᵢ, β + h/√n⟫) - b(⟪xᵢ, β⟫) - Yᵢ ⟪xᵢ, h/√n⟫]`
and `Uₙ = n^{-1/2} ∑ (Yᵢ - b'(⟪xᵢ, β⟫)) xᵢ`. The proof combines the law of large numbers for
`b''(⟪xᵢ, β⟫) ⟪xᵢ, h⟫²` with a third-order Taylor bound. -/
private lemma tendstoInMeasure_glmProcess {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {b : ℝ → ℝ} (hb : ContDiff ℝ 3 b)
    (hR : ∀ᵐ x ∂Px, ‖x‖ ≤ R) (β : EuclideanSpace ℝ (Fin p))
    (X : ℕ → Ω → EuclideanSpace ℝ (Fin p)) (Y : ℕ → Ω → ℝ)
    (hiid' : IsIndependentIdenticallyDistributed P (fun i ω ↦ (X i ω, Y i ω)) (Px ⊗ₘ κ))
    (haeR : ∀ᵐ ω ∂P, ∀ i, ‖X i ω‖ ≤ max R 0) (h : EuclideanSpace ℝ (Fin p)) :
    TendstoInMeasure P (fun (n : ℕ) ω ↦ ∑ i ∈ Finset.range n,
        (b (inner ℝ (X i ω) (β + (Real.sqrt n)⁻¹ • h)) - b (inner ℝ (X i ω) β) -
          Y i ω * inner ℝ (X i ω) ((Real.sqrt n)⁻¹ • h)) +
        ⟪(Real.sqrt n)⁻¹ • ∑ i ∈ Finset.range n,
          (Y i ω - deriv b (inner ℝ (X i ω) β)) • X i ω, h⟫_ℝ -
        ⟪h, Matrix.toEuclideanCLM (𝕜 := ℝ) (canonicalGLMInformation Px b β) h⟫_ℝ / 2)
      atTop (fun _ ↦ 0) := by
  have hb2 : Continuous (iteratedDeriv 2 b) := hb.continuous_iteratedDeriv 2 (by norm_num)
  set R0 := max R 0 with hR0
  set A : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p) :=
    Matrix.toEuclideanCLM (𝕜 := ℝ) (canonicalGLMInformation Px b β) with hA_def
  set U : ℕ → Ω → EuclideanSpace ℝ (Fin p) := fun n ω ↦
    (Real.sqrt n)⁻¹ • ∑ i ∈ Finset.range n, (Y i ω - deriv b (inner ℝ (X i ω) β)) • X i ω
    with hU
  set Z : ℕ → Ω → EuclideanSpace ℝ (Fin p) → ℝ := fun n ω h ↦ ∑ i ∈ Finset.range n,
    (b (inner ℝ (X i ω) (β + (Real.sqrt n)⁻¹ • h)) - b (inner ℝ (X i ω) β) -
      Y i ω * inner ℝ (X i ω) ((Real.sqrt n)⁻¹ • h)) with hZ
  change TendstoInMeasure P (fun (n : ℕ) ω ↦ Z n ω h + ⟪U n ω, h⟫_ℝ - ⟪h, A h⟫_ℝ / 2) atTop _
  set q := ⟪h, A h⟫_ℝ with hq_def
  set sfun : EuclideanSpace ℝ (Fin p) × ℝ → ℝ :=
    fun z ↦ iteratedDeriv 2 b (inner ℝ z.1 β) * inner ℝ z.1 h ^ 2 with hsfun
  have hgc : Continuous fun x : EuclideanSpace ℝ (Fin p) ↦
      iteratedDeriv 2 b (inner ℝ x β) * inner ℝ x h ^ 2 := by fun_prop
  have hq : ∫ z, sfun z ∂(Px ⊗ₘ κ) = q := by
    have := integral_comp_fst_compProd (Px := Px) (κ := κ) hgc
    rw [hsfun, this, integral_iteratedDeriv_mul_inner_sq hR hb2, hq_def, hA_def,
      Matrix.inner_toEuclideanCLM]
  have hsint : Integrable sfun (Px ⊗ₘ κ) := by
    have : Integrable (fun x : EuclideanSpace ℝ (Fin p) ↦
        iteratedDeriv 2 b (inner ℝ x β) * inner ℝ x h ^ 2) ((Px ⊗ₘ κ).map Prod.fst) := by
      rw [map_fst_compProd]
      exact integrable_of_continuous hR hgc
    exact this.comp_measurable measurable_fst
  have hwlln := tendstoInMeasure_sampleMean_of_iid P (Px ⊗ₘ κ) _ hiid' sfun
    (by fun_prop) hsint
  rw [hq] at hwlln
  set Qn : ℕ → Ω → ℝ := fun n ω ↦ (1 / 2 : ℝ) *
    ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, sfun (X i ω, Y i ω) - q) with hQn
  have h1 : TendstoInMeasure P Qn atTop (fun _ ↦ 0) := by
    refine tendstoInMeasure_const_mul_zero P _ (1 / 2) fun ε hε ↦ ?_
    simpa [edist_dist, Real.dist_eq] using hwlln ε hε
  have hR00 : 0 ≤ R0 := le_max_right _ _
  obtain ⟨M, hM0, hM⟩ := exists_abs_sum_taylor_le hb (R := R0) β
  set u : ℕ → ℝ := fun n ↦ n * (M * (R0 * ((Real.sqrt n)⁻¹ * ‖h‖)) ^ 3) with hu_def
  have hinv : Tendsto (fun n : ℕ ↦ (Real.sqrt n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hu : Tendsto u atTop (𝓝 0) := by
    have e : ∀ n : ℕ, u n = M * (R0 * ‖h‖) ^ 3 * (Real.sqrt n)⁻¹ := by
      intro n
      simp only [hu_def]
      rcases eq_or_ne (Real.sqrt n) 0 with h0 | h0
      · have : (n : ℝ) = 0 := by
          rw [← Real.sq_sqrt (Nat.cast_nonneg (n : ℕ)), h0]; ring
        simp [this]
      · have hn : (n : ℝ) = Real.sqrt n ^ 2 := (Real.sq_sqrt (Nat.cast_nonneg _)).symm
        nth_rewrite 1 [hn]
        field_simp
    rw [show u = fun n : ℕ ↦ M * (R0 * ‖h‖) ^ 3 * (Real.sqrt n)⁻¹ from funext e]
    simpa using hinv.const_mul (M * (R0 * ‖h‖) ^ 3)
  have hrem : TendstoInMeasure P (fun (n : ℕ) ω ↦
      Z n ω h + ⟪U n ω, h⟫_ℝ - q / 2 - Qn n ω) atTop (fun _ ↦ 0) := by
    refine tendstoInMeasure_zero_of_abs_le P (fun n _ ↦ u n) _ (fun _ _ ↦ 0) one_pos ?_
      (tendstoInMeasure_const_of_tendsto P u hu)
      (tendstoInMeasure_const_of_tendsto P _ tendsto_const_nhds)
    have hev : ∀ᶠ n : ℕ in atTop, R0 * ((Real.sqrt n)⁻¹ * ‖h‖) ≤ 1 := by
      have : Tendsto (fun n : ℕ ↦ R0 * ((Real.sqrt n)⁻¹ * ‖h‖)) atTop (𝓝 0) := by
        simpa using (hinv.mul_const ‖h‖).const_mul R0
      exact this.eventually (eventually_le_nhds one_pos)
    filter_upwards [hev] with n hn
    filter_upwards [haeR] with ω hω _
    have key := hM n (fun i ↦ X i ω) (Real.sqrt n)⁻¹ h (by positivity) hω hn
    have hs2 : ((Real.sqrt n)⁻¹) ^ 2 = (n : ℝ)⁻¹ := by
      rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    have hUh : ⟪U n ω, h⟫_ℝ = ∑ i ∈ Finset.range n,
        (Y i ω - deriv b (inner ℝ (X i ω) β)) * inner ℝ (X i ω) ((Real.sqrt n)⁻¹ • h) := by
      simp only [hU, real_inner_smul_left, sum_inner, inner_smul_right, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ ↦ by ring
    have hid : Z n ω h + ⟪U n ω, h⟫_ℝ - q / 2 - Qn n ω = ∑ i ∈ Finset.range n,
        (b (inner ℝ (X i ω) (β + (Real.sqrt n)⁻¹ • h)) - b (inner ℝ (X i ω) β) -
          deriv b (inner ℝ (X i ω) β) * inner ℝ (X i ω) ((Real.sqrt n)⁻¹ • h) -
          iteratedDeriv 2 b (inner ℝ (X i ω) β) *
            inner ℝ (X i ω) ((Real.sqrt n)⁻¹ • h) ^ 2 / 2) := by
      rw [show Z n ω h + ⟪U n ω, h⟫_ℝ - q / 2 - Qn n ω = Z n ω h + ⟪U n ω, h⟫_ℝ -
          1 / 2 * ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, sfun (X i ω, Y i ω)) by
        simp only [hQn]; ring]
      rw [hUh, Finset.mul_sum, Finset.mul_sum]
      simp only [hZ]
      rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      simp only [hsfun, inner_smul_right, mul_pow, hs2]
      ring
    have hu0 : 0 ≤ u n := mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg hM0 (pow_nonneg (mul_nonneg hR00 (by positivity)) 3))
    rw [hid, abs_of_nonneg hu0]
    exact key
  refine (tendstoInMeasure_add_zero P Qn _ h1 hrem).congr
    (fun n ↦ ae_of_all _ fun ω ↦ ?_) EventuallyEq.rfl
  simp only
  ring

end RandomDesign

/-- The rescaled negative log-likelihood process of a canonical-link model,
`h ↦ ∑_{i<n} (b(⟪xᵢ, β + h/√n⟫) - b(⟪xᵢ, β⟫) - yᵢ ⟪xᵢ, h/√n⟫)`, is convex when `b` is. -/
private theorem convexOn_canonicalGLMProcess {b : ℝ → ℝ} (hbconv : ConvexOn ℝ univ b)
    (β : EuclideanSpace ℝ (Fin p)) (x : ℕ → EuclideanSpace ℝ (Fin p)) (y : ℕ → ℝ) (n : ℕ) :
    ConvexOn ℝ univ fun h : EuclideanSpace ℝ (Fin p) ↦ ∑ i ∈ Finset.range n,
      (b (inner ℝ (x i) (β + (Real.sqrt n)⁻¹ • h)) - b (inner ℝ (x i) β) -
        y i * inner ℝ (x i) ((Real.sqrt n)⁻¹ • h)) := by
  refine ⟨convex_univ, fun u _ v _ a a' ha ha' hab ↦ ?_⟩
  simp only [smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  set s := (Real.sqrt n)⁻¹
  have key : inner ℝ (x i) (β + s • (a • u + a' • v)) =
      a • inner ℝ (x i) (β + s • u) + a' • inner ℝ (x i) (β + s • v) := by
    simp only [inner_add_right, inner_smul_right, smul_eq_mul]
    linear_combination (-(inner ℝ (x i) β)) * hab
  have hlin : inner ℝ (x i) (s • (a • u + a' • v)) =
      a * inner ℝ (x i) (s • u) + a' * inner ℝ (x i) (s • v) := by
    simp only [inner_add_right, inner_smul_right]
    ring
  have hρ := hbconv.2 (mem_univ (inner ℝ (x i) (β + s • u)))
    (mem_univ (inner ℝ (x i) (β + s • v))) ha ha' hab
  rw [key, hlin]
  simp only [smul_eq_mul] at hρ ⊢
  have : (a + a') * b (inner ℝ (x i) β) = b (inner ℝ (x i) β) := by rw [hab, one_mul]
  nlinarith

/-- A root `β̂` of the canonical-link likelihood equations minimizes the rescaled process
`h ↦ ∑_{i<n} (b(⟪xᵢ, β + h/√n⟫) - b(⟪xᵢ, β⟫) - yᵢ ⟪xᵢ, h/√n⟫)` at `h = √n (β̂ - β)`. -/
private theorem canonicalGLMProcess_le_of_isCanonicalGLMRoot {b : ℝ → ℝ}
    (hdiff : Differentiable ℝ b) (hbconv : ConvexOn ℝ univ b) (β : EuclideanSpace ℝ (Fin p))
    (x : ℕ → EuclideanSpace ℝ (Fin p)) (y : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n)
    {βh : EuclideanSpace ℝ (Fin p)} (hω : IsCanonicalGLMRoot b n x y βh)
    (h : EuclideanSpace ℝ (Fin p)) :
    ∑ i ∈ Finset.range n,
      (b (inner ℝ (x i) (β + (Real.sqrt n)⁻¹ • (Real.sqrt n • (βh - β)))) -
        b (inner ℝ (x i) β) - y i * inner ℝ (x i) ((Real.sqrt n)⁻¹ • (Real.sqrt n • (βh - β)))) ≤
      ∑ i ∈ Finset.range n, (b (inner ℝ (x i) (β + (Real.sqrt n)⁻¹ • h)) -
        b (inner ℝ (x i) β) - y i * inner ℝ (x i) ((Real.sqrt n)⁻¹ • h)) := by
  set s := (Real.sqrt n)⁻¹ with hs_def
  set a := Real.sqrt n • (βh - β) with ha_def
  have hs : Real.sqrt n ≠ 0 := Real.sqrt_ne_zero'.2 (by exact_mod_cast hn)
  have hβ' : β + s • a = βh := by
    rw [ha_def, smul_smul, hs_def, inv_mul_cancel₀ hs, one_smul, add_sub_cancel]
  rw [IsCanonicalGLMRoot, ← hβ'] at hω
  have hsum : ∑ i ∈ Finset.range n, (y i - deriv b (inner ℝ (x i) (β + s • a))) *
      (inner ℝ (x i) (s • h) - inner ℝ (x i) (s • a)) = 0 := by
    have := congrArg (fun w ↦ ⟪w, s • h - s • a⟫_ℝ) hω
    simp only [sum_inner] at this
    simpa only [real_inner_smul_left, inner_zero_left, inner_sub_right, mul_sub, sub_self]
      using this
  calc _ = ∑ i ∈ Finset.range n,
        ((b (inner ℝ (x i) (β + s • a)) - b (inner ℝ (x i) β) -
          y i * inner ℝ (x i) (s • a)) -
        (y i - deriv b (inner ℝ (x i) (β + s • a))) *
          (inner ℝ (x i) (s • h) - inner ℝ (x i) (s • a))) := by
        symm
        rw [Finset.sum_sub_distrib, hsum, sub_zero]
    _ ≤ _ := by
        refine Finset.sum_le_sum fun i _ ↦ ?_
        have htan := add_mul_sub_le_of_convexOn_of_hasDerivWithinAt hbconv
          (hdiff (inner ℝ (x i) (β + s • a))).hasDerivAt.hasDerivWithinAt
          (inner ℝ (x i) (β + s • h))
        have hvu : inner ℝ (x i) (β + s • h) - inner ℝ (x i) (β + s • a) =
            inner ℝ (x i) (s • h) - inner ℝ (x i) (s • a) := by
          simp only [inner_add_right]; ring
        rw [hvu] at htan
        linarith

/-- Studentization of a Gaussian limit: if `αₙ ⇒ N(0, φ J⁻¹)` with `J` positive definite and
`φ̂ₙ → φ > 0` in probability, then `φ̂ₙ^{-1/2} J^{1/2} αₙ ⇒ N(0, I)`. -/
private theorem tendstoInDistribution_studentized_glm {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {J : Matrix (Fin p) (Fin p) ℝ} (hJ : J.PosDef)
    {φ : ℝ} (hφ : 0 < φ) (α : ℕ → Ω → EuclideanSpace ℝ (Fin p))
    (hαm : ∀ n, Measurable (α n))
    (hlim1 : TendstoInDistribution α atTop id (fun _ ↦ P) (multivariateGaussian 0 (φ • J⁻¹)))
    (φhat : ℕ → Ω → ℝ) (hφm : ∀ n, Measurable (φhat n))
    (hφcons : TendstoInMeasure P φhat atTop (fun _ ↦ φ)) :
    TendstoInDistribution (fun (n : ℕ) ω ↦ (Real.sqrt (φhat n ω))⁻¹ •
        Matrix.toEuclideanLin (CFC.sqrt J) (α n ω)) atTop id (fun _ ↦ P)
      (multivariateGaussian 0 1) := by
  have hdet : IsUnit J.det := (Matrix.isUnit_iff_isUnit_det _).1 hJ.isUnit
  set S := CFC.sqrt J with hS_def
  have hJ0 : 0 ≤ J := Matrix.nonneg_iff_posSemidef.2 hJ.posSemidef
  have hSS : S * S = J := CFC.sqrt_mul_sqrt_self J hJ0
  have hS0 : S.PosSemidef := Matrix.nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg J)
  have hSt : S.transpose = S := (Matrix.isHermitian_iff_isSymm.1 hS0.isHermitian).eq
  have hSdet : IsUnit S.det := by
    rw [← hSS, Matrix.det_mul] at hdet
    exact isUnit_of_mul_isUnit_left hdet
  have hSJS : S * J⁻¹ * S = 1 := by
    rw [← hSS, Matrix.mul_inv_rev, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hSdet,
      Matrix.one_mul, Matrix.nonsing_inv_mul _ hSdet]
  set k := (Real.sqrt φ)⁻¹ with hk_def
  have hk : k * k * φ = 1 := by
    rw [hk_def, ← mul_inv, Real.mul_self_sqrt hφ.le, inv_mul_cancel₀ hφ.ne']
  set Mk := k • S with hMk
  have hS1 : (φ • J⁻¹).PosSemidef := hJ.inv.posSemidef.smul hφ.le
  have hT : TendstoInDistribution (fun (n : ℕ) ω ↦ Mk.toEuclideanLin (α n ω)) atTop id
      (fun _ ↦ P) (multivariateGaussian 0 1) := by
    have hm := TauCeti.Probability.map_affine_multivariateGaussian 0 hS1 Mk 0
    simp only [add_zero, map_zero] at hm
    refine tendstoInDistribution_of_map_eq (hlim1.continuous_comp
      (LinearMap.continuous_of_finiteDimensional Mk.toEuclideanLin)) aemeasurable_id ?_
    rw [Measure.map_id, Function.comp_id, hm]
    have hM : Mk * (φ • J⁻¹) * Mk.transpose = 1 := by
      rw [hMk, Matrix.transpose_smul, hSt, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.mul_smul, Matrix.smul_mul, hSJS, smul_smul, smul_smul]
      rw [hk, one_smul]
    rw [hM]
  set V : ℕ → Ω → EuclideanSpace ℝ (Fin p) := fun n ω ↦ S.toEuclideanLin (α n ω) with hV
  have hVd : TendstoInDistribution V atTop id (fun _ ↦ P)
      ((multivariateGaussian 0 (φ • J⁻¹)).map S.toEuclideanLin) := by
    have := hlim1.continuous_comp (LinearMap.continuous_of_finiteDimensional S.toEuclideanLin)
    refine tendstoInDistribution_of_map_eq this (by fun_prop) ?_
    rw [Function.comp_id, Measure.map_id]
  have hc : TendstoInMeasure P (fun (n : ℕ) ω ↦ (Real.sqrt (φhat n ω))⁻¹ - k) atTop
      (fun _ ↦ 0) := by
    have hcont : ContinuousAt (fun x ↦ (Real.sqrt x)⁻¹ - k) φ :=
      (Real.continuous_sqrt.continuousAt.inv₀ (Real.sqrt_ne_zero'.2 hφ)).sub continuousAt_const
    simpa [hk_def] using tendstoInMeasure_comp_of_continuousAt P φhat φ _ hcont hφcons
  have hsm := tendstoInMeasure_smul_zero P _ V hc hVd
  refine tendstoInDistribution_of_tendstoInMeasure_sub_of_measurable P _ _
    (fun n ↦ (LinearMap.continuous_of_finiteDimensional _).measurable.comp (hαm n))
    (fun n ↦ ((Real.continuous_sqrt.measurable.comp (hφm n)).inv).smul
      ((LinearMap.continuous_of_finiteDimensional _).measurable.comp (hαm n))) hT ?_
  refine hsm.congr (fun n ↦ ae_of_all _ fun ω ↦ ?_) EventuallyEq.rfl
  simp only [hV, hMk, map_smul, LinearMap.smul_apply, sub_smul, Function.comp_apply]

/-- The normalized canonical GLM score converges to its Gaussian information limit. -/
private theorem tendstoInDistribution_canonicalGLM_score {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Measure ℝ) (b : ℝ → ℝ) (hb : ContDiff ℝ 3 b)
    (φ : ℝ) (hφ : 0 < φ)
    (hlaw : ∀ θ, IsProbabilityMeasure (exponentialDispersionLaw ν b φ θ))
    (Px : Measure (EuclideanSpace ℝ (Fin p))) [IsProbabilityMeasure Px]
    (κ : Kernel (EuclideanSpace ℝ (Fin p)) ℝ) [IsMarkovKernel κ]
    (β : EuclideanSpace ℝ (Fin p))
    (hκ : ∀ x, κ x = exponentialDispersionLaw ν b φ (inner ℝ x β))
    (R : ℝ) (hR : ∀ᵐ x ∂Px, ‖x‖ ≤ R)
    (X : ℕ → Ω → EuclideanSpace ℝ (Fin p)) (Y : ℕ → Ω → ℝ)
    (hiid' : IsIndependentIdenticallyDistributed P (fun i w ↦ (X i w,Y i w)) (Px ⊗ₘ κ))
    (hJ : (canonicalGLMInformation Px b β).PosDef) :
    let U := fun (n : ℕ) w ↦ (Real.sqrt n)⁻¹ • ∑ i ∈ Finset.range n,
      (Y i w-deriv b (inner ℝ (X i w) β)) • X i w
    (∀ n, Measurable (U n)) ∧ TendstoInDistribution U atTop id (fun _ ↦ P)
      (multivariateGaussian 0 (φ • canonicalGLMInformation Px b β)) := by
  intro U
  let J := canonicalGLMInformation Px b β
  have hXm : ∀ i, Measurable (X i) := fun i ↦ measurable_fst.comp (hiid'.1 i)
  have hYm : ∀ i, Measurable (Y i) := fun i ↦ measurable_snd.comp (hiid'.1 i)
  have hd1 : Continuous (deriv b) := hb.continuous_deriv (by norm_num)
  have hUm : ∀ n, Measurable (U n) := fun n ↦ by
    have := hXm; have := hYm
    dsimp only [U]
    fun_prop
  have hS : (φ • J).PosSemidef := hJ.posSemidef.smul hφ.le
  refine ⟨hUm,?_⟩
  refine TendstoInDistribution.of_inner aemeasurable_id (fun n ↦ (hUm n).aemeasurable)
    fun v ↦ ?_
  obtain ⟨h2, h0, hsq⟩ := memLp_score_and_integral hb hφ hlaw hR hκ v
  have key := tendstoInDistribution_inv_sqrt_mul_sum_of_iid P (Px ⊗ₘ κ) _ hiid'
    (fun z ↦ (z.2 - deriv b (inner ℝ z.1 β)) * inner ℝ z.1 v) (by fun_prop) h2 h0
  have hfun : (fun (n : ℕ) ω ↦ ⟪U n ω, v⟫_ℝ) = fun (n : ℕ) ω ↦ (Real.sqrt n)⁻¹ *
      ∑ i ∈ Finset.range n, (Y i ω - deriv b (inner ℝ (X i ω) β)) * inner ℝ (X i ω) v := by
    funext n ω
    simp only [U, real_inner_smul_left, sum_inner]
  rw [hfun]
  refine tendstoInDistribution_of_map_eq key (by fun_prop) ?_
  have hW : (fun z : EuclideanSpace ℝ (Fin p) ↦ ⟪id z, v⟫_ℝ) = fun z ↦ ⟪v, z⟫_ℝ :=
    funext fun z ↦ real_inner_comm _ _
  rw [hW, TauCeti.Probability.map_inner_multivariateGaussian 0 v hS, Measure.map_id,
    inner_zero_right, ← Matrix.coe_toEuclideanCLM_eq_toEuclideanLin, hsq]
  congr 2
  change ⟪v, Matrix.toEuclideanCLM (𝕜 := ℝ) (φ • J) v⟫_ℝ = _
  rw [Matrix.inner_toEuclideanCLM, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

/-- GAPS 105.3, canonical-link form: for independent and identically distributed pairs
`(xᵢ, Yᵢ)` whose response given the covariate is exponential-dispersion with natural parameter
`⟪x, β⟫`, with covariates bounded by `R`, smooth cumulant function, natural parameter space all
of `ℝ`, and nonsingular `J = E[x xᵀ b''(⟪x, β⟫)]`, every measurable root `β̂` of the likelihood
equations satisfies `√n (β̂ - β) ⇒ N(0, φ J⁻¹)`, and
`φ̂^{-1/2} J^{1/2} √n (β̂ - β) ⇒ N(0, I_p)` for every consistent `φ̂`. Restrictions of scope:
canonical link (`g = (b')⁻¹`), bounded covariates, and natural parameter space `ℝ`; the
general twice-differentiable link is not covered. Consistency of `β̂` is not assumed: the log
likelihood is concave, so every root is a maximizer, and the argument goes through the
convexity lemma `CKSD.tendstoInMeasure_sub_of_convexOn_of_isMinOn`. -/
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
  classical
  set J := canonicalGLMInformation Px b β with hJ_def
  obtain ⟨hZm, hind, hlawZ⟩ := hiid
  have hiid' : IsIndependentIdenticallyDistributed P (fun i ω ↦ (X i ω, Y i ω)) (Px ⊗ₘ κ) :=
    ⟨hZm, hind, hlawZ⟩
  have hXm : ∀ i, Measurable (X i) := fun i ↦ measurable_fst.comp (hZm i)
  have hYm : ∀ i, Measurable (Y i) := fun i ↦ measurable_snd.comp (hZm i)
  have hd1 : Continuous (deriv b) := hb.continuous_deriv (by norm_num)
  have hb2 : Continuous (iteratedDeriv 2 b) := hb.continuous_iteratedDeriv 2 (by norm_num)
  have hdiff : Differentiable ℝ b := hb.differentiable (by norm_num)
  have hbconv : ConvexOn ℝ univ b := by
    refine convexOn_univ_of_deriv2_nonneg hdiff ?_ fun x ↦ ?_
    · have := hb.differentiable_iteratedDeriv 1 (by norm_num)
      rwa [iteratedDeriv_one] at this
    · rw [← iteratedDeriv_eq_iterate]
      exact iteratedDeriv_two_nonneg hφ hlaw x
  -- covariates are bounded almost surely
  set R0 := max R 0 with hR0
  have haeR : ∀ᵐ ω ∂P, ∀ i, ‖X i ω‖ ≤ R0 := by
    refine ae_all_iff.2 fun i ↦ ?_
    have h1 : ∀ᵐ z ∂(Px ⊗ₘ κ), ‖z.1‖ ≤ R0 := by
      have := hR
      rw [← map_fst_compProd (Px := Px) (κ := κ)] at this
      exact (ae_of_ae_map measurable_fst.aemeasurable this).mono fun z hz ↦
        hz.trans (le_max_left _ _)
    rw [← hlawZ i] at h1
    exact ae_of_ae_map (hZm i).aemeasurable h1
  -- the information operator
  set A : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p) :=
    Matrix.toEuclideanCLM (𝕜 := ℝ) J with hA_def
  set B : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p) :=
    Matrix.toEuclideanCLM (𝕜 := ℝ) J⁻¹ with hB_def
  have hdet : IsUnit J.det := (Matrix.isUnit_iff_isUnit_det _).1 hJ.isUnit
  have hAB : ∀ u, A (B u) = u := fun u ↦ by
    change (Matrix.toEuclideanCLM (𝕜 := ℝ) J * Matrix.toEuclideanCLM (𝕜 := ℝ) J⁻¹) u = u
    rw [← map_mul, Matrix.mul_nonsing_inv _ hdet, map_one]
    rfl
  have hAsymm : ∀ u v, ⟪A u, v⟫_ℝ = ⟪u, A v⟫_ℝ :=
    fun u v ↦ (Matrix.isSymmetric_toEuclideanLin_iff.2 hJ.isHermitian) u v
  obtain ⟨c, hc, hA⟩ := exists_pos_mul_sq_le_inner_toEuclideanCLM hJ
  -- the normalized score and its central limit theorem
  set U : ℕ → Ω → EuclideanSpace ℝ (Fin p) := fun n ω ↦
    (Real.sqrt n)⁻¹ • ∑ i ∈ Finset.range n, (Y i ω - deriv b (inner ℝ (X i ω) β)) • X i ω
    with hU
  have hUm : ∀ n, Measurable (U n) := fun n ↦ by
    have := hXm; have := hYm
    fun_prop
  have hS : (φ • J).PosSemidef := hJ.posSemidef.smul hφ.le
  have hclt : TendstoInDistribution U atTop id (fun _ ↦ P) (multivariateGaussian 0 (φ • J)) := by
    have hh := (tendstoInDistribution_canonicalGLM_score P ν b hb φ hφ hlaw Px κ β
      hκ R hR X Y hiid' hJ).2
    simpa only [hU,hJ_def] using hh
  have htight : ∀ η > (0 : ℝ≥0∞), ∃ M : ℝ, ∀ᶠ n in atTop, P {ω | M < ‖U n ω‖} ≤ η := by
    intro η hη
    rcases eq_or_ne η ⊤ with rfl | hηt
    · exact ⟨0, Eventually.of_forall fun _ ↦ le_top⟩
    obtain ⟨M, -, hM⟩ := exists_measureReal_lt_norm_le_of_tendstoInDistribution P U hclt
      (ENNReal.toReal_pos hη.ne' hηt)
    refine ⟨M, hM.mono fun n hn ↦ ?_⟩
    rw [← ofReal_measureReal]
    exact (ENNReal.ofReal_le_iff_le_toReal hηt).2 hn
  -- the convex process
  set Z : ℕ → Ω → EuclideanSpace ℝ (Fin p) → ℝ := fun n ω h ↦ ∑ i ∈ Finset.range n,
    (b (inner ℝ (X i ω) (β + (Real.sqrt n)⁻¹ • h)) - b (inner ℝ (X i ω) β) -
      Y i ω * inner ℝ (X i ω) ((Real.sqrt n)⁻¹ • h)) with hZ
  have hZc : ∀ n ω, ConvexOn ℝ univ (Z n ω) := fun n ω ↦
    convexOn_canonicalGLMProcess hbconv β (fun i ↦ X i ω) (fun i ↦ Y i ω) n
  -- roots are minimizers
  set α : ℕ → Ω → EuclideanSpace ℝ (Fin p) := fun n ω ↦ Real.sqrt n • (βhat n ω - β) with hα
  have hmin' : ∀ᶠ n in atTop, ∀ᵐ ω ∂P, ∀ h, Z n ω (α n ω) ≤ Z n ω h := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    filter_upwards [hroot n hn] with ω hω h
    exact canonicalGLMProcess_le_of_isCanonicalGLMRoot hdiff hbconv β _ _ hn hω h
  -- pointwise convergence of the convex process
  have hpt : ∀ h, ∀ ε > 0, Tendsto (fun n ↦
      P {ω | ε ≤ |Z n ω h + ⟪U n ω, h⟫_ℝ - ⟪h, A h⟫_ℝ / 2|}) atTop (𝓝 0) := by
    intro h ε hε
    have H : TendstoInMeasure P (fun (n : ℕ) ω ↦ Z n ω h + ⟪U n ω, h⟫_ℝ - ⟪h, A h⟫_ℝ / 2)
        atTop (fun _ ↦ 0) := by
      exact tendstoInMeasure_glmProcess P hb hR β X Y hiid' haeR h
    simpa [Real.dist_eq] using tendstoInMeasure_iff_dist.1 H ε hε
  have hlin := tendstoInMeasure_sub_of_convexOn_of_isMinOn Z hZc U A B hAB hAsymm hc hA hpt
    htight α hmin'
  -- the limit law of `√n (β̂ₙ - β)`
  have hsymm : J⁻¹.transpose = J⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, (Matrix.isHermitian_iff_isSymm.1 hJ.isHermitian).eq]
  have hlim1 : TendstoInDistribution α atTop id (fun _ ↦ P)
      (multivariateGaussian 0 (φ • J⁻¹)) := by
    set g : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p) :=
      fun y ↦ (J⁻¹).toEuclideanLin y + 0 with hg
    have hgc : Continuous g := (LinearMap.continuous_of_finiteDimensional _).add continuous_const
    have hmap := TauCeti.Probability.map_affine_multivariateGaussian 0 hS J⁻¹ 0
    have hlimU : TendstoInDistribution (fun (n : ℕ) ↦ g ∘ U n) atTop id (fun _ ↦ P)
        (multivariateGaussian 0 (φ • J⁻¹)) := by
      refine tendstoInDistribution_of_map_eq (hclt.continuous_comp hgc) aemeasurable_id ?_
      rw [Measure.map_id, Function.comp_id, hmap, hsymm, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]
      simp
    refine tendstoInDistribution_of_tendstoInMeasure_sub_of_measurable P _ _
      (fun n ↦ hgc.measurable.comp (hUm n)) (fun n ↦ by have := hβm n; fun_prop) hlimU ?_
    refine hlin.congr (fun n ↦ ae_of_all _ fun ω ↦ ?_) EventuallyEq.rfl
    simp only [hα, hg, Function.comp_apply, add_zero, hB_def,
      ← Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
    rfl
  refine ⟨hlim1, ?_⟩
  exact tendstoInDistribution_studentized_glm P hJ hφ α
    (fun n ↦ by have := hβm n; fun_prop) hlim1 φhat hφm hφcons

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
  classical
  -- Convexity controls the minimizers without needing the stated consistency assumptions.
  clear hcons hcons'
  let J := canonicalGLMInformation Px b β
  let S := CFC.sqrt J⁻¹
  obtain ⟨F,hF,hFlinear,hFquad⟩ := exists_glm_whitening hJ hφ
  let K := L.map F.symm.toLinearMap
  let U := fun (n : ℕ) w ↦ (Real.sqrt n)⁻¹ • ∑ i ∈ Finset.range n,
    (Y i w-deriv b (inner ℝ (X i w) β)) • X i w
  obtain ⟨hUm,hclt⟩ := tendstoInDistribution_canonicalGLM_score P ν b hb φ hφ hlaw Px κ β
    hκ R hR X Y hiid hJ
  change (∀ n, Measurable (U n)) at hUm
  change TendstoInDistribution U atTop id (fun _ ↦ P) (multivariateGaussian 0 (φ • J)) at hclt
  let W := fun (n : ℕ) w ↦ (Real.sqrt φ)⁻¹ • S.toEuclideanLin (U n w)
  have hWm : ∀ n, Measurable (W n) := fun n ↦ by
    change Measurable ((fun x : EuclideanSpace ℝ (Fin p) ↦
      (Real.sqrt φ)⁻¹ • S.toEuclideanLin x) ∘ U n)
    exact ((LinearMap.continuous_of_finiteDimensional S.toEuclideanLin).const_smul
      (Real.sqrt φ)⁻¹).measurable.comp (hUm n)
  have hWclt : TendstoInDistribution W atTop id (fun _ ↦ P)
      (stdGaussian (EuclideanSpace ℝ (Fin p))) := by
    have hJJ : J⁻¹⁻¹=J := Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hJ.isUnit)
    have hc : TendstoInMeasure P (fun (_ : ℕ) (_ : Ω) ↦ φ) atTop (fun _ ↦ φ) := by
      rw [tendstoInMeasure_iff_norm]
      intro ε hε
      simp [hε.not_ge]
    have hJlocal : J.PosDef := hJ
    have hh := tendstoInDistribution_studentized_glm P hJlocal.inv hφ U hUm
      (by simpa only [hJJ] using hclt) (fun _ _ ↦ φ) (fun _ ↦ measurable_const) hc
    simpa only [multivariateGaussian_zero_one] using hh
  have hXm : ∀ i, Measurable (X i) := fun i ↦ measurable_fst.comp (hiid.1 i)
  have hYm : ∀ i, Measurable (Y i) := fun i ↦ measurable_snd.comp (hiid.1 i)
  have hdiff : Differentiable ℝ b := hb.differentiable (by norm_num)
  have hbconv : ConvexOn ℝ univ b := by
    refine convexOn_univ_of_deriv2_nonneg hdiff ?_ fun x ↦ ?_
    · have := hb.differentiable_iteratedDeriv 1 (by norm_num)
      rwa [iteratedDeriv_one] at this
    · rw [← iteratedDeriv_eq_iterate]
      exact iteratedDeriv_two_nonneg hφ hlaw x
  have haeR : ∀ᵐ w ∂P, ∀ i, ‖X i w‖ ≤ max R 0 := by
    refine ae_all_iff.2 fun i ↦ ?_
    have h1 : ∀ᵐ z ∂(Px ⊗ₘ κ), ‖z.1‖ ≤ max R 0 := by
      have hh := hR
      rw [← map_fst_compProd (Px := Px) (κ := κ)] at hh
      exact (ae_of_ae_map measurable_fst.aemeasurable hh).mono fun z hz ↦
        hz.trans (le_max_left _ _)
    rw [← hiid.2.2 i] at h1
    exact ae_of_ae_map (hiid.1 i).aemeasurable h1
  let Z0 := fun (n : ℕ) w h ↦ ∑ i ∈ Finset.range n,
    (b (inner ℝ (X i w) (β+(Real.sqrt n)⁻¹ • h))-b (inner ℝ (X i w) β)-
      Y i w * inner ℝ (X i w) ((Real.sqrt n)⁻¹ • h))
  let Z := fun (n : ℕ) w h ↦ Z0 n w (F h)/φ
  have hZc : ∀ n w, ConvexOn ℝ univ (Z n w) := by
    intro n w
    have hh := convexOn_canonicalGLMProcess hbconv β (fun i ↦ X i w) (fun i ↦ Y i w) n
    refine ⟨convex_univ, fun x _ y _ a b ha hb hab ↦ ?_⟩
    have hxy := hh.2 (mem_univ (F x)) (mem_univ (F y)) ha hb hab
    have hscaled := div_le_div_of_nonneg_right hxy hφ.le
    simpa only [Z,Z0,map_add,map_smul,smul_eq_mul,add_div,mul_div_assoc] using hscaled
  have hpt : ∀ h, ∀ ε > 0, Tendsto (fun n ↦
      P {w | ε ≤ |Z n w h+inner ℝ (W n w) h-‖h‖^2/2|}) atTop (𝓝 0) := by
    intro h ε hε
    have hh := tendstoInMeasure_glmProcess P hb hR β X Y hiid haeR (F h)
    have hscaled := tendstoInMeasure_const_mul_zero P _ φ⁻¹ hh
    have heq (n) (w) : φ⁻¹ * (Z0 n w (F h)+inner ℝ (U n w) (F h)-
        inner ℝ (F h) (J.toEuclideanLin (F h))/2) =
        Z n w h+inner ℝ (W n w) h-‖h‖^2/2 := by
      rw [← hFlinear,← hFquad]
      dsimp only [Z]
      ring
    have hscaled' : TendstoInMeasure P (fun n w ↦ Z n w h+inner ℝ (W n w) h-‖h‖^2/2)
        atTop (fun _ ↦ 0) := by
      refine hscaled.congr (fun n ↦ ae_of_all _ fun w ↦ ?_) EventuallyEq.rfl
      simpa only [Z0,U,J,← Matrix.coe_toEuclideanCLM_eq_toEuclideanLin, ContinuousLinearMap.coe_coe] using heq n w
    simpa only [Real.dist_eq,sub_zero] using (tendstoInMeasure_iff_dist.1 hscaled') ε hε
  let α := fun (n : ℕ) w ↦ F.symm (Real.sqrt n • (βhat n w-β))
  let β0 := fun (n : ℕ) w ↦ F.symm (Real.sqrt n • (βtilde n w-β))
  have hβ0mem (n) (w) (hw : βtilde n w ∈ L) : β0 n w ∈ K := by
    exact Submodule.mem_map.2 ⟨Real.sqrt n • (βtilde n w-β),
      L.smul_mem _ (L.sub_mem hw hβL),rfl⟩
  let βK := fun (n : ℕ) w ↦ if hh : β0 n w ∈ K then (⟨β0 n w,hh⟩ : K) else 0
  have hβKcoe (n) (w) (hw : βtilde n w ∈ L) : (βK n w : EuclideanSpace ℝ (Fin p)) = β0 n w := by
    simp only [βK,dite_eq_left (hβ0mem n w hw)]
  have hZLL (n) (w) (h) : Z n w h =
      canonicalGLMLogLikelihood b φ n (fun i ↦ X i w) (fun i ↦ Y i w) β-
      canonicalGLMLogLikelihood b φ n (fun i ↦ X i w) (fun i ↦ Y i w)
        (β+(Real.sqrt n)⁻¹ • F h) := by
    simp only [Z,Z0,canonicalGLMLogLikelihood,← Finset.sum_div]
    rw [← sub_div,← Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    simp only [inner_add_right]
    ring
  have hαcenter (n : ℕ) (hn : 0 < n) (w) : β+(Real.sqrt n)⁻¹ • F (α n w)=βhat n w := by
    simp only [α,F.apply_symm_apply,smul_smul,
      inv_mul_cancel₀ (Real.sqrt_ne_zero'.2 (Nat.cast_pos.2 hn)),one_smul,add_sub_cancel]
  have hβcenter (n : ℕ) (hn : 0 < n) (w) (hw : βtilde n w ∈ L) :
      β+(Real.sqrt n)⁻¹ • F (βK n w)=βtilde n w := by
    rw [hβKcoe n w hw]
    simp only [β0,F.apply_symm_apply,smul_smul,
      inv_mul_cancel₀ (Real.sqrt_ne_zero'.2 (Nat.cast_pos.2 hn)),one_smul,add_sub_cancel]
  have hminα : ∀ᶠ n in atTop, ∀ᵐ w ∂P, ∀ h, Z n w (α n w) ≤ Z n w h := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    filter_upwards [hroot n hn] with w hw h
    have hle := canonicalGLMProcess_le_of_isCanonicalGLMRoot hdiff hbconv β _ _ hn hw (F h)
    have hdiv := div_le_div_of_nonneg_right hle hφ.le
    simpa only [Z,Z0,α,F.apply_symm_apply] using hdiv
  have hminβ : ∀ᶠ n in atTop, ∀ᵐ w ∂P, ∀ h : K, Z n w (βK n w) ≤ Z n w h := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    filter_upwards [hmax n] with w hw h
    have hFh : F (h : EuclideanSpace ℝ (Fin p)) ∈ L := by
      obtain ⟨v,hv,he⟩ := Submodule.mem_map.1 h.property
      rw [← he]
      change F (F.symm v) ∈ L
      simpa only [F.apply_symm_apply] using hv
    have hnew : β+(Real.sqrt n)⁻¹ • F (h : EuclideanSpace ℝ (Fin p)) ∈ L :=
      L.add_mem hβL (L.smul_mem _ hFh)
    have hh := hw.2 _ hnew
    rw [hZLL,hZLL,hβcenter n (by omega) w hw.1]
    linarith
  let D := fun (n : ℕ) w ↦ 2*(canonicalGLMLogLikelihood b φ n (fun i ↦ X i w)
    (fun i ↦ Y i w) (βhat n w)-canonicalGLMLogLikelihood b φ n (fun i ↦ X i w)
      (fun i ↦ Y i w) (βtilde n w))
  have hDm : ∀ n, Measurable (D n) := by
    intro n
    have hβ := hβm n
    have hβ' := hβm' n
    have hm_b := hb.continuous.measurable
    dsimp only [D,canonicalGLMLogLikelihood]
    fun_prop
  have hDeq (n : ℕ) : D n =ᵐ[P] fun w ↦ -2*(Z n w (α n w)-Z n w (βK n w)) := by
    filter_upwards [hmax n] with w hw
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [D,Z,Z0,canonicalGLMLogLikelihood]
    · rw [hZLL,hZLL,hαcenter n hn w,hβcenter n hn w hw.1]
      dsimp only [D]
      ring
  have hdim : Module.finrank ℝ Kᗮ = p-Module.finrank ℝ L := by
    have hdim1 := K.finrank_add_finrank_orthogonal
    have hdim2 : Module.finrank ℝ K = Module.finrank ℝ L := F.symm.finrank_map_eq L
    simp only [finrank_euclideanSpace,Fintype.card_fin,hdim2] at hdim1
    omega
  have hlimit := tendstoInDistribution_convex_deviance P Z hZc W hWm hWclt hpt K α βK
    hminα hminβ D hDm hDeq
  simpa only [hdim] using hlimit

end CKSD
