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

* `CKSD.tendsto_in_distribution_canonical_glm_root`: asymptotic normality
  `√n (β̂ - β) ⇒ N(0, φ J⁻¹)` of roots of the likelihood equations, and its studentized form.
* `CKSD.tendsto_in_distribution_canonical_glm_deviance`: the deviance difference of nested
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
lemma lintegral_exp_mul_eq (hφ : 0 < φ)
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
lemma integrable_exp_mul (hφ : 0 < φ)
    (hlaw : ∀ θ, IsProbabilityMeasure (exponentialDispersionLaw ν b φ θ)) (s : ℝ) :
    Integrable (fun y ↦ Real.exp (s * y)) ν :=
  ⟨(by fun_prop : Measurable fun y : ℝ ↦ Real.exp (s * y)).aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ ↦ (Real.exp_pos _).le)).2
      (by rw [lintegral_exp_mul_eq hφ hlaw]; exact ENNReal.ofReal_lt_top)⟩

lemma mem_interior_integrable_exp_set (hφ : 0 < φ)
    (hlaw : ∀ θ, IsProbabilityMeasure (exponentialDispersionLaw ν b φ θ)) (s : ℝ) :
    s ∈ interior (integrableExpSet id ν) := by
  have : integrableExpSet id ν = univ :=
    eq_univ_of_forall fun t ↦ by simpa [integrableExpSet] using integrable_exp_mul hφ hlaw t
  rw [this, interior_univ]; trivial

/-- `mgf ν (s) = exp (b(φ s) / φ)`. -/
lemma mgf_id_eq (hφ : 0 < φ)
    (hlaw : ∀ θ, IsProbabilityMeasure (exponentialDispersionLaw ν b φ θ)) (s : ℝ) :
    mgf id ν s = Real.exp (b (φ * s) / φ) := by
  rw [mgf, integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ ↦ (Real.exp_pos _).le)
    (by fun_prop : Measurable fun y : ℝ ↦ Real.exp (s * id y)).aestronglyMeasurable]
  simp only [id]
  rw [lintegral_exp_mul_eq hφ hlaw, ENNReal.toReal_ofReal (Real.exp_pos _).le]

/-- The cumulant function is a rescaled cumulant generating function:
`b θ = φ · cgf_ν (θ / φ)`. -/
lemma eq_mul_cgf (hφ : 0 < φ)
    (hlaw : ∀ θ, IsProbabilityMeasure (exponentialDispersionLaw ν b φ θ)) :
    b = fun θ ↦ φ * cgf id ν (φ⁻¹ * θ) := by
  funext θ
  rw [cgf, mgf_id_eq hφ hlaw, Real.log_exp, mul_inv_cancel_left₀ hφ.ne']
  field_simp

lemma cont_diff_cgf (hφ : 0 < φ)
    (hlaw : ∀ θ, IsProbabilityMeasure (exponentialDispersionLaw ν b φ θ)) {n : WithTop ℕ∞} :
    ContDiff ℝ n (cgf id ν) :=
  AnalyticOnNhd.contDiff fun s _ ↦ analyticOnNhd_cgf s (mem_interior_integrable_exp_set hφ hlaw s)

lemma deriv_eq_deriv_cgf (hφ : 0 < φ)
    (hlaw : ∀ θ, IsProbabilityMeasure (exponentialDispersionLaw ν b φ θ)) (θ : ℝ) :
    deriv b θ = deriv (cgf id ν) (φ⁻¹ * θ) := by
  have hd : DifferentiableAt ℝ (cgf id ν) (φ⁻¹ * θ) :=
    (cont_diff_cgf hφ hlaw (n := 1)).differentiable one_ne_zero _
  have h := (hd.hasDerivAt.comp θ ((hasDerivAt_id θ).const_mul φ⁻¹)).const_mul φ
  have h' : HasDerivAt (fun θ ↦ φ * cgf id ν (φ⁻¹ * θ)) (deriv (cgf id ν) (φ⁻¹ * θ)) θ := by
    simp only [Function.comp_def, mul_one] at h
    rwa [← mul_assoc, mul_comm φ, mul_assoc, mul_inv_cancel₀ hφ.ne', mul_one] at h
  rw [eq_mul_cgf hφ hlaw, h'.deriv]

lemma iterated_deriv_two_eq (hφ : 0 < φ)
    (hlaw : ∀ θ, IsProbabilityMeasure (exponentialDispersionLaw ν b φ θ)) (θ : ℝ) :
    iteratedDeriv 2 b θ = φ⁻¹ * iteratedDeriv 2 (cgf id ν) (φ⁻¹ * θ) := by
  rw [eq_mul_cgf hφ hlaw, iteratedDeriv_const_mul_field,
    iteratedDeriv_comp_const_mul (cont_diff_cgf hφ hlaw) φ⁻¹]
  field_simp

/-- Integrals against the exponential dispersion law. -/
lemma integral_exponential_dispersion_law (g : ℝ → ℝ) (θ : ℝ) :
    ∫ y, g y ∂(exponentialDispersionLaw ν b φ θ) =
      ∫ y, Real.exp ((y * θ - b θ) / φ) * g y ∂ν := by
  rw [exponentialDispersionLaw]
  have := integral_withDensity_eq_integral_smul (μ := ν)
    (f := fun y ↦ (Real.exp ((y * θ - b θ) / φ)).toNNReal) (by fun_prop) g
  simp only [ENNReal.ofReal] at this ⊢
  rw [this]
  refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
  simp [NNReal.smul_def, Real.coe_toNNReal _ (Real.exp_pos _).le]

lemma integrable_exponential_dispersion_law_iff {g : ℝ → ℝ} (θ : ℝ) :
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
lemma exp_div_eq (hφ : 0 < φ)
    (hlaw : ∀ θ, IsProbabilityMeasure (exponentialDispersionLaw ν b φ θ)) (θ y : ℝ) :
    Real.exp ((y * θ - b θ) / φ) = Real.exp (φ⁻¹ * θ * id y) / mgf id ν (φ⁻¹ * θ) := by
  rw [mgf_id_eq hφ hlaw, mul_inv_cancel_left₀ hφ.ne', ← Real.exp_sub]
  congr 1
  simp only [id]
  field_simp

/-- Polynomial moments of the exponential dispersion law are finite. -/
lemma integrable_pow_exponential_dispersion_law (hφ : 0 < φ)
    (hlaw : ∀ θ, IsProbabilityMeasure (exponentialDispersionLaw ν b φ θ)) (θ : ℝ) (k : ℕ) :
    Integrable (fun y ↦ y ^ k) (exponentialDispersionLaw ν b φ θ) := by
  rw [integrable_exponential_dispersion_law_iff]
  have h := (integrable_pow_mul_exp_of_mem_interior_integrableExpSet
    (mem_interior_integrable_exp_set hφ hlaw (φ⁻¹ * θ)) k).div_const (mgf id ν (φ⁻¹ * θ))
  refine h.congr (ae_of_all _ fun y ↦ ?_)
  simp only [exp_div_eq hφ hlaw, id]
  ring

/-- The mean of the exponential dispersion law is `b'(θ)`. -/
lemma integral_id_exponential_dispersion_law (hφ : 0 < φ)
    (hlaw : ∀ θ, IsProbabilityMeasure (exponentialDispersionLaw ν b φ θ)) (θ : ℝ) :
    ∫ y, y ∂(exponentialDispersionLaw ν b φ θ) = deriv b θ := by
  rw [integral_exponential_dispersion_law, deriv_eq_deriv_cgf hφ hlaw,
    deriv_cgf (mem_interior_integrable_exp_set hφ hlaw _), ← integral_div]
  refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
  simp only [exp_div_eq hφ hlaw, id]
  ring

/-- The variance of the exponential dispersion law is `φ b''(θ)`. -/
lemma integral_sq_sub_exponential_dispersion_law (hφ : 0 < φ)
    (hlaw : ∀ θ, IsProbabilityMeasure (exponentialDispersionLaw ν b φ θ)) (θ : ℝ) :
    ∫ y, (y - deriv b θ) ^ 2 ∂(exponentialDispersionLaw ν b φ θ) =
      φ * iteratedDeriv 2 b θ := by
  rw [integral_exponential_dispersion_law, iterated_deriv_two_eq hφ hlaw,
    iteratedDeriv_two_cgf_eq_integral (mem_interior_integrable_exp_set hφ hlaw _),
    deriv_eq_deriv_cgf hφ hlaw, mul_inv_cancel_left₀ hφ.ne', ← integral_div]
  refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
  simp only [exp_div_eq hφ hlaw, id]
  ring

/-- The cumulant function is convex: `b'' ≥ 0`. -/
lemma iterated_deriv_two_nonneg (hφ : 0 < φ)
    (hlaw : ∀ θ, IsProbabilityMeasure (exponentialDispersionLaw ν b φ θ)) (θ : ℝ) :
    0 ≤ iteratedDeriv 2 b θ := by
  have h := integral_sq_sub_exponential_dispersion_law hφ hlaw θ
  have h0 : 0 ≤ ∫ y, (y - deriv b θ) ^ 2 ∂(exponentialDispersionLaw ν b φ θ) :=
    integral_nonneg fun _ ↦ sq_nonneg _
  rw [h] at h0
  exact nonneg_of_mul_nonneg_right (by linarith) hφ

end ExponentialDispersion

section RandomDesign

/-- Second-order Taylor bound for a `C³` function on a bounded set:
`|b(θ + t) - b θ - b'(θ) t - b''(θ) t² / 2| ≤ M |t|³` for `|θ| ≤ K`, `|t| ≤ 1`. -/
lemma exists_abs_taylor_two_le {b : ℝ → ℝ} (hb : ContDiff ℝ 3 b) (K : ℝ) :
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
lemma exists_abs_sum_taylor_le {b : ℝ → ℝ} (hb : ContDiff ℝ 3 b) {R : ℝ}
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
lemma integrable_of_continuous (hR : ∀ᵐ x ∂Px, ‖x‖ ≤ R) {E : Type*}
    [NormedAddCommGroup E] {f : EuclideanSpace ℝ (Fin p) → E} (hf : Continuous f) :
    Integrable f Px := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin p)) R)
    |>.exists_bound_of_continuousOn hf.continuousOn
  exact Integrable.of_bound hf.aestronglyMeasurable C
    (hR.mono fun x hx ↦ hC x (mem_closedBall_zero_iff.2 hx))

variable {κ : Kernel (EuclideanSpace ℝ (Fin p)) ℝ} [IsMarkovKernel κ]

/-- The covariate marginal of `Px ⊗ κ` is `Px`. -/
lemma map_fst_comp_prod : (Px ⊗ₘ κ).map Prod.fst = Px := Measure.fst_compProd Px κ

/-- Integrals of functions of the covariate alone against `Px ⊗ κ`. -/
lemma integral_comp_fst_comp_prod {g : EuclideanSpace ℝ (Fin p) → ℝ} (hg : Continuous g) :
    ∫ z, g z.1 ∂(Px ⊗ₘ κ) = ∫ x, g x ∂Px := by
  conv_rhs => rw [← map_fst_comp_prod (Px := Px) (κ := κ)]
  exact (integral_map measurable_fst.aemeasurable hg.aestronglyMeasurable).symm

open Matrix in
/-- `∫ b''(⟪x, β⟫) ⟪x, h⟫² dPx = hᵀ J h`. -/
lemma integral_iterated_deriv_mul_inner_sq (hR : ∀ᵐ x ∂Px, ‖x‖ ≤ R) {b : ℝ → ℝ}
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
lemma mem_lp_score_and_integral {ν : Measure ℝ} {b : ℝ → ℝ} (hb : ContDiff ℝ 3 b)
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
    have h2 := integrable_pow_exponential_dispersion_law hφ hlaw (inner ℝ x β) 2
    have h1 := integrable_pow_exponential_dispersion_law hφ hlaw (inner ℝ x β) 1
    exact (((h2.sub (h1.const_mul (2 * c))).add (integrable_const (c ^ 2))).mul_const a).congr
      (ae_of_all _ fun y ↦ by simp only [Pi.add_apply, Pi.sub_apply]; ring)
  have hsq : ∀ x, ∫ y, g (x, y) ^ 2 ∂(κ x) =
      φ * (iteratedDeriv 2 b (inner ℝ x β) * inner ℝ x v ^ 2) := fun x ↦ by
    simp only [hg_def, mul_pow]
    rw [hκ, integral_mul_const, integral_sq_sub_exponential_dispersion_law hφ hlaw]
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
      have h1 := integrable_pow_exponential_dispersion_law hφ hlaw (inner ℝ x β) 1
      simp only [pow_one] at h1
      rw [integral_mul_const, hκ, integral_sub h1 (integrable_const _),
        integral_id_exponential_dispersion_law hφ hlaw, integral_const, probReal_univ, one_smul,
        sub_self, zero_mul]
    simp only [this, integral_zero]
  · rw [Measure.integral_compProd hint2]
    simp only [hsq]
    rw [integral_const_mul, integral_iterated_deriv_mul_inner_sq hR hb2]

/-- Slutsky's lemma for scalar factors: if `cₙ → 0` in probability and `Vₙ` converges in
distribution, then `cₙ Vₙ → 0` in probability. -/
lemma tendsto_in_measure_smul_zero {Ω Ω' E : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [OpensMeasurableSpace E] (μ : Measure Ω) [IsProbabilityMeasure μ] {μ' : Measure Ω'}
    [IsProbabilityMeasure μ'] (c : ℕ → Ω → ℝ) (V : ℕ → Ω → E) {W : Ω' → E}
    (hc : TendstoInMeasure μ c atTop (fun _ ↦ 0))
    (hV : TendstoInDistribution V atTop W (fun _ ↦ μ) μ') :
    TendstoInMeasure μ (fun (n : ℕ) ω ↦ c n ω • V n ω) atTop (fun _ ↦ 0) := by
  have hb := is_bounded_in_probability_of_tendsto_in_distribution μ (fun n ω ↦ ‖V n ω‖)
    (hV.continuous_comp continuous_norm)
  have h := tendsto_in_measure_mul_zero_of_is_bounded_in_probability μ _ c hb hc
  intro ε hε
  refine (h ε hε).congr fun n ↦ ?_
  congr 1
  ext ω
  simp [enorm_smul, mul_comm]

/-- Pointwise convergence in probability of the centred GLM log-likelihood process:
`Zₙ(h) + ⟪Uₙ, h⟫ → ⟪h, J h⟫ / 2`, where `Zₙ(h) = ∑ [b(⟪xᵢ, β + h/√n⟫) - b(⟪xᵢ, β⟫) - Yᵢ ⟪xᵢ, h/√n⟫]`
and `Uₙ = n^{-1/2} ∑ (Yᵢ - b'(⟪xᵢ, β⟫)) xᵢ`. The proof combines the law of large numbers for
`b''(⟪xᵢ, β⟫) ⟪xᵢ, h⟫²` with a third-order Taylor bound. -/
lemma tendsto_in_measure_glm_process {Ω : Type*} [MeasurableSpace Ω]
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
    have := integral_comp_fst_comp_prod (Px := Px) (κ := κ) hgc
    rw [hsfun, this, integral_iterated_deriv_mul_inner_sq hR hb2, hq_def, hA_def,
      Matrix.inner_toEuclideanCLM]
  have hsint : Integrable sfun (Px ⊗ₘ κ) := by
    have : Integrable (fun x : EuclideanSpace ℝ (Fin p) ↦
        iteratedDeriv 2 b (inner ℝ x β) * inner ℝ x h ^ 2) ((Px ⊗ₘ κ).map Prod.fst) := by
      rw [map_fst_comp_prod]
      exact integrable_of_continuous hR hgc
    exact this.comp_measurable measurable_fst
  have hwlln := tendsto_in_measure_sample_mean_of_iid P (Px ⊗ₘ κ) _ hiid' sfun
    (by fun_prop) hsint
  rw [hq] at hwlln
  set Qn : ℕ → Ω → ℝ := fun n ω ↦ (1 / 2 : ℝ) *
    ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, sfun (X i ω, Y i ω) - q) with hQn
  have h1 : TendstoInMeasure P Qn atTop (fun _ ↦ 0) := by
    refine tendsto_in_measure_const_mul_zero P _ (1 / 2) fun ε hε ↦ ?_
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
    refine tendsto_in_measure_zero_of_abs_le P (fun n _ ↦ u n) _ (fun _ _ ↦ 0) one_pos ?_
      (tendsto_in_measure_const_of_tendsto P u hu)
      (tendsto_in_measure_const_of_tendsto P _ tendsto_const_nhds)
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
  refine (tendsto_in_measure_add_zero P Qn _ h1 hrem).congr
    (fun n ↦ ae_of_all _ fun ω ↦ ?_) EventuallyEq.rfl
  simp only
  ring

end RandomDesign
end CKSD
