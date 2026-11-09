module

public import CKSD.Inference.NeymanPearson
public import CKSD.Inference.IntervalTestConstruction
public import CKSD.Inference.Model
public import CKSD.Inference.ExponentialFamily
public import CKSD.Inference.Sufficiency
public import TauCeti.Probability.Distributions.Gaussian.Projection
public import TauCeti.Probability.Distributions.StudentT.ChiSquared

/-!
# Uniformly most powerful tests

One-sided and two-sided optimal tests of Section 101: the Karlin–Rubin theorem for families with
monotone likelihood ratio, the essential completeness of one-sided tests, interval tests in
exponential families, least favorable mixtures, and the Gaussian sample laws behind Student's
`t`-test.

## Main definitions

* `CKSD.intervalTest`: the randomized two-sided interval test in a real statistic.

## Main results

* `CKSD.isUniformlyMostPowerfulTest_of_monotone_likelihood_ratio`: Karlin–Rubin (GAPS 101.15).
* `CKSD.gaussian_sample_mean_residual_laws`: for a Gaussian sample, the residual sum of squares
  is `σ² χ²_{n-1}`, independent of the sample mean, and the `t` statistic has Student's law with
  `n - 1` degrees of freedom (GAPS 101.17).
* `CKSD.exists_ump_interval_test`: UMP interval tests in a scalar exponential family (GAPS 101.50).
* `CKSD.exists_one_sided_test_risk_le`: one-sided tests are essentially complete (GAPS 101.53).
* `CKSD.most_powerful_of_mixture_null`: most powerful tests against a least favorable mixture
  (GAPS 101.54).

## References

* E. L. Lehmann and J. P. Romano, *Testing Statistical Hypotheses*, Chapter 3 and Section 5.2.
* The Gaussian sample laws use TauCeti's `HasLaw.iIndepFun_orthogonalProjectionOnto_stdGaussian`,
  `HasLaw.norm_sq_orthogonalProjectionOnto_stdGaussian`, and
  `TauCeti.Probability.hasLaw_studentT_of_gaussian_chiSquared`.
* The interval tests of GAPS 101.50 follow Lehmann–Romano, Theorem 3.7.1: the sizes at `η₁` and
  `η₂` come from a window of quantile levels (`CKSD.Inference.IntervalTestConstruction`, built on
  TauCeti's inverse transform sampling `MeasureTheory.Measure.measurePreserving_quantile`), and
  optimality and the level from the generalized Neyman–Pearson lemma
  `CKSD.integral_le_of_generalized_neyman_pearson` with exponential-sum thresholds.
-/
@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

attribute [local instance] Classical.propDecidable

variable {Θ X S V : Type*} [MeasurableSpace X] [MeasurableSpace S]
  [MeasurableSpace V]

/-- GAPS 101.15: the Karlin–Rubin theorem. In a family with everywhere positive densities whose
likelihood ratios `f b / f a` (`a < b`) are nondecreasing functions of `T`, the threshold test
`thresholdTest T c γ` of size `α` at `θ₀` is uniformly most powerful of level `α` for
`θ ≤ θ₀` against `θ > θ₀`. Positivity of the densities avoids the convention for ratios with zero
denominator. The monotonicity of the power function is not included. -/
theorem isUniformlyMostPowerfulTest_of_monotone_likelihood_ratio (P : ℝ → Measure X)
    (μ : Measure X) [∀ θ, IsProbabilityMeasure (P θ)] (f : ℝ → X → ℝ)
    (hf : ∀ θ, HasDensity (P θ) μ (f θ)) (hpos : ∀ θ x, 0 < f θ x)
    (T : X → ℝ) (hT : Measurable T)
    (hmlr : ∀ a b, a < b → ∃ r : ℝ → ℝ, Monotone r ∧ ∀ x, f b x / f a x = r (T x))
    (θ₀ c γ α : ℝ) (hγ : γ ∈ Icc 0 1) (hsize : (∫ x, thresholdTest T c γ x ∂P θ₀) = α) :
    IsUniformlyMostPowerfulTest P (Iic θ₀) (Ioi θ₀) α (thresholdTest T c γ) := by
  have hφ : IsStatisticalTest (thresholdTest T c γ) := isStatisticalTest_thresholdTest hT c hγ
  have step (a b : ℝ) (hab : a < b) (ψ : X → ℝ) (hψ : IsStatisticalTest ψ)
      (hle : (∫ x, ψ x ∂P a) ≤ ∫ x, thresholdTest T c γ x ∂P a) :
      (∫ x, ψ x ∂P b) ≤ ∫ x, thresholdTest T c γ x ∂P b := by
    obtain ⟨r, hr, hratio⟩ := hmlr a b hab
    exact integral_le_integral_thresholdTest_of_monotone_likelihood_ratio μ (P a) (P b) (f a)
      (f b) (hf a) (hf b) (hpos a) (hpos b) T r hr hratio c γ hφ ψ hψ hle
  refine ⟨hφ, fun θ hθ ↦ ?_, fun ψ hψ hlevel θ hθ ↦ ?_⟩
  · rcases (mem_Iic.1 hθ).lt_or_eq with hlt | rfl
    · set β := ∫ x, thresholdTest T c γ x ∂P θ
      have h := step θ θ₀ hlt (fun _ ↦ β) (IsStatisticalTest.const (hφ.integral_mem_Icc _))
        (by simp [β])
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h
      rw [← hsize]
      exact h
    · exact hsize.le
  · exact step θ₀ θ hθ ψ hψ ((hlevel θ₀ (mem_Iic.2 le_rfl)).trans hsize.symm.le)

/-- Standardization of a Gaussian sample: the coordinates `(xᵢ - m) / √v` of an i.i.d.
`N(m, v)` sample form a standard Gaussian vector in Euclidean space. -/
theorem hasLaw_standardize_pi_gaussianReal (n : ℕ) (m : ℝ) (v : ℝ≥0) (hv : 0 < v) :
    HasLaw (fun x : Fin n → ℝ ↦ WithLp.toLp 2 (fun i ↦ (x i - m) / Real.sqrt v))
      (stdGaussian (EuclideanSpace ℝ (Fin n))) (Measure.pi fun _ : Fin n ↦ gaussianReal m v) := by
  have h1 : (gaussianReal m v).map (fun t ↦ (t - m) / Real.sqrt v) = gaussianReal 0 1 := by
    have : (fun t : ℝ ↦ (t - m) / Real.sqrt v) = (· / Real.sqrt v) ∘ (· - m) := rfl
    rw [this, ← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_sub_const,
      gaussianReal_map_div_const]
    congr 1
    · simp
    · ext
      simp [Real.sq_sqrt (NNReal.coe_nonneg v), (NNReal.coe_pos.2 hv).ne']
  have hm : Measurable (fun x : Fin n → ℝ ↦ fun i ↦ (x i - m) / Real.sqrt v) := by fun_prop
  refine ⟨((WithLp.measurable_toLp 2 _).comp hm).aemeasurable, ?_⟩
  have : (fun x : Fin n → ℝ ↦ WithLp.toLp 2 (fun i ↦ (x i - m) / Real.sqrt v)) =
      (WithLp.toLp 2) ∘ (fun x : Fin n → ℝ ↦ fun i ↦ (x i - m) / Real.sqrt v) := rfl
  rw [this, ← Measure.map_map (WithLp.measurable_toLp 2 _) hm,
    Measure.pi_map_pi (f := fun _ t ↦ (t - m) / Real.sqrt v) (fun _ ↦ by fun_prop)]
  simp_rw [h1]
  exact map_pi_eq_stdGaussian


/-- A unit linear functional of a standard Gaussian vector is standard Gaussian, from Mathlib's
`variance_dual_stdGaussian` and `integral_strongDual_stdGaussian`. -/
theorem stdGaussian_map_inner_of_norm_eq_one {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (w : E) (hw : ‖w‖ = 1) :
    (stdGaussian E).map (fun y ↦ inner ℝ w y) = gaussianReal 0 1 := by
  have hL : (fun y ↦ inner ℝ w y) = ⇑(innerSL ℝ w) := rfl
  rw [hL, (inferInstance : IsGaussian ((stdGaussian E).map (innerSL ℝ w))).eq_gaussianReal,
    integral_map (by fun_prop) (by fun_prop), variance_map (by fun_prop) (by fun_prop)]
  simp only [id_eq, Function.id_comp]
  rw [show (∫ x, innerSL ℝ w x ∂stdGaussian E) = 0 from integral_strongDual_stdGaussian _,
    variance_dual_stdGaussian, innerSL_apply_norm, hw]
  simp

/-- GAPS 101.17: chi-squared residual law and independence from the sample mean.
The proof projects the standardized sample onto the constants and their orthogonal complement,
using TauCeti's `HasLaw.iIndepFun_orthogonalProjectionOnto_stdGaussian`,
`HasLaw.norm_sq_orthogonalProjectionOnto_stdGaussian`, and
`TauCeti.Probability.hasLaw_studentT_of_gaussian_chiSquared`. -/
theorem gaussian_sample_mean_residual_laws (n : ℕ) (hn : 2 ≤ n) (m : ℝ) (v : ℝ≥0) (hv : 0 < v) :
    let P := Measure.pi (fun _ : Fin n ↦ gaussianReal m v);
    let mean := fun x : Fin n → ℝ ↦ (∑ i, x i) / n;
    let ss := fun x : Fin n → ℝ ↦ ∑ i, (x i - mean x) ^ 2;
    P.map (fun x ↦ ss x / v) = TauCeti.Probability.chiSquaredMeasure (n - 1 : ℕ) ∧
      IndepFun mean ss P ∧
      P.map (fun x ↦ Real.sqrt n * (mean x - m) /
        Real.sqrt (ss x / (n - 1 : ℕ))) = TauCeti.Probability.studentTMeasure (n - 1 : ℕ) := by
  intro P mean ss
  let one : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun _ ↦ 1)
  let K : Submodule ℝ (EuclideanSpace ℝ (Fin n)) := ℝ ∙ one
  let Y : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n) := fun x ↦ WithLp.toLp 2 (fun i ↦ (x i - m) / Real.sqrt v)
  have hY : HasLaw Y (stdGaussian (EuclideanSpace ℝ (Fin n))) P := hasLaw_standardize_pi_gaussianReal n m v hv
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hsv : Real.sqrt v ≠ 0 := (Real.sqrt_pos.2 (NNReal.coe_pos.2 hv)).ne'
  have hinner : ∀ y : EuclideanSpace ℝ (Fin n), inner ℝ one y = ∑ i, y i := by
    intro y; rw [EuclideanSpace.inner_eq_star_dotProduct]; simp [one, dotProduct]
  have hone : ‖one‖ ^ 2 = n := by
    rw [EuclideanSpace.real_norm_sq_eq]; simp [one]
  have hprojK : ∀ y : EuclideanSpace ℝ (Fin n), (K.starProjection y) = (inner ℝ one y / n) • one := by
    intro y; rw [Submodule.starProjection_singleton, hone]; simp
  -- the residual sum of squares is `v` times the squared length of the residual projection
  have hss : ∀ x, ss x = v * ‖Kᗮ.orthogonalProjectionOnto (Y x)‖ ^ 2 := by
    intro x
    rw [← Submodule.norm_coe, Submodule.coe_orthogonalProjectionOnto_apply,
      Submodule.starProjection_orthogonal_val, hprojK, hinner, EuclideanSpace.real_norm_sq_eq,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [Y, one, mean, WithLp.ofLp_sub, WithLp.ofLp_smul, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul, mul_one]
    rw [← Finset.sum_div, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hv2 : Real.sqrt v ^ 2 = v := Real.sq_sqrt (NNReal.coe_nonneg v)
    field_simp
    rw [hv2]
    ring
  -- the sample mean is a function of the projection onto the constants
  have hmean : ∀ x, mean x = m + Real.sqrt v * (inner ℝ one (K.orthogonalProjectionOnto (Y x) : EuclideanSpace ℝ (Fin n)) / n) := by
    intro x
    rw [Submodule.coe_orthogonalProjectionOnto_apply,
      ← Submodule.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.2 (Submodule.mem_span_singleton_self one), hinner]
    simp only [Y, mean, ← Finset.sum_div, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring
  have hinnerK : ∀ y, inner ℝ one (K.orthogonalProjectionOnto y : EuclideanSpace ℝ (Fin n)) =
      inner ℝ one y := by
    intro y
    rw [Submodule.coe_orthogonalProjectionOnto_apply,
      ← Submodule.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.2 (Submodule.mem_span_singleton_self one)]
  -- independence of the two projections
  have hK : Pairwise fun i j : Bool ↦ (bif i then K else Kᗮ) ⟂ (bif j then K else Kᗮ) := by
    intro i j hij
    cases i <;> cases j
    · exact absurd rfl hij
    · exact K.isOrtho_orthogonal_right.symm
    · exact K.isOrtho_orthogonal_right
    · exact absurd rfl hij
  have hTF : IndepFun (fun x ↦ K.orthogonalProjectionOnto (Y x))
      (fun x ↦ Kᗮ.orthogonalProjectionOnto (Y x)) P :=
    (hY.iIndepFun_orthogonalProjectionOnto_stdGaussian (fun b ↦ bif b then K else Kᗮ) hK).indepFun
      (i := true) (j := false) (by decide)
  -- the residual squared length is chi-squared with `n - 1` degrees of freedom
  have hone0 : one ≠ 0 := by
    intro h
    rw [h, norm_zero] at hone
    exact hn0 (by rw [← hone]; ring)
  have hfin : Module.finrank ℝ Kᗮ = n - 1 := by
    have : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = (n - 1) + 1) :=
      ⟨by rw [finrank_euclideanSpace_fin]; omega⟩
    exact Submodule.finrank_orthogonal_span_singleton hone0
  have hV : HasLaw (fun x ↦ ‖Kᗮ.orthogonalProjectionOnto (Y x)‖ ^ 2)
      (TauCeti.Probability.chiSquaredMeasure (n - 1 : ℕ)) P := by
    have := hY.norm_sq_orthogonalProjectionOnto_stdGaussian Kᗮ
    rwa [hfin] at this
  refine ⟨?_, ?_, ?_⟩
  · rw [← hV.map_eq]
    congr 1
    funext x
    rw [hss x]
    field_simp
  · have := hTF.comp (φ := fun z : K ↦ m + Real.sqrt v *
        (inner ℝ one (z : EuclideanSpace ℝ (Fin n)) / n))
      (ψ := fun z : Kᗮ ↦ (v : ℝ) * ‖z‖ ^ 2) (by fun_prop) (by fun_prop)
    convert this using 1
    · funext x; exact hmean x
    · funext x; exact hss x
  · let w : EuclideanSpace ℝ (Fin n) := (Real.sqrt n)⁻¹ • one
    have hsn : Real.sqrt n ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
    have hw : ‖w‖ = 1 := by
      have h1 : ‖one‖ = Real.sqrt n := by
        rw [← hone, Real.sqrt_sq (norm_nonneg _)]
      rw [norm_smul, h1, norm_inv, Real.norm_eq_abs, abs_of_pos (Real.sqrt_pos.2 (by positivity)),
        inv_mul_cancel₀ hsn]
    have hZ : HasLaw (fun x ↦ inner ℝ w (Y x)) (gaussianReal 0 1) P :=
      HasLaw.comp ⟨by fun_prop, stdGaussian_map_inner_of_norm_eq_one w hw⟩ hY
    have hZV : IndepFun (fun x ↦ inner ℝ w (Y x))
        (fun x ↦ ‖Kᗮ.orthogonalProjectionOnto (Y x)‖ ^ 2) P := by
      have := hTF.comp (φ := fun z : K ↦ (Real.sqrt n)⁻¹ *
          inner ℝ one (z : EuclideanSpace ℝ (Fin n)))
        (ψ := fun z : Kᗮ ↦ ‖z‖ ^ 2) (by fun_prop) (by fun_prop)
      convert this using 1
      · funext x
        simp only [Function.comp_apply, hinnerK, w, inner_smul_left]
        simp
      · rfl
    have hν : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by
      have : 1 ≤ n - 1 := by omega
      exact_mod_cast this
    rw [← (TauCeti.Probability.hasLaw_studentT_of_gaussian_chiSquared hν hZV hZ hV).map_eq]
    congr 1
    funext x
    rw [hmean x, hss x, mul_div_assoc (v : ℝ), Real.sqrt_mul (NNReal.coe_nonneg v)]
    simp only [w, inner_smul_left, hinnerK]
    have hn2 : Real.sqrt n ^ 2 = n := Real.sq_sqrt (by positivity)
    simp only [RCLike.conj_to_real, add_sub_cancel_left]
    field_simp
    rw [hn2, mul_comm]

/-- The two-sided interval test in a real statistic value `T`: reject when `c₁ < T < c₂`, reject
with probability `γ₁` at `T = c₁` and `γ₂` at `T = c₂`, and accept otherwise. -/
def intervalTest (T : ℝ) (c₁ c₂ γ₁ γ₂ : ℝ) : ℝ :=
  if c₁ < T ∧ T < c₂ then 1 else if T = c₁ then γ₁ else if T = c₂ then γ₂ else 0

/-- The interval test is measurable in the statistic value. -/
private theorem measurable_intervalTest (c₁ c₂ γ₁ γ₂ : ℝ) :
    Measurable fun t ↦ intervalTest t c₁ c₂ γ₁ γ₂ := by
  unfold intervalTest
  refine Measurable.ite ?_ measurable_const (Measurable.ite ?_ measurable_const
    (Measurable.ite ?_ measurable_const measurable_const))
  · exact measurableSet_Ioo
  · exact measurableSet_singleton _
  · exact measurableSet_singleton _

/-- With randomizations in `[0, 1]` the interval test takes values in `[0, 1]`. -/
private theorem intervalTest_mem_Icc {c₁ c₂ γ₁ γ₂ : ℝ} (hγ₁ : γ₁ ∈ Icc (0 : ℝ) 1)
    (hγ₂ : γ₂ ∈ Icc (0 : ℝ) 1) (t : ℝ) : intervalTest t c₁ c₂ γ₁ γ₂ ∈ Icc (0 : ℝ) 1 := by
  unfold intervalTest
  split_ifs
  · exact ⟨zero_le_one, le_rfl⟩
  · exact hγ₁
  · exact hγ₂
  · exact ⟨le_rfl, zero_le_one⟩

/-- The interval test rejects strictly inside the interval. -/
private theorem intervalTest_of_mem_Ioo {c₁ c₂ γ₁ γ₂ t : ℝ} (ht : t ∈ Ioo c₁ c₂) :
    intervalTest t c₁ c₂ γ₁ γ₂ = 1 := by
  simp [intervalTest, ht.1, ht.2]

/-- The interval test accepts outside the closed interval. -/
private theorem intervalTest_of_notMem_Icc {c₁ c₂ γ₁ γ₂ t : ℝ} (hc : c₁ ≤ c₂)
    (ht : t ∉ Icc c₁ c₂) : intervalTest t c₁ c₂ γ₁ γ₂ = 0 := by
  simp only [mem_Icc, not_and_or, not_le] at ht
  rcases ht with ht | ht
  · simp [intervalTest, ht.ne, (ht.trans_le hc).ne, not_lt.2 ht.le]
  · simp [intervalTest, ht.ne', (hc.trans_lt ht).ne', not_lt.2 ht.le]

namespace RealExponentialFamily

variable {X : Type*} [MeasurableSpace X] (F : RealExponentialFamily X)

/-- The partition function `∫ e^{θ T} d base` is positive on the parameter domain. -/
private theorem integral_exp_mul_pos {θ : ℝ} (hθ : θ ∈ F.domain) :
    0 < ∫ x, Real.exp (θ * F.statistic x) ∂F.base := by
  have : NeZero F.base := ⟨F.base_ne_zero⟩
  exact integral_exp_pos (F.integrable_exp θ hθ)

/-- The density `e^{θ T - A(θ)}` is the normalized exponential tilt. -/
private theorem exp_mul_sub_cumulant {θ : ℝ} (hθ : θ ∈ F.domain) (x : X) :
    Real.exp (θ * F.statistic x - F.cumulant θ) =
      (∫ x, Real.exp (θ * F.statistic x) ∂F.base)⁻¹ * Real.exp (θ * F.statistic x) := by
  rw [Real.exp_sub, cumulant, Real.exp_log (F.integral_exp_mul_pos hθ), div_eq_inv_mul]

/-- The density `e^{θ T - A(θ)}` is integrable. -/
private theorem integrable_density {θ : ℝ} (hθ : θ ∈ F.domain) :
    Integrable (fun x ↦ Real.exp (θ * F.statistic x - F.cumulant θ)) F.base := by
  simp_rw [F.exp_mul_sub_cumulant hθ]
  exact (F.integrable_exp θ hθ).const_mul _

/-- The density `e^{θ T - A(θ)}` integrates to one. -/
private theorem integral_density {θ : ℝ} (hθ : θ ∈ F.domain) :
    ∫ x, Real.exp (θ * F.statistic x - F.cumulant θ) ∂F.base = 1 := by
  simp_rw [F.exp_mul_sub_cumulant hθ]
  rw [integral_const_mul, inv_mul_cancel₀ (F.integral_exp_mul_pos hθ).ne']

/-- Measurability of the density `e^{θ T - A(θ)}`. -/
private theorem measurable_density (θ : ℝ) :
    Measurable fun x ↦ Real.exp (θ * F.statistic x - F.cumulant θ) := by
  have := F.measurable_statistic
  fun_prop

/-- Integrals against the law at `η` are integrals against the base measure with density. -/
private theorem integral_law (η : F.domain) (φ : X → ℝ) :
    ∫ x, φ x ∂F.law η = ∫ x, Real.exp (η.val * F.statistic x - F.cumulant η.val) * φ x ∂F.base :=
  integral_withDensity_ofReal F.base (F.measurable_density η.val) (fun _ ↦ (Real.exp_pos _).le) φ

/-- Integrability against the law at `η`. -/
private theorem integrable_law_iff (η : F.domain) (φ : X → ℝ) :
    Integrable φ (F.law η) ↔
      Integrable (fun x ↦ Real.exp (η.val * F.statistic x - F.cumulant η.val) * φ x) F.base :=
  integrable_withDensity_ofReal_iff F.base (F.measurable_density η.val)
    (fun _ ↦ (Real.exp_pos _).le) φ

/-- The laws of a regular scalar exponential family are probability measures. -/
private theorem isProbabilityMeasure_law (η : F.domain) : IsProbabilityMeasure (F.law η) := by
  constructor
  rw [law, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (F.integrable_density η.2)
      (ae_of_all _ fun _ ↦ (Real.exp_pos _).le), F.integral_density η.2, ENNReal.ofReal_one]

/-- Change of reference parameter for the densities. -/
private theorem mul_exp_mul_density (θ ζ K : ℝ) (x : X) :
    K * Real.exp (F.cumulant ζ - F.cumulant θ) * Real.exp (ζ * F.statistic x - F.cumulant ζ) =
      Real.exp (θ * F.statistic x - F.cumulant θ) *
        (K * Real.exp ((ζ - θ) * F.statistic x)) := by
  rw [mul_assoc, ← Real.exp_add, mul_left_comm, ← Real.exp_add]
  ring_nf

/-- **Generalized Neyman–Pearson comparison in a scalar exponential family.** If `φ` rejects
where `K₁ e^{(ζ₁ - θ) T} + K₂ e^{(ζ₂ - θ) T} < 1` and accepts where it exceeds `1`, and `ψ`
satisfies the side conditions `Kᵢ E_{ζᵢ} ψ ≤ Kᵢ E_{ζᵢ} φ`, then `E_θ ψ ≤ E_θ φ`. -/
private theorem integral_le_of_exp_threshold (θ ζ₁ ζ₂ : F.domain) (K₁ K₂ : ℝ) {φ ψ : X → ℝ}
    (hφ : IsStatisticalTest φ) (hψ : IsStatisticalTest ψ)
    (hthr : ∀ x, (K₁ * Real.exp ((ζ₁.val - θ.val) * F.statistic x) +
        K₂ * Real.exp ((ζ₂.val - θ.val) * F.statistic x) < 1 → φ x = 1) ∧
      (1 < K₁ * Real.exp ((ζ₁.val - θ.val) * F.statistic x) +
        K₂ * Real.exp ((ζ₂.val - θ.val) * F.statistic x) → φ x = 0))
    (h₁ : K₁ * ∫ x, ψ x ∂F.law ζ₁ ≤ K₁ * ∫ x, φ x ∂F.law ζ₁)
    (h₂ : K₂ * ∫ x, ψ x ∂F.law ζ₂ ≤ K₂ * ∫ x, φ x ∂F.law ζ₂) :
    ∫ x, ψ x ∂F.law θ ≤ ∫ x, φ x ∂F.law θ := by
  set p : ℝ → X → ℝ := fun s x ↦ Real.exp (s * F.statistic x - F.cumulant s) with hp
  have hcomm : ∀ (s : F.domain) (χ : X → ℝ), ∫ x, χ x ∂F.law s = ∫ x, χ x * p s.val x ∂F.base :=
    fun s χ ↦ by rw [F.integral_law]; simp_rw [mul_comm]; rfl
  have key := integral_le_of_generalized_neyman_pearson (m := 2) F.base (p θ.val)
    ![p ζ₁.val, p ζ₂.val]
    ![K₁ * Real.exp (F.cumulant ζ₁.val - F.cumulant θ.val),
      K₂ * Real.exp (F.cumulant ζ₂.val - F.cumulant θ.val)]
    (F.integrable_density θ.2) (fun i ↦ by
      fin_cases i
      · exact F.integrable_density ζ₁.2
      · exact F.integrable_density ζ₂.2) φ ψ hφ hψ (ae_of_all _ fun x ↦ ?_) (fun i ↦ ?_)
  · rw [hcomm, hcomm]; exact key
  · simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, p,
      F.mul_exp_mul_density θ.val, ← mul_add]
    have hpos := Real.exp_pos (θ.val * F.statistic x - F.cumulant θ.val)
    refine ⟨fun h ↦ (hthr x).1 ?_, fun h ↦ (hthr x).2 ?_⟩
    · simpa using (mul_lt_iff_lt_one_right hpos).1 h
    · simpa using (lt_mul_iff_one_lt_right hpos).1 h
  · fin_cases i
    · simp only [Fin.zero_eta, Matrix.cons_val_zero]
      rw [← hcomm, ← hcomm, mul_comm K₁, mul_assoc, mul_assoc]
      exact mul_le_mul_of_nonneg_left h₁ (Real.exp_pos _).le
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [← hcomm, ← hcomm, mul_comm K₂, mul_assoc, mul_assoc]
      exact mul_le_mul_of_nonneg_left h₂ (Real.exp_pos _).le


/-- The flipped comparison: if `φ` has size `α` at `ζ₁` and `ζ₂`, accepts where
`K₁ e^{(ζ₁ - θ) T} + K₂ e^{(ζ₂ - θ) T} < 1` and rejects where it exceeds `1`, then
`E_θ φ ≤ α`. This is `integral_le_of_exp_threshold` for `1 - φ` against the constant test
`1 - α`. -/
private theorem integral_le_of_exp_threshold_flip (θ ζ₁ ζ₂ : F.domain) (K₁ K₂ : ℝ) {α : ℝ}
    (hα : α ∈ Icc (0 : ℝ) 1) {φ : X → ℝ} (hφ : IsStatisticalTest φ)
    (h₁ : ∫ x, φ x ∂F.law ζ₁ = α) (h₂ : ∫ x, φ x ∂F.law ζ₂ = α)
    (hthr : ∀ x, (K₁ * Real.exp ((ζ₁.val - θ.val) * F.statistic x) +
        K₂ * Real.exp ((ζ₂.val - θ.val) * F.statistic x) < 1 → φ x = 0) ∧
      (1 < K₁ * Real.exp ((ζ₁.val - θ.val) * F.statistic x) +
        K₂ * Real.exp ((ζ₂.val - θ.val) * F.statistic x) → φ x = 1)) :
    ∫ x, φ x ∂F.law θ ≤ α := by
  have hconst : IsStatisticalTest (fun _ : X ↦ 1 - α) :=
    ⟨measurable_const, fun _ ↦ ⟨by linarith [hα.2], by linarith [hα.1]⟩⟩
  have hside : ∀ (ζ : F.domain), ∫ x, φ x ∂F.law ζ = α → ∀ K : ℝ,
      K * ∫ x, (1 - α) ∂F.law ζ ≤ K * ∫ x, (1 - φ x) ∂F.law ζ := fun ζ hζ K ↦ by
    have := F.isProbabilityMeasure_law ζ
    rw [hφ.integral_one_sub, hζ, integral_const, probReal_univ, one_smul]
  have key := F.integral_le_of_exp_threshold θ ζ₁ ζ₂ K₁ K₂ hφ.one_sub hconst
    (fun x ↦ ⟨fun h ↦ by rw [(hthr x).1 h, sub_zero], fun h ↦ by rw [(hthr x).2 h, sub_self]⟩)
    (hside ζ₁ h₁ _) (hside ζ₂ h₂ _)
  have := F.isProbabilityMeasure_law θ
  rw [hφ.integral_one_sub, integral_const, probReal_univ, one_smul] at key
  linarith

/-- **Two-point size construction.** In a regular scalar exponential family, for `η₁ < η₂` and
`α ∈ (0, 1)` some interval test in the natural statistic has size exactly `α` at `η₁` and at
`η₂`. Its window of quantile levels of the law of `T` under `η₁` is chosen by the intermediate
value theorem applied to the likelihood ratio `dP_{η₂} / dP_{η₁}`, a strictly increasing
function of `T`. -/
private theorem exists_intervalTest_integral_eq (η₁ η₂ : F.domain) (hη : η₁.val < η₂.val)
    {α : ℝ} (hα : α ∈ Ioo 0 1) :
    ∃ c₁ c₂ γ₁ γ₂ : ℝ, c₁ ≤ c₂ ∧ γ₁ ∈ Icc 0 1 ∧ γ₂ ∈ Icc 0 1 ∧
      ∫ x, intervalTest (F.statistic x) c₁ c₂ γ₁ γ₂ ∂F.law η₁ = α ∧
      ∫ x, intervalTest (F.statistic x) c₁ c₂ γ₁ γ₂ ∂F.law η₂ = α := by
  have hTm : Measurable F.statistic := F.measurable_statistic
  have := F.isProbabilityMeasure_law η₁
  set μ₁ := (F.law η₁).map F.statistic with hμ₁
  have : IsProbabilityMeasure μ₁ :=
    (Measure.isProbabilityMeasure_map_iff hTm.aemeasurable).2 inferInstance
  -- The likelihood ratio `dP_{η₂} / dP_{η₁}` as a function of the statistic.
  set L : ℝ → ℝ := fun t ↦
    Real.exp ((η₂.val - η₁.val) * t + (F.cumulant η₁.val - F.cumulant η₂.val)) with hL
  have hLmono : StrictMono L := fun s t hst ↦ Real.exp_lt_exp.2 (by nlinarith [sub_pos.2 hη])
  have hLm : Measurable L := hLmono.monotone.measurable
  have hp₂ : ∀ x, Real.exp (η₂.val * F.statistic x - F.cumulant η₂.val) =
      Real.exp (η₁.val * F.statistic x - F.cumulant η₁.val) * L (F.statistic x) := fun x ↦ by
    simp only [hL]; rw [← Real.exp_add]; ring_nf
  have hmapint : ∀ g : ℝ → ℝ, Measurable g →
      ∫ t, g t ∂μ₁ = ∫ x, g (F.statistic x) ∂F.law η₁ :=
    fun g hg ↦ integral_map hTm.aemeasurable hg.aestronglyMeasurable
  have hLi : Integrable L μ₁ := by
    rw [integrable_map_measure hLm.aestronglyMeasurable hTm.aemeasurable, F.integrable_law_iff]
    exact (F.integrable_density η₂.2).congr (ae_of_all _ fun x ↦ hp₂ x)
  have hL1 : ∫ t, L t ∂μ₁ = 1 := by
    rw [hmapint L hLm, F.integral_law]
    simp_rw [← hp₂]
    exact F.integral_density η₂.2
  have hnc : ¬ ∃ c, ∀ᵐ t ∂μ₁, L t = c := by
    rintro ⟨c, hc⟩
    rw [ae_map_iff hTm.aemeasurable (p := fun t ↦ L t = c) (hLm (measurableSet_singleton c))]
      at hc
    obtain ⟨x₀, hx₀⟩ := hc.exists
    have hT : ∀ᵐ x ∂F.law η₁, F.statistic x = F.statistic x₀ :=
      hc.mono fun x hx ↦ hLmono.injective (hx.trans hx₀.symm)
    have hac : F.base ≪ F.law η₁ := withDensity_absolutelyContinuous'
      (F.measurable_density η₁.val).ennreal_ofReal.aemeasurable
      (ae_of_all _ fun x ↦ by simp [Real.exp_pos])
    exact F.nonconstant (F.statistic x₀) (hac.ae_le hT)
  -- The two-point size construction.
  obtain ⟨a, ha0, ha1, ha⟩ := exists_setIntegral_comp_quantile_eq_mul μ₁ hLmono.monotone hLi
    hnc hα
  rw [hL1, mul_one] at ha
  obtain ⟨c₁, c₂, γ₁, γ₂, hc, hγ₁, hγ₂, hW⟩ :=
    exists_intervalWeight_integral_eq_setIntegral_quantile μ₁ ha0 (by linarith [hα.1]) ha1
  have hW' : ∀ ψ : ℝ → ℝ, Integrable ψ μ₁ →
      ∫ t, intervalTest t c₁ c₂ γ₁ γ₂ * ψ t ∂μ₁ = ∫ v in Ioo a (a + α), ψ (μ₁.quantile v) :=
    fun ψ hψ ↦ by
      rw [← hW ψ hψ]
      congr 1
  have hImeas := measurable_intervalTest c₁ c₂ γ₁ γ₂
  set φ : X → ℝ := fun x ↦ intervalTest (F.statistic x) c₁ c₂ γ₁ γ₂ with hφdef
  have hsize₁ : ∫ x, φ x ∂F.law η₁ = α := by
    have h := hW' (fun _ ↦ 1) (integrable_const _)
    simp only [mul_one, setIntegral_const, smul_eq_mul,
      Real.volume_real_Ioo_of_le (by linarith [hα.1] : a ≤ a + α), add_sub_cancel_left] at h
    rw [← h, hmapint _ hImeas]
  have hsize₂ : ∫ x, φ x ∂F.law η₂ = α := by
    rw [F.integral_law]
    simp_rw [hp₂, mul_assoc]
    rw [← F.integral_law η₁ (fun x ↦ L (F.statistic x) * φ x),
      ← hmapint (fun t ↦ L t * intervalTest t c₁ c₂ γ₁ γ₂) (hLm.mul hImeas), ← ha, ← hW' L hLi]
    simp_rw [mul_comm]
  exact ⟨c₁, c₂, γ₁, γ₂, hc, hγ₁, hγ₂, hsize₁, hsize₂⟩

end RealExponentialFamily

/-- GAPS 101.50: in a regular scalar natural exponential family, for `η₁ < η₂` and `α ∈ (0, 1)`
there is an interval test in the natural statistic with size exactly `α` at `η₁` and at `η₂`; it
is uniformly most powerful of level `α` for `η ≤ η₁ or η ≥ η₂` against `η₁ < η < η₂`. -/
theorem exists_ump_interval_test {X : Type*} [MeasurableSpace X]
    (F : RealExponentialFamily X) (η₁ η₂ : F.domain) (hη : η₁.val < η₂.val)
    (α : ℝ) (hα : α ∈ Ioo 0 1) :
    ∃ c₁ c₂ γ₁ γ₂ : ℝ, c₁ ≤ c₂ ∧ γ₁ ∈ Icc 0 1 ∧ γ₂ ∈ Icc 0 1 ∧
      testPower F.law (fun x ↦ intervalTest (F.statistic x) c₁ c₂ γ₁ γ₂) η₁ = α ∧
      testPower F.law (fun x ↦ intervalTest (F.statistic x) c₁ c₂ γ₁ γ₂) η₂ = α ∧
      IsUniformlyMostPowerfulTest F.law {η | η.val ≤ η₁.val ∨ η₂.val ≤ η.val}
        {η | η₁.val < η.val ∧ η.val < η₂.val} α
        (fun x ↦ intervalTest (F.statistic x) c₁ c₂ γ₁ γ₂) := by
  obtain ⟨c₁, c₂, γ₁, γ₂, hc, hγ₁, hγ₂, hsize₁, hsize₂⟩ :=
    F.exists_intervalTest_integral_eq η₁ η₂ hη hα
  have hIin : ∀ t ∈ Ioo c₁ c₂, intervalTest t c₁ c₂ γ₁ γ₂ = 1 := fun t ht ↦
    intervalTest_of_mem_Ioo ht
  have hIout : ∀ t ∉ Icc c₁ c₂, intervalTest t c₁ c₂ γ₁ γ₂ = 0 := fun t ht ↦
    intervalTest_of_notMem_Icc hc ht
  set φ : X → ℝ := fun x ↦ intervalTest (F.statistic x) c₁ c₂ γ₁ γ₂ with hφdef
  have hφ : IsStatisticalTest φ :=
    ⟨(measurable_intervalTest c₁ c₂ γ₁ γ₂).comp F.measurable_statistic,
      fun x ↦ intervalTest_mem_Icc hγ₁ hγ₂ _⟩
  refine ⟨c₁, c₂, γ₁, γ₂, hc, hγ₁, hγ₂, hsize₁, hsize₂, hφ, ?_, ?_⟩
  · -- Level `α` on the two-sided null hypothesis.
    have hα' : α ∈ Icc (0 : ℝ) 1 := ⟨hα.1.le, hα.2.le⟩
    intro θ hθ
    change ∫ x, φ x ∂F.law θ ≤ α
    rcases hθ with h | h
    · rcases h.lt_or_eq with h | h
      · -- `θ < η₁`: `e^{(η₁ - θ) t} (1 - h t) / A` with `h = A e^{(θ - η₁) t} + B e^{(η₂ - η₁) t}`.
        obtain ⟨A, B, hA, hB, hAB⟩ := exists_mul_exp_add_mul_exp_le_one_iff
          (sub_neg.2 h) (sub_pos.2 hη) hc
        refine F.integral_le_of_exp_threshold_flip θ η₁ η₂ A⁻¹ (-(B * A⁻¹)) hα' hφ hsize₁ hsize₂
          fun x ↦ ?_
        simp only [hφdef]
        generalize F.statistic x = t
        have e1 : Real.exp ((η₁.val - θ.val) * t) * Real.exp ((θ.val - η₁.val) * t) = 1 := by
          rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
        have e2 : Real.exp ((η₁.val - θ.val) * t) * Real.exp ((η₂.val - η₁.val) * t) =
            Real.exp ((η₂.val - θ.val) * t) := by rw [← Real.exp_add]; ring_nf
        have hAinv : A⁻¹ * A = 1 := inv_mul_cancel₀ hA.ne'
        have hG : A⁻¹ * Real.exp ((η₁.val - θ.val) * t) +
            -(B * A⁻¹) * Real.exp ((η₂.val - θ.val) * t) - 1 =
            Real.exp ((η₁.val - θ.val) * t) * A⁻¹ * (1 - (A * Real.exp ((θ.val - η₁.val) * t) +
              B * Real.exp ((η₂.val - η₁.val) * t))) := by
          linear_combination e1 + Real.exp ((η₁.val - θ.val) * t) *
            Real.exp ((θ.val - η₁.val) * t) * hAinv + B * A⁻¹ * e2
        have hw : 0 < Real.exp ((η₁.val - θ.val) * t) * A⁻¹ := by positivity
        refine ⟨fun hlt ↦ hIout t fun hm ↦ ?_, fun hgt ↦ hIin t ?_⟩
        · have := (hAB t).1 hm
          nlinarith [mul_nonneg hw.le (sub_nonneg.2 this)]
        · by_contra hn
          have := (hAB t).2 hn
          nlinarith [mul_nonneg hw.le (sub_nonneg.2 this)]
      · rw [Subtype.ext h]; exact hsize₁.le
    · rcases h.lt_or_eq with h | h
      · -- `η₂ < θ`: `e^{(η₂ - θ) t} (1 - h t) / B` with `h = A e^{(η₁ - η₂) t} + B e^{(θ - η₂) t}`.
        obtain ⟨A, B, hA, hB, hAB⟩ := exists_mul_exp_add_mul_exp_le_one_iff
          (sub_neg.2 hη) (sub_pos.2 h) hc
        refine F.integral_le_of_exp_threshold_flip θ η₁ η₂ (-(A * B⁻¹)) B⁻¹ hα' hφ hsize₁ hsize₂
          fun x ↦ ?_
        simp only [hφdef]
        generalize F.statistic x = t
        have e1 : Real.exp ((η₂.val - θ.val) * t) * Real.exp ((θ.val - η₂.val) * t) = 1 := by
          rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
        have e2 : Real.exp ((η₂.val - θ.val) * t) * Real.exp ((η₁.val - η₂.val) * t) =
            Real.exp ((η₁.val - θ.val) * t) := by rw [← Real.exp_add]; ring_nf
        have hBinv : B⁻¹ * B = 1 := inv_mul_cancel₀ hB.ne'
        have hG : -(A * B⁻¹) * Real.exp ((η₁.val - θ.val) * t) +
            B⁻¹ * Real.exp ((η₂.val - θ.val) * t) - 1 =
            Real.exp ((η₂.val - θ.val) * t) * B⁻¹ * (1 - (A * Real.exp ((η₁.val - η₂.val) * t) +
              B * Real.exp ((θ.val - η₂.val) * t))) := by
          linear_combination e1 + Real.exp ((η₂.val - θ.val) * t) *
            Real.exp ((θ.val - η₂.val) * t) * hBinv + A * B⁻¹ * e2
        have hw : 0 < Real.exp ((η₂.val - θ.val) * t) * B⁻¹ := by positivity
        refine ⟨fun hlt ↦ hIout t fun hm ↦ ?_, fun hgt ↦ hIin t ?_⟩
        · have := (hAB t).1 hm
          nlinarith [mul_nonneg hw.le (sub_nonneg.2 this)]
        · by_contra hn
          have := (hAB t).2 hn
          nlinarith [mul_nonneg hw.le (sub_nonneg.2 this)]
      · rw [← Subtype.ext h]; exact hsize₂.le
  · -- Most powerful against every alternative between `η₁` and `η₂`.
    intro ψ hψ hψlev θ hθ
    obtain ⟨A, B, hA, hB, hAB⟩ := exists_mul_exp_add_mul_exp_le_one_iff
      (sub_neg.2 hθ.1) (sub_pos.2 hθ.2) hc
    refine F.integral_le_of_exp_threshold θ η₁ η₂ A B hφ hψ (fun x ↦ ⟨fun hlt ↦ ?_, fun hgt ↦ ?_⟩)
      (mul_le_mul_of_nonneg_left (hsize₁ ▸ hψlev η₁ (Or.inl le_rfl)) hA.le)
      (mul_le_mul_of_nonneg_left (hsize₂ ▸ hψlev η₂ (Or.inr le_rfl)) hB.le)
    · refine hIin _ ?_
      by_contra hn
      exact absurd ((hAB (F.statistic x)).2 hn) (not_le.2 hlt)
    · exact hIout _ fun hm ↦ absurd ((hAB (F.statistic x)).1 hm) (not_le.2 hgt)

/-- GAPS 101.53: one-sided tests form an essentially complete class for two-decision problems in
a family with monotone likelihood ratio. The densities are everywhere positive (so the laws are
mutually absolutely continuous), the loss `L θ` of rejecting (`true`) minus accepting (`false`)
is positive below `θ₀` and negative above it, and the threshold may be infinite. For every test
`φ` there is a threshold test in `T` whose risk `L θ false + (L θ true - L θ false) · power` is at
most that of `φ` at every `θ`. The threshold test matches the size of `φ` at `θ₀`
(`exists_integral_thresholdTest_eq`); the two Neyman–Pearson steps of the Karlin–Rubin argument
then compare powers below and above `θ₀`. -/
theorem exists_one_sided_test_risk_le {X : Type*} [MeasurableSpace X]
    (P : ℝ → Measure X) (μ : Measure X) [∀ θ, IsProbabilityMeasure (P θ)]
    (f : ℝ → X → ℝ) (hf : ∀ θ, HasDensity (P θ) μ (f θ))
    (hpos : ∀ θ x, 0 < f θ x) (T : X → ℝ) (hT : Measurable T)
    (hmlr : ∀ a b, a < b → ∃ r : ℝ → ℝ, Monotone r ∧ ∀ x, f b x / f a x = r (T x))
    (L : ℝ → Bool → ℝ) (θ₀ : ℝ)
    (hlow : ∀ θ < θ₀, 0 < L θ true - L θ false)
    (hhigh : ∀ θ > θ₀, L θ true - L θ false < 0)
    (φ : X → ℝ) (hφ : IsStatisticalTest φ) :
    ∃ c : EReal, ∃ γ ∈ Icc (0 : ℝ) 1,
      IsStatisticalTest (thresholdTest (fun x ↦ (T x : EReal)) c γ) ∧ ∀ θ,
        L θ false + (L θ true - L θ false) *
            testPower P (thresholdTest (fun x ↦ (T x : EReal)) c γ) θ ≤
          L θ false + (L θ true - L θ false) * testPower P φ θ := by
  -- a test with the same size at `θ₀`, smaller power below `θ₀` and larger power above it has
  -- smaller risk everywhere
  have hfinal : ∀ ψ : X → ℝ, (∀ θ < θ₀, testPower P ψ θ ≤ testPower P φ θ) →
      (∀ θ > θ₀, testPower P φ θ ≤ testPower P ψ θ) → testPower P ψ θ₀ = testPower P φ θ₀ →
      ∀ θ, L θ false + (L θ true - L θ false) * testPower P ψ θ ≤
        L θ false + (L θ true - L θ false) * testPower P φ θ := by
    intro ψ hlo hhi heq θ
    rcases lt_trichotomy θ θ₀ with h | rfl | h
    · have := mul_le_mul_of_nonneg_left (hlo θ h) (hlow θ h).le
      linarith
    · rw [heq]
    · have := mul_le_mul_of_nonpos_left (hhi θ h) (hhigh θ h).le
      linarith
  have hTe : Measurable fun x ↦ (T x : EReal) := measurable_coe_real_ereal.comp hT
  have hψtest : ∀ (c : EReal) (γ : ℝ), γ ∈ Icc (0 : ℝ) 1 →
      IsStatisticalTest (thresholdTest (fun x ↦ (T x : EReal)) c γ) :=
    fun c γ hγ ↦ isStatisticalTest_thresholdTest hTe c hγ
  have hφb : ∀ θ, testPower P φ θ ∈ Icc (0 : ℝ) 1 := fun θ ↦ hφ.integral_mem_Icc (P θ)
  have h01 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  rcases (hφb θ₀).1.lt_or_eq with hβ0 | hβ0
  · rcases (hφb θ₀).2.lt_or_eq with hβ1 | hβ1
    · -- a genuine threshold
      obtain ⟨c, γ, hγ, hsize⟩ := exists_integral_thresholdTest_eq (P θ₀) hT ⟨hβ0, hβ1⟩
      have hreal : thresholdTest (fun x ↦ (T x : EReal)) (c : EReal) γ = thresholdTest T c γ := by
        funext x; simp only [thresholdTest, EReal.coe_lt_coe_iff, EReal.coe_eq_coe_iff]
      have hthr := isStatisticalTest_thresholdTest hT c hγ
      refine ⟨(c : EReal), γ, hγ, hψtest c γ hγ, hfinal _ ?_ ?_ ?_⟩ <;> rw [hreal]
      · intro θ hθ
        obtain ⟨r, hr, hratio⟩ := hmlr θ θ₀ hθ
        exact integral_thresholdTest_le_of_monotone_likelihood_ratio μ (P θ) (P θ₀) (f θ)
          (f θ₀) (hf θ) (hf θ₀) (hpos θ) (hpos θ₀) T r hr hratio c γ hthr φ hφ
          (by rw [hsize]; exact le_rfl)
      · intro θ hθ
        obtain ⟨r, hr, hratio⟩ := hmlr θ₀ θ hθ
        exact integral_le_integral_thresholdTest_of_monotone_likelihood_ratio μ (P θ₀) (P θ)
          (f θ₀) (f θ) (hf θ₀) (hf θ) (hpos θ₀) (hpos θ) T r hr hratio c γ hthr φ hφ
          (by rw [hsize]; exact le_rfl)
      · exact hsize
    · -- size one: reject always
      have h1 : ∀ θ, testPower P (thresholdTest (fun x ↦ (T x : EReal)) ⊥ 0) θ = 1 := by
        intro θ
        simp [testPower, thresholdTest, EReal.bot_lt_coe]
      refine ⟨⊥, 0, h01, hψtest ⊥ 0 h01, hfinal _ ?_ ?_ ?_⟩
      · intro θ _
        rw [h1]
        have h0 : (∫ x, (1 - φ x) ∂P θ₀) = 0 := by
          rw [hφ.integral_one_sub]
          change 1 - testPower P φ θ₀ = 0
          linarith
        have h2 := integral_eq_zero_of_integral_eq_zero_of_pos_density (hf θ₀) (hf θ) (hpos θ₀)
          hφ.one_sub.1 hφ.one_sub.nonneg hφ.one_sub.le_one h0
        rw [hφ.integral_one_sub] at h2
        unfold testPower
        linarith
      · intro θ _
        rw [h1]; exact (hφb θ).2
      · rw [h1]; exact hβ1.symm
  · -- size zero: never reject
    have h1 : ∀ θ, testPower P (thresholdTest (fun x ↦ (T x : EReal)) ⊤ 0) θ = 0 := by
      intro θ
      simp [testPower, thresholdTest]
    refine ⟨⊤, 0, h01, hψtest ⊤ 0 h01, hfinal _ ?_ ?_ ?_⟩
    · intro θ _
      rw [h1]; exact (hφb θ).1
    · intro θ _
      rw [h1]
      have h2 := integral_eq_zero_of_integral_eq_zero_of_pos_density (hf θ₀) (hf θ) (hpos θ₀)
        hφ.1 hφ.nonneg hφ.le_one hβ0.symm
      unfold testPower
      rw [h2]
    · rw [h1]; exact hβ0

/-- GAPS 101.54: least favorable distributions, sufficiency part. Let `Λ` be a prior on the
parameter space of a composite null hypothesis `P`. If `φ` has level `α` at every null parameter
and is most powerful at level `α` for the simple null `P ∘ₘ Λ` against the alternative `Q`, then
`φ` is most powerful at level `α` for the composite null against `Q`. The least-favorability of
`Λ` and the concentration of `Λ` on the set where the power equals `α` are not included. -/
theorem most_powerful_of_mixture_null {Θ X : Type*} [MeasurableSpace Θ] [MeasurableSpace X]
    (P : Kernel Θ X) [IsMarkovKernel P] (Λ : Measure Θ) [IsProbabilityMeasure Λ]
    (Q : Measure X) (α : ℝ) (φ : X → ℝ)
    (hφ : IsStatisticalTest φ) (hlevel : ∀ θ, (∫ x, φ x ∂P θ) ≤ α)
    (hopt : ∀ ψ, IsStatisticalTest ψ → (∫ x, ψ x ∂P ∘ₘ Λ) ≤ α →
      (∫ x, ψ x ∂Q) ≤ ∫ x, φ x ∂Q) :
    HasTestLevel P univ α φ ∧ ∀ ψ, IsStatisticalTest ψ → (∀ θ, (∫ x, ψ x ∂P θ) ≤ α) →
      (∫ x, ψ x ∂Q) ≤ ∫ x, φ x ∂Q := by
  refine ⟨⟨hφ, fun θ _ ↦ hlevel θ⟩, ?_⟩
  intro ψ hψ hψlevel
  apply hopt ψ hψ
  rw [integral_comp_eq_integral_integral P Λ ψ (hψ.integrable _)]
  calc (∫ θ, ∫ x, ψ x ∂P θ ∂Λ) ≤ ∫ _θ, α ∂Λ := by
        apply integral_mono_of_nonneg
        · exact ae_of_all _ fun θ ↦ hψ.integral_nonneg _
        · exact integrable_const α
        · exact ae_of_all _ hψlevel
    _ = α := by simp

end CKSD
