module

public import CKSD.Inference.NeymanPearson
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
  sorry

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
