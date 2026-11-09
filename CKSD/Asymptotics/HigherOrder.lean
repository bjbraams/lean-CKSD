module

public import CKSD.Asymptotics.Basic
public import TauCeti.Probability.Distributions.ChiSquared.Basic
public import TauCeti.Probability.Distributions.StudentT.Basic
public import TauCeti.Probability.Distributions.FisherSnedecor.Basic
public import Mathlib.MeasureTheory.Measure.LevyConvergence
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.Probability.StrongLaw
public import TauCeti.Probability.Cdf
public import TauCeti.MeasureTheory.Measure.ProductKernel
import TauCeti.Probability.Distributions.Gaussian.Basic
import TauCeti.Probability.Distributions.Gaussian.Moments

/-!
# Robustness, Edgeworth expansion, and bootstrap of the mean

Higher-order and robustness results of Section 102.

## Main results

* `CKSD.integral_huberScore_sq_le`: Hampel's optimality of the Huber score at the Gaussian model
  (GAPS 102.44), from `CKSD.integral_mul_huberScore_gaussianReal`.
* `CKSD.exists_uniform_edgeworth_expansion`: the one-term Edgeworth expansion of the
  standardized mean (GAPS 102.49).
* `CKSD.tendstoInMeasure_bootstrap_mean_kolmogorovDistance`: consistency of the
  nonparametric bootstrap of the mean (GAPS 102.51).

## Implementation notes

The Huber computation uses TauCeti's `hasDerivAt_gaussianPDFReal`,
`integrable_gaussianReal_iff_integrable_gaussianPDFReal_smul`, and `integral_sq_gaussianReal`.

The bootstrap of the mean follows the classical argument of Bickel and Freedman (1981) and
Singh (1981): along a sample path where the strong law holds for `X` and `X²`, the bootstrap
characteristic functions converge (Mathlib's `Complex.tendsto_pow_exp_of_isLittleO_sub_add_div`
and the Taylor bound `Complex.exp_bound`), Lévy's continuity theorem
(`ProbabilityMeasure.tendsto_iff_tendsto_charFun`) and the portmanteau theorem give pointwise
convergence of distribution functions, and Pólya's theorem upgrades this to the Kolmogorov
distance using TauCeti's `Measure.continuous_cdf_of_noAtoms`. Measurability of the random
Kolmogorov distance uses TauCeti's `measurable_probabilityMeasure_pi_const_toMeasure`, and the
strong law is Mathlib's `strong_law_ae`.
-/
@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- The standard Gaussian density times `x ^ n` is Lebesgue integrable. -/
theorem integrable_gaussianPDFReal_mul_pow (n : ℕ) :
    Integrable (fun x : ℝ ↦ gaussianPDFReal 0 1 x * x ^ n) := by
  have h : Integrable (fun x : ℝ ↦ x ^ n) (gaussianReal 0 1) := by
    have hm : MemLp id (n : ℝ≥0∞) (gaussianReal 0 1) := by
      simpa using memLp_id_gaussianReal (μ := 0) (v := 1) (n : ℝ≥0)
    exact hm.integrable_norm_pow'.mono' (by fun_prop)
      (ae_of_all _ fun x ↦ by simp)
  simpa [smul_eq_mul] using
    (TauCeti.Probability.integrable_gaussianReal_iff_integrable_gaussianPDFReal_smul
      (μ := 0) (v := 1) one_ne_zero).1 h

/-- For a standard Gaussian, `∫ x (x - k)⁺ dΦ = P(X > k)`; proved by integrating
`x (x - k) φ(x) = (-(x - k) φ(x))' + φ(x)` over `(k, ∞)`. -/
theorem integral_mul_max_sub_gaussianReal (k : ℝ) :
    ∫ x, x * max (x - k) 0 ∂gaussianReal 0 1 = (gaussianReal 0 1).real (Ioi k) := by
  set p := gaussianPDFReal 0 1 with hp
  have h0 := integrable_gaussianPDFReal_mul_pow 0
  have h1 := integrable_gaussianPDFReal_mul_pow 1
  have h2 := integrable_gaussianPDFReal_mul_pow 2
  simp only [pow_zero, mul_one, pow_one] at h0 h1
  set F : ℝ → ℝ := fun x ↦ -(x - k) * p x with hF
  set F' : ℝ → ℝ := fun x ↦ -p x + (x - k) * x * p x with hF'
  have hderiv : ∀ x, HasDerivAt F (F' x) x := by
    intro x
    have := ((hasDerivAt_id x).sub_const k).neg.mul
      (TauCeti.Probability.hasDerivAt_gaussianPDFReal 0 1 x)
    convert this using 1
    · funext y; simp [hF, p]
    · simp [hF', p]; ring
  have hFint : Integrable F := by
    have : Integrable (fun x ↦ -(p x * x) + k * p x) := (h1.neg).add (h0.const_mul k)
    refine this.congr (ae_of_all _ fun x ↦ ?_)
    simp only [hF]; ring
  have hF'int : Integrable F' := by
    have : Integrable (fun x ↦ -p x + p x * x ^ 2 - k * (p x * x)) :=
      ((h0.neg).add h2).sub (h1.const_mul k)
    refine this.congr (ae_of_all _ fun x ↦ ?_)
    simp only [hF']; ring
  have hlim : Tendsto F atTop (𝓝 0) :=
    tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi (a := k) (fun x _ ↦ hderiv x)
      hF'int.integrableOn hFint.integrableOn
  have hI : ∫ x in Ioi k, F' x = 0 := by
    rw [integral_Ioi_of_hasDerivAt_of_tendsto (hderiv k).continuousAt.continuousWithinAt
      (fun x _ ↦ hderiv x) hF'int.integrableOn hlim]
    simp [hF]
  have hP : (gaussianReal 0 1).real (Ioi k) = ∫ x in Ioi k, p x := by
    rw [measureReal_def, gaussianReal_apply_eq_integral 0 one_ne_zero,
      ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Ioi
        fun x _ ↦ gaussianPDFReal_nonneg _ _ x)]
  rw [hP, integral_gaussianReal_eq_integral_smul one_ne_zero,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi k)]
  · calc ∫ x in Ioi k, p x • (x * max (x - k) 0) = ∫ x in Ioi k, (F' x + p x) := by
          refine setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ ?_
          have : max (x - k) 0 = x - k := max_eq_left (by simp at hx; linarith)
          simp only [smul_eq_mul, this, hF']; ring
      _ = ∫ x in Ioi k, p x := by
          rw [integral_add hF'int.integrableOn h0.integrableOn, hI, zero_add]
  · intro x hx
    have : max (x - k) 0 = 0 := max_eq_right (by simp at hx; linarith)
    simp [this]


/-- `x (x - k)⁺` is integrable for the standard Gaussian. -/
theorem integrable_mul_max_sub_gaussianReal (k : ℝ) :
    Integrable (fun x ↦ x * max (x - k) 0) (gaussianReal 0 1) := by
  have h2 : Integrable (fun x : ℝ ↦ x ^ 2) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal' (μ := 0) (v := 1) 2 ENNReal.ofNat_ne_top).integrable_sq
  have h1 : Integrable (fun x : ℝ ↦ x) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal' (μ := 0) (v := 1) 1 ENNReal.one_ne_top).integrable le_rfl
  refine (h2.add (h1.norm.const_mul |k|)).mono' (by fun_prop) (ae_of_all _ fun x ↦ ?_)
  simp only [norm_mul, Real.norm_eq_abs]
  have : |max (x - k) 0| ≤ |x| + |k| := by
    rcases le_total (x - k) 0 with h | h
    · simp [max_eq_right h]; positivity
    · rw [max_eq_left h, abs_of_nonneg h]; linarith [le_abs_self x, neg_abs_le k]
  calc |x| * |max (x - k) 0| ≤ |x| * (|x| + |k|) := by gcongr
    _ = x ^ 2 + |k| * |x| := by rw [mul_add, ← sq, sq_abs]; ring

/-- For `k ≥ 0` and a standard Gaussian, `∫ x ψ_k(x) dΦ = 2Φ(k) - 1`, where `ψ_k` is the
clipped Huber score. -/
theorem integral_mul_huberScore_gaussianReal {k : ℝ} (hk : 0 ≤ k) :
    ∫ x, x * huberScore k x ∂gaussianReal 0 1 = 2 * cdf (gaussianReal 0 1) k - 1 := by
  have hsplit : ∀ x, x * huberScore k x =
      x ^ 2 - x * max (x - k) 0 - (-x) * max (-x - k) 0 := by
    intro x
    unfold huberScore
    rcases le_total x (-k) with h | h
    · rw [min_eq_right (by linarith), max_eq_left h, max_eq_right (by linarith),
        max_eq_left (by linarith)]; ring
    rcases le_total x k with h' | h'
    · rw [min_eq_right h', max_eq_right h, max_eq_right (by linarith),
        max_eq_right (by linarith)]; ring
    · rw [min_eq_left h', max_eq_right (by linarith), max_eq_left (by linarith),
        max_eq_right (by linarith)]; ring
  have h2 : Integrable (fun x : ℝ ↦ x ^ 2) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal' (μ := 0) (v := 1) 2 ENNReal.ofNat_ne_top).integrable_sq
  have hA := integrable_mul_max_sub_gaussianReal k
  have hmap : (gaussianReal 0 1).map (fun x ↦ -x) = gaussianReal 0 1 := by
    simp [gaussianReal_map_neg]
  have hB : Integrable (fun x ↦ (-x) * max (-x - k) 0) (gaussianReal 0 1) := by
    have := hA
    rw [← hmap] at this
    exact (integrable_map_measure (g := fun x ↦ x * max (x - k) 0) (f := fun x : ℝ ↦ -x)
      (by fun_prop) (by fun_prop)).1 this
  have hBint : ∫ x, (-x) * max (-x - k) 0 ∂gaussianReal 0 1 =
      ∫ x, x * max (x - k) 0 ∂gaussianReal 0 1 := by
    conv_rhs => rw [← hmap]
    rw [integral_map (by fun_prop) (by fun_prop)]
  simp_rw [hsplit]
  rw [integral_sub (f := fun x ↦ x ^ 2 - x * max (x - k) 0)
    (g := fun x ↦ -x * max (-x - k) 0) (h2.sub hA) hB, integral_sub h2 hA, hBint,
    integral_mul_max_sub_gaussianReal, TauCeti.Probability.integral_sq_gaussianReal, cdf_eq_real,
    ← compl_Iic, measureReal_compl measurableSet_Iic]
  simp
  ring

/-- The clipped Huber score is bounded by the clipping constant. -/
theorem abs_huberScore_le {k : ℝ} (hk : 0 ≤ k) (x : ℝ) : |huberScore k x| ≤ k := by
  unfold huberScore
  exact abs_le.2 ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

/-- The clipped Huber score is measurable. -/
theorem measurable_huberScore (k : ℝ) : Measurable (huberScore k) := by
  unfold huberScore; fun_prop

/-- GAPS 102.44, Hampel optimality part of the Huber statement. Under the standard Gaussian
model, with `a = 2 Φ(k) - 1`, the normalized Huber score `ψ_k / a` has the smallest second moment
among measurable scores `φ` bounded by `k / a` with `∫ x φ(x) dΦ(x) = 1`; that is, it minimizes
the asymptotic variance among location M-estimators with gross-error sensitivity at most
`k / a`. -/
theorem integral_huberScore_sq_le (k : ℝ) (hk : 0 < k) (φ : ℝ → ℝ) (hm : Measurable φ)
    (hbound : ∀ x, |φ x| ≤ k / (2 * cdf (gaussianReal 0 1) k - 1))
    (h1 : (∫ x, x * φ x ∂gaussianReal 0 1) = 1) :
    (∫ x, (huberScore k x / (2 * cdf (gaussianReal 0 1) k - 1)) ^ 2 ∂gaussianReal 0 1) ≤
      ∫ x, φ x ^ 2 ∂gaussianReal 0 1 := by
  set G := gaussianReal 0 1 with hG
  set a := 2 * cdf G k - 1 with ha
  have hx : Integrable (fun x : ℝ ↦ x) G :=
    (memLp_id_gaussianReal' (μ := 0) (v := 1) 1 ENNReal.one_ne_top).integrable le_rfl
  have hhm := measurable_huberScore k
  have hxh : Integrable (fun x ↦ x * huberScore k x) G := by
    refine (hx.norm.const_mul k).mono' (by fun_prop) (ae_of_all _ fun x ↦ ?_)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, mul_comm]
    exact mul_le_mul_of_nonneg_right (abs_huberScore_le hk.le x) (abs_nonneg x)
  have hI : ∫ x, x * huberScore k x ∂G = a := integral_mul_huberScore_gaussianReal hk.le
  have ha : 0 < a := by
    rw [← hI]
    have hnn : 0 ≤ fun x ↦ x * huberScore k x := fun x ↦ by
      unfold huberScore
      rcases le_total x 0 with h | h
      · exact mul_nonneg_of_nonpos_of_nonpos h (max_le (by linarith) (min_le_of_right_le h))
      · exact mul_nonneg h (le_max_of_le_right (le_min hk.le h))
    rw [integral_pos_iff_support_of_nonneg hnn hxh]
    have hsupp : ({0}ᶜ : Set ℝ) ⊆ Function.support fun x ↦ x * huberScore k x := by
      intro x hx0
      simp only [mem_compl_iff, mem_singleton_iff] at hx0
      simp only [Function.mem_support]
      refine mul_ne_zero hx0 ?_
      unfold huberScore
      rcases lt_or_gt_of_ne hx0 with h | h
      · exact (max_lt (by linarith) (min_lt_of_right_lt h)).ne
      · exact (lt_max_of_lt_right (lt_min hk h)).ne'
    refine lt_of_lt_of_le ?_ (measure_mono hsupp)
    have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
    rw [prob_compl_eq_one_sub (measurableSet_singleton 0),
      measure_singleton (μ := gaussianReal 0 1)]
    simp
  set ψ : ℝ → ℝ := fun x ↦ huberScore k x / a with hψ
  have hψb : ∀ x, |ψ x| ≤ k / a := fun x ↦ by
    simp only [hψ, abs_div, abs_of_pos ha]
    exact div_le_div_of_nonneg_right (abs_huberScore_le hk.le x) ha.le
  have hψm : Measurable ψ := hhm.div_const a
  have hφ2 : Integrable (fun x ↦ φ x ^ 2) G :=
    Integrable.of_bound (by fun_prop) ((k / a) ^ 2) (ae_of_all _ fun x ↦ by
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hbound x) 2)
  have hψ2 : Integrable (fun x ↦ ψ x ^ 2) G :=
    Integrable.of_bound (by fun_prop) ((k / a) ^ 2) (ae_of_all _ fun x ↦ by
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hψb x) 2)
  have hxφ : Integrable (fun x ↦ x * φ x) G := by
    refine (hx.norm.mul_const (k / a)).mono' (by fun_prop) (ae_of_all _ fun x ↦ ?_)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hbound x) (abs_nonneg x)
  have hxψ : Integrable (fun x ↦ x * ψ x) G := by
    refine (hx.norm.mul_const (k / a)).mono' (by fun_prop) (ae_of_all _ fun x ↦ ?_)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hψb x) (abs_nonneg x)
  have hxψ1 : ∫ x, x * ψ x ∂G = 1 := by
    simp only [hψ, mul_div_assoc']
    rw [integral_div, hI, div_self ha.ne']
  have hpt : ∀ x, ψ x ^ 2 + 2 / a * (x * φ x - x * ψ x) ≤ φ x ^ 2 := by
    intro x
    have key : 0 ≤ (φ x - ψ x) * (huberScore k x - x) := by
      have hb := abs_le.1 (hbound x)
      unfold huberScore at hψ ⊢
      rcases le_total x (-k) with h | h
      · have e : max (-k) (min k x) = -k :=
          max_eq_left (min_le_of_right_le h)
        have : ψ x = -k / a := by simp [hψ, e, neg_div]
        rw [e, this]
        exact mul_nonneg (by linarith [hb.1, neg_div a k]) (by linarith)
      rcases le_total x k with h' | h'
      · have e : max (-k) (min k x) = x := by rw [min_eq_right h', max_eq_right h]
        rw [e]; simp
      · have e : max (-k) (min k x) = k := by
          rw [min_eq_left h', max_eq_right (by linarith)]
        have : ψ x = k / a := by simp [hψ, e]
        rw [e, this]
        exact mul_nonneg_of_nonpos_of_nonpos (by linarith [hb.2]) (by linarith)
    have hid : φ x ^ 2 - (ψ x ^ 2 + 2 / a * (x * φ x - x * ψ x)) =
        (φ x - ψ x) ^ 2 + 2 * ((φ x - ψ x) * (huberScore k x - x)) / a := by
      simp only [hψ]; field_simp; ring
    have : 0 ≤ (φ x - ψ x) ^ 2 + 2 * ((φ x - ψ x) * (huberScore k x - x)) / a := by positivity
    linarith
  calc ∫ x, (huberScore k x / a) ^ 2 ∂G = ∫ x, ψ x ^ 2 ∂G := rfl
    _ = ∫ x, ψ x ^ 2 + 2 / a * (x * φ x - x * ψ x) ∂G := by
        rw [integral_add (f := fun x ↦ ψ x ^ 2) (g := fun x ↦ 2 / a * (x * φ x - x * ψ x))
          hψ2 ((hxφ.sub hxψ).const_mul _), integral_const_mul,
          integral_sub hxφ hxψ, h1, hxψ1]
        ring
    _ ≤ ∫ x, φ x ^ 2 ∂G :=
        integral_mono (hψ2.add ((hxφ.sub hxψ).const_mul _)) hφ2 hpt


/-- GAPS 102.49: the one-term Edgeworth expansion of the standardized mean. For an i.i.d. sequence
with mean zero, variance one, finite third absolute moment `ρ = E X³`, and a nonlattice law, the
distribution function of `√n X̄ₙ` is `Φ(t) - φ(t) (t² - 1) ρ / (6 √n) + o(n^{-1/2})` uniformly
in `t`. -/
theorem exists_uniform_edgeworth_expansion {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure ℝ) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hiid : IsIndependentIdenticallyDistributed μ X P) (h3 : Integrable
      (fun x ↦ |x| ^ 3) P)
    (h0 : (∫ x, x ∂P) = 0) (h1 : (∫ x, x ^ 2 ∂P) = 1)
    (hnonlattice : ∀ a : ℝ, ∀ b > 0, P (range fun j : ℤ ↦ a + b * j) < 1) :
    let ρ := ∫ x, x ^ 3 ∂P;
    ∃ e : ℕ → ℝ, Tendsto (fun n : ℕ ↦ Real.sqrt n * e n) atTop (𝓝 0) ∧
      ∀ (n : ℕ), n ≥ 1 → ∀ t, |μ.real {ω | Real.sqrt n * sampleAverage X n ω ≤ t} -
        (cdf (gaussianReal 0 1) t - gaussianPDFReal 0 1 t * (t ^ 2 - 1) *
          ρ / (6 * Real.sqrt n))| ≤ e n := by
  sorry

/-- Pólya's theorem: pointwise convergence of distribution functions to a continuous
distribution function implies convergence in Kolmogorov distance. -/
private theorem tendsto_kolmogorovDistance_of_tendsto_cdf (ν : ℕ → Measure ℝ) (ρ : Measure ℝ)
    (hc : Continuous (cdf ρ)) (h : ∀ t, Tendsto (fun n ↦ cdf (ν n) t) atTop (𝓝 (cdf ρ t))) :
    Tendsto (fun n ↦ kolmogorovDistance (ν n) ρ) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨M, hM⟩ := exists_nat_gt (4 / ε + 2)
  have hM0 : (0 : ℝ) < M := by have : 0 < 4 / ε := by positivity
                               linarith
  have hMε : 3 / (M : ℝ) < ε := by
    rw [div_lt_iff₀ hM0]
    have : 4 / ε < M := by linarith
    rw [div_lt_iff₀ hε] at this
    linarith
  set F := cdf ρ
  have hgrid : ∀ k ∈ Finset.Ioo 0 M, ∃ s, F s = (k : ℝ) / M := by
    intro k hk
    rw [Finset.mem_Ioo] at hk
    have hk0 : (0 : ℝ) < k / M := div_pos (by exact_mod_cast hk.1) hM0
    have hk1 : (k : ℝ) / M < 1 := (div_lt_one hM0).2 (by exact_mod_cast hk.2)
    obtain ⟨a, ha⟩ := ((tendsto_cdf_atBot (μ := ρ)).eventually (gt_mem_nhds hk0)).exists
    obtain ⟨b, hb⟩ := ((tendsto_cdf_atTop (μ := ρ)).eventually (lt_mem_nhds hk1)).exists
    exact intermediate_value_univ a b hc ⟨ha.le, hb.le⟩
  choose! g hg using hgrid
  have hev : ∀ᶠ n in atTop, ∀ k ∈ Finset.Ioo 0 M, |cdf (ν n) (g k) - F (g k)| < 1 / M := by
    rw [Finset.eventually_all]
    intro k _
    have := (h (g k)).sub_const (F (g k))
    rw [sub_self] at this
    filter_upwards [this.eventually (Metric.ball_mem_nhds 0 (by positivity : (0 : ℝ) < 1 / M))]
      with n hn
    simpa [Real.dist_eq] using hn
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  refine ⟨N, fun n hn ↦ ?_⟩
  have hpt : ∀ t, |cdf (ν n) t - F t| ≤ 3 / M := by
    intro t
    set G := cdf (ν n)
    set k := ⌊(M : ℝ) * F t⌋₊ with hk
    have hFt0 := cdf_nonneg (μ := ρ) t
    have hFt1 := cdf_le_one (μ := ρ) t
    have hkle : (k : ℝ) ≤ M * F t := Nat.floor_le (by positivity)
    have hklt : M * F t < k + 1 := Nat.lt_floor_add_one _
    have hkM : k ≤ M := by
      have : (k : ℝ) ≤ M := hkle.trans (by nlinarith)
      exact_mod_cast this
    have hG0 := cdf_nonneg (μ := ν n) t
    have hG1 := cdf_le_one (μ := ν n) t
    have hlo : k / (M : ℝ) ≤ F t := by rw [div_le_iff₀ hM0]; linarith
    have hhi : F t < (k + 1) / (M : ℝ) := by rw [lt_div_iff₀ hM0]; linarith
    rw [abs_le]
    constructor
    · -- lower bound on `G t - F t`
      by_cases hk2 : 2 ≤ k
      · have hmem : k - 1 ∈ Finset.Ioo 0 M := Finset.mem_Ioo.2 ⟨by omega, by omega⟩
        have hgk := hg (k - 1) hmem
        have hcast : ((k - 1 : ℕ) : ℝ) = k - 1 := by
          rw [Nat.cast_sub (by omega)]; simp
        rw [hcast] at hgk
        have hlt : g (k - 1) < t := by
          refine lt_of_not_ge fun hle ↦ ?_
          have := monotone_cdf (μ := ρ) hle
          rw [hgk] at this
          have : (k : ℝ) / M ≤ (k - 1) / M := hlo.trans this
          rw [div_le_div_iff_of_pos_right hM0] at this
          linarith
        have h1 := monotone_cdf (μ := ν n) hlt.le
        have h2 := hN n hn (k - 1) hmem
        rw [hgk, abs_lt] at h2
        have h3 : (k + 1) / (M : ℝ) - ((k - 1) / M - 1 / M) = 3 / M := by ring
        linarith
      · have : (k : ℝ) ≤ 1 := by exact_mod_cast (by omega : k ≤ 1)
        have : F t < 2 / M := hhi.trans_le (by
          rw [div_le_div_iff_of_pos_right hM0]; linarith)
        have : (2 : ℝ) / M ≤ 3 / M := by rw [div_le_div_iff_of_pos_right hM0]; norm_num
        linarith
    · -- upper bound on `G t - F t`
      by_cases hk1 : k + 1 < M
      · have hmem : k + 1 ∈ Finset.Ioo 0 M := Finset.mem_Ioo.2 ⟨by omega, hk1⟩
        have hgk := hg (k + 1) hmem
        push_cast at hgk
        have hlt : t < g (k + 1) := by
          refine lt_of_not_ge fun hle ↦ ?_
          have := monotone_cdf (μ := ρ) hle
          rw [hgk] at this
          linarith
        have h1 := monotone_cdf (μ := ν n) hlt.le
        have h2 := hN n hn (k + 1) hmem
        rw [hgk, abs_lt] at h2
        have h3 : (k + 1) / (M : ℝ) + 1 / M - k / M = 2 / M := by ring
        have : (2 : ℝ) / M ≤ 3 / M := by rw [div_le_div_iff_of_pos_right hM0]; norm_num
        linarith
      · have hkM' : (M : ℝ) ≤ k + 1 := by exact_mod_cast (by omega : M ≤ k + 1)
        have : 1 - 1 / (M : ℝ) ≤ F t := by
          refine le_trans ?_ hlo
          rw [one_sub_div hM0.ne', div_le_div_iff_of_pos_right hM0]; linarith
        have : (1 : ℝ) / M ≤ 3 / M := by rw [div_le_div_iff_of_pos_right hM0]; norm_num
        linarith
  have hKD0 : 0 ≤ kolmogorovDistance (ν n) ρ :=
    Real.sSup_nonneg (by rintro _ ⟨t, rfl⟩; exact abs_nonneg _)
  have hKD : kolmogorovDistance (ν n) ρ ≤ 3 / M :=
    csSup_le (range_nonempty _) (by rintro _ ⟨t, rfl⟩; exact hpt t)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hKD0]
  exact hKD.trans_lt hMε

/-- The integral against the empirical measure is the sample average. -/
private theorem integral_empiricalMeasure_fin {n : ℕ} (x : Fin n → ℝ) {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] (f : ℝ → F) :
    ∫ y, f y ∂(empiricalMeasure n x) = (n : ℝ)⁻¹ • ∑ i, f (x i) := by
  rw [empiricalMeasure, integral_smul_measure, integral_finsetSum_measure]
  · simp
  · intro i _
    exact integrable_dirac (by simp)

/-- The characteristic function of the bootstrap law of `√n (X̄*ₙ - c)` is the `n`-th power of
the empirical characteristic function of the scaled centred sample. -/
private theorem charFun_bootstrap {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) (c s : ℝ) :
    charFun ((Measure.pi fun _ : Fin n ↦ empiricalMeasure n x).map
        (fun y : Fin n → ℝ ↦ Real.sqrt n * ((∑ i, y i) / n - c))) s =
      ((n : ℂ)⁻¹ * ∑ i, Complex.exp ((((Real.sqrt n)⁻¹ * (x i - c) * s : ℝ) : ℂ) *
        Complex.I)) ^ n := by
  have := isProbabilityMeasure_empiricalMeasure hn x
  have hsq : Real.sqrt n ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast hn)).ne'
  have hf : ∀ y : Fin n → ℝ, Real.sqrt n * ((∑ i, y i) / n - c) =
      ∑ i, (Real.sqrt n)⁻¹ * (y i - c) := fun y ↦ by
    rw [← Finset.mul_sum, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have h2 := Real.sq_sqrt (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp
    rw [h2]
  rw [charFun_apply_real, integral_map (by fun_prop) (by fun_prop)]
  simp_rw [hf, Complex.ofReal_sum, Finset.mul_sum, Finset.sum_mul, Complex.exp_sum]
  rw [integral_fintype_prod_eq_prod (f := fun _ y ↦ Complex.exp
    ((s : ℂ) * (((Real.sqrt n)⁻¹ * (y - c) : ℝ) : ℂ) * Complex.I))]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, integral_empiricalMeasure_fin]
  congr 1
  simp only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_natCast]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  congr 2
  push_cast
  ring

/-- Third-order Taylor bound for the average of `exp (i wᵢ)` when `|wᵢ| ≤ 1` and `∑ wᵢ = 0`. -/
private theorem norm_avg_exp_sub_le {n : ℕ} (hn : 0 < n) (w : Fin n → ℝ) (hw : ∀ i, |w i| ≤ 1)
    (hsum : ∑ i, w i = 0) :
    ‖(n : ℂ)⁻¹ * ∑ i, Complex.exp ((w i : ℂ) * Complex.I) -
        (1 - (n : ℂ)⁻¹ * ∑ i, ((w i ^ 2 : ℝ) : ℂ) / 2)‖ ≤ (n : ℝ)⁻¹ * ∑ i, |w i| ^ 3 := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hexp : (1 : ℂ) - (n : ℂ)⁻¹ * ∑ i, ((w i ^ 2 : ℝ) : ℂ) / 2 =
      (n : ℂ)⁻¹ * ∑ i, ∑ m ∈ Finset.range 3, ((w i : ℂ) * Complex.I) ^ m / m.factorial := by
    have h0 : ∑ i, ((w i : ℂ) * Complex.I) = 0 := by
      rw [← Finset.sum_mul, ← Complex.ofReal_sum, hsum]; simp
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Finset.sum_add_distrib,
      zero_add, pow_zero, pow_one, Nat.factorial_zero, Nat.factorial_one,
      Nat.cast_one, div_one, h0, add_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
    have h2 : ∑ i, ((w i : ℂ) * Complex.I) ^ 2 / ((Nat.factorial 2 : ℕ) : ℂ) =
        -∑ i, ((w i ^ 2 : ℝ) : ℂ) / 2 := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [mul_pow, Complex.I_sq]; push_cast; simp [Nat.factorial]; ring
    rw [h2, mul_add, inv_mul_cancel₀ hn']
    ring
  rw [hexp, ← mul_sub, ← Finset.sum_sub_distrib, norm_mul]
  have hninv : ‖(n : ℂ)⁻¹‖ = (n : ℝ)⁻¹ := by simp
  rw [hninv]
  refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_))
    (by positivity)
  have hnorm : ‖(w i : ℂ) * Complex.I‖ = |w i| := by simp
  have hb := Complex.exp_bound (x := (w i : ℂ) * Complex.I) (hnorm ▸ hw i) (n := 3) (by norm_num)
  rw [hnorm] at hb
  refine hb.trans ?_
  have : ((Nat.succ 3 : ℕ) : ℝ) * ((Nat.factorial 3 : ℕ) * (3 : ℕ) : ℝ)⁻¹ ≤ 1 := by
    simp [Nat.factorial]; norm_num
  have h3 : 0 ≤ |w i| ^ 3 := by positivity
  nlinarith

/-- If `aₙ / n → 0`, then eventually every `aᵢ` with `i < n` is at most `ε n`. -/
private theorem eventually_forall_lt_le_mul (a : ℕ → ℝ) (ha : Tendsto (fun n ↦ a n / n) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ n : ℕ in atTop, ∀ i < n, a i ≤ ε * n := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 (ha.eventually (gt_mem_nhds hε))
  set C := ∑ j ∈ Finset.range (N + 1), |a j|
  filter_upwards [eventually_ge_atTop (N + 1),
    (tendsto_natCast_atTop_atTop.const_mul_atTop hε).eventually (eventually_ge_atTop C)]
    with n hn hCn i hi
  by_cases hiN : N + 1 ≤ i
  · have h1 := hN i (by omega)
    have hi0 : (0 : ℝ) < i := by exact_mod_cast (by omega : 0 < i)
    rw [div_lt_iff₀ hi0] at h1
    have : (i : ℝ) ≤ n := by exact_mod_cast hi.le
    nlinarith
  · have h1 : |a i| ≤ C := Finset.single_le_sum (f := fun j ↦ |a j|) (fun _ _ ↦ abs_nonneg _)
      (Finset.mem_range.2 (by omega))
    exact (le_abs_self _).trans (h1.trans hCn)

/-- If the averages of `xᵢ` and `xᵢ²` converge to `m` and `σ² + m²`, then the empirical variance
converges to `σ²`. -/
private theorem tendsto_avg_sq_sub_avg (x : ℕ → ℝ) (m σ2 : ℝ)
    (hm : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, x i) atTop (𝓝 m))
    (h2 : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, x i ^ 2) atTop
      (𝓝 (σ2 + m ^ 2))) :
    Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
      (x i - (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, x j) ^ 2) atTop (𝓝 σ2) := by
  set c : ℕ → ℝ := fun n ↦ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, x i with hc
  set v : ℕ → ℝ := fun n ↦ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, (x i - c n) ^ 2 with hv
  have hsumx : ∀ n : ℕ, 0 < n → ∑ i ∈ Finset.range n, x i = n * c n := fun n hn ↦ by
    simp only [c]; field_simp
  have hvform : ∀ n : ℕ, 0 < n →
      v n = (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, x i ^ 2 - c n ^ 2 := fun n hn ↦ by
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    simp only [v, sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
      ← Finset.mul_sum, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [hsumx n hn]
    field_simp
    ring
  have hvlim : Tendsto v atTop (𝓝 σ2) := by
    have h := h2.sub (hm.pow 2)
    rw [add_sub_cancel_right] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [hvform n hn]
  exact hvlim

/-- Along a sequence whose first two empirical moments converge and with `xₙ² / n → 0`, the
bootstrap characteristic functions converge pointwise to that of `N(0, σ²)`. -/
private theorem tendsto_charFun_bootstrapLaw (x : ℕ → ℝ) (m σ2 : ℝ)
    (hm : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, x i) atTop (𝓝 m))
    (h2 : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, x i ^ 2) atTop
      (𝓝 (σ2 + m ^ 2)))
    (hx : Tendsto (fun n : ℕ ↦ x n ^ 2 / n) atTop (𝓝 0)) (s : ℝ) :
    Tendsto (fun n : ℕ ↦ charFun ((Measure.pi fun _ : Fin n ↦
        empiricalMeasure n (fun i ↦ x i.val)).map (fun y : Fin n → ℝ ↦ Real.sqrt n *
          ((∑ i, y i) / n - (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, x i))) s) atTop
      (𝓝 (Complex.exp (-(σ2 * s ^ 2 / 2)))) := by
  set c : ℕ → ℝ := fun n ↦ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, x i with hc
  set v : ℕ → ℝ := fun n ↦ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, (x i - c n) ^ 2 with hv
  have hsumx : ∀ n : ℕ, 0 < n → ∑ i ∈ Finset.range n, x i = n * c n := fun n hn ↦ by
    simp only [c]; field_simp
  have hvlim : Tendsto v atTop (𝓝 σ2) := tendsto_avg_sq_sub_avg x m σ2 hm h2
  set ψ : ℕ → ℂ := fun n ↦ (n : ℂ)⁻¹ * ∑ i : Fin n,
    Complex.exp ((((Real.sqrt n)⁻¹ * (x i - c n) * s : ℝ) : ℂ) * Complex.I) with hψ
  have hchar : ∀ᶠ n : ℕ in atTop, ψ n ^ n = charFun ((Measure.pi fun _ : Fin n ↦
        empiricalMeasure n (fun i ↦ x i.val)).map (fun y : Fin n → ℝ ↦ Real.sqrt n *
          ((∑ i, y i) / n - (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, x i))) s := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [charFun_bootstrap hn]
  refine (Complex.tendsto_pow_exp_of_isLittleO_sub_add_div _ ?_).congr' hchar
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  set K : ℝ := s ^ 2 + 1 with hK
  set V : ℝ := |σ2| + 1 with hV
  have hK0 : 0 < K := by positivity
  have hV0 : 0 < V := by positivity
  set η : ℝ := min 1 (ε / (2 * K * V)) with hη
  have hη0 : 0 < η := lt_min one_pos (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηε : η ≤ ε / (2 * K * V) := min_le_right _ _
  set δ : ℝ := η ^ 2 / (4 * K) with hδ
  have hδ0 : 0 < δ := by positivity
  have hE1 := eventually_forall_lt_le_mul (fun i ↦ x i ^ 2) hx hδ0
  have hE2 : ∀ᶠ n : ℕ in atTop, c n ^ 2 ≤ δ * n := by
    have hb : Tendsto (fun n : ℕ ↦ c n ^ 2 / n) atTop (𝓝 0) := by
      have := (hm.pow 2).mul (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop)
      rw [mul_zero] at this
      refine this.congr fun n ↦ ?_
      simp only [c, div_eq_mul_inv, Function.comp_apply]
    filter_upwards [hb.eventually (gt_mem_nhds hδ0), eventually_gt_atTop 0] with n hn hn0
    have : (0 : ℝ) < n := by exact_mod_cast hn0
    rw [div_lt_iff₀ this] at hn
    exact hn.le
  have hE3 : ∀ᶠ n : ℕ in atTop, |v n - σ2| ≤ ε / K := by
    have hvl := hvlim.sub_const σ2
    rw [sub_self] at hvl
    filter_upwards [hvl.eventually (Metric.closedBall_mem_nhds 0
      (by positivity : 0 < ε / K))] with n hn
    simpa [Real.dist_eq] using hn
  have hE4 : ∀ᶠ n : ℕ in atTop, v n ≤ V := by
    filter_upwards [hvlim.eventually (gt_mem_nhds (by
      have := le_abs_self σ2; linarith : σ2 < V))] with n hn
    exact hn.le
  filter_upwards [hE1, hE2, hE3, hE4, eventually_gt_atTop 0] with n h1 h2 h3 h4 hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hsq : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn'.le
  have hsq0 : 0 < Real.sqrt n := Real.sqrt_pos.2 hn'
  set w : Fin n → ℝ := fun i ↦ (Real.sqrt n)⁻¹ * (x i - c n) * s with hw
  have hw2 : ∀ i : Fin n, w i ^ 2 = s ^ 2 * (x i - c n) ^ 2 / n := fun i ↦ by
    simp only [w]; rw [mul_pow, mul_pow, inv_pow, hsq]; field_simp
  have hwle : ∀ i : Fin n, |w i| ≤ η := fun i ↦ by
    have hxi := h1 i i.2
    have hsK : s ^ 2 ≤ K := by linarith
    have hz : (x i - c n) ^ 2 ≤ 2 * (x i ^ 2 + c n ^ 2) := by nlinarith [sq_nonneg (x i + c n)]
    have : w i ^ 2 ≤ η ^ 2 := by
      rw [hw2, div_le_iff₀ hn']
      calc s ^ 2 * (x i - c n) ^ 2 ≤ K * (2 * (x i ^ 2 + c n ^ 2)) :=
            mul_le_mul hsK hz (sq_nonneg _) hK0.le
        _ ≤ K * (2 * (δ * n + δ * n)) := by gcongr
        _ = η ^ 2 * n := by simp only [δ]; field_simp; ring
    exact abs_le_of_sq_le_sq' this hη0.le |> fun h ↦ abs_le.2 h
  have hwsum : ∑ i, w i = 0 := by
    simp only [w, ← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [Fin.sum_univ_eq_sum_range (f := x), hsumx n hn]
    ring
  have hbound := norm_avg_exp_sub_le hn w (fun i ↦ (hwle i).trans hη1) hwsum
  have hw2sum : ∑ i : Fin n, w i ^ 2 = s ^ 2 * v n := by
    simp only [hw2, ← Finset.sum_div, ← Finset.mul_sum, v]
    rw [Fin.sum_univ_eq_sum_range (f := fun i ↦ (x i - c n) ^ 2)]
    field_simp
  have hcube : (n : ℝ)⁻¹ * ∑ i, |w i| ^ 3 ≤ η * s ^ 2 * v n / n := by
    have : ∑ i, |w i| ^ 3 ≤ η * ∑ i, w i ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ ↦ ?_
      have : |w i| ^ 3 = |w i| * w i ^ 2 := by rw [← sq_abs (w i)]; ring
      rw [this]
      exact mul_le_mul_of_nonneg_right (hwle i) (sq_nonneg _)
    rw [hw2sum] at this
    rw [div_eq_inv_mul, mul_comm (n : ℝ)⁻¹ _] at *
    calc (∑ i, |w i| ^ 3) * (n : ℝ)⁻¹ ≤ η * (s ^ 2 * v n) * (n : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ = _ := by ring
  have hψeq : ψ n = (n : ℂ)⁻¹ * ∑ i, Complex.exp ((w i : ℂ) * Complex.I) := rfl
  have hquad : (n : ℂ)⁻¹ * ∑ i, ((w i ^ 2 : ℝ) : ℂ) / 2 = ((s ^ 2 * v n / (2 * n) : ℝ) : ℂ) := by
    rw [← Finset.sum_div, ← Complex.ofReal_sum, hw2sum]; push_cast; field_simp
  have hsplit : ψ n - (1 + (-(σ2 * s ^ 2 / 2) : ℂ) / n) =
      (ψ n - (1 - (n : ℂ)⁻¹ * ∑ i, ((w i ^ 2 : ℝ) : ℂ) / 2)) +
        ((s ^ 2 * (σ2 - v n) / (2 * n) : ℝ) : ℂ) := by
    rw [hquad]; push_cast; field_simp; ring
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  rw [← hψeq] at hbound
  have hnorm1 : ‖(1 / (n : ℂ))‖ = 1 / (n : ℝ) := by simp
  rw [hnorm1, Complex.norm_real, Real.norm_eq_abs]
  have hA : η * s ^ 2 * v n / n ≤ ε / 2 * (1 / n) := by
    rw [div_eq_mul_one_div]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    have hv0 : 0 ≤ v n := by simp only [v]; positivity
    calc η * s ^ 2 * v n ≤ (ε / (2 * K * V)) * K * V := by
          gcongr
          · linarith
      _ = ε / 2 := by field_simp
  have hB : |s ^ 2 * (σ2 - v n) / (2 * n)| ≤ ε / 2 * (1 / n) := by
    rw [abs_div, abs_mul, abs_of_nonneg (sq_nonneg s), abs_of_pos (by positivity : (0:ℝ) < 2 * n),
      abs_sub_comm]
    rw [div_le_iff₀ (by positivity)]
    have : s ^ 2 * |v n - σ2| ≤ K * (ε / K) := mul_le_mul (by linarith) h3 (abs_nonneg _) hK0.le
    rw [mul_div_cancel₀ _ hK0.ne'] at this
    field_simp
    linarith
  linarith [hbound.trans hcube]

/-- Deterministic bootstrap consistency: under the conclusions of the strong law along a fixed
sequence, the bootstrap law of the mean converges to `N(0, σ²)` in Kolmogorov distance. -/
private theorem tendsto_kolmogorovDistance_bootstrapLaw (x : ℕ → ℝ) (m σ2 : ℝ) (hσ : 0 < σ2)
    (hm : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, x i) atTop (𝓝 m))
    (h2 : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, x i ^ 2) atTop
      (𝓝 (σ2 + m ^ 2)))
    (hx : Tendsto (fun n : ℕ ↦ x n ^ 2 / n) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ ↦ kolmogorovDistance ((Measure.pi fun _ : Fin n ↦
        empiricalMeasure n (fun i ↦ x i.val)).map (fun y : Fin n → ℝ ↦ Real.sqrt n *
          ((∑ i, y i) / n - (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, x i))) (gaussianReal 0 σ2.toNNReal))
      atTop (𝓝 0) := by
  set B : ℕ → Measure ℝ := fun n ↦ (Measure.pi fun _ : Fin n ↦
        empiricalMeasure n (fun i ↦ x i.val)).map (fun y : Fin n → ℝ ↦ Real.sqrt n *
          ((∑ i, y i) / n - (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, x i)) with hB
  have hBp : ∀ n, IsProbabilityMeasure (B (n + 1)) := fun n ↦ by
    have := isProbabilityMeasure_empiricalMeasure (Nat.succ_pos n) (fun i ↦ x i.val)
    exact (Measure.isProbabilityMeasure_map_iff (by fun_prop)).2 inferInstance
  let Bp : ℕ → ProbabilityMeasure ℝ := fun n ↦ ⟨B (n + 1), hBp n⟩
  let G : ProbabilityMeasure ℝ := ⟨gaussianReal 0 σ2.toNNReal, inferInstance⟩
  have hlim : Tendsto Bp atTop (𝓝 G) := by
    rw [ProbabilityMeasure.tendsto_iff_tendsto_charFun]
    intro t
    have h := (tendsto_charFun_bootstrapLaw x m σ2 hm h2 hx t).comp (tendsto_add_atTop_nat 1)
    convert h using 2
    · rfl
    · simp only [G, ProbabilityMeasure.coe_mk, charFun_gaussianReal, Complex.ofReal_zero,
        mul_zero, zero_mul, zero_sub, Real.coe_toNNReal _ hσ.le]
  have hns : NullSingletonClass (gaussianReal 0 σ2.toNNReal) :=
    nullSingletonClass_gaussianReal (Real.toNNReal_pos.2 hσ).ne'
  have hnsG : NullSingletonClass (G : Measure ℝ) := hns
  have hcdf : ∀ t, Tendsto (fun n ↦ cdf (B (n + 1)) t) atTop
      (𝓝 (cdf (gaussianReal 0 σ2.toNNReal) t)) := by
    intro t
    have hfr : (G : Measure ℝ) (frontier (Iic t)) = 0 := by
      rw [frontier_Iic]; exact measure_singleton t
    have h := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hlim hfr
    have h' := (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h
    convert h' using 1
    · funext n
      simp only [Function.comp_apply, Bp, ProbabilityMeasure.coe_mk]
      rw [cdf_eq_real]; rfl
    · rw [cdf_eq_real]; rfl
  have hc : Continuous (cdf (gaussianReal 0 σ2.toNNReal)) :=
    Measure.continuous_cdf_of_noAtoms _
  exact (tendsto_add_atTop_iff_nat 1).1
    (tendsto_kolmogorovDistance_of_tendsto_cdf (fun n ↦ B (n + 1)) _ hc hcdf)


/-- By right-continuity of distribution functions, the Kolmogorov distance is a supremum over
rational points. -/
private theorem kolmogorovDistance_eq_iSup_rat (P Q : Measure ℝ) :
    kolmogorovDistance P Q = ⨆ q : ℚ, |cdf P q - cdf Q q| := by
  have hb : ∀ t, |cdf P t - cdf Q t| ≤ 1 := fun t ↦ by
    rw [abs_le]; constructor <;>
      linarith [cdf_nonneg P t, cdf_le_one P t, cdf_nonneg Q t, cdf_le_one Q t]
  have hB : BddAbove (range fun q : ℚ ↦ |cdf P q - cdf Q q|) :=
    ⟨1, by rintro _ ⟨q, rfl⟩; exact hb q⟩
  unfold kolmogorovDistance
  apply le_antisymm
  · refine csSup_le (range_nonempty _) ?_
    rintro _ ⟨t, rfl⟩
    have hc : ContinuousWithinAt (fun s ↦ |cdf P s - cdf Q s|) (Ioi t) t :=
      ((((cdf P).right_continuous t).sub ((cdf Q).right_continuous t)).abs).mono
        Ioi_subset_Ici_self
    have hq : ∀ k : ℕ, ∃ q : ℚ, t < q ∧ (q : ℝ) < t + 1 / (k + 1) := fun k ↦
      exists_rat_btwn (lt_add_of_pos_right t Nat.one_div_pos_of_nat)
    choose q hq1 hq2 using hq
    have hu : Tendsto (fun k ↦ (q k : ℝ)) atTop (𝓝[>] t) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun k ↦ hq1 k⟩
      have h0 : Tendsto (fun k : ℕ ↦ t + 1 / ((k : ℝ) + 1)) atTop (𝓝 t) := by
        simpa using (tendsto_const_nhds (x := t)).add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0
        (fun k ↦ (hq1 k).le) fun k ↦ (hq2 k).le
    exact le_of_tendsto' (hc.tendsto.comp hu) fun k ↦ le_ciSup hB (q k)
  · exact ciSup_le fun q ↦ le_csSup ⟨1, by rintro _ ⟨t, rfl⟩; exact hb t⟩ ⟨(q : ℝ), rfl⟩

/-- The Kolmogorov distance of a random bootstrap law is measurable, through the measurability
of TauCeti's random product measures. -/
private theorem measurable_kolmogorovDistance_bootstrap {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (hn : 0 < n) (x : Ω → Fin n → ℝ) (hx : Measurable x) (c : Ω → ℝ) (hc : Measurable c)
    (ρ : Measure ℝ) :
    Measurable fun ω ↦ kolmogorovDistance ((Measure.pi fun _ : Fin n ↦
      empiricalMeasure n (x ω)).map (fun y : Fin n → ℝ ↦ Real.sqrt n * ((∑ i, y i) / n - c ω)))
        ρ := by
  have hE : Measurable fun ω ↦ empiricalMeasure n (x ω) := by
    refine Measure.measurable_of_measurable_coe _ fun s hs ↦ ?_
    simp only [empiricalMeasure, smul_apply, smul_eq_mul, FunLike.coe_sum, Finset.sum_apply]
    refine Measurable.const_mul (Finset.measurable_sum _ fun i _ ↦ ?_) _
    exact (Measure.measurable_coe hs).comp (Measure.measurable_dirac.comp ((measurable_pi_apply i).comp hx))
  let ν : Ω → ProbabilityMeasure ℝ := fun ω ↦
    ⟨empiricalMeasure n (x ω), isProbabilityMeasure_empiricalMeasure hn (x ω)⟩
  have hν : Measurable ν := hE.subtype_mk
  let κ : Kernel Ω (Fin n → ℝ) :=
    ⟨fun ω ↦ (ProbabilityMeasure.pi fun _ : Fin n ↦ ν ω).toMeasure,
      TauCeti.MeasureTheory.measurable_probabilityMeasure_pi_const_toMeasure ν hν⟩
  have : IsMarkovKernel κ := ⟨fun ω ↦ (ProbabilityMeasure.pi fun _ : Fin n ↦ ν ω).prop⟩
  have hg : Measurable fun p : Ω × (Fin n → ℝ) ↦
      Real.sqrt n * ((∑ i, p.2 i) / n - c p.1) := by fun_prop
  simp_rw [kolmogorovDistance_eq_iSup_rat]
  refine Measurable.iSup fun q ↦ ?_
  refine continuous_abs.measurable.comp (Measurable.sub ?_ measurable_const)
  have hrw : ∀ ω, cdf ((Measure.pi fun _ : Fin n ↦ empiricalMeasure n (x ω)).map
      (fun y : Fin n → ℝ ↦ Real.sqrt n * ((∑ i, y i) / n - c ω))) q =
      (κ ω (Prod.mk ω ⁻¹' {p | Real.sqrt n * ((∑ i, p.2 i) / n - c p.1) ≤ q})).toReal := by
    intro ω
    have hgω : Measurable fun y : Fin n → ℝ ↦ Real.sqrt n * ((∑ i, y i) / n - c ω) := by
      fun_prop
    have : IsProbabilityMeasure (Measure.pi fun _ : Fin n ↦ empiricalMeasure n (x ω)) := by
      have := isProbabilityMeasure_empiricalMeasure hn (x ω); infer_instance
    have := (Measure.isProbabilityMeasure_map_iff hgω.aemeasurable).2
      (inferInstance : IsProbabilityMeasure (Measure.pi fun _ : Fin n ↦ empiricalMeasure n (x ω)))
    rw [cdf_eq_real, Measure.real_def, Measure.map_apply hgω measurableSet_Iic]
    rfl
  simp_rw [hrw]
  exact ENNReal.measurable_toReal.comp
    (Kernel.measurable_kernel_prodMk_left (measurableSet_le hg measurable_const))

/-- If the Cesàro averages of `a` converge, then `aₙ / n → 0`. -/
private theorem tendsto_div_of_tendsto_avg (a : ℕ → ℝ) (L : ℝ)
    (h : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, a i) atTop (𝓝 L)) :
    Tendsto (fun n : ℕ ↦ a n / n) atTop (𝓝 0) := by
  have h1 := h.comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun n : ℕ ↦ (1 + 1 / (n : ℝ)) *
      (((n + 1 : ℕ) : ℝ)⁻¹ * ∑ i ∈ Finset.range (n + 1), a i) -
        (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, a i) atTop (𝓝 ((1 + 0) * L - L)) :=
    ((tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat).mul h1).sub h
  rw [add_zero, one_mul, sub_self] at h2
  refine h2.congr' ((eventually_gt_atTop 0).mono fun n hn ↦ ?_)
  have hn' : (n : ℝ) ≠ 0 := by positivity
  rw [Finset.sum_range_succ]
  push_cast
  field_simp
  ring

/-- Strong law of large numbers for a measurable integrable statistic of an i.i.d. sequence. -/
private theorem ae_tendsto_avg_of_iid {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {P : Measure ℝ} {X : ℕ → Ω → ℝ}
    (hiid : IsIndependentIdenticallyDistributed μ X P) (s : ℝ → ℝ) (hs : Measurable s)
    (hint : Integrable s P) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, s (X i ω)) atTop
      (𝓝 (∫ x, s x ∂P)) := by
  have hm := hiid.1
  have hlaw := hiid.2.2 0
  have hint0 : Integrable (s ∘ X 0) μ := by
    rw [← hlaw] at hint
    exact hint.comp_measurable (hm 0)
  have hslln := strong_law_ae (fun i ↦ s ∘ X i) hint0 (hiid.pairwise_indepFun_comp hs)
    (hiid.identDistrib_comp hs)
  have hmean : μ[s ∘ X 0] = ∫ x, s x ∂P := by
    rw [← hlaw, integral_map (hm 0).aemeasurable hs.aestronglyMeasurable]; rfl
  rw [hmean] at hslln
  filter_upwards [hslln] with ω hω
  simpa [smul_eq_mul] using hω

/-- GAPS 102.51: bootstrap consistency for the mean. For an i.i.d. sequence with finite positive
variance `σ²`, the Kolmogorov distance between the bootstrap law of `√n (X̄*ₙ - X̄ₙ)` (resampling
from the empirical measure) and `N(0, σ²)` tends to zero in probability. -/
theorem tendstoInMeasure_bootstrap_mean_kolmogorovDistance {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure ℝ) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hiid : IsIndependentIdenticallyDistributed μ X P) (h2 : MemLp id 2 P)
    (hv : 0 < Var[id; P]) :
    TendstoInMeasure μ (fun (n : ℕ) ω ↦ kolmogorovDistance
      ((Measure.pi fun _ : Fin n ↦ empiricalMeasure n (fun i ↦ X i.val ω)).map
        (fun y : Fin n → ℝ ↦ Real.sqrt n * ((∑ i, y i) / n - sampleAverage X n ω)))
      (gaussianReal 0 (Real.toNNReal (Var[id; P])))) atTop (fun _ ↦ 0) := by
  have hX := hiid.1
  have hA := ae_tendsto_avg_of_iid hiid id measurable_id (h2.integrable one_le_two)
  have hB := ae_tendsto_avg_of_iid hiid (fun x ↦ x ^ 2) (measurable_id.pow_const 2)
    (by simpa using h2.integrable_sq)
  have hvar : Var[id; P] + (∫ x, id x ∂P) ^ 2 = ∫ x, x ^ 2 ∂P := by
    rw [variance_eq_sub h2]; simp
  have hshift : TendstoInMeasure μ (fun (n : ℕ) ω ↦ kolmogorovDistance
      ((Measure.pi fun _ : Fin (n + 1) ↦ empiricalMeasure (n + 1) (fun i ↦ X i.val ω)).map
        (fun y : Fin (n + 1) → ℝ ↦ Real.sqrt (n + 1 : ℕ) *
          ((∑ i, y i) / (n + 1 : ℕ) - sampleAverage X (n + 1) ω)))
      (gaussianReal 0 (Real.toNNReal (Var[id; P])))) atTop (fun _ ↦ 0) := by
    refine tendstoInMeasure_of_tendsto_ae (fun n ↦ ?_) ?_
    · refine (measurable_kolmogorovDistance_bootstrap (n := n + 1) n.succ_pos
        (fun ω i ↦ X i.val ω) ?_ (sampleAverage X (n + 1)) ?_ _).aestronglyMeasurable
      · exact Measurable.of_eval fun i : Fin (n + 1) ↦ hX i.val
      · exact (Finset.measurable_sum (Finset.range (n + 1)) fun i _ ↦ hX i).const_mul _
    · filter_upwards [hA, hB] with ω hωA hωB
      have hx := tendsto_div_of_tendsto_avg (fun i ↦ X i ω ^ 2) _ hωB
      rw [← hvar] at hωB
      have := tendsto_kolmogorovDistance_bootstrapLaw (fun i ↦ X i ω) _ _ hv hωA hωB hx
      exact this.comp (tendsto_add_atTop_nat 1)
  exact fun ε hε ↦ (tendsto_add_atTop_iff_nat 1).1 (hshift ε hε)


end CKSD
