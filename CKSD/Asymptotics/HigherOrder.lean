module

public import CKSD.Asymptotics.Basic
public import TauCeti.Probability.Distributions.ChiSquared.Basic
public import TauCeti.Probability.Distributions.StudentT.Basic
public import TauCeti.Probability.Distributions.FisherSnedecor.Basic
import TauCeti.Probability.Distributions.Gaussian.Basic
import TauCeti.Probability.Distributions.Gaussian.Moments

/-!
# Asymptotics: HigherOrder

Sources: `GAPS.md`, `SYNOPSIS102.md`, and `STRUCTURE102.md`.
Declarations adapted from this project's section drafts.
The Huber computation uses TauCeti's `hasDerivAt_gaussianPDFReal`,
`integrable_gaussianReal_iff_integrable_gaussianPDFReal_smul`, and `integral_sq_gaussianReal`.
The docstrings specify the scope of each result; `sorry` marks unfinished proofs.
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
    integral_mul_max_sub_gaussianReal, TauCeti.Probability.integral_sq_gaussianReal, CKSD.cdf,
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

/-- GAPS 102.44, Hampel optimality part of the Huber statement. -/
theorem integral_huberScore_sq_le (k : ℝ) (hk : 0 < k) :
    let G := gaussianReal 0 1;
    let a := 2 * cdf G k - 1;
    ∀ (φ : ℝ → ℝ),
    ∀ (hm : Measurable φ),
    ∀ (hbound : ∀ x, |φ x| ≤ k / a),
    ∀ (h1 : (∫ x, x * φ x ∂G) = 1),
    (∫ x, (huberScore k x / a) ^ 2 ∂G) ≤ ∫ x, φ x ^ 2 ∂G := by
  intro G a φ hm hbound h1
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


/-- GAPS 102.49: uniform one-term Edgeworth expansion under the stated nonlattice condition. -/
theorem uniform_edgeworth_expansion {Ω : Type*} [MeasurableSpace Ω]
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

/-- GAPS 102.51: conditional bootstrap consistency of the mean, for positive variance. -/
theorem tendstoInProbabilityConst_bootstrap_mean_kolmogorovDistance {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure ℝ) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hiid : IsIndependentIdenticallyDistributed μ X P) (h2 : MemLp id 2 P)
    (hv : 0 < variance P id) :
    TendstoInProbabilityConst μ (fun n ω ↦ kolmogorovDistance
      ((Measure.pi fun _ : Fin n ↦ empiricalMeasure n (fun i ↦ X i.val ω)).map
        (fun y : Fin n → ℝ ↦ Real.sqrt n * ((∑ i, y i) / n - sampleAverage X n ω)))
      (gaussianReal 0 (Real.toNNReal (variance P id)))) 0 := by
  sorry


end CKSD
