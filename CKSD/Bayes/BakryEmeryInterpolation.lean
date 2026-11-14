module

public import CKSD.Bayes.LangevinSampling
public import TauCeti.MeasureTheory.Integral.PrekopaLeindler
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Convex.Deriv
/-!
# Prékopa–Leindler proof of the Bakry–Émery entropy estimate

Strong monotonicity of a potential's gradient gives tangent paraboloids and strong-convexity
interpolation. Combining this with a quadratic upper Taylor bound for a bounded logarithmic
perturbation gives a Prékopa–Leindler estimate. Differentiating at weight zero yields the sharp
entropy-energy constant `1 / (2 * m)`.

The Prékopa–Leindler inequality is imported from TauCeti. Mathlib supplies dominated
parametric differentiation, scalar calculus and integration.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators ContDiff
namespace CKSD

/-- A strongly monotone gradient gives a lower tangent paraboloid at every base point. -/
theorem potential_add_inner_add_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (V : E → ℝ) (G : E → E) (m : ℝ) (hG : ∀ x, HasGradientAt V (G x) x)
    (hm : ∀ x y, m * ‖x - y‖ ^ 2 ≤ inner ℝ (G x - G y) (x - y)) (x y : E) :
    V x + inner ℝ (G x) (y - x) + m / 2 * ‖y - x‖ ^ 2 ≤ V y := by
  let v := y - x
  let φ : ℝ → ℝ := fun t ↦ V (x + t • v) - V x - t * inner ℝ (G x) v - m / 2 * t ^ 2 * ‖v‖ ^ 2
  have hd (t : ℝ) : HasDerivAt φ
      (inner ℝ (G (x + t • v)) v - inner ℝ (G x) v - m * t * ‖v‖ ^ 2) t := by
    have h1 : HasDerivAt (fun s : ℝ ↦ V (x + s • v)) (inner ℝ (G (x + t • v)) v) t := by
      have := (hG (x + t • v)).hasFDerivAt.comp_hasDerivAt t
        (((hasDerivAt_id t).smul_const v).const_add x)
      simpa only [Function.comp_def, id_eq, one_smul, InnerProductSpace.toDual_apply_apply] using! this
    have h2 := ((h1.sub_const (V x)).sub ((hasDerivAt_id t).mul_const (inner ℝ (G x) v))).sub
      (((hasDerivAt_pow 2 t).const_mul (m / 2)).mul_const (‖v‖ ^ 2))
    refine (h2.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun s ↦ rfl)
    simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, one_mul]
    ring
  have hmono : MonotoneOn φ (Ici 0) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (fun t _ ↦ (hd t).continuousAt.continuousWithinAt) (fun t _ ↦ (hd t).hasDerivWithinAt) ?_
    intro t ht
    rw [interior_Ici, mem_Ioi] at ht
    have h := hm (x + t • v) x
    rw [add_sub_cancel_left, real_inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos ht,
      mul_pow, inner_sub_left] at h
    have hi : m * t * ‖v‖ ^ 2 ≤ inner ℝ (G (x + t • v)) v - inner ℝ (G x) v := by
      refine le_of_mul_le_mul_left ?_ ht
      nlinarith [h]
    linarith
  have h01 := hmono (mem_Ici.2 le_rfl) (mem_Ici.2 zero_le_one) zero_le_one
  dsimp only [φ, v] at h01
  simp only [zero_smul, add_zero, zero_mul, one_smul, one_mul, sub_self, one_pow,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_sub_cancel] at h01
  linarith

/-- Tangent paraboloids imply the strong convexity interpolation inequality. -/
theorem potential_interpolation_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (V : E → ℝ) (G : E → E) (m : ℝ) (hG : ∀ x, HasGradientAt V (G x) x)
    (hm : ∀ x y, m * ‖x - y‖ ^ 2 ≤ inner ℝ (G x - G y) (x - y))
    (x y : E) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    V ((1 - t) • x + t • y) ≤ (1 - t) * V x + t * V y - m / 2 * t * (1 - t) * ‖x - y‖ ^ 2 := by
  let z := (1 - t) • x + t • y
  have hx := potential_add_inner_add_le V G m hG hm z x
  have hy := potential_add_inner_add_le V G m hG hm z y
  have hxz : x - z = t • (x - y) := by dsimp [z]; module
  have hyz : y - z = (1 - t) • (y - x) := by dsimp [z]; module
  rw [hxz, real_inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0, mul_pow] at hx
  rw [hyz, real_inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 ht1),
    mul_pow, norm_sub_rev, inner_sub_right] at hy
  rw [inner_sub_right] at hx
  have := add_le_add (mul_le_mul_of_nonneg_left hx (sub_nonneg.2 ht1))
    (mul_le_mul_of_nonneg_left hy ht0)
  nlinarith

/-- A scalar Young inequality with an arbitrary positive quadratic coefficient. -/
theorem two_mul_le_mul_sq_add_div (p q c : ℝ) (hc : 0 < c) :
    2 * p * q ≤ c * q ^ 2 + p ^ 2 / c := by
  apply (mul_le_mul_iff_right₀ hc).1
  rw [mul_add, mul_comm c (p ^ 2 / c), div_mul_cancel₀ _ hc.ne']
  nlinarith [sq_nonneg (c * q - p)]

/-- The pointwise exponential comparison used in the Prékopa–Leindler proof of LSI. -/
theorem exponential_interpolation_exponent_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (V : E → ℝ) (G : E → E) (m : ℝ) (hG : ∀ x, HasGradientAt V (G x) x)
    (hm : ∀ x y, m * ‖x - y‖ ^ 2 ≤ inner ℝ (G x - G y) (x - y))
    (g : E → ℝ) (Dg : E → E →L[ℝ] ℝ) (H : ℝ)
    (hg : ∀ x z, g x ≤ g z + Dg z (x - z) + H / 2 * ‖x - z‖ ^ 2)
    (x y : E) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hc : 0 < m - t * H) :
    let z := (1 - t) • x + t • y;
    (1 - t) * (g x - V x) + t * (-V y) ≤
      (1 - t) * g z + (t * (1 - t) / (2 * (m - t * H))) * ‖Dg z‖ ^ 2 - V z := by
  intro z
  have hz := potential_interpolation_le V G m hG hm x y ht0 ht1
  change V z ≤ _ at hz
  have hxz : x - z = t • (x - y) := by dsimp [z]; module
  have htg := hg x z
  rw [hxz, map_smul, smul_eq_mul, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0, mul_pow] at htg
  have hd : Dg z (x - y) ≤ ‖Dg z‖ * ‖x - y‖ :=
    (le_abs_self _).trans ((Dg z).le_opNorm _)
  have htg' : g x ≤ g z + t * (‖Dg z‖ * ‖x - y‖) + H / 2 * (t ^ 2 * ‖x - y‖ ^ 2) := by
    have := mul_le_mul_of_nonneg_left hd ht0
    linarith
  have hy := two_mul_le_mul_sq_add_div ‖Dg z‖ ‖x - y‖ (m - t * H) hc
  have hy' := mul_le_mul_of_nonneg_left hy (mul_nonneg ht0 (sub_nonneg.2 ht1))
  have hg' := mul_le_mul_of_nonneg_left htg' (sub_nonneg.2 ht1)
  have hratio : t * (1 - t) / (2 * (m - t * H)) * ‖Dg z‖ ^ 2 =
      t * (1 - t) * (‖Dg z‖ ^ 2 / (m - t * H)) / 2 := by field_simp
  rw [hratio]
  nlinarith

/-- The Prékopa–Leindler interpolation estimate for a smooth log-density perturbation. -/
theorem integral_exponential_interpolation_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (V : E → ℝ) (G : E → E) (m : ℝ) (hG : ∀ x, HasGradientAt V (G x) x)
    (hm : ∀ x y, m * ‖x - y‖ ^ 2 ≤ inner ℝ (G x - G y) (x - y))
    (g : E → ℝ) (Dg : E → E →L[ℝ] ℝ) (H : ℝ)
    (hg : ∀ x z, g x ≤ g z + Dg z (x - z) + H / 2 * ‖x - z‖ ^ 2)
    (hgm : Measurable g) (hDgm : Measurable fun x ↦ ‖Dg x‖)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hc : 0 < m - t * H)
    (hI : Integrable (fun x ↦ Real.exp (g x - V x)))
    (hZ : Integrable (fun x ↦ Real.exp (-V x)))
    (hJ : Integrable (fun x ↦ Real.exp ((1 - t) * g x +
      (t * (1 - t) / (2 * (m - t * H))) * ‖Dg x‖ ^ 2 - V x))) :
    (∫ x, Real.exp (g x - V x)) ^ (1 - t) * (∫ x, Real.exp (-V x)) ^ t ≤
      ∫ x, Real.exp ((1 - t) * g x +
        (t * (1 - t) / (2 * (m - t * H))) * ‖Dg x‖ ^ 2 - V x) := by
  have hVm : Measurable V :=
    (continuous_iff_continuousAt.2 fun x ↦ (hG x).hasFDerivAt.continuousAt).measurable
  have hPL := TauCeti.hasPrekopaLeindler_volume E ht0 ht1
  have hpoint (x y : E) :
      ENNReal.ofReal (Real.exp (g x - V x)) ^ (1 - t) *
        ENNReal.ofReal (Real.exp (-V y)) ^ t ≤
      ENNReal.ofReal (Real.exp ((1 - t) * g ((1 - t) • x + t • y) +
        (t * (1 - t) / (2 * (m - t * H))) * ‖Dg ((1 - t) • x + t • y)‖ ^ 2 -
          V ((1 - t) • x + t • y))) := by
    rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ENNReal.ofReal_rpow_of_pos (Real.exp_pos _),
      Real.rpow_def_of_pos (Real.exp_pos _), Real.rpow_def_of_pos (Real.exp_pos _),
      Real.log_exp, Real.log_exp, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.2
    simpa only [mul_comm] using exponential_interpolation_exponent_le V G m hG hm g Dg H hg x y ht0 ht1 hc
  rw [Measure.hasPrekopaLeindler_def] at hPL
  have h := hPL ((hgm.sub hVm).exp.ennreal_ofReal) (hVm.neg.exp.ennreal_ofReal)
    (show Measurable (fun x : E ↦ ENNReal.ofReal (Real.exp ((1 - t) * g x +
      (t * (1 - t) / (2 * (m - t * H))) * ‖Dg x‖ ^ 2 - V x))) from
        (((hgm.const_mul _).add ((hDgm.pow_const (2 : ℕ)).const_mul _)).sub hVm).exp.ennreal_ofReal) hpoint
  simp only [Pi.sub_apply, Pi.neg_apply, ENNReal.rpow_eq_pow] at h
  rw [← ofReal_integral_eq_lintegral_ofReal hI (ae_of_all _ fun x ↦ (Real.exp_pos _).le),
    ← ofReal_integral_eq_lintegral_ofReal hZ (ae_of_all _ fun x ↦ (Real.exp_pos _).le),
    ← ofReal_integral_eq_lintegral_ofReal hJ (ae_of_all _ fun x ↦ (Real.exp_pos _).le),
    ENNReal.ofReal_rpow_of_pos (integral_exp_pos hI),
    ENNReal.ofReal_rpow_of_pos (integral_exp_pos hZ),
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (integral_exp_pos hI).le _)] at h
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h

/-- Differentiate a bounded exponential perturbation under a finite-density integral. -/
theorem has_deriv_at_integral_exponential_perturbation {E : Type*} [MeasurableSpace E]
    (μ : Measure E) (V g h : E → ℝ) (hV : Measurable V) (hg : Measurable g) (hh : Measurable h)
    {M : ℝ} (_hM : 0 ≤ M) (hgM : ∀ x, |g x| ≤ M) (hhM : ∀ x, |h x| ≤ M)
    (hint : Integrable (fun x ↦ Real.exp (-V x)) μ)
    (c c' : ℝ → ℝ) (hc0 : c 0 = 0) (hcc : ContinuousAt c 0) (hc'c : ContinuousAt c' 0)
    (hcd : ∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt c (c' t) t) :
    HasDerivAt (fun t ↦ ∫ x, Real.exp ((1 - t) * g x + c t * h x - V x) ∂μ)
      (∫ x, Real.exp (g x - V x) * (-g x + c' 0 * h x) ∂μ) 0 := by
  let B := |c' 0| + 1
  let s := {t : ℝ | |t| < 1 ∧ |c t| < 1 ∧ |c' t| < B ∧ HasDerivAt c (c' t) t}
  have hs : s ∈ 𝓝 (0 : ℝ) := by
    have h1 : ∀ᶠ t in 𝓝 (0 : ℝ), |t| < 1 :=
      (continuousAt_id.abs).eventually (gt_mem_nhds (by norm_num))
    have h2 : ∀ᶠ t in 𝓝 (0 : ℝ), |c t| < 1 := hcc.abs.eventually (gt_mem_nhds (by change |c 0| < 1; rw [hc0]; norm_num))
    have h3 : ∀ᶠ t in 𝓝 (0 : ℝ), |c' t| < B := hc'c.abs.eventually (gt_mem_nhds (by dsimp [B]; linarith))
    exact h1.and (h2.and (h3.and hcd))
  let F := fun t x ↦ Real.exp ((1 - t) * g x + c t * h x - V x)
  let F' := fun t x ↦ Real.exp ((1 - t) * g x + c t * h x - V x) * (-g x + c' t * h x)
  have hF0 : Integrable (F 0) μ := by
    refine (hint.const_mul (Real.exp M)).mono' (by dsimp [F]; fun_prop) (ae_of_all _ fun x ↦ ?_)
    dsimp [F]
    rw [hc0, zero_mul, add_zero, sub_zero, one_mul, Real.abs_exp, ← Real.exp_add]
    apply Real.exp_le_exp.2
    linarith [(le_abs_self (g x)).trans (hgM x)]
  have hbound : ∀ᵐ x ∂μ, ∀ t ∈ s, ‖F' t x‖ ≤ Real.exp (3 * M) * Real.exp (-V x) * (M + B * M) := by
    refine ae_of_all _ fun x t ht ↦ ?_
    have ht1 : |1 - t| ≤ 2 := by
      have := abs_sub 1 t
      norm_num at this
      linarith [ht.1]
    have hE : (1 - t) * g x + c t * h x ≤ 3 * M := by
      have h1 := mul_le_mul ht1 (hgM x) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
      have h2 := mul_le_mul ht.2.1.le (hhM x) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
      rw [← abs_mul] at h1 h2
      nlinarith [le_abs_self ((1 - t) * g x), le_abs_self (c t * h x)]
    have hD : |-g x + c' t * h x| ≤ M + B * M := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_neg, abs_mul]
      exact add_le_add (hgM x) (mul_le_mul ht.2.2.1.le (hhM x) (abs_nonneg _) (by dsimp [B]; positivity))
    dsimp [F']
    rw [abs_mul, Real.abs_exp]
    apply mul_le_mul _ hD (abs_nonneg _) (by positivity)
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  have hdiff : ∀ᵐ x ∂μ, ∀ t ∈ s, HasDerivAt (fun t ↦ F t x) (F' t x) t := by
    refine ae_of_all _ fun x t ht ↦ ?_
    have hd := (((hasDerivAt_const t 1).sub (hasDerivAt_id t)).mul_const (g x)).add
      ((ht.2.2.2).mul_const (h x)) |>.sub_const (V x)
    dsimp [F, F']
    simpa only [Pi.sub_apply, Pi.add_apply, id_eq, sub_zero, zero_sub, neg_one_mul] using hd.exp
  obtain ⟨_, hder⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (F := F) (F' := F') hs
    (Eventually.of_forall fun t ↦ by dsimp [F]; fun_prop) hF0
    (show AEStronglyMeasurable (F' 0) μ by dsimp [F']; fun_prop)
    hbound ((hint.const_mul (Real.exp (3 * M))).mul_const (M + B * M)) hdiff
  simpa only [F', hc0, sub_zero, one_mul, zero_mul, add_zero] using hder

/-- Right-hand comparison of differentiable functions compares derivatives at a contact point. -/
theorem has_deriv_at_le_of_eventually_le_right {F J : ℝ → ℝ} {f j : ℝ}
    (hF : HasDerivAt F f 0) (hJ : HasDerivAt J j 0) (heq : F 0 = J 0)
    (hle : ∀ᶠ t in 𝓝[>] (0 : ℝ), F t ≤ J t) : f ≤ j := by
  apply le_of_tendsto_of_tendsto (hasDerivAt_iff_tendsto_slope_left_right.1 hF).2
    (hasDerivAt_iff_tendsto_slope_left_right.1 hJ).2
  filter_upwards [hle, self_mem_nhdsWithin] with t ht ht0
  simp only [mem_Ioi] at ht0
  simp only [slope_def_field, sub_zero]
  exact div_le_div_of_nonneg_right (by linarith) ht0.le

/-- Sharp entropy-energy inequality for bounded log-density perturbations with bounded derivative
and a global quadratic upper Taylor bound. -/
theorem entropy_exponential_le_of_quadratic_upper_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (V : E → ℝ) (G : E → E) (m : ℝ) (hm0 : 0 < m) (hG : ∀ x, HasGradientAt V (G x) x)
    (hm : ∀ x y, m * ‖x - y‖ ^ 2 ≤ inner ℝ (G x - G y) (x - y))
    (g : E → ℝ) (Dg : E → E →L[ℝ] ℝ) (H : ℝ)
    (hg : ∀ x z, g x ≤ g z + Dg z (x - z) + H / 2 * ‖x - z‖ ^ 2)
    (hgm : Measurable g) (hDgm : Measurable fun x ↦ ‖Dg x‖)
    {M : ℝ} (hM : 0 ≤ M) (hgM : ∀ x, |g x| ≤ M) (hDgM : ∀ x, ‖Dg x‖ ^ 2 ≤ M)
    (hZ : Integrable (fun x ↦ Real.exp (-V x))) :
    (∫ x, Real.exp (g x - V x) * g x) -
        (∫ x, Real.exp (g x - V x)) *
          (Real.log (∫ x, Real.exp (g x - V x)) - Real.log (∫ x, Real.exp (-V x))) ≤
      (1 / (2 * m)) * ∫ x, Real.exp (g x - V x) * ‖Dg x‖ ^ 2 := by
  have hVm : Measurable V :=
    (continuous_iff_continuousAt.2 fun x ↦ (hG x).hasFDerivAt.continuousAt).measurable
  have hI : Integrable (fun x ↦ Real.exp (g x - V x)) := by
    refine (hZ.const_mul (Real.exp M)).mono' ((hgm.sub hVm).exp.aestronglyMeasurable) (ae_of_all _ fun x ↦ ?_)
    rw [Real.norm_eq_abs, Real.abs_exp, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith [(le_abs_self (g x)).trans (hgM x)])
  let A := ∫ x, Real.exp (g x - V x)
  let Z := ∫ x, Real.exp (-V x)
  have hA : 0 < A := integral_exp_pos hI
  have hZ0 : 0 < Z := integral_exp_pos hZ
  let c : ℝ → ℝ := fun t ↦ t * (1 - t) / (2 * (m - t * H))
  let c' : ℝ → ℝ := fun t ↦ ((1 - 2 * t) * (2 * (m - t * H)) + t * (1 - t) * (2 * H)) /
    (2 * (m - t * H)) ^ 2
  have hc0 : c 0 = 0 := by simp [c]
  have hcd (t : ℝ) (ht : m - t * H ≠ 0) : HasDerivAt c (c' t) t := by
    have h1 : HasDerivAt (fun t : ℝ ↦ t * (1 - t)) (1 - 2 * t) t := by
      have hd := (hasDerivAt_id t).mul ((hasDerivAt_const t 1).sub (hasDerivAt_id t))
      change HasDerivAt (fun s : ℝ ↦ s * (1 - s)) (1 * (1 - t) + t * (0 - 1)) t at hd
      exact hd.congr_deriv (by ring)
    have h2 : HasDerivAt (fun t : ℝ ↦ 2 * (m - t * H)) (-2 * H) t := by
      have hd := (((hasDerivAt_const t m).sub ((hasDerivAt_id t).mul_const H)).const_mul 2)
      change HasDerivAt (fun s : ℝ ↦ 2 * (m - s * H)) (2 * (0 - 1 * H)) t at hd
      exact hd.congr_deriv (by ring)
    have hd := h1.div h2 (mul_ne_zero (by norm_num) ht)
    change HasDerivAt c (((1 - 2 * t) * (2 * (m - t * H)) - t * (1 - t) * (-2 * H)) /
      (2 * (m - t * H)) ^ 2) t at hd
    exact hd.congr_deriv (by dsimp [c']; ring)
  have hcc : ContinuousAt c 0 := (hcd 0 (by simpa using hm0.ne')).continuousAt
  have hc'c : ContinuousAt c' 0 := by
    dsimp [c']
    fun_prop (disch := simp [hm0.ne'])
  have hpos : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < m - t * H :=
    (continuous_const.sub (continuous_id.mul_const H)).continuousAt.eventually (lt_mem_nhds (by change (0 : ℝ) < m - 0 * H; simpa using hm0))
  have hct : ∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt c (c' t) t := hpos.mono fun t ht ↦ hcd t ht.ne'
  have hc'0 : c' 0 = 1 / (2 * m) := by dsimp [c']; field_simp [hm0.ne']; ring
  let F : ℝ → ℝ := fun t ↦ Real.exp ((1 - t) * Real.log A + t * Real.log Z)
  let J : ℝ → ℝ := fun t ↦ ∫ x, Real.exp ((1 - t) * g x + c t * ‖Dg x‖ ^ 2 - V x)
  have hderJ := has_deriv_at_integral_exponential_perturbation volume V g (fun x ↦ ‖Dg x‖ ^ 2)
    hVm hgm (hDgm.pow_const (2 : ℕ)) hM hgM (fun x ↦ by rw [abs_of_nonneg (sq_nonneg _)]; exact hDgM x)
    hZ c c' hc0 hcc hc'c hct
  rw [hc'0] at hderJ
  have hderF : HasDerivAt F (A * (-Real.log A + Real.log Z)) 0 := by
    have hd := (((hasDerivAt_const 0 1).sub (hasDerivAt_id 0)).mul_const (Real.log A)).add
      ((hasDerivAt_id 0).mul_const (Real.log Z))
    convert hd.exp using 1 <;> simp only [Pi.sub_apply, Pi.add_apply, id_eq, sub_zero, one_mul,
      zero_mul, add_zero, zero_sub, neg_one_mul, Real.exp_log hA]; ring
  have heq : F 0 = J 0 := by simp [F, J, hc0, Real.exp_log hA, A]
  have hle : ∀ᶠ t in 𝓝[>] (0 : ℝ), F t ≤ J t := by
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one, hpos.filter_mono nhdsWithin_le_nhds] with t ht htm
    have hJ : Integrable (fun x ↦ Real.exp ((1 - t) * g x + c t * ‖Dg x‖ ^ 2 - V x)) := by
      refine (hZ.const_mul (Real.exp ((|1 - t| + |c t|) * M))).mono'
        (by dsimp [c]; fun_prop) (ae_of_all _ fun x ↦ ?_)
      rw [Real.norm_eq_abs, Real.abs_exp, ← Real.exp_add]
      apply Real.exp_le_exp.2
      have h1 := mul_le_mul_of_nonneg_left (hgM x) (abs_nonneg (1 - t))
      have h2 := mul_le_mul_of_nonneg_left (hDgM x) (abs_nonneg (c t))
      have h3 := (le_abs_self ((1 - t) * g x)).trans (by simpa only [abs_mul] using h1)
      have h4 := mul_le_mul_of_nonneg_right (le_abs_self (c t)) (sq_nonneg ‖Dg x‖)
      nlinarith
    have h := integral_exponential_interpolation_le V G m hG hm g Dg H hg hgm hDgm
      ht.1.le ht.2.le htm hI hZ hJ
    simpa only [F, J, A, Z, c, Real.rpow_def_of_pos hA, Real.rpow_def_of_pos hZ0,
      ← Real.exp_add, mul_comm] using h
  have hder := has_deriv_at_le_of_eventually_le_right hderF hderJ heq hle
  have hgg : Integrable (fun x ↦ Real.exp (g x - V x) * g x) :=
    hI.mul_bdd hgm.aestronglyMeasurable (ae_of_all _ fun x ↦ by simpa only [Real.norm_eq_abs] using hgM x)
  have hgd : Integrable (fun x ↦ Real.exp (g x - V x) * ‖Dg x‖ ^ 2) :=
    hI.mul_bdd (hDgm.pow_const (2 : ℕ)).aestronglyMeasurable
      (ae_of_all _ fun x ↦ by rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hDgM x)
  have he : (∫ x, Real.exp (g x - V x) * (-g x + (1 / (2 * m)) * ‖Dg x‖ ^ 2)) =
      -(∫ x, Real.exp (g x - V x) * g x) + (1 / (2 * m)) * ∫ x, Real.exp (g x - V x) * ‖Dg x‖ ^ 2 := by
    simp_rw [mul_add, mul_neg, ← mul_assoc, mul_comm _ (1 / (2 * m)), mul_assoc]
    have hneg : Integrable (fun x ↦ -(Real.exp (g x - V x) * g x)) := hgg.neg
    have hmul : Integrable (fun x ↦ (1 / (2 * m)) * (Real.exp (g x - V x) * ‖Dg x‖ ^ 2)) :=
      hgd.const_mul _
    rw [integral_add hneg hmul, integral_neg, integral_const_mul]
  rw [he] at hder
  change A * (-Real.log A + Real.log Z) ≤ _ at hder
  change _ - A * (Real.log A - Real.log Z) ≤ _
  nlinarith

end CKSD
