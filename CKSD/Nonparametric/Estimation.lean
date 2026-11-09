module

public import CKSD.Nonparametric.Basic
public import CKSD.Inference.Density
public import CKSD.Asymptotics.Lindeberg.Basic
public import TauCeti.Analysis.Calculus.Taylor

/-!
# Empirical distribution functions, kernel density estimation, and rank statistics

Classical one-dimensional nonparametric estimation: the Dvoretzky–Kiefer–Wolfowitz–Massart
inequality, the pointwise central limit theorem and the universal `L¹` consistency of kernel
density estimators, the representer theorem for penalized empirical risk over a Hilbert space,
and the exact moments of linear rank statistics under uniformly distributed ranks.

## Main definitions

* `CKSD.uniformPermMeasure n`: the uniform probability measure on the permutations of `Fin n`.
* `CKSD.linearRankStatistic a c σ`: the linear rank statistic `∑ᵢ cᵢ a(σ i)`.

## Main results

* `CKSD.measure_kolmogorovSmirnovStatistic_gt_le`: `P(√n ‖F_n - F‖_∞ > t) ≤ 2 exp(-2t²)`.
* `CKSD.tendstoInDistribution_kernelDensityEstimator`: the bias-corrected central limit
  theorem for the kernel density estimator at a point.
* `CKSD.ae_tendsto_integral_abs_kernelDensityEstimator_sub`: `∫ |f̂_n - f| → 0` almost surely.
* `CKSD.minimizer_mem_span_of_feature_vectors`: the representer theorem.
* `CKSD.integral_linearRankStatistic`, `CKSD.variance_linearRankStatistic`: the mean
  `N c̄ ā` and the variance `(N - 1)⁻¹ ∑ (cᵢ - c̄)² ∑ (a(i) - ā)²` of a linear rank statistic.

The kernel density central limit theorem applies the Lindeberg–Feller theorem
`CKSD.tendstoInDistribution_sum_of_lindeberg_of_iIndepFun` to the centred kernel evaluations;
the variance and bias are computed by the change of variables `x = t - h u`, Mathlib's dominated
convergence theorem and Taylor expansions (Mathlib's `taylor_isLittleO_univ`, TauCeti's
`TauCeti.abs_sub_taylorWithinEval_le`), and Slutsky's lemma
`CKSD.tendstoInDistribution_of_tendstoInMeasure_sub_of_measurable` removes the deterministic
bias term.

Sources: GAPS 103.1, 103.4, 103.5, 103.8, and 103.14.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

open scoped CKSD

attribute [local instance] Classical.propDecidable

-- Use the common rank measurable structure.
attribute [local instance] rankMeasurableSpace

/-- GAPS 103.1: the Dvoretzky–Kiefer–Wolfowitz inequality with Massart's constant. For i.i.d.
real observations and every `t > 0`, `P(√n sup_x |F_n(x) - F(x)| > t) ≤ 2 exp(-2 t²)`. -/
theorem measure_kolmogorovSmirnovStatistic_gt_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure ℝ) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hiid : IsIndependentIdenticallyDistributed μ X P) (n : ℕ) (hn : 0 < n)
    (t : ℝ) (ht : 0 < t) :
    μ.real {ω | t < Real.sqrt n * kolmogorovSmirnovStatistic X P n ω} ≤ 2 * Real.exp
      (-2 * t ^ 2) := by
  sorry

/-- First-order Taylor bound: if `|f''| ≤ C`, then `|f (t + s) - f t - s f'(t)| ≤ C s² / 2`. -/
private theorem abs_sub_sub_mul_deriv_le {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {C : ℝ}
    (hC : ∀ x, |deriv (deriv f) x| ≤ C) (t s : ℝ) :
    |f (t + s) - f t - s * deriv f t| ≤ C * s ^ 2 / 2 := by
  have h := TauCeti.abs_sub_taylorWithinEval_le (n := 1) (f := f) (hf.of_le (by norm_num))
    (M := C) (fun x ↦ by simpa [iteratedDeriv_succ] using hC x) t (t + s)
  have htay : taylorWithinEval f 1 univ t (t + s) = f t + s * deriv f t := by
    simp [taylor_within_apply, iteratedDerivWithin_univ, iteratedDeriv_succ]
  rw [htay, add_sub_cancel_left, sq_abs] at h
  rw [sub_sub]; simpa using h

/-- Second-order Taylor expansion at `t` with a little-o remainder. -/
private theorem isLittleO_sub_taylor_two {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (t : ℝ) :
    (fun s ↦ f (t + s) - f t - s * deriv f t - s ^ 2 / 2 * deriv (deriv f) t) =o[𝓝 0]
      fun s ↦ s ^ 2 := by
  have h := (taylor_isLittleO_univ (x₀ := t) hf).comp_tendsto
    (by simpa using (continuous_const_add t).tendsto 0 : Tendsto (fun s : ℝ ↦ t + s) (𝓝 0) (𝓝 t))
  refine h.congr (fun s ↦ ?_) (fun s ↦ by simp)
  have htay : taylorWithinEval f 2 univ t (t + s) =
      f t + s * deriv f t + s ^ 2 / 2 * deriv (deriv f) t := by
    simp [taylor_within_apply, iteratedDerivWithin_univ, iteratedDeriv_succ]
    left; ring
  simp only [Function.comp_apply, htay]; ring

/-- Change of variables `x = t - h u`: `∫ F((t - x) / h) f(x) dx = h ∫ F(u) f(t - h u) du`. -/
private theorem integral_comp_div_mul_eq (F f : ℝ → ℝ) (t : ℝ) {h : ℝ} (hh : 0 < h) :
    ∫ x, F ((t - x) / h) * f x = h * ∫ u, F u * f (t - h * u) := by
  have h1 : ∫ u, F u * f (t - h * u) = ∫ u, (fun y ↦ F (y / h) * f (t - y)) (h * u) := by
    congr 1; ext u; simp only; rw [mul_div_cancel_left₀ _ hh.ne']
  have h2 := integral_sub_left_eq_self (μ := volume) (fun x ↦ F ((t - x) / h) * f x) t
  simp only [sub_sub_cancel] at h2
  rw [h1, Measure.integral_comp_mul_left (fun y ↦ F (y / h) * f (t - y)) h, abs_inv,
    abs_of_pos hh, smul_eq_mul, h2]
  field_simp

/-- Dominated convergence for kernel smoothing at a point: if `|G| ≤ c K` with `K`, `|u| K` and
`u² K` integrable and `f` is `C²` with bounded `f''`, then `∫ G(u) f(t - h u) du → f(t) ∫ G`
as `h → 0⁺`. -/
private theorem tendsto_integral_mul_comp_sub_mul {f K G : ℝ → ℝ} (hfm : Measurable f)
    (hf : ContDiff ℝ 2 f) {C : ℝ} (hC : ∀ x, |deriv (deriv f) x| ≤ C)
    (hKi : Integrable K) (hK1 : Integrable fun u ↦ |u| * K u)
    (hK2 : Integrable fun u ↦ u ^ 2 * K u) (hGm : Measurable G) {c : ℝ}
    (hG : ∀ u, |G u| ≤ c * K u) {h : ℕ → ℝ} (hh : ∀ n, 0 < h n)
    (hh0 : Tendsto h atTop (𝓝 0)) (t : ℝ) :
    Tendsto (fun n ↦ ∫ u, G u * f (t - h n * u)) atTop (𝓝 ((∫ u, G u) * f t)) := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  rw [← integral_mul_const]
  set D1 := deriv f t
  let bound : ℝ → ℝ := fun u ↦ c * |f t| * K u + c * |D1| * (|u| * K u) +
    c * C / 2 * (u ^ 2 * K u)
  refine tendsto_integral_filter_of_dominated_convergence bound ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun n ↦
      (hGm.mul (hfm.comp (by fun_prop))).aestronglyMeasurable
  · filter_upwards [hh0.eventually (eventually_le_nhds one_pos)] with n hn
    refine ae_of_all _ fun u ↦ ?_
    have hT := abs_sub_sub_mul_deriv_le hf hC t (-(h n * u))
    rw [← sub_eq_add_neg] at hT
    have hu1 : |h n * u| ≤ |u| := by
      rw [abs_mul, abs_of_pos (hh n)]; exact mul_le_of_le_one_left (abs_nonneg _) hn
    have hf' : |f (t - h n * u)| ≤ |f t| + |u| * |D1| + C * u ^ 2 / 2 := by
      have h1 : |-(h n * u) * D1| ≤ |u| * |D1| := by
        rw [abs_mul, abs_neg]; exact mul_le_mul_of_nonneg_right hu1 (abs_nonneg _)
      have h2 : C * (-(h n * u)) ^ 2 / 2 ≤ C * u ^ 2 / 2 := by
        rw [neg_sq, ← sq_abs, ← sq_abs u]
        gcongr
      have := abs_sub_abs_le_abs_sub (f (t - h n * u)) (f t + -(h n * u) * D1)
      have h3 : |f t + -(h n * u) * D1| ≤ |f t| + |-(h n * u) * D1| := abs_add_le _ _
      rw [show f (t - h n * u) - (f t + -(h n * u) * D1) =
        f (t - h n * u) - f t - -(h n * u) * D1 by ring] at this
      linarith
    rw [Real.norm_eq_abs, abs_mul]
    calc |G u| * |f (t - h n * u)| ≤ (c * K u) * (|f t| + |u| * |D1| + C * u ^ 2 / 2) :=
          mul_le_mul (hG u) hf' (abs_nonneg _) ((abs_nonneg _).trans (hG u))
      _ = bound u := by simp only [bound]; ring
  · exact ((hKi.const_mul _).add (hK1.const_mul _)).add (hK2.const_mul _)
  · refine ae_of_all _ fun u ↦ ?_
    have : Tendsto (fun n ↦ t - h n * u) atTop (𝓝 t) := by
      simpa using tendsto_const_nhds.sub (hh0.mul_const u)
    exact ((hf.continuous.tendsto t).comp this).const_mul (G u)

/-- The first moment of an integrable symmetric kernel vanishes. -/
private theorem integral_mul_eq_zero_of_symm {K : ℝ → ℝ} (hKsym : ∀ x, K (-x) = K x) :
    ∫ u, u * K u = 0 := by
  have h := integral_neg_eq_self (μ := volume) (fun u ↦ u * K u)
  simp only [hKsym, neg_mul, integral_neg] at h
  linarith

/-- The bias of the kernel smoother is `o(h²)`: for a symmetric kernel `K ≥ 0` with
`∫ K = 1` and `∫ u² K < ∞`, and a `C²` function `f` with bounded `f''`,
`(∫ K(u) f(t - h u) du - f(t) - h² μ₂(K) f''(t) / 2) / h² → 0` as `h → 0⁺`. -/
private theorem tendsto_bias_div_sq {f K : ℝ → ℝ} (hfm : Measurable f)
    (hf : ContDiff ℝ 2 f) {C : ℝ} (hC : ∀ x, |deriv (deriv f) x| ≤ C) (hKm : Measurable K)
    (hK0 : ∀ u, 0 ≤ K u) (hKi : Integrable K) (hK1 : Integrable fun u ↦ |u| * K u)
    (hK2 : Integrable fun u ↦ u ^ 2 * K u) (hKsym : ∀ x, K (-x) = K x) (hK1' : ∫ u, K u = 1)
    {h : ℕ → ℝ} (hh : ∀ n, 0 < h n) (hh0 : Tendsto h atTop (𝓝 0)) (t : ℝ) :
    Tendsto (fun n ↦ ((∫ u, K u * f (t - h n * u)) - f t -
      h n ^ 2 / 2 * (∫ u, u ^ 2 * K u) * deriv (deriv f) t) / h n ^ 2) atTop (𝓝 0) := by
  set D1 := deriv f t
  set D2 := deriv (deriv f) t
  set R : ℝ → ℝ := fun s ↦ f (t + s) - f t - s * D1 - s ^ 2 / 2 * D2 with hR
  have hRle : ∀ s, |R s| ≤ (C + |D2|) / 2 * s ^ 2 := fun s ↦ by
    have h1 := abs_sub_sub_mul_deriv_le hf hC t s
    have h2 : |s ^ 2 / 2 * D2| = s ^ 2 / 2 * |D2| := by
      rw [abs_mul, abs_of_nonneg (by positivity)]
    calc |R s| ≤ |f (t + s) - f t - s * D1| + |s ^ 2 / 2 * D2| := abs_sub _ _
      _ ≤ _ := by rw [h2]; linarith
  have hKu : Integrable fun u ↦ u * K u :=
    hK1.mono' (by fun_prop) (ae_of_all _ fun u ↦ by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hK0 u)])
  have hint : ∀ a : ℝ, Integrable fun u ↦ K u * f (t - a * u) := fun a ↦ by
    refine (((hKi.const_mul (|f t|)).add (hK1.const_mul (|a| * |D1|))).add
      (hK2.const_mul (C * a ^ 2 / 2))).mono' (hKm.mul (hfm.comp (by fun_prop))).aestronglyMeasurable
      (ae_of_all _ fun u ↦ ?_)
    have hT := abs_sub_sub_mul_deriv_le hf hC t (-(a * u))
    rw [← sub_eq_add_neg] at hT
    have h3 : |f (t - a * u)| ≤ |f t| + |a| * |D1| * |u| + C * a ^ 2 / 2 * u ^ 2 := by
      have := abs_sub_abs_le_abs_sub (f (t - a * u)) (f t + -(a * u) * D1)
      have h4 : |f t + -(a * u) * D1| ≤ |f t| + |a| * |D1| * |u| := by
        refine (abs_add_le _ _).trans_eq ?_
        rw [abs_mul, abs_neg, abs_mul]; ring
      rw [show f (t - a * u) - (f t + -(a * u) * D1) =
        f (t - a * u) - f t - -(a * u) * D1 by ring] at this
      have : C * (-(a * u)) ^ 2 / 2 = C * a ^ 2 / 2 * u ^ 2 := by ring
      linarith
    simp only [Pi.add_apply, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hK0 u)]
    nlinarith [hK0 u]
  have hid : ∀ n, (∫ u, K u * f (t - h n * u)) - f t -
      h n ^ 2 / 2 * (∫ u, u ^ 2 * K u) * D2 = ∫ u, K u * R (-(h n * u)) := fun n ↦ by
    have hexp : (fun u ↦ K u * R (-(h n * u))) = fun u ↦ K u * f (t - h n * u) - f t * K u +
        h n * D1 * (u * K u) - h n ^ 2 / 2 * D2 * (u ^ 2 * K u) := by
      ext u; simp only [hR, ← sub_eq_add_neg]; ring
    rw [hexp, integral_sub _ (hK2.const_mul _), integral_add _ (hKu.const_mul _),
      integral_sub (hint _) (hKi.const_mul _), integral_const_mul, integral_const_mul,
      integral_const_mul, hK1', integral_mul_eq_zero_of_symm hKsym]
    · ring
    · exact (hint _).sub (hKi.const_mul _)
    · exact ((hint _).sub (hKi.const_mul _)).add (hKu.const_mul _)
  simp_rw [hid, ← integral_div]
  have hlo := (isLittleO_sub_taylor_two hf t).tendsto_div_nhds_zero
  have hRm : Measurable R := by fun_prop
  have hmain := tendsto_integral_of_dominated_convergence (μ := volume)
    (F := fun n u ↦ K u * R (-(h n * u)) / h n ^ 2) (f := fun _ ↦ (0 : ℝ))
    (fun u ↦ (C + |D2|) / 2 * (u ^ 2 * K u))
    (fun n ↦ ((hKm.mul (hRm.comp (measurable_const.mul measurable_id).neg)).div_const _
      ).aestronglyMeasurable) (hK2.const_mul _) (fun n ↦ ae_of_all _ fun u ↦ ?_)
    (ae_of_all _ fun u ↦ ?_)
  · simpa using hmain
  · have hn := (hh n).ne'
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_nonneg (hK0 u), abs_of_nonneg (sq_nonneg (h n)),
      div_le_iff₀ (by positivity)]
    have := hRle (-(h n * u))
    have hK := hK0 u
    calc K u * |R (-(h n * u))| ≤ K u * ((C + |D2|) / 2 * (-(h n * u)) ^ 2) :=
          mul_le_mul_of_nonneg_left this hK
      _ = _ := by ring
  · rcases eq_or_ne u 0 with rfl | hu
    · simp [hR]
    have hs : Tendsto (fun n ↦ -(h n * u)) atTop (𝓝 0) := by
      simpa using (hh0.mul_const u).neg
    have := ((hlo.comp hs).const_mul (K u * u ^ 2))
    rw [mul_zero] at this
    refine this.congr fun n ↦ ?_
    have hn := (hh n).ne'
    simp only [Function.comp_apply, hR]
    field_simp
    ring

/-- Integrals of `x ↦ F((t - x) / h)` against a law with density `f`. -/
private theorem integral_comp_div_eq_of_hasDensity {P : Measure ℝ} {f : ℝ → ℝ}
    (hf : HasDensity P volume f) (F : ℝ → ℝ) (t : ℝ) {h : ℝ} (hh : 0 < h) :
    ∫ x, F ((t - x) / h) ∂P = h * ∫ u, F u * f (t - h * u) := by
  rw [hf.integral_eq]
  simp_rw [mul_comm (f _)]
  exact integral_comp_div_mul_eq F f t hh

/-- GAPS 103.4: the pointwise central limit theorem for the kernel density estimator. For a
bounded symmetric probability kernel `K` with finite second moment `μ₂(K)` and a twice
continuously differentiable density `f` with bounded `f''`, if `h → 0`, `nh → ∞`, and
`nh⁵ = O(1)`, then `√(nh) (f̂_h(t) - f(t) - h² μ₂(K) f''(t) / 2) ⇒ N(0, R(K) f(t))` with
`R(K) = ∫ K²`. When `f(t) = 0` the limit is the point mass at `0`. -/
theorem tendstoInDistribution_kernelDensityEstimator {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure ℝ) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hiid : IsIndependentIdenticallyDistributed μ X P) (f K : ℝ → ℝ)
    (hf : HasDensity P volume f) (hf2 : ContDiff ℝ 2 f)
    (hDb : ∃ C, ∀ x, |deriv (deriv f) x| ≤ C)
    (hKm : Measurable K) (hKpos : ∀ x, 0 ≤ K x) (hKsym : ∀ x, K (-x) = K x)
    (hKb : ∃ C, ∀ x, K x ≤ C) (hK1 : (∫ x, K x) = 1) (hK2 : Integrable (fun x ↦ x ^ 2 * K x) volume)
    (h : ℕ → ℝ) (hh : ∀ n : ℕ, 0 < h n) (hh0 : Tendsto h atTop (𝓝 0))
    (hnh : Tendsto (fun n : ℕ ↦ (n : ℝ) * h n) atTop atTop)
    (hnh5 : ∃ C, ∀ᶠ n : ℕ in atTop, (n : ℝ) * h n ^ 5 ≤ C)
    (t : ℝ) :
    TendstoInDistribution (fun (n : ℕ) ω ↦ Real.sqrt ((n : ℝ) * h n) *
      (kernelDensityEstimator X K h n ω t - f t - h n ^ 2 / 2 *
        (∫ u, u ^ 2 * K u) * deriv (deriv f) t)) atTop id (fun _ ↦ μ)
      (gaussianReal 0 (Real.toNNReal ((∫ u, K u ^ 2) * f t))) := by
  obtain ⟨C, hC⟩ := hDb
  obtain ⟨CK, hCK⟩ := hKb
  obtain ⟨C5, hC5⟩ := hnh5
  have hfm := hf.1
  have hKi : Integrable K := Integrable.of_integral_ne_zero (by rw [hK1]; norm_num)
  have hK1i : Integrable fun u ↦ |u| * K u := by
    refine (hKi.add hK2).mono' (by fun_prop) (ae_of_all _ fun u ↦ ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_nonneg (hKpos u)]
    have : |u| ≤ 1 + u ^ 2 := by nlinarith [abs_nonneg u, sq_abs u]
    simp only [Pi.add_apply]
    nlinarith [hKpos u]
  have hKabs : ∀ x, |K x| ≤ CK := fun x ↦ by rw [abs_of_nonneg (hKpos x)]; exact hCK x
  set D2 := deriv (deriv f) t
  set μ₂ := ∫ u, u ^ 2 * K u
  -- the smoothed density and second moment
  set A : ℕ → ℝ := fun n ↦ ∫ u, K u * f (t - h n * u) with hA
  set A2 : ℕ → ℝ := fun n ↦ ∫ u, K u ^ 2 * f (t - h n * u) with hA2
  have hAlim : Tendsto A atTop (𝓝 (f t)) := by
    simpa [hK1] using tendsto_integral_mul_comp_sub_mul hfm hf2 hC hKi hK1i hK2 hKm
      (c := 1) (fun u ↦ by rw [one_mul]; exact le_of_eq (abs_of_nonneg (hKpos u))) hh hh0 t
  have hA2lim : Tendsto A2 atTop (𝓝 ((∫ u, K u ^ 2) * f t)) :=
    tendsto_integral_mul_comp_sub_mul hfm hf2 hC hKi hK1i hK2 (hKm.pow_const 2)
      (c := CK) (fun u ↦ by
        rw [abs_of_nonneg (sq_nonneg _), sq]
        exact mul_le_mul_of_nonneg_right (hCK u) (hKpos u)) hh hh0 t
  -- the centred summands
  set m : ℕ → ℝ := fun n ↦ ∫ x, K ((t - x) / h n) ∂P with hm
  have hmA : ∀ n, m n = h n * A n := fun n ↦
    integral_comp_div_eq_of_hasDensity hf K t (hh n)
  have hmabs : ∀ n, |m n| ≤ CK := fun n ↦ by
    have := norm_integral_le_of_norm_le_const (μ := P) (C := CK)
      (f := fun x ↦ K ((t - x) / h n)) (ae_of_all _ fun x ↦ hKabs _)
    simpa using this
  set r : ℕ → ℝ := fun n ↦ Real.sqrt ((n : ℝ) * h n) with hr
  set g : ℕ → ℝ → ℝ := fun n x ↦ (K ((t - x) / h n) - m n) / r n with hg
  have hgm : ∀ n, Measurable (g n) := fun n ↦
    ((hKm.comp ((measurable_const.sub measurable_id).div_const _)).sub_const _).div_const _
  have hgb : ∀ n x, |g n x| ≤ 2 * CK / r n := fun n x ↦ by
    simp only [hg, abs_div]
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    have hCK0 : 0 ≤ CK := (abs_nonneg _).trans (hKabs 0)
    refine div_le_div_of_nonneg_right ?_ (Real.sqrt_nonneg _)
    have h1 := hKabs ((t - x) / h n)
    have h2 := hmabs n
    rw [abs_le] at h1 h2 ⊢
    constructor <;> linarith
  have hint_map : ∀ (j : ℕ) (φ : ℝ → ℝ), Measurable φ →
      ∫ ω, φ (X j ω) ∂μ = ∫ x, φ x ∂P := fun j φ hφ ↦ by
    rw [← hiid.2.2 j, integral_map (hiid.1 j).aemeasurable hφ.aestronglyMeasurable]
  have hKL : ∀ n, MemLp (fun x ↦ K ((t - x) / h n)) 2 P := fun n ↦
    MemLp.of_bound
      (hKm.comp ((measurable_const.sub measurable_id).div_const _)).aestronglyMeasurable
      CK (ae_of_all _ fun x ↦ by rw [Real.norm_eq_abs]; exact hKabs _)
  set Y : ℕ → ℕ → Ω → ℝ := fun n j ω ↦ g n (X j ω) with hY
  have hYm : ∀ n j, Measurable (Y n j) := fun n j ↦ (hgm n).comp (hiid.1 j)
  have hY2 : ∀ n j, MemLp (Y n j) 2 μ := fun n j ↦
    MemLp.of_bound (hYm n j).aestronglyMeasurable (2 * CK / r n)
      (ae_of_all _ fun ω ↦ by rw [Real.norm_eq_abs]; exact hgb n _)
  have hY0 : ∀ n j, ∫ ω, Y n j ω ∂μ = 0 := fun n j ↦ by
    rw [hint_map j (g n) (hgm n)]
    simp only [hg]
    rw [integral_div, integral_sub ((hKL n).integrable one_le_two) (integrable_const _),
      integral_const]
    simp [hm]
  have hind : ∀ n, iIndepFun (Y n) μ := fun n ↦ hiid.2.1.comp (fun _ ↦ g n) (fun _ ↦ hgm n)
  -- the variances of the row sums
  have hsq : ∀ n, 0 < n →
      ∑ j ∈ Finset.range n, ∫ ω, Y n j ω ^ 2 ∂μ = A2 n - h n * A n ^ 2 := by
    intro n hn
    have hq : ∫ x, K ((t - x) / h n) ^ 2 ∂P = h n * A2 n :=
      integral_comp_div_eq_of_hasDensity hf (fun u ↦ K u ^ 2) t (hh n)
    have hKP : Integrable (fun x ↦ K ((t - x) / h n)) P := (hKL n).integrable one_le_two
    have hKP2 : Integrable (fun x ↦ K ((t - x) / h n) ^ 2) P := (hKL n).integrable_sq
    have hKP' : Integrable (fun x ↦ 2 * m n * K ((t - x) / h n)) P := hKP.const_mul _
    have hI1 : Integrable (fun x ↦ K ((t - x) / h n) ^ 2 - 2 * m n * K ((t - x) / h n)) P :=
      hKP2.sub hKP'
    have hnh0 : 0 < (n : ℝ) * h n := mul_pos (Nat.cast_pos.mpr hn) (hh n)
    have hterm : ∀ j, ∫ ω, Y n j ω ^ 2 ∂μ = (h n * A2 n - m n ^ 2) / (n * h n) := by
      intro j
      rw [hint_map j (fun x ↦ g n x ^ 2) ((hgm n).pow_const 2)]
      simp only [hg, hr, div_pow]
      rw [integral_div, Real.sq_sqrt hnh0.le]
      congr 1
      have hexp : ∀ x, (K ((t - x) / h n) - m n) ^ 2 =
          K ((t - x) / h n) ^ 2 - 2 * m n * K ((t - x) / h n) + m n ^ 2 := fun x ↦ by ring
      simp_rw [hexp]
      rw [integral_add hI1 (integrable_const _), integral_sub hKP2 hKP', integral_const_mul,
        integral_const, hq]
      simp only [hm, probReal_univ, smul_eq_mul, one_mul]
      ring
    rw [Finset.sum_congr rfl fun j _ ↦ hterm j, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, hmA]
    have hh0' := (hh n).ne'
    field_simp
  have hvar : Tendsto (fun n ↦ ∑ j ∈ Finset.range n, ∫ ω, Y n j ω ^ 2 ∂μ) atTop
      (𝓝 ((∫ u, K u ^ 2) * f t)) := by
    have := hA2lim.sub (hh0.mul (hAlim.pow 2))
    rw [zero_mul, sub_zero] at this
    exact this.congr' (eventually_atTop.2 ⟨1, fun n hn ↦ (hsq n hn).symm⟩)
  -- the Lindeberg condition holds trivially for bounded summands
  have hr_lim : Tendsto (fun n ↦ 2 * CK / r n) atTop (𝓝 0) := by
    have := (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hnh)).const_mul (2 * CK)
    simpa [hr, div_eq_mul_inv] using this
  have hlin : ∀ ε > 0, Tendsto (fun n ↦ ∑ j ∈ Finset.range n,
      ∫ ω, (if ε < |Y n j ω| then Y n j ω ^ 2 else 0) ∂μ) atTop (𝓝 0) := by
    intro ε hε
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hr_lim.eventually (gt_mem_nhds hε)] with n hn
    symm
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    have : (fun ω ↦ if ε < |Y n j ω| then Y n j ω ^ 2 else 0) = fun _ ↦ 0 := by
      ext ω
      split_ifs with hcon
      · exact absurd hcon (not_lt.mpr ((hgb n _).trans hn.le))
      · rfl
    rw [this, integral_zero]
  have hclt := tendstoInDistribution_sum_of_lindeberg_of_iIndepFun μ Y (fun n ↦ n) hY2 hY0 hind
    _ hvar hlin
  -- the deterministic bias term
  set c : ℕ → ℝ := fun n ↦ r n * (A n - f t - h n ^ 2 / 2 * μ₂ * D2) with hc
  have hdiff : ∀ (n : ℕ) (ω : Ω), r n * (kernelDensityEstimator X K h n ω t - f t -
      h n ^ 2 / 2 * μ₂ * D2) - ∑ j ∈ Finset.range n, Y n j ω = c n := by
    intro n ω
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hr, hc]
    have hnh0 : 0 < (n : ℝ) * h n := mul_pos (Nat.cast_pos.mpr hn) (hh n)
    have hr2 : r n ^ 2 = n * h n := Real.sq_sqrt hnh0.le
    have hr0 : r n ≠ 0 := (Real.sqrt_pos.mpr hnh0).ne'
    have hh0' := (hh n).ne'
    rw [kernelDensityEstimator_eq]
    simp only [hY, hg, hc]
    rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, hmA, ← mul_assoc, ← hr2]
    generalize (∑ i ∈ Finset.range n, K ((t - X i ω) / h n)) = S
    field_simp
    ring
  have hQ := tendsto_bias_div_sq hfm hf2 hC hKm hKpos hKi hK1i hK2 hKsym hK1 hh hh0 t
  have hcl : Tendsto c atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (by simpa using (hQ.abs.const_mul (Real.sqrt (max C5 0))))
    filter_upwards [hC5] with n hn
    have hh0' := (hh n).ne'
    have hrh : |r n * h n ^ 2| ≤ Real.sqrt (max C5 0) := by
      refine Real.abs_le_sqrt ?_
      rw [mul_pow, Real.sq_sqrt (by have := hh n; positivity)]
      calc (n : ℝ) * h n * (h n ^ 2) ^ 2 = n * h n ^ 5 := by ring
        _ ≤ max C5 0 := hn.trans (le_max_left _ _)
    have : c n = r n * h n ^ 2 * ((A n - f t - h n ^ 2 / 2 * μ₂ * D2) / h n ^ 2) := by
      simp only [hc]; field_simp
    rw [this, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right hrh (abs_nonneg _)
  have hkde : ∀ n, Measurable fun ω ↦ kernelDensityEstimator X K h n ω t := fun n ↦ by
    simp_rw [kernelDensityEstimator_eq]
    exact (Finset.measurable_sum _ fun i _ ↦
      hKm.comp ((measurable_const.sub (hiid.1 i)).div_const _)).div_const _
  refine tendstoInDistribution_of_tendstoInMeasure_sub_of_measurable μ _ _
    (fun n ↦ Finset.measurable_sum _ fun j _ ↦ hYm n j)
    (fun n ↦ (((hkde n).sub_const _).sub_const _).const_mul _) hclt ?_
  have : (fun (n : ℕ) ω ↦ r n * (kernelDensityEstimator X K h n ω t - f t -
      h n ^ 2 / 2 * μ₂ * D2) - ∑ j ∈ Finset.range n, Y n j ω) = fun n _ ↦ c n :=
    funext₂ hdiff
  rw [this]
  exact tendstoInMeasure_const_of_tendsto μ c hcl


/-- GAPS 103.5: universal `L¹` consistency of the kernel density estimator, in dimension one.
For a bounded compactly supported kernel with `∫ K = 1`, if `h → 0` and `nh → ∞`, then
`∫ |f̂_n - f| → 0` almost surely for every density `f`. -/
theorem ae_tendsto_integral_abs_kernelDensityEstimator_sub {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure ℝ) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hiid : IsIndependentIdenticallyDistributed μ X P) (f K : ℝ → ℝ)
    (hf : HasDensity P volume f) (hKm : Measurable K) (hK1 : (∫ x, K x) = 1)
    (hKb : ∃ C, ∀ x, |K x| ≤ C)
    (hKc : ∃ R > 0, ∀ x, R < |x| → K x = 0)
    (h : ℕ → ℝ) (hh : ∀ n : ℕ, 0 < h n) (hh0 : Tendsto h atTop (𝓝 0))
    (hnh : Tendsto (fun n : ℕ ↦ (n : ℝ) * h n) atTop atTop) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ ∫ t, |kernelDensityEstimator X K h n ω t - f t|) atTop (𝓝 0) := by
  sorry

/-- GAPS 103.8: the representer theorem, in its Hilbert feature-vector formulation. A
minimizer `f` of `∑ᵢ L(yᵢ, ⟪f, vᵢ⟫) + λ ‖f‖²` with `λ > 0` lies in the span of the feature
vectors `vᵢ`. -/
theorem minimizer_mem_span_of_feature_vectors
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] {n : ℕ} (v : Fin n → H)
    (y : Fin n → ℝ)
    (L : ℝ → ℝ → ℝ) (lambda : ℝ) (hlambda : 0 < lambda) (f : H)
    (hmin : ∀ g : H, (∑ i, L (y i) (inner ℝ f (v i))) + lambda * ‖f‖ ^ 2 ≤
      (∑ i, L (y i) (inner ℝ g (v i))) + lambda * ‖g‖ ^ 2) :
    f ∈ Submodule.span ℝ (range v) := by
  let S := Submodule.span ℝ (range v)
  let : FiniteDimensional ℝ S := FiniteDimensional.span_of_finite ℝ (finite_range v)
  have hinner (i : Fin n) : inner ℝ (S.starProjection f) (v i) = inner ℝ f (v i) := by
    have h := S.starProjection_inner_eq_zero f (v i) (Submodule.subset_span (mem_range_self i))
    rw [inner_sub_left] at h
    exact (sub_eq_zero.mp h).symm
  have h := hmin (S.starProjection f)
  simp_rw [hinner] at h
  have hnorm := S.norm_starProjection_apply_le f
  apply (S.mem_iff_norm_starProjection f).mpr
  have hs : ‖f‖ ^ 2 ≤ ‖S.starProjection f‖ ^ 2 :=
    (mul_le_mul_iff_right₀ hlambda).mp (by linarith only [h])
  nlinarith [norm_nonneg f, norm_nonneg (S.starProjection f)]

/-- Summing `f (σ i)` over all permutations: `n * ∑_σ f (σ i) = n! * ∑_k f k`. -/
theorem natCast_mul_sum_perm_apply {n : ℕ} (f : Fin n → ℝ) (i : Fin n) :
    (n : ℝ) * ∑ σ : Equiv.Perm (Fin n), f (σ i) = n.factorial * ∑ k, f k := by
  have hind : ∀ i' : Fin n, ∑ σ : Equiv.Perm (Fin n), f (σ i') =
      ∑ σ : Equiv.Perm (Fin n), f (σ i) := by
    intro i'
    refine Fintype.sum_equiv (Equiv.mulRight (Equiv.swap i i')) _ _ fun σ ↦ ?_
    simp [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
  calc (n : ℝ) * ∑ σ : Equiv.Perm (Fin n), f (σ i)
      = ∑ i' : Fin n, ∑ σ : Equiv.Perm (Fin n), f (σ i') := by
        rw [Finset.sum_congr rfl fun i' _ ↦ hind i', Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
    _ = ∑ σ : Equiv.Perm (Fin n), ∑ k, f k := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun σ _ ↦ Equiv.sum_comp σ f
    _ = n.factorial * ∑ k, f k := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
          nsmul_eq_mul]

/-- Summing `a (σ i) a (σ j)` over permutations for `i ≠ j`. -/
theorem natCast_mul_sum_perm_apply_mul_apply {n : ℕ} (a : Fin n → ℝ) (i j : Fin n)
    (hij : i ≠ j) :
    (n : ℝ) * (n - 1) * ∑ σ : Equiv.Perm (Fin n), a (σ i) * a (σ j) =
      n.factorial * ((∑ k, a k) ^ 2 - ∑ k, a k ^ 2) := by
  set F := fun j' : Fin n ↦ ∑ σ : Equiv.Perm (Fin n), a (σ i) * a (σ j') with hF
  have hind : ∀ j', j' ≠ i → F j' = F j := by
    intro j' hj'
    refine Fintype.sum_equiv (Equiv.mulRight (Equiv.swap j j')) _ _ fun σ ↦ ?_
    simp only [Equiv.coe_mulRight, Equiv.Perm.mul_apply, Equiv.swap_apply_left]
    rw [Equiv.swap_apply_of_ne_of_ne hij hj'.symm]
  have hdiag : (n : ℝ) * F i = n.factorial * ∑ k, a k ^ 2 := by
    have := natCast_mul_sum_perm_apply (fun k ↦ a k ^ 2) i
    simpa [hF, sq] using this
  have htot : (n : ℝ) * ∑ j', F j' = n.factorial * (∑ k, a k) ^ 2 := by
    have hsum : ∑ j', F j' = ∑ σ : Equiv.Perm (Fin n), a (σ i) * ∑ k, a k := by
      simp only [hF]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun σ _ ↦ ?_
      rw [← Finset.mul_sum, Equiv.sum_comp σ a]
    rw [hsum, ← Finset.sum_mul, ← mul_assoc, natCast_mul_sum_perm_apply a i]
    ring
  have hsplit : ∑ j', F j' = F i + ((n : ℝ) - 1) * F j := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    congr 1
    rw [Finset.sum_congr rfl fun j' hj' ↦ hind j' (Finset.ne_of_mem_erase hj'),
      Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    have : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (by rintro rfl; exact i.elim0)
    push_cast [this]
    ring
  rw [hsplit] at htot
  change (n : ℝ) * (n - 1) * F j = _
  linear_combination htot - hdiag

/-- The uniform probability measure on the permutations of `Fin n`: the law of the rank vector
of `n` independent observations from a continuous distribution. -/
def uniformPermMeasure (n : ℕ) : Measure (Equiv.Perm (Fin n)) :=
  ((Nat.factorial n : ℝ≥0∞)⁻¹) • (Measure.count : Measure (Equiv.Perm (Fin n)))

/-- The linear rank statistic `∑ᵢ cᵢ a(σ i)` with regression constants `c` and scores `a`. -/
def linearRankStatistic {n : ℕ} (a c : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) : ℝ :=
  ∑ i, c i * a (σ i)

/-- The exact mean and variance of a linear rank statistic under uniform ranks. -/
private theorem integral_and_variance_linearRankStatistic (n : ℕ) (hn : 2 ≤ n)
    (a c : Fin n → ℝ) :
    let P := uniformPermMeasure n;
    let abar := (∑ i, a i) / n;
    let cbar := (∑ i, c i) / n;
    let T := linearRankStatistic a c;
    (∫ σ, T σ ∂P) = (n : ℝ) * abar * cbar ∧
      Var[T; P] = (∑ i, (c i - cbar) ^ 2) *
        (∑ i, (a i - abar) ^ 2) / (n - 1 : ℕ) := by
  intro P abar cbar T
  have : MeasurableSingletonClass (Equiv.Perm (Fin n)) :=
    ⟨fun _ ↦ MeasurableSpace.measurableSet_top⟩
  have hint : ∀ g : Equiv.Perm (Fin n) → ℝ,
      ∫ σ, g σ ∂P = (n.factorial : ℝ)⁻¹ * ∑ σ, g σ := by
    intro g
    simp only [P, uniformPermMeasure]
    rw [integral_smul_measure, integral_count, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      smul_eq_mul]
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hn1 : (n : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hfac : (n.factorial : ℝ) ≠ 0 := by positivity
  set A := ∑ k, a k
  set C := ∑ k, c k
  set Sa := ∑ k, a k ^ 2
  set Sc := ∑ k, c k ^ 2
  -- first moments
  have hsum1 : ∀ i, ∑ σ : Equiv.Perm (Fin n), a (σ i) = n.factorial * A / n := by
    intro i
    rw [eq_div_iff hn0, mul_comm, natCast_mul_sum_perm_apply]
  have hmean : ∫ σ, T σ ∂P = A * C / n := by
    rw [hint]
    simp only [T, linearRankStatistic]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hsum1, ← Finset.sum_mul]
    field_simp
    simp only [C]
    ring
  -- second moments
  have hsum2 : ∀ i j, ∑ σ : Equiv.Perm (Fin n), a (σ i) * a (σ j) =
      if i = j then n.factorial * Sa / n
      else n.factorial * (A ^ 2 - Sa) / (n * (n - 1)) := by
    intro i j
    split_ifs with h
    · subst h
      rw [eq_div_iff hn0, mul_comm]
      simp only [← sq]
      exact natCast_mul_sum_perm_apply (fun k ↦ a k ^ 2) i
    · rw [eq_div_iff (mul_ne_zero hn0 hn1), mul_comm]
      exact natCast_mul_sum_perm_apply_mul_apply a i j h
  have hsq : ∑ σ, T σ ^ 2 = Sc * (n.factorial * Sa / n) +
      (C ^ 2 - Sc) * (n.factorial * (A ^ 2 - Sa) / (n * (n - 1))) := by
    set K : ℝ := n.factorial * (A ^ 2 - Sa) / (n * (n - 1)) with hK
    set D : ℝ := n.factorial * Sa / n with hD
    have hexpand : ∑ σ, T σ ^ 2 =
        ∑ i, ∑ j, ∑ σ : Equiv.Perm (Fin n), c i * a (σ i) * (c j * a (σ j)) := by
      simp only [T, linearRankStatistic, sq, Finset.sum_mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [Finset.sum_comm]
    have hterm : ∀ i j, ∑ σ : Equiv.Perm (Fin n), c i * a (σ i) * (c j * a (σ j)) =
        c i * c j * K + if i = j then c i * c j * (D - K) else 0 := by
      intro i j
      have h2 := hsum2 i j
      calc ∑ σ : Equiv.Perm (Fin n), c i * a (σ i) * (c j * a (σ j))
          = c i * c j * ∑ σ : Equiv.Perm (Fin n), a (σ i) * a (σ j) := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun σ _ ↦ by ring
        _ = _ := by rw [h2]; split_ifs <;> ring
    rw [hexpand]
    simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    have h1 : ∑ i, ∑ j, c i * c j * K = C ^ 2 * K := by
      rw [sq, Finset.sum_mul_sum, Finset.sum_mul]
      simp_rw [Finset.sum_mul]
    have h2 : ∑ i, c i * c i * (D - K) = Sc * (D - K) := by
      rw [Finset.sum_mul]; simp only [sq]
    rw [h1, h2]
    ring
  have hvar : Var[T; P] = (n.factorial : ℝ)⁻¹ * ∑ σ, T σ ^ 2 - (A * C / n) ^ 2 := by
    rw [variance_eq_integral (measurable_of_countable T).aemeasurable]
    rw [hmean, hint]
    have hexp : ∀ σ, (T σ - A * C / n) ^ 2 =
        T σ ^ 2 - 2 * (A * C / n) * T σ + (A * C / n) ^ 2 := fun σ ↦ by ring
    simp_rw [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
    have hm := hmean
    rw [hint] at hm
    rw [mul_add, mul_sub, ← mul_assoc _ (2 * (A * C / n)), mul_comm _ (2 * (A * C / n)),
      mul_assoc, hm]
    field_simp
    ring
  refine ⟨?_, ?_⟩
  · rw [hmean]; simp only [abar, cbar, A, C]; field_simp
  · rw [hvar, hsq]
    have hc : ∑ i, (c i - cbar) ^ 2 = Sc - C ^ 2 / n := by
      simp only [cbar, sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      field_simp
      ring
    have ha : ∑ i, (a i - abar) ^ 2 = Sa - A ^ 2 / n := by
      simp only [abar, sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      field_simp
      ring
    rw [hc, ha]
    have : ((n - 1 : ℕ) : ℝ) = n - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    rw [this]
    field_simp
    ring

/-- GAPS 103.14: the mean of a linear rank statistic under uniform ranks,
`E T_N = N c̄ ā`. -/
theorem integral_linearRankStatistic (n : ℕ) (hn : 2 ≤ n) (a c : Fin n → ℝ) :
    ∫ σ, linearRankStatistic a c σ ∂uniformPermMeasure n =
      (n : ℝ) * ((∑ i, a i) / n) * ((∑ i, c i) / n) :=
  (integral_and_variance_linearRankStatistic n hn a c).1

/-- GAPS 103.14: the variance of a linear rank statistic under uniform ranks,
`Var T_N = (N - 1)⁻¹ ∑ᵢ (cᵢ - c̄)² ∑ᵢ (a(i) - ā)²`. -/
theorem variance_linearRankStatistic (n : ℕ) (hn : 2 ≤ n) (a c : Fin n → ℝ) :
    Var[linearRankStatistic a c; uniformPermMeasure n] =
      (∑ i, (c i - (∑ i, c i) / n) ^ 2) * (∑ i, (a i - (∑ i, a i) / n) ^ 2) / (n - 1 : ℕ) :=
  (integral_and_variance_linearRankStatistic n hn a c).2

end CKSD
