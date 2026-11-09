module

public import CKSD.Processes.Basic
public import CKSD.Asymptotics.Basic
public import CKSD.Asymptotics.Lindeberg.Basic
public import Mathlib.Probability.CramerWold
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.Independence.Integration
public import Mathlib.Analysis.Normed.Group.Tannery
public import TauCeti.Probability.Distributions.Gaussian.ChiSquared
public import TauCeti.Probability.Distributions.ChiSquared.Basic
public import TauCeti.Probability.Distributions.Exponential.Basic

/-!
# Limit laws of the periodogram of a linear process

The periodogram ordinates of a linear process `X_t = ∑_l ψ_l Z_{t-l}` with iid noise and
absolutely summable coefficients, at Fourier frequencies `2πk_n(j)/n` converging to distinct
frequencies in `(0, π)`, divided by the spectral density, converge jointly in law to
independent standard exponential variables (GAPS 106.6; Brockwell–Davis, Theorems 10.3.1 and
10.3.2).

The proof has three parts. Orthogonality of the trigonometric functions at Fourier frequencies
and the Lindeberg–Feller theorem with the Cramér–Wold device give a central limit theorem for
the normalized cosine and sine sums of the noise; half the squared length of a pair of
independent standard normal variables is standard exponential. The discrete Fourier transform
of `X` is approximated by `ψ(e^{-iν}) ∑_t Z_t e^{-itν}` with an `L¹` error `o(√n)`, uniformly in
the frequency, by a dominated-convergence argument over the filter. Stochastic algebra and
Slutsky's lemma combine the two.

## Main results

* `CKSD.sum_range_cos_mul_cos_fourier`, `CKSD.sum_range_sin_mul_sin_fourier`,
  `CKSD.sum_range_cos_mul_sin_fourier`: orthogonality of the trigonometric functions at the
  Fourier frequencies `2πk/n`, `0 < k < n/2`.
* `CKSD.tendstoInDistribution_fourierTrig_sum`: joint asymptotic normality of the cosine and
  sine sums of iid noise at distinct Fourier frequencies.
* `CKSD.map_stdGaussian_half_sum_sq`: halved squared lengths of coordinate pairs of a standard
  Gaussian vector are independent standard exponential variables.
* `CKSD.IsIIDNoise.tendstoInMeasure_dft_filter_sub`: the linear-process approximation of the
  discrete Fourier transform.

The limit law of the normalized periodogram at Fourier frequencies,
`CKSD.IsIIDNoise.tendstoInDistribution_periodogram_filter_div`, is in
`CKSD.Processes.FilteredPeriodogram`.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace CKSD

/-- Sums of `n`-th roots of unity: `∑_{t < n} e^{2πi r t / n} = 0` when `n ∤ r`. -/
theorem sum_range_exp_two_pi_mul_div_eq_zero {n : ℕ} (hn : 0 < n) {r : ℤ}
    (hr : ¬ (n : ℤ) ∣ r) :
    ∑ t ∈ Finset.range n, Complex.exp (((2 * Real.pi * r * t / n : ℝ) : ℂ) * Complex.I) = 0 := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  set ζ := Complex.exp (2 * Real.pi * Complex.I * r / n) with hζ
  have hpow : ∀ t : ℕ, Complex.exp (((2 * Real.pi * r * t / n : ℝ) : ℂ) * Complex.I) = ζ ^ t :=
    fun t ↦ by
      rw [hζ, ← Complex.exp_nat_mul]
      congr 1; push_cast; ring
  have hζ1 : ζ ≠ 1 := by
    intro h
    obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.1 h
    apply hr
    refine ⟨k, ?_⟩
    have : (r : ℂ) = n * k := by field_simp at hk; exact hk
    exact_mod_cast this
  have hζn : ζ ^ n = 1 := by
    rw [hζ, ← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
    exact ⟨r, by field_simp⟩
  simp_rw [hpow]
  rw [geom_sum_eq hζ1, hζn, sub_self, zero_div]

/-- `∑_{t < n} cos (2π r t / n) = 0` when `n ∤ r`. -/
theorem sum_range_cos_two_pi_mul_div_eq_zero {n : ℕ} (hn : 0 < n) {r : ℤ}
    (hr : ¬ (n : ℤ) ∣ r) :
    ∑ t ∈ Finset.range n, Real.cos (2 * Real.pi * r * t / n) = 0 := by
  have h := congrArg Complex.re (sum_range_exp_two_pi_mul_div_eq_zero hn hr)
  simpa only [Complex.re_sum, Complex.exp_ofReal_mul_I_re, Complex.zero_re] using h

/-- `∑_{t < n} sin (2π r t / n) = 0` when `n ∤ r`. -/
theorem sum_range_sin_two_pi_mul_div_eq_zero {n : ℕ} (hn : 0 < n) {r : ℤ}
    (hr : ¬ (n : ℤ) ∣ r) :
    ∑ t ∈ Finset.range n, Real.sin (2 * Real.pi * r * t / n) = 0 := by
  have h := congrArg Complex.im (sum_range_exp_two_pi_mul_div_eq_zero hn hr)
  simpa only [Complex.im_sum, Complex.exp_ofReal_mul_I_im, Complex.zero_im] using h

/-- For Fourier indices `0 < k, l < n/2`, neither `k + l` nor (for `k ≠ l`) `k - l` is a
multiple of `n`. -/
private theorem not_dvd_add_sub_of_fourier {n : ℕ} {k l : ℤ} (hk : 0 < 2 * k ∧ 2 * k < n)
    (hl : 0 < 2 * l ∧ 2 * l < n) :
    ¬ (n : ℤ) ∣ k + l ∧ (k ≠ l → ¬ (n : ℤ) ∣ k - l) := by
  constructor
  · rintro ⟨c, hc⟩
    rcases lt_trichotomy c 0 with h | rfl | h <;> nlinarith
  · intro hkl ⟨c, hc⟩
    rcases lt_trichotomy c 0 with h | rfl | h
    · nlinarith
    · exact hkl (by linarith)
    · nlinarith

/-- Discrete orthogonality of cosines at Fourier frequencies `2πk/n`, `0 < k < n/2`:
`∑_{t < n} cos (2πkt/n) cos (2πlt/n) = (n/2) 1{k = l}`. -/
theorem sum_range_cos_mul_cos_fourier {n : ℕ} {k l : ℤ} (hk : 0 < 2 * k ∧ 2 * k < n)
    (hl : 0 < 2 * l ∧ 2 * l < n) :
    ∑ t ∈ Finset.range n, Real.cos (2 * Real.pi * k * t / n) * Real.cos (2 * Real.pi * l * t / n) =
      if k = l then (n : ℝ) / 2 else 0 := by
  have hn : 0 < n := by omega
  obtain ⟨hadd, hsub⟩ := not_dvd_add_sub_of_fourier hk hl
  have h : ∀ t : ℕ, Real.cos (2 * Real.pi * k * t / n) * Real.cos (2 * Real.pi * l * t / n) =
      (Real.cos (2 * Real.pi * ((k - l : ℤ) : ℝ) * t / n) +
        Real.cos (2 * Real.pi * ((k + l : ℤ) : ℝ) * t / n)) / 2 := fun t ↦ by
    have := Real.cos_add (2 * Real.pi * k * t / n) (2 * Real.pi * l * t / n)
    have := Real.cos_sub (2 * Real.pi * k * t / n) (2 * Real.pi * l * t / n)
    push_cast
    rw [show 2 * Real.pi * ((k : ℝ) + l) * t / n =
      2 * Real.pi * k * t / n + 2 * Real.pi * l * t / n by ring,
      show 2 * Real.pi * ((k : ℝ) - l) * t / n =
      2 * Real.pi * k * t / n - 2 * Real.pi * l * t / n by ring]
    linarith
  simp_rw [h, ← Finset.sum_div, Finset.sum_add_distrib,
    sum_range_cos_two_pi_mul_div_eq_zero hn hadd, add_zero]
  split_ifs with hkl
  · subst hkl; simp
  · rw [sum_range_cos_two_pi_mul_div_eq_zero hn (hsub hkl), zero_div]

/-- Discrete orthogonality of sines at Fourier frequencies `2πk/n`, `0 < k < n/2`:
`∑_{t < n} sin (2πkt/n) sin (2πlt/n) = (n/2) 1{k = l}`. -/
theorem sum_range_sin_mul_sin_fourier {n : ℕ} {k l : ℤ} (hk : 0 < 2 * k ∧ 2 * k < n)
    (hl : 0 < 2 * l ∧ 2 * l < n) :
    ∑ t ∈ Finset.range n, Real.sin (2 * Real.pi * k * t / n) * Real.sin (2 * Real.pi * l * t / n) =
      if k = l then (n : ℝ) / 2 else 0 := by
  have hn : 0 < n := by omega
  obtain ⟨hadd, hsub⟩ := not_dvd_add_sub_of_fourier hk hl
  have h : ∀ t : ℕ, Real.sin (2 * Real.pi * k * t / n) * Real.sin (2 * Real.pi * l * t / n) =
      (Real.cos (2 * Real.pi * ((k - l : ℤ) : ℝ) * t / n) -
        Real.cos (2 * Real.pi * ((k + l : ℤ) : ℝ) * t / n)) / 2 := fun t ↦ by
    have := Real.cos_add (2 * Real.pi * k * t / n) (2 * Real.pi * l * t / n)
    have := Real.cos_sub (2 * Real.pi * k * t / n) (2 * Real.pi * l * t / n)
    push_cast
    rw [show 2 * Real.pi * ((k : ℝ) + l) * t / n =
      2 * Real.pi * k * t / n + 2 * Real.pi * l * t / n by ring,
      show 2 * Real.pi * ((k : ℝ) - l) * t / n =
      2 * Real.pi * k * t / n - 2 * Real.pi * l * t / n by ring]
    linarith
  simp_rw [h, ← Finset.sum_div, Finset.sum_sub_distrib,
    sum_range_cos_two_pi_mul_div_eq_zero hn hadd, sub_zero]
  split_ifs with hkl
  · subst hkl; simp
  · rw [sum_range_cos_two_pi_mul_div_eq_zero hn (hsub hkl), zero_div]

/-- Discrete orthogonality of cosines and sines at Fourier frequencies `2πk/n`, `0 < k < n/2`:
`∑_{t < n} cos (2πkt/n) sin (2πlt/n) = 0`. -/
theorem sum_range_cos_mul_sin_fourier {n : ℕ} {k l : ℤ} (hk : 0 < 2 * k ∧ 2 * k < n)
    (hl : 0 < 2 * l ∧ 2 * l < n) :
    ∑ t ∈ Finset.range n, Real.cos (2 * Real.pi * k * t / n) * Real.sin (2 * Real.pi * l * t / n) =
      0 := by
  have hn : 0 < n := by omega
  obtain ⟨hadd, hsub⟩ := not_dvd_add_sub_of_fourier hk hl
  have h : ∀ t : ℕ, Real.cos (2 * Real.pi * k * t / n) * Real.sin (2 * Real.pi * l * t / n) =
      (Real.sin (2 * Real.pi * ((k + l : ℤ) : ℝ) * t / n) -
        Real.sin (2 * Real.pi * ((k - l : ℤ) : ℝ) * t / n)) / 2 := fun t ↦ by
    have := Real.sin_add (2 * Real.pi * k * t / n) (2 * Real.pi * l * t / n)
    have := Real.sin_sub (2 * Real.pi * k * t / n) (2 * Real.pi * l * t / n)
    push_cast
    rw [show 2 * Real.pi * ((k : ℝ) + l) * t / n =
      2 * Real.pi * k * t / n + 2 * Real.pi * l * t / n by ring,
      show 2 * Real.pi * ((k : ℝ) - l) * t / n =
      2 * Real.pi * k * t / n - 2 * Real.pi * l * t / n by ring]
    linarith
  simp_rw [h, ← Finset.sum_div, Finset.sum_sub_distrib,
    sum_range_sin_two_pi_mul_div_eq_zero hn hadd, zero_sub]
  by_cases hkl : k = l
  · subst hkl; simp
  · rw [sum_range_sin_two_pi_mul_div_eq_zero hn (hsub hkl)]; simp

/-- The trigonometric coordinate functions: `cos` for `i = 0` and `sin` for `i = 1`. -/
def fourierTrig (i : Fin 2) (θ : ℝ) : ℝ :=
  if i = 0 then Real.cos θ else Real.sin θ

/-- The trigonometric coordinate functions are bounded by one. -/
theorem abs_fourierTrig_le_one (i : Fin 2) (θ : ℝ) : |fourierTrig i θ| ≤ 1 := by
  unfold fourierTrig; split_ifs
  · exact Real.abs_cos_le_one θ
  · exact Real.abs_sin_le_one θ

/-- Discrete orthogonality of the cosine and sine vectors at distinct Fourier frequencies
`2π k_j / n`, `0 < k_j < n/2`: `∑_{t < n} φ_p(t) φ_{p'}(t) = (n/2) 1{p = p'}`. -/
theorem sum_range_fourierTrig_mul {m n : ℕ} {k : Fin m → ℤ} (hk : ∀ j, 0 < 2 * k j ∧ 2 * k j < n)
    (hinj : Function.Injective k) (p p' : Fin m × Fin 2) :
    ∑ t ∈ Finset.range n, fourierTrig p.2 (2 * Real.pi * k p.1 * t / n) *
      fourierTrig p'.2 (2 * Real.pi * k p'.1 * t / n) = if p = p' then (n : ℝ) / 2 else 0 := by
  obtain ⟨j, i⟩ := p
  obtain ⟨j', i'⟩ := p'
  have hjj : (k j = k j') ↔ j = j' := hinj.eq_iff
  fin_cases i <;> fin_cases i' <;>
    simp only [fourierTrig, Fin.zero_eta, Fin.mk_one, Fin.isValue, ↓reduceIte, one_ne_zero,
      Prod.mk.injEq, and_true, and_false, zero_ne_one]
  · rw [sum_range_cos_mul_cos_fourier (hk j) (hk j')]; simp only [hjj]
  · exact sum_range_cos_mul_sin_fourier (hk j) (hk j')
  · rw [← sum_range_cos_mul_sin_fourier (hk j') (hk j)]
    exact Finset.sum_congr rfl fun t _ ↦ mul_comm _ _
  · rw [sum_range_sin_mul_sin_fourier (hk j) (hk j')]; simp only [hjj]

/-- The scalar projection `z ↦ ⟪z, s⟫` of the standard Gaussian law is `N(0, ‖s‖²)`. -/
theorem map_inner_stdGaussian {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (s : E) :
    (stdGaussian E).map (fun z ↦ inner ℝ z s) = gaussianReal 0 (‖s‖ ^ 2).toNNReal := by
  have h1 : (fun z : E ↦ inner ℝ z s) = ⇑(innerSL ℝ s) := by
    funext z; simp [innerSL_apply_apply, real_inner_comm]
  rw [h1, IsGaussian.map_eq_gaussianReal, integral_strongDual_stdGaussian,
    variance_dual_stdGaussian, innerSL_apply_norm]

/-- Central limit theorem for the discrete Fourier transform of iid noise at Fourier
frequencies: if eventually `0 < k_n(j) < n/2` with distinct `k_n(j)`, the normalized cosine and
sine sums `√(2/(nσ²)) ∑_{t<n} Z_t φ_i(2π k_n(j) t / n)` converge jointly in law to independent
standard normal variables. -/
theorem tendstoInDistribution_fourierTrig_sum {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Z : ℤ → Ω → ℝ} {σsq : ℝ}
    (hZ : IsIIDNoise μ Z σsq) {m : ℕ} (k : ℕ → Fin m → ℤ)
    (hk : ∀ᶠ n in atTop, (∀ j, 0 < 2 * k n j ∧ 2 * k n j < n) ∧ Function.Injective (k n)) :
    TendstoInDistribution (fun (n : ℕ) ω ↦ (WithLp.toLp 2 fun p : Fin m × Fin 2 ↦
      Real.sqrt (2 / (n * σsq)) * ∑ t ∈ Finset.range n,
        Z t ω * fourierTrig p.2 (2 * Real.pi * k n p.1 * t / n) :
        EuclideanSpace ℝ (Fin m × Fin 2))) atTop id (fun _ ↦ μ)
      (stdGaussian (EuclideanSpace ℝ (Fin m × Fin 2))) := by
  set c : ℕ → ℝ := fun n ↦ Real.sqrt (2 / (n * σsq)) with hc
  set φ : ℕ → Fin m × Fin 2 → ℕ → ℝ := fun n p t ↦
    fourierTrig p.2 (2 * Real.pi * k n p.1 * t / n) with hφ
  have hmeas : ∀ n : ℕ, Measurable fun ω ↦ (WithLp.toLp 2 fun p : Fin m × Fin 2 ↦
      c n * ∑ t ∈ Finset.range n, Z t ω * φ n p t : EuclideanSpace ℝ (Fin m × Fin 2)) :=
    fun n ↦ (WithLp.measurable_toLp 2 _).comp (measurable_pi_iff.2 fun p ↦
      measurable_const.mul (Finset.measurable_fun_sum _ fun t _ ↦
        (hZ.measurable _).mul_const _))
  refine TendstoInDistribution.of_inner aemeasurable_id (fun n ↦ (hmeas n).aemeasurable)
    fun s ↦ ?_
  set a : ℕ → ℕ → ℝ := fun n t ↦ c n * ∑ p, s p * φ n p t with ha
  have hinner : ∀ (n : ℕ) ω, inner ℝ (WithLp.toLp 2 fun p : Fin m × Fin 2 ↦
      c n * ∑ t ∈ Finset.range n, Z t ω * φ n p t : EuclideanSpace ℝ (Fin m × Fin 2)) s =
      ∑ t ∈ Finset.range n, a n t * Z t ω := fun n ω ↦ by
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, ha, Finset.mul_sum,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun t _ ↦ by ring
  have hσ := hZ.pos
  -- the variances of the projected sums
  have hsq : ∀ᶠ n in atTop, ∑ t ∈ Finset.range n, a n t ^ 2 = ‖s‖ ^ 2 / σsq := by
    filter_upwards [hk, eventually_gt_atTop 0] with n ⟨hkn, hinj⟩ hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have horth := sum_range_fourierTrig_mul hkn hinj
    calc ∑ t ∈ Finset.range n, a n t ^ 2
        = c n ^ 2 * ∑ p, ∑ p', s p * s p' *
            ∑ t ∈ Finset.range n, φ n p t * φ n p' t := by
          simp only [ha, sq, Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun p _ ↦ ?_
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun p' _ ↦ Finset.sum_congr rfl fun t _ ↦ by ring
      _ = c n ^ 2 * ∑ p, s p ^ 2 * ((n : ℝ) / 2) := by
          simp only [hφ, horth, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
            ↓reduceIte, sq]
      _ = ‖s‖ ^ 2 / σsq := by
          rw [EuclideanSpace.real_norm_sq_eq, ← Finset.sum_mul, hc, Real.sq_sqrt (by positivity)]
          field_simp
  -- the Lindeberg theorem for the weighted sums
  have hclt := tendstoInDistribution_sum_of_lindeberg_of_iIndepFun μ
    (fun n t ω ↦ a n t * Z t ω) (fun n ↦ n)
    (fun n t ↦ (hZ.memLp_two t).const_mul _)
    (fun n t ↦ by rw [integral_const_mul, hZ.integral_eq_zero', mul_zero])
    (fun n ↦ (hZ.iIndepFun.precomp Nat.cast_injective).comp (fun t x ↦ a n t * x)
      fun t ↦ measurable_const.mul measurable_id)
    (‖s‖ ^ 2) ?_ ?_
  · refine (tendstoInDistribution_of_map_eq hclt (by fun_prop) ?_).congr
      (fun n ↦ ae_of_all _ fun ω ↦ (hinner n ω).symm) (ae_of_all _ fun _ ↦ rfl)
    rw [Measure.map_id]
    exact map_inner_stdGaussian s
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [hsq] with n hn
    simp_rw [mul_pow, integral_const_mul, hZ.integral_sq', ← Finset.sum_mul, hn]
    field_simp
  · intro ε hε
    set S : ℝ := ∑ p, |s p| with hS
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun p _ ↦ abs_nonneg _
    set τ : ℕ → ℝ := fun n ↦ ε / (c n * (S + 1)) with hτ
    set g : ℝ → ℝ := fun r ↦ ∫ ω, (if r < |Z 0 ω| then Z 0 ω ^ 2 else 0) ∂μ with hg
    have hab : ∀ n t, |a n t| ≤ c n * S := fun n t ↦ by
      have hc0 : 0 ≤ c n := Real.sqrt_nonneg _
      simp only [ha, abs_mul, abs_of_nonneg hc0, hS]
      refine mul_le_mul_of_nonneg_left ?_ hc0
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p _ ↦ ?_)
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (abs_fourierTrig_le_one _ _)
    have hterm : ∀ n, 0 < n → ∀ t, ∫ ω, (if ε < |a n t * Z t ω| then (a n t * Z t ω) ^ 2
        else 0) ∂μ ≤ a n t ^ 2 * g (τ n) := fun n hn t ↦ by
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      have hcn : 0 < c n := Real.sqrt_pos.2 (div_pos two_pos (mul_pos hn' hσ))
      have hid : ∫ ω, (if τ n < |Z t ω| then Z t ω ^ 2 else 0) ∂μ = g (τ n) := by
        have hf : Measurable fun x : ℝ ↦ if τ n < |x| then x ^ 2 else 0 :=
          Measurable.ite (measurableSet_lt measurable_const continuous_abs.measurable)
            (measurable_id.pow_const 2) measurable_const
        exact ((hZ.identDistrib t).comp hf).integral_eq
      rw [← hid, ← integral_const_mul]
      refine integral_mono_of_nonneg (ae_of_all _ fun ω ↦ by
          simp only [Pi.zero_apply]; split_ifs <;> positivity)
        (((hZ.memLp_two t).integrable_sq.mono' (Measurable.ite (measurableSet_lt
          measurable_const (continuous_abs.measurable.comp (hZ.measurable t)))
          ((hZ.measurable t).pow_const 2) measurable_const).aestronglyMeasurable
          (ae_of_all _ fun ω ↦ by
            simp only [Real.norm_eq_abs]; split_ifs <;> simp [sq_nonneg])).const_mul _) ?_
      refine ae_of_all _ fun ω ↦ ?_
      simp only
      split_ifs with h1 h2
      · rw [mul_pow]
      · exfalso; apply h2
        have hpos : 0 < |a n t| := by
          by_contra h0; push Not at h0
          have : a n t = 0 := abs_nonpos_iff.1 h0
          simp [this] at h1; linarith
        rw [abs_mul] at h1
        have hle : |a n t| < c n * (S + 1) := by
          have := hab n t; nlinarith
        calc τ n = ε / (c n * (S + 1)) := rfl
          _ ≤ ε / |a n t| := div_le_div_of_nonneg_left hε.le hpos hle.le
          _ < |Z t ω| := by rw [div_lt_iff₀ hpos]; linarith
      · positivity
      · simp
    have hτ : Tendsto τ atTop atTop := by
      have hc0 : Tendsto c atTop (𝓝 0) := by
        have : Tendsto (fun n : ℕ ↦ 2 / ((n : ℝ) * σsq)) atTop (𝓝 0) := by
          refine Tendsto.div_atTop tendsto_const_nhds ?_
          exact tendsto_natCast_atTop_atTop.atTop_mul_const hσ
        have h := (Real.continuous_sqrt.tendsto 0).comp this
        rw [Real.sqrt_zero] at h
        exact h
      have hpos : ∀ᶠ n in atTop, 0 < c n * (S + 1) := by
        filter_upwards [eventually_gt_atTop 0] with n hn
        have : (0 : ℝ) < n := by exact_mod_cast hn
        exact mul_pos (Real.sqrt_pos.2 (div_pos two_pos (mul_pos this hσ))) (by linarith)
      have h0 : Tendsto (fun n ↦ c n * (S + 1)) atTop (𝓝[>] 0) :=
        tendsto_nhdsWithin_iff.2 ⟨by simpa using hc0.mul_const (S + 1), hpos⟩
      exact (tendsto_inv_nhdsGT_zero.comp h0).const_mul_atTop hε |>.congr fun n ↦ by
        simp [hτ, div_eq_mul_inv]
    have hg : Tendsto (fun n ↦ g (τ n)) atTop (𝓝 0) := by
      have h := tendsto_integral_filter_of_dominated_convergence (fun ω ↦ Z 0 ω ^ 2)
        (F := fun n ω ↦ if τ n < |Z 0 ω| then Z 0 ω ^ 2 else 0) (f := fun _ ↦ 0)
        (Eventually.of_forall fun n ↦ (Measurable.ite (measurableSet_lt measurable_const
          (continuous_abs.measurable.comp (hZ.measurable 0))) ((hZ.measurable 0).pow_const 2)
          measurable_const).aestronglyMeasurable)
        (Eventually.of_forall fun n ↦ ae_of_all _ fun ω ↦ by
          split_ifs <;> simp [sq_nonneg])
        (hZ.memLp_two 0).integrable_sq
        (ae_of_all _ fun ω ↦ tendsto_const_nhds.congr' (by
          filter_upwards [hτ.eventually_gt_atTop |Z 0 ω|] with n hn
          simp only [ite_eq_right (not_lt.2 hn.le)]))
      simpa using h
    refine squeeze_zero' (Eventually.of_forall fun n ↦ Finset.sum_nonneg fun t _ ↦
      integral_nonneg fun ω ↦ by simp only; split_ifs <;> positivity) ?_
      (by simpa using hg.const_mul (‖s‖ ^ 2 / σsq))
    filter_upwards [hsq, eventually_gt_atTop 0] with n hn hn0
    refine (Finset.sum_le_sum fun t _ ↦ hterm n hn0 t).trans_eq ?_
    rw [← Finset.sum_mul, hn]

/-- Half the squared norm of two independent standard normal variables is standard
exponential: `(Z₀² + Z₁²)/2 ∼ Exp(1)`, from `χ²₂ = Exp(1/2)`. -/
theorem map_half_sum_sq_pi_gaussianReal :
    (Measure.pi fun _ : Fin 2 ↦ gaussianReal 0 1).map (fun z ↦ (z 0 ^ 2 + z 1 ^ 2) / 2) =
      expMeasure 1 := by
  have h := TauCeti.Probability.map_sum_sq_pi_gaussianReal (ι := Fin 2) 1
  have hf : (fun z : Fin 2 → ℝ ↦ (z 0 ^ 2 + z 1 ^ 2) / 2) =
      (fun x ↦ (1 / 2 : ℝ) * x) ∘ fun z ↦ ∑ i, z i ^ 2 := by
    funext z; simp [Fin.sum_univ_two]; ring
  rw [hf, ← Measure.map_map (by fun_prop) (by fun_prop), h]
  simp only [NNReal.coe_one, one_mul, Fintype.card_fin, Nat.cast_ofNat, Measure.map_id']
  rw [TauCeti.Probability.chiSquaredMeasure_two,
    TauCeti.Probability.expMeasure_map_const_mul (by norm_num) (by norm_num)]
  norm_num

/-- The halved squared lengths of the coordinate pairs of a standard Gaussian vector on
`Fin m × Fin 2` are independent standard exponential variables. -/
theorem map_stdGaussian_half_sum_sq (m : ℕ) :
    (stdGaussian (EuclideanSpace ℝ (Fin m × Fin 2))).map (fun u ↦
      (WithLp.toLp 2 fun j : Fin m ↦ (u (j, 0) ^ 2 + u (j, 1) ^ 2) / 2 :
        EuclideanSpace ℝ (Fin m))) =
      (Measure.pi fun _ : Fin m ↦ expMeasure 1).map (WithLp.toLp 2) := by
  rw [← map_pi_eq_stdGaussian, Measure.map_map (by fun_prop) (by fun_prop)]
  have hcurry : (Measure.pi fun _ : Fin m × Fin 2 ↦ gaussianReal 0 1).map
      (MeasurableEquiv.curry (Fin m) (Fin 2) ℝ) =
      Measure.pi fun _ : Fin m ↦ Measure.pi fun _ : Fin 2 ↦ gaussianReal 0 1 := by
    have h := Measure.infinitePi_map_curry (ι := Fin m) (κ := Fin 2) (X := ℝ)
      (fun _ _ ↦ gaussianReal 0 1)
    simp only [Measure.infinitePi_eq_pi] at h
    exact h
  have hf : ((fun u : EuclideanSpace ℝ (Fin m × Fin 2) ↦
      (WithLp.toLp 2 fun j : Fin m ↦ (u (j, 0) ^ 2 + u (j, 1) ^ 2) / 2 :
        EuclideanSpace ℝ (Fin m))) ∘ WithLp.toLp 2) =
      WithLp.toLp 2 ∘ (fun z : Fin m → Fin 2 → ℝ ↦ fun j ↦ (z j 0 ^ 2 + z j 1 ^ 2) / 2) ∘
        MeasurableEquiv.curry (Fin m) (Fin 2) ℝ := by
    funext y; rfl
  rw [hf, ← Measure.map_map (by fun_prop) (by fun_prop),
    ← Measure.map_map (by fun_prop) (MeasurableEquiv.measurable _), hcurry,
    Measure.pi_map_pi (f := fun (_ : Fin m) (z : Fin 2 → ℝ) ↦ (z 0 ^ 2 + z 1 ^ 2) / 2)
      (fun _ ↦ by fun_prop)]
  simp_rw [map_half_sum_sq_pi_gaussianReal]

/-- Second moments of weighted sums of iid noise at distinct times:
`𝔼[(∑_{t<n} a_t Z_{s(t)})²] = σ² ∑_{t<n} a_t²` for injective `s`. -/
theorem IsIIDNoise.integral_sq_sum_mul {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Z : ℤ → Ω → ℝ} {σsq : ℝ}
    (hZ : IsIIDNoise μ Z σsq) {s : ℕ → ℤ} (hs : Function.Injective s) (a : ℕ → ℝ) (n : ℕ) :
    ∫ ω, (∑ t ∈ Finset.range n, a t * Z (s t) ω) ^ 2 ∂μ =
      σsq * ∑ t ∈ Finset.range n, a t ^ 2 := by
  have hint : ∀ t u, Integrable (fun ω ↦ a t * Z (s t) ω * (a u * Z (s u) ω)) μ := fun t u ↦
    ((hZ.memLp_two _).const_mul _).integrable_mul ((hZ.memLp_two _).const_mul _)
  have hcross : ∀ t u, ∫ ω, a t * Z (s t) ω * (a u * Z (s u) ω) ∂μ =
      if t = u then σsq * a t ^ 2 else 0 := fun t u ↦ by
    split_ifs with htu
    · subst htu
      have : (fun ω ↦ a t * Z (s t) ω * (a t * Z (s t) ω)) = fun ω ↦ a t ^ 2 * Z (s t) ω ^ 2 := by
        funext ω; ring
      rw [this, integral_const_mul, hZ.integral_sq']; ring
    · have hind : IndepFun (Z (s t)) (Z (s u)) μ :=
        hZ.iIndepFun.indepFun (hs.ne htu)
      have h := IndepFun.integral_fun_mul_eq_mul_integral hind
        (hZ.measurable _).aestronglyMeasurable (hZ.measurable _).aestronglyMeasurable
      rw [hZ.integral_eq_zero', zero_mul] at h
      have : (fun ω ↦ a t * Z (s t) ω * (a u * Z (s u) ω)) =
          fun ω ↦ (a t * a u) * (Z (s t) ω * Z (s u) ω) := by funext ω; ring
      rw [this, integral_const_mul, h, mul_zero]
  simp_rw [sq, Finset.sum_mul_sum]
  rw [integral_finsetSum _ fun t _ ↦ integrable_finsetSum _ fun u _ ↦ hint t u]
  simp_rw [integral_finsetSum _ fun u _ ↦ hint _ u, hcross, Finset.sum_ite_eq,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun t ht ↦ ?_
  simp [ht, sq]

/-- For a square-integrable real random variable under a probability measure,
`𝔼|Y| ≤ √(𝔼 Y²)`. -/
private theorem integral_abs_le_sqrt_integral_sq {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Y : Ω → ℝ} (hY : MemLp Y 2 μ) :
    ∫ ω, |Y ω| ∂μ ≤ Real.sqrt (∫ ω, Y ω ^ 2 ∂μ) := by
  have habs : MemLp (fun ω ↦ |Y ω|) 2 μ := hY.abs
  have hv := variance_nonneg (fun ω ↦ |Y ω|) μ
  rw [variance_eq_sub habs] at hv
  have hsq : ∫ ω, (fun ω ↦ |Y ω|) ω ^ 2 ∂μ = ∫ ω, Y ω ^ 2 ∂μ := by
    simp only [sq_abs]
  simp only [Pi.pow_apply] at hv
  rw [hsq] at hv
  refine Real.le_sqrt_of_sq_le ?_
  linarith

/-- First absolute moments of complex weighted sums of iid noise at distinct times: for
`‖c_t‖ ≤ 1`, `𝔼‖∑_{t<n} Z_{s(t)} c_t‖ ≤ 2 √(σ² n)`. -/
theorem IsIIDNoise.integral_norm_sum_mul_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Z : ℤ → Ω → ℝ} {σsq : ℝ}
    (hZ : IsIIDNoise μ Z σsq) {s : ℕ → ℤ} (hs : Function.Injective s) (c : ℕ → ℂ)
    (hc : ∀ t, ‖c t‖ ≤ 1) (n : ℕ) :
    ∫ ω, ‖∑ t ∈ Finset.range n, (Z (s t) ω : ℂ) * c t‖ ∂μ ≤ 2 * Real.sqrt (σsq * n) := by
  have hpart : ∀ a : ℕ → ℝ, (∀ t, |a t| ≤ 1) →
      ∫ ω, |∑ t ∈ Finset.range n, a t * Z (s t) ω| ∂μ ≤ Real.sqrt (σsq * n) := fun a ha ↦ by
    have hm : MemLp (fun ω ↦ ∑ t ∈ Finset.range n, a t * Z (s t) ω) 2 μ :=
      memLp_finsetSum _ fun t _ ↦ (hZ.memLp_two _).const_mul _
    refine (integral_abs_le_sqrt_integral_sq hm).trans (Real.sqrt_le_sqrt ?_)
    rw [hZ.integral_sq_sum_mul hs]
    refine mul_le_mul_of_nonneg_left ?_ hZ.pos.le
    calc ∑ t ∈ Finset.range n, a t ^ 2 ≤ ∑ t ∈ Finset.range n, (1 : ℝ) :=
          Finset.sum_le_sum fun t _ ↦ by
            rw [← sq_abs]; exact pow_le_one₀ (abs_nonneg _) (ha t)
      _ = n := by simp
  have hre := hpart (fun t ↦ (c t).re) fun t ↦ (Complex.abs_re_le_norm _).trans (hc t)
  have him := hpart (fun t ↦ (c t).im) fun t ↦ (Complex.abs_im_le_norm _).trans (hc t)
  have hint : ∀ a : ℕ → ℝ, Integrable (fun ω ↦ |∑ t ∈ Finset.range n, a t * Z (s t) ω|) μ :=
    fun a ↦ (integrable_finsetSum _ fun t _ ↦
      ((hZ.memLp_two _).integrable one_le_two).const_mul _).abs
  calc ∫ ω, ‖∑ t ∈ Finset.range n, (Z (s t) ω : ℂ) * c t‖ ∂μ
      ≤ ∫ ω, (|∑ t ∈ Finset.range n, (c t).re * Z (s t) ω| +
          |∑ t ∈ Finset.range n, (c t).im * Z (s t) ω|) ∂μ := by
        refine integral_mono_of_nonneg (ae_of_all _ fun ω ↦ norm_nonneg _)
          ((hint _).add (hint _)) (ae_of_all _ fun ω ↦ ?_)
        refine (Complex.norm_le_abs_re_add_abs_im _).trans_eq ?_
        simp only [Complex.re_sum, Complex.im_sum, Complex.re_ofReal_mul, Complex.im_ofReal_mul,
          mul_comm (Z _ ω)]
    _ ≤ 2 * Real.sqrt (σsq * n) := by
        rw [integral_add (hint _) (hint _)]; linarith

/-- Telescoping: `∑_{t<n} (f(t + d) - f(t)) = ∑_{l<d} (f(n + l) - f(l))`. -/
private theorem sum_range_sub_shift {G : Type*} [AddCommGroup G] (f : ℤ → G) (n d : ℕ) :
    ∑ t ∈ Finset.range n, (f (t + d) - f t) = ∑ l ∈ Finset.range d, (f (n + l) - f l) := by
  induction d with
  | zero => simp
  | succ d ih =>
    have h1 : ∑ t ∈ Finset.range n, (f ((t : ℤ) + (d + 1 : ℕ)) - f t) =
        ∑ t ∈ Finset.range n, (f (((t + 1 : ℕ) : ℤ) + d) - f ((t : ℤ) + d)) +
          ∑ t ∈ Finset.range n, (f ((t : ℤ) + d) - f t) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun t _ ↦ ?_
      have : ((t : ℤ) + 1 + d) = (t : ℤ) + (d + 1) := by ring
      push_cast; rw [this]; exact (sub_add_sub_cancel _ _ _).symm
    rw [h1, ih, Finset.sum_range_sub (fun t : ℕ ↦ f ((t : ℤ) + d)), Finset.sum_range_succ]
    rw [Nat.cast_zero, zero_add]
    abel

/-- Shift bound: if `𝔼‖W_s‖ ≤ M` for integrable `W_s`, then
`𝔼‖∑_{t<n} (W_{t-j} - W_t)‖ ≤ 2 |j| M`. -/
theorem integral_norm_sum_shift_sub_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {W : ℤ → Ω → ℂ} (hW : ∀ s, Integrable (W s) μ) {M : ℝ}
    (hM : ∀ s, ∫ ω, ‖W s ω‖ ∂μ ≤ M) (n : ℕ) (j : ℤ) :
    ∫ ω, ‖∑ t ∈ Finset.range n, (W (t - j) ω - W t ω)‖ ∂μ ≤ 2 * j.natAbs * M := by
  have key : ∀ (d : ℕ) (A B : ℕ → ℤ), (∀ ω, ‖∑ t ∈ Finset.range n, (W (t - j) ω - W t ω)‖ ≤
      ∑ l ∈ Finset.range d, (‖W (A l) ω‖ + ‖W (B l) ω‖)) → d = j.natAbs →
      ∫ ω, ‖∑ t ∈ Finset.range n, (W (t - j) ω - W t ω)‖ ∂μ ≤ 2 * j.natAbs * M := by
    intro d A B hle hd
    have hi : ∀ s, Integrable (fun ω ↦ ‖W s ω‖) μ := fun s ↦ (hW s).norm
    calc ∫ ω, ‖∑ t ∈ Finset.range n, (W (t - j) ω - W t ω)‖ ∂μ
        ≤ ∫ ω, ∑ l ∈ Finset.range d, (‖W (A l) ω‖ + ‖W (B l) ω‖) ∂μ :=
          integral_mono_of_nonneg (ae_of_all _ fun ω ↦ norm_nonneg _)
            (integrable_finsetSum _ fun l _ ↦ ((hi (A l)).add (hi (B l)) :)) (ae_of_all _ hle)
      _ = ∑ l ∈ Finset.range d, (∫ ω, ‖W (A l) ω‖ ∂μ + ∫ ω, ‖W (B l) ω‖ ∂μ) := by
          have hab : ∀ l ∈ Finset.range d,
              Integrable (fun ω ↦ ‖W (A l) ω‖ + ‖W (B l) ω‖) μ := fun l _ ↦ (hi _).add (hi _)
          rw [integral_finsetSum _ hab]
          exact Finset.sum_congr rfl fun l _ ↦ integral_add (hi _) (hi _)
      _ ≤ ∑ l ∈ Finset.range d, (M + M) :=
          Finset.sum_le_sum fun l _ ↦ add_le_add (hM _) (hM _)
      _ = 2 * j.natAbs * M := by simp [hd]; ring
  rcases Int.eq_nat_or_neg j with ⟨d, rfl | rfl⟩
  · refine key d (fun l ↦ (n : ℤ) + l - d) (fun l ↦ (l : ℤ) - d) (fun ω ↦ ?_) (by simp)
    have h := sum_range_sub_shift (fun s ↦ W (s - d) ω) n d
    have h' : ∑ t ∈ Finset.range n, (W ((t : ℤ) - d) ω - W t ω) =
        -∑ l ∈ Finset.range d, (W ((n : ℤ) + l - d) ω - W ((l : ℤ) - d) ω) := by
      rw [← h, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun t _ ↦ ?_
      simp only [add_sub_cancel_right, neg_sub]
    rw [h', norm_neg]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ ↦ norm_sub_le _ _)
  · refine key d (fun l ↦ (n : ℤ) + l) (fun l ↦ (l : ℤ)) (fun ω ↦ ?_) (by simp)
    have h := sum_range_sub_shift (fun s ↦ W s ω) n d
    simp only [sub_neg_eq_add]
    rw [h]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ ↦ norm_sub_le _ _)

/-- Deterministic linear-filter approximation of a discrete Fourier transform: if
`∑_j |ψ_j| < ∞` and `∑_j |ψ_j| |z_{s-j}| < ∞` for every `s`, then with `e(s) = e^{-isν}`,
`‖∑_{t<n} (∑_j ψ_j z_{t-j}) e(t) - (∑_j ψ_j e(j)) ∑_{t<n} z_t e(t)‖`
is at most `∑_j |ψ_j| ‖∑_{t<n} (z_{t-j} e(t-j) - z_t e(t))‖`. -/
private theorem norm_dft_filter_sub_le (ψ : ℤ → ℝ) (hψ : Summable fun j ↦ |ψ j|)
    (z : ℤ → ℝ) (hz : ∀ s, Summable fun j ↦ |ψ j| * |z (s - j)|) (ν : ℝ) (n : ℕ) :
    ‖∑ t ∈ Finset.range n, ((∑' j, ψ j * z (t - j) : ℝ) : ℂ) *
        Complex.exp (-((t : ℝ) * ν : ℝ) * Complex.I) -
      (∑' j : ℤ, (ψ j : ℂ) * Complex.exp (-((j : ℝ) * ν : ℝ) * Complex.I)) *
        ∑ t ∈ Finset.range n, (z t : ℂ) * Complex.exp (-((t : ℝ) * ν : ℝ) * Complex.I)‖ ≤
      ∑' j, |ψ j| * ‖∑ t ∈ Finset.range n,
        ((z (t - j) : ℂ) * Complex.exp (-((((t : ℤ) - j : ℤ) : ℝ) * ν : ℝ) * Complex.I) -
          (z t : ℂ) * Complex.exp (-(((t : ℤ) : ℝ) * ν : ℝ) * Complex.I))‖ := by
  set e : ℤ → ℂ := fun s ↦ Complex.exp (-((s : ℝ) * ν : ℝ) * Complex.I) with he
  have hen : ∀ s, ‖e s‖ = 1 := fun s ↦ by simp [e, Complex.norm_exp]
  have hmul : ∀ (t : ℕ) (j : ℤ), Complex.exp (-((t : ℝ) * ν : ℝ) * Complex.I) =
      e j * e ((t : ℤ) - j) := fun t j ↦ by
    simp only [he, ← Complex.exp_add]; congr 1; push_cast; ring
  have hcast : ∀ t : ℕ, Complex.exp (-((t : ℝ) * ν : ℝ) * Complex.I) = e t := fun t ↦ by
    simp [he]
  set V : ℤ → ℂ := fun j ↦ ∑ t ∈ Finset.range n,
    ((z (t - j) : ℂ) * e ((t : ℤ) - j) - (z t : ℂ) * e t) with hV
  -- summability of the pieces
  have hsa : ∀ t : ℕ, Summable fun j ↦ (ψ j : ℂ) * e j * ((z (t - j) : ℂ) * e ((t : ℤ) - j)) :=
    fun t ↦ (hz t).of_norm_bounded fun j ↦ by
      simp only [norm_mul, hen, Complex.norm_real, Real.norm_eq_abs, mul_one]; rfl
  have hsb : Summable fun j ↦ (ψ j : ℂ) * e j *
      ∑ t ∈ Finset.range n, (z t : ℂ) * e t :=
    (hψ.mul_right ‖∑ t ∈ Finset.range n, (z t : ℂ) * e t‖).of_norm_bounded fun j ↦ by
      simp [hen]
  have hsA : Summable fun j ↦ (ψ j : ℂ) * e j *
      ∑ t ∈ Finset.range n, (z (t - j) : ℂ) * e ((t : ℤ) - j) := by
    have := summable_sum (s := Finset.range n) fun t _ ↦ hsa t
    refine this.congr fun j ↦ ?_
    rw [Finset.mul_sum]
  have h1 : ∑ t ∈ Finset.range n, ((∑' j, ψ j * z (t - j) : ℝ) : ℂ) *
      Complex.exp (-((t : ℝ) * ν : ℝ) * Complex.I) = ∑' j, (ψ j : ℂ) * e j *
        ∑ t ∈ Finset.range n, (z (t - j) : ℂ) * e ((t : ℤ) - j) := by
    have hrow : ∀ t : ℕ, ((∑' j, ψ j * z (t - j) : ℝ) : ℂ) *
        Complex.exp (-((t : ℝ) * ν : ℝ) * Complex.I) =
        ∑' j, (ψ j : ℂ) * e j * ((z (t - j) : ℂ) * e ((t : ℤ) - j)) := fun t ↦ by
      rw [Complex.ofReal_tsum, ← tsum_mul_right]
      refine tsum_congr fun j ↦ ?_
      rw [hmul t j]; push_cast; ring
    simp_rw [hrow]
    rw [← Summable.tsum_finsetSum fun t _ ↦ hsa t]
    exact tsum_congr fun j ↦ (Finset.mul_sum _ _ _).symm
  have h2 : (∑' j : ℤ, (ψ j : ℂ) * Complex.exp (-((j : ℝ) * ν : ℝ) * Complex.I)) *
      ∑ t ∈ Finset.range n, (z t : ℂ) * Complex.exp (-((t : ℝ) * ν : ℝ) * Complex.I) =
      ∑' j, (ψ j : ℂ) * e j * ∑ t ∈ Finset.range n, (z t : ℂ) * e t := by
    rw [← tsum_mul_right]; simp_rw [hcast]; rfl
  have hdiff : ∀ j, (ψ j : ℂ) * e j *
      ∑ t ∈ Finset.range n, (z (t - j) : ℂ) * e ((t : ℤ) - j) -
      (ψ j : ℂ) * e j * ∑ t ∈ Finset.range n, (z t : ℂ) * e t = (ψ j : ℂ) * e j * V j :=
    fun j ↦ by rw [← mul_sub, ← Finset.sum_sub_distrib]
  rw [h1, h2, ← hsA.tsum_sub hsb]
  simp_rw [hdiff]
  have hnorm : ∀ j, ‖(ψ j : ℂ) * e j * V j‖ = |ψ j| * ‖V j‖ := fun j ↦ by
    rw [norm_mul, norm_mul, hen, Complex.norm_real, Real.norm_eq_abs, mul_one]
  have hsV : Summable fun j ↦ |ψ j| * ‖V j‖ := by
    refine Summable.of_nonneg_of_le (fun j ↦ by positivity) (fun j ↦ ?_)
      ((summable_sum (s := Finset.range n) fun t _ ↦ hz t).add
        (hψ.mul_right (∑ t ∈ Finset.range n, |z t|)))
    rw [← Finset.mul_sum, ← mul_add, ← Finset.sum_add_distrib]
    refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans
      (Finset.sum_le_sum fun t _ ↦ (norm_sub_le _ _).trans_eq ?_)) (abs_nonneg _)
    simp [hen]
  refine (norm_tsum_le_tsum_norm (hsV.congr fun j ↦ (hnorm j).symm)).trans_eq ?_
  refine tsum_congr fun j ↦ ?_
  rw [hnorm]

/-- First absolute moment bound `𝔼|Z_t| ≤ σ` for iid noise of variance `σ²`. -/
theorem IsIIDNoise.integral_abs_le_sqrt {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {Z : ℤ → Ω → ℝ} {σsq : ℝ} (hZ : IsIIDNoise μ Z σsq) (t : ℤ) :
    ∫ ω, |Z t ω| ∂μ ≤ Real.sqrt σsq :=
  (integral_abs_le_sqrt_integral_sq (hZ.memLp_two t)).trans_eq (by rw [hZ.integral_sq' t])

/-- For iid noise and an absolutely summable filter, almost surely
`∑_j |ψ_j| |Z_{s-j}| < ∞` for every `s`. -/
theorem IsIIDNoise.ae_summable_abs_mul {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {Z : ℤ → Ω → ℝ} {σsq : ℝ} (hZ : IsIIDNoise μ Z σsq)
    {ψ : ℤ → ℝ} (hψ : Summable fun j ↦ |ψ j|) :
    ∀ᵐ ω ∂μ, ∀ s : ℤ, Summable fun j ↦ |ψ j| * |Z (s - j) ω| := by
  rw [ae_all_iff]; intro s
  have hE : ∀ u, ∫⁻ ω, ‖Z u ω‖ₑ ∂μ ≤ ENNReal.ofReal (Real.sqrt σsq) := fun u ↦ by
    rw [← ofReal_integral_norm_eq_lintegral_enorm ((hZ.memLp_two u).integrable one_le_two)]
    exact ENNReal.ofReal_le_ofReal (by simpa using hZ.integral_abs_le_sqrt u)
  have hψe : ∑' j, ‖ψ j‖ₑ ≠ ⊤ := by
    simp_rw [← ofReal_norm, Real.norm_eq_abs]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ abs_nonneg _) hψ]
    exact ENNReal.ofReal_ne_top
  have hmeas : ∀ j, Measurable fun ω ↦ ‖ψ j‖ₑ * ‖Z (s - j) ω‖ₑ := fun j ↦
    (hZ.measurable _).enorm.const_mul _
  have hfin : ∫⁻ ω, ∑' j, ‖ψ j‖ₑ * ‖Z (s - j) ω‖ₑ ∂μ ≠ ⊤ := by
    rw [lintegral_tsum fun j ↦ (hmeas j).aemeasurable]
    refine ne_top_of_le_ne_top (b := (∑' j, ‖ψ j‖ₑ) * ENNReal.ofReal (Real.sqrt σsq))
      (ENNReal.mul_ne_top hψe ENNReal.ofReal_ne_top) ?_
    rw [← ENNReal.tsum_mul_right]
    refine CompleteLattice.summable.tsum_le_tsum (fun j ↦ ?_) CompleteLattice.summable
    rw [lintegral_const_mul _ (hZ.measurable _).enorm]
    exact mul_le_mul_right (hE _) _
  filter_upwards [ae_lt_top' (Measurable.tsum hmeas).aemeasurable hfin] with ω hω
  refine (ENNReal.summable_toReal hω.ne).congr fun j ↦ ?_
  simp [ENNReal.toReal_mul]

/-- `ofReal (∑ f) ≤ ∑ ofReal f` for nonnegative real families, summable or not. -/
private theorem ofReal_tsum_le {ι : Type*} {f : ι → ℝ} (hf : ∀ i, 0 ≤ f i) :
    ENNReal.ofReal (∑' i, f i) ≤ ∑' i, ENNReal.ofReal (f i) := by
  by_cases hs : Summable f
  · rw [ENNReal.ofReal_tsum_of_nonneg hf hs]
  · simp [tsum_eq_zero_of_not_summable hs]

/-- Moment bounds for the shifted-window differences
`V_j = ∑_{t<n} (Z_{t-j} e(t-j) - Z_t e(t))`, `e(s) = e^{-isν}`, of iid noise:
`𝔼‖V_j‖ ≤ 2 |j| σ` and `𝔼‖V_j‖ ≤ 4 √(σ² n)`. -/
private theorem IsIIDNoise.integral_norm_shift_window_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Z : ℤ → Ω → ℝ} {σsq : ℝ}
    (hZ : IsIIDNoise μ Z σsq) (ν : ℝ) (n : ℕ) (j : ℤ) :
    Integrable (fun ω ↦ ‖∑ t ∈ Finset.range n,
        ((Z (t - j) ω : ℂ) * Complex.exp (-((((t : ℤ) - j : ℤ) : ℝ) * ν : ℝ) * Complex.I) -
          (Z t ω : ℂ) * Complex.exp (-(((t : ℤ) : ℝ) * ν : ℝ) * Complex.I))‖) μ ∧
    ∫ ω, ‖∑ t ∈ Finset.range n,
        ((Z (t - j) ω : ℂ) * Complex.exp (-((((t : ℤ) - j : ℤ) : ℝ) * ν : ℝ) * Complex.I) -
          (Z t ω : ℂ) * Complex.exp (-(((t : ℤ) : ℝ) * ν : ℝ) * Complex.I))‖ ∂μ ≤
        2 * j.natAbs * Real.sqrt σsq ∧
    ∫ ω, ‖∑ t ∈ Finset.range n,
        ((Z (t - j) ω : ℂ) * Complex.exp (-((((t : ℤ) - j : ℤ) : ℝ) * ν : ℝ) * Complex.I) -
          (Z t ω : ℂ) * Complex.exp (-(((t : ℤ) : ℝ) * ν : ℝ) * Complex.I))‖ ∂μ ≤
        4 * Real.sqrt (σsq * n) := by
  set W : ℤ → Ω → ℂ := fun s ω ↦ (Z s ω : ℂ) * Complex.exp (-((s : ℝ) * ν : ℝ) * Complex.I)
  have hWi : ∀ s, Integrable (W s) μ := fun s ↦
    (((hZ.memLp_two s).integrable one_le_two).ofReal).mul_const _
  have hWn : ∀ s ω, ‖W s ω‖ = |Z s ω| := fun s ω ↦ by
    simp only [W]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, ← Complex.ofReal_neg,
      Complex.norm_exp_ofReal_mul_I, mul_one]
  have hA := hZ.integral_norm_sum_mul_le (s := fun t : ℕ ↦ (t : ℤ) - j)
    (fun a b h ↦ by simpa using h) (fun t ↦ Complex.exp (-((((t : ℤ) - j : ℤ) : ℝ) * ν : ℝ) *
      Complex.I)) (fun t ↦ by simp [Complex.norm_exp]) n
  have hB := hZ.integral_norm_sum_mul_le (s := fun t : ℕ ↦ (t : ℤ))
    (fun a b h ↦ by simpa using h) (fun t ↦ Complex.exp (-(((t : ℤ) : ℝ) * ν : ℝ) *
      Complex.I)) (fun t ↦ by simp [Complex.norm_exp]) n
  have hiA : Integrable (fun ω ↦ ‖∑ t ∈ Finset.range n, W ((t : ℤ) - j) ω‖) μ :=
    (integrable_finsetSum _ fun t _ ↦ hWi _).norm
  have hiB : Integrable (fun ω ↦ ‖∑ t ∈ Finset.range n, W (t : ℤ) ω‖) μ :=
    (integrable_finsetSum _ fun t _ ↦ hWi _).norm
  have hint : Integrable (fun ω ↦ ‖∑ t ∈ Finset.range n, (W ((t : ℤ) - j) ω - W t ω)‖) μ :=
    (integrable_finsetSum _ fun t _ ↦ (hWi _).sub (hWi _)).norm
  refine ⟨hint, ?_, ?_⟩
  · refine integral_norm_sum_shift_sub_le hWi (fun s ↦ ?_) n j
    simp_rw [hWn]; exact hZ.integral_abs_le_sqrt s
  · calc ∫ ω, ‖∑ t ∈ Finset.range n, (W ((t : ℤ) - j) ω - W t ω)‖ ∂μ
        ≤ ∫ ω, (‖∑ t ∈ Finset.range n, W ((t : ℤ) - j) ω‖ +
            ‖∑ t ∈ Finset.range n, W (t : ℤ) ω‖) ∂μ := by
          refine integral_mono hint (hiA.add hiB) fun ω ↦ ?_
          simp only [Finset.sum_sub_distrib]
          exact norm_sub_le _ _
      _ ≤ 2 * Real.sqrt (σsq * n) + 2 * Real.sqrt (σsq * n) := by
          rw [integral_add hiA hiB]; exact add_le_add hA hB
      _ = 4 * Real.sqrt (σsq * n) := by ring

/-- Linear-process approximation of the discrete Fourier transform, uniformly along any
frequency sequence `ν_n`: for iid noise and `∑_j |ψ_j| < ∞`,
`n^{-1/2} ‖∑_{t<n} X_t e^{-itν_n} - ψ(e^{-iν_n}) ∑_{t<n} Z_t e^{-itν_n}‖ → 0` in probability,
where `X_t = ∑_j ψ_j Z_{t-j}` and `ψ(e^{-iν}) = ∑_j ψ_j e^{-ijν}`
(Brockwell–Davis, Theorem 10.3.1). -/
theorem IsIIDNoise.tendstoInMeasure_dft_filter_sub {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Z : ℤ → Ω → ℝ} {σsq : ℝ}
    (hZ : IsIIDNoise μ Z σsq) {ψ : ℤ → ℝ} (hψ : Summable fun j ↦ |ψ j|) (ν : ℕ → ℝ) :
    TendstoInMeasure μ (fun (n : ℕ) ω ↦ (Real.sqrt n)⁻¹ *
      ‖∑ t ∈ Finset.range n, ((∑' j, ψ j * Z (t - j) ω : ℝ) : ℂ) *
          Complex.exp (-((t : ℝ) * ν n : ℝ) * Complex.I) -
        (∑' j : ℤ, (ψ j : ℂ) * Complex.exp (-((j : ℝ) * ν n : ℝ) * Complex.I)) *
          ∑ t ∈ Finset.range n, (Z t ω : ℂ) * Complex.exp (-((t : ℝ) * ν n : ℝ) * Complex.I)‖)
      atTop 0 := by
  set V : ℕ → ℤ → Ω → ℝ := fun n j ω ↦ ‖∑ t ∈ Finset.range n,
    ((Z (t - j) ω : ℂ) * Complex.exp (-((((t : ℤ) - j : ℤ) : ℝ) * ν n : ℝ) * Complex.I) -
      (Z t ω : ℂ) * Complex.exp (-(((t : ℤ) : ℝ) * ν n : ℝ) * Complex.I))‖ with hV
  have hVb := fun n j ↦ hZ.integral_norm_shift_window_le (ν n) n j
  set c : ℕ → ℤ → ℝ := fun n j ↦ ∫ ω, V n j ω ∂μ with hc
  have hc0 : ∀ n j, 0 ≤ c n j := fun n j ↦ integral_nonneg fun ω ↦ norm_nonneg _
  have hσ := Real.sqrt_nonneg σsq
  -- the deterministic bound sequence
  set g : ℕ → ℝ := fun n ↦ ∑' j, |ψ j| * ((Real.sqrt n)⁻¹ * c n j) with hg
  have hterm : ∀ n : ℕ, 1 ≤ n → ∀ j, |ψ j| * ((Real.sqrt n)⁻¹ * c n j) ≤ |ψ j| * (4 * √σsq) :=
    fun n hn j ↦ by
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      have hn' : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
      rw [inv_mul_le_iff₀ hn']
      refine (hVb n j).2.2.trans_eq ?_
      rw [Real.sqrt_mul' _ (Nat.cast_nonneg n)]; ring
  have hgt : Tendsto g atTop (𝓝 0) := by
    have := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
      (f := fun (n : ℕ) j ↦ |ψ j| * ((Real.sqrt n)⁻¹ * c n j)) (g := fun _ ↦ 0)
      (hψ.mul_right (4 * √σsq)) (fun j ↦ ?_) ?_
    · simpa using this
    · have hs : Tendsto (fun n : ℕ ↦ (Real.sqrt n)⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp
          (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
      have hup := (hs.mul_const (2 * j.natAbs * √σsq)).const_mul |ψ j|
      simp only [zero_mul, mul_zero] at hup
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
        (fun n ↦ mul_nonneg (abs_nonneg _) (mul_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _))
          (hc0 n j))) fun n ↦ ?_
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hVb n j).2.1
        (inv_nonneg.2 (Real.sqrt_nonneg _))) (abs_nonneg _)
    · filter_upwards [eventually_ge_atTop 1] with n hn j
      rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _)
        (mul_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _)) (hc0 n j)))]
      exact hterm n hn j
  -- the `L¹` bound
  have hgs : ∀ n : ℕ, 1 ≤ n → Summable fun j ↦ |ψ j| * ((Real.sqrt n)⁻¹ * c n j) := fun n hn ↦
    Summable.of_nonneg_of_le (fun j ↦ mul_nonneg (abs_nonneg _)
      (mul_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _)) (hc0 n j))) (hterm n hn)
      (hψ.mul_right _)
  have hL1 : ∀ n : ℕ, 1 ≤ n → eLpNorm ((fun ω ↦ (Real.sqrt n)⁻¹ *
      ‖∑ t ∈ Finset.range n, ((∑' j, ψ j * Z (t - j) ω : ℝ) : ℂ) *
          Complex.exp (-((t : ℝ) * ν n : ℝ) * Complex.I) -
        (∑' j : ℤ, (ψ j : ℂ) * Complex.exp (-((j : ℝ) * ν n : ℝ) * Complex.I)) *
          ∑ t ∈ Finset.range n, (Z t ω : ℂ) * Complex.exp (-((t : ℝ) * ν n : ℝ) * Complex.I)‖)
        - 0) 1 μ ≤ ENNReal.ofReal (g n) := fun n hn ↦ by
    have hX : ∀ t : ℤ, Measurable fun ω ↦ ∑' j, ψ j * Z (t - j) ω := fun t ↦
      Measurable.tsum fun j ↦ (hZ.measurable _).const_mul _
    have hZm := hZ.measurable
    rw [sub_zero, eLpNorm_one_eq_lintegral_enorm (by fun_prop)]
    have hmeasV : ∀ j, Measurable (V n j) := fun j ↦ by
      have := hZ.measurable; simp only [hV]; fun_prop
    calc ∫⁻ ω, ‖(Real.sqrt n)⁻¹ * ‖_‖‖ₑ ∂μ
        ≤ ∫⁻ ω, ∑' j, ENNReal.ofReal ((Real.sqrt n)⁻¹ * (|ψ j| * V n j ω)) ∂μ := by
          refine lintegral_mono_ae ?_
          filter_upwards [hZ.ae_summable_abs_mul hψ] with ω hω
          rw [← ofReal_norm, Real.norm_of_nonneg (mul_nonneg (inv_nonneg.2
            (Real.sqrt_nonneg _)) (norm_nonneg _))]
          refine (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
            (norm_dft_filter_sub_le ψ hψ (fun s ↦ Z s ω) hω (ν n) n)
            (inv_nonneg.2 (Real.sqrt_nonneg _)))).trans ?_
          rw [← tsum_mul_left]
          exact ofReal_tsum_le fun j ↦ mul_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _))
            (mul_nonneg (abs_nonneg _) (norm_nonneg _))
      _ = ∑' j, ENNReal.ofReal (|ψ j| * ((Real.sqrt n)⁻¹ * c n j)) := by
          rw [lintegral_tsum fun j ↦ (((hmeasV j).const_mul _).const_mul _).ennreal_ofReal
            |>.aemeasurable]
          refine tsum_congr fun j ↦ ?_
          rw [← ofReal_integral_eq_lintegral_ofReal (((hVb n j).1.const_mul _).const_mul _)
            (ae_of_all _ fun ω ↦ mul_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _))
              (mul_nonneg (abs_nonneg _) (norm_nonneg _)))]
          rw [integral_const_mul, integral_const_mul]; congr 1; ring
      _ = ENNReal.ofReal (g n) := by
          rw [ENNReal.ofReal_tsum_of_nonneg (fun j ↦ mul_nonneg (abs_nonneg _)
            (mul_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _)) (hc0 n j))) (hgs n hn)]
  refine tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero ?_
  have h0 : Tendsto (fun n ↦ ENNReal.ofReal (g n)) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal hgt
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h0
    (Eventually.of_forall fun _ ↦ bot_le) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact hL1 n hn

end CKSD
