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
public import CKSD.Processes.PeriodogramLimits

/-!
# Limit law of the normalized periodogram of a linear process

The periodogram ordinates of a linear process `X_t = ∑_l ψ_l Z_{t-l}` with iid noise and
absolutely summable coefficients, at Fourier frequencies `2πk_n(j)/n` converging to distinct
frequencies in `(0, π)`, divided by the spectral density, converge jointly in law to
independent standard exponential variables (GAPS 106.6; Brockwell–Davis, Theorems 10.3.1 and
10.3.2). The central limit theorem for the noise and the linear-process approximation of the
discrete Fourier transform are in `CKSD.Processes.PeriodogramLimits`; stochastic algebra and
Slutsky's lemma combine the two.

## Main results

* `CKSD.sq_norm_sum_range_mul_cexp`: the squared modulus of a real discrete Fourier transform.
* `CKSD.eventually_round_fourier`: properties of the nearest Fourier frequencies.
* `CKSD.IsIIDNoise.tendstoInDistribution_periodogram_filter_div`: the limit law of the
  normalized periodogram at Fourier frequencies.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace CKSD

/-- The squared modulus of a real discrete Fourier transform:
`|∑_{t<n} z_t e^{-itν}|² = (∑_{t<n} z_t cos tν)² + (∑_{t<n} z_t sin tν)²`. -/
theorem sq_norm_sum_range_mul_cexp (z : ℕ → ℝ) (ν : ℝ) (n : ℕ) :
    ‖∑ t ∈ Finset.range n, (z t : ℂ) * Complex.exp (-((t : ℝ) * ν : ℝ) * Complex.I)‖ ^ 2 =
      (∑ t ∈ Finset.range n, z t * Real.cos (t * ν)) ^ 2 +
        (∑ t ∈ Finset.range n, z t * Real.sin (t * ν)) ^ 2 := by
  have ht : ∀ t : ℕ, (z t : ℂ) * Complex.exp (-((t : ℝ) * ν : ℝ) * Complex.I) =
      ((z t * Real.cos (t * ν) : ℝ) : ℂ) - ((z t * Real.sin (t * ν) : ℝ) : ℂ) * Complex.I :=
    fun t ↦ by
      rw [← Complex.ofReal_neg, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
        Real.cos_neg, Real.sin_neg]
      push_cast; ring
  rw [Finset.sum_congr rfl fun t _ ↦ ht t, Finset.sum_sub_distrib, ← Finset.sum_mul,
    ← Complex.ofReal_sum, ← Complex.ofReal_sum, Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

/-- A Euclidean vector is bounded in norm by the sum of the absolute values of its
coordinates. -/
private theorem EuclideanSpace.norm_le_sum_abs {ι : Type*} [Fintype ι] (v : EuclideanSpace ℝ ι) :
    ‖v‖ ≤ ∑ i, |v i| := by
  rw [EuclideanSpace.norm_eq]
  refine Real.sqrt_le_iff.2 ⟨Finset.sum_nonneg fun i _ ↦ abs_nonneg _, ?_⟩
  simp_rw [Real.norm_eq_abs]
  exact Finset.sum_sq_le_sq_sum_of_nonneg fun i _ ↦ abs_nonneg _

/-- Convergence to `0` in probability of Euclidean vectors follows from convergence of each
coordinate. -/
theorem tendstoInMeasure_euclidean_of_forall_apply {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {ι : Type*} [Fintype ι]
    (Y : ℕ → Ω → EuclideanSpace ℝ ι)
    (h : ∀ i, TendstoInMeasure μ (fun n ω ↦ Y n ω i) atTop (fun _ ↦ 0)) :
    TendstoInMeasure μ Y atTop (fun _ ↦ 0) := by
  classical
  have habs : ∀ i, TendstoInMeasure μ (fun n ω ↦ |Y n ω i|) atTop (fun _ ↦ 0) := fun i ↦ by
    have := h i
    rw [tendstoInMeasure_iff_dist] at this ⊢
    simpa only [Real.dist_eq, sub_zero, abs_abs] using this
  have hsum : ∀ s : Finset ι,
      TendstoInMeasure μ (fun n ω ↦ ∑ i ∈ s, |Y n ω i|) atTop (fun _ ↦ 0) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simpa using tendstoInMeasure_const_of_tendsto μ (fun _ ↦ (0 : ℝ)) tendsto_const_nhds
    | insert i s hi ih =>
      simp_rw [Finset.sum_insert hi]
      exact tendstoInMeasure_add_zero μ _ _ (habs i) ih
  have hn : TendstoInMeasure μ (fun n ω ↦ ‖Y n ω‖) atTop (fun _ ↦ 0) :=
    tendstoInMeasure_zero_of_abs_le μ _ _ (fun _ _ ↦ 0) one_pos
      (Eventually.of_forall fun n ↦ ae_of_all _ fun ω _ ↦ by
        rw [abs_norm, abs_of_nonneg (Finset.sum_nonneg fun i _ ↦ abs_nonneg _)]
        exact EuclideanSpace.norm_le_sum_abs _)
      (hsum Finset.univ) (tendstoInMeasure_const_of_tendsto μ _ tendsto_const_nhds)
  rw [tendstoInMeasure_iff_norm] at hn ⊢
  simpa only [sub_zero, norm_norm] using hn

/-- Stochastic algebra for squared moduli: if `‖a_n - b_n‖ → 0` in probability and
`‖b_n‖ ≤ C R_n` with `R_n` bounded in probability, then `‖a_n‖² - ‖b_n‖² → 0` in
probability. -/
theorem tendstoInMeasure_sq_norm_sub_sq_norm {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {E : Type*} [NormedAddCommGroup E]
    (a b : ℕ → Ω → E) (R : ℕ → Ω → ℝ) (C : ℝ)
    (hab : TendstoInMeasure μ (fun n ω ↦ ‖a n ω - b n ω‖) atTop (fun _ ↦ 0))
    (hb : ∀ n ω, ‖b n ω‖ ≤ C * R n ω) (hR : IsBoundedInProbability μ R) :
    TendstoInMeasure μ (fun n ω ↦ ‖a n ω‖ ^ 2 - ‖b n ω‖ ^ 2) atTop (fun _ ↦ 0) := by
  set D : ℕ → Ω → ℝ := fun n ω ↦ ‖a n ω - b n ω‖
  have hD := isBoundedInProbability_of_tendstoInMeasure μ D 0 hab
  have hX : TendstoInMeasure μ (fun n ω ↦ D n ω * D n ω + 2 * C * (R n ω * D n ω)) atTop
      (fun _ ↦ 0) :=
    tendstoInMeasure_add_zero μ _ _
      (tendstoInMeasure_mul_zero_of_isBoundedInProbability μ D D hD hab)
      (tendstoInMeasure_const_mul_zero μ _ _
        (tendstoInMeasure_mul_zero_of_isBoundedInProbability μ R D hR hab))
  refine tendstoInMeasure_zero_of_abs_le μ _ _ (fun _ _ ↦ 0) one_pos
    (Eventually.of_forall fun n ↦ ae_of_all _ fun ω _ ↦ ?_) hX
    (tendstoInMeasure_const_of_tendsto μ _ tendsto_const_nhds)
  have h1 : |‖a n ω‖ - ‖b n ω‖| ≤ D n ω := abs_norm_sub_norm_le _ _
  have h2 : ‖a n ω‖ + ‖b n ω‖ ≤ D n ω + 2 * ‖b n ω‖ := by
    have := norm_le_norm_add_norm_sub' (a n ω) (b n ω)
    simp only [D]; rw [norm_sub_rev] at this ⊢; linarith [norm_sub_rev (a n ω) (b n ω)]
  have hD0 : 0 ≤ D n ω := norm_nonneg _
  have hX0 : 0 ≤ D n ω * D n ω + 2 * C * (R n ω * D n ω) := by
    nlinarith [hb n ω, norm_nonneg (b n ω)]
  rw [abs_of_nonneg hX0, sq_sub_sq, abs_mul, abs_of_nonneg (by positivity :
    0 ≤ ‖a n ω‖ + ‖b n ω‖)]
  calc (‖a n ω‖ + ‖b n ω‖) * |‖a n ω‖ - ‖b n ω‖|
      ≤ D n ω * (D n ω + 2 * ‖b n ω‖) := by
        rw [mul_comm]; exact mul_le_mul h1 h2 (by positivity) hD0
    _ ≤ D n ω * D n ω + 2 * C * (R n ω * D n ω) := by nlinarith [hb n ω]

/-- Boundedness in probability depends only on the eventual values of the sequence. -/
theorem IsBoundedInProbability.congr' {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X Y : ℕ → Ω → ℝ} (hX : IsBoundedInProbability μ X) (h : ∀ᶠ n in atTop, X n = Y n) :
    IsBoundedInProbability μ Y := by
  intro ε hε
  obtain ⟨C, hC, hev⟩ := hX ε hε
  exact ⟨C, hC, by filter_upwards [hev, h] with n hn hn'; rwa [← hn']⟩

/-- Continuity of the transfer function `x ↦ ∑_j ψ_j e^{-ijx}` of an absolutely summable
filter. -/
theorem continuous_tsum_mul_cexp {ψ : ℤ → ℝ} (hψ : Summable fun j ↦ |ψ j|) :
    Continuous fun x : ℝ ↦ ∑' j : ℤ, (ψ j : ℂ) * Complex.exp (-((j : ℝ) * x : ℝ) * Complex.I) :=
  continuous_tsum (fun j ↦ by fun_prop) hψ fun j x ↦ by
    rw [norm_mul, ← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs]

/-- The transfer function of an absolutely summable filter is bounded by `∑_j |ψ_j|`. -/
theorem norm_tsum_mul_cexp_le {ψ : ℤ → ℝ} (hψ : Summable fun j ↦ |ψ j|) (x : ℝ) :
    ‖∑' j : ℤ, (ψ j : ℂ) * Complex.exp (-((j : ℝ) * x : ℝ) * Complex.I)‖ ≤ ∑' j, |ψ j| := by
  have hn : ∀ j : ℤ, ‖(ψ j : ℂ) * Complex.exp (-((j : ℝ) * x : ℝ) * Complex.I)‖ = |ψ j| :=
    fun j ↦ by
      rw [norm_mul, ← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs]
  simp_rw [← hn]
  exact norm_tsum_le_tsum_norm (hψ.congr fun j ↦ (hn j).symm)

/-- Nearest Fourier frequencies to distinct frequencies `x_j ∈ (0, π)`: with
`k_n(j) = round(n x_j / (2π))`, eventually `0 < 2 k_n(j) < n` and the `k_n(j)` are distinct,
and `2π k_n(j) / n → x_j`. -/
theorem eventually_round_fourier {m : ℕ} {x : Fin m → ℝ} (hx : Function.Injective x)
    (hx0 : ∀ j, 0 < x j) (hxπ : ∀ j, x j < Real.pi) :
    (∀ᶠ n : ℕ in atTop, (∀ j, 0 < 2 * round ((n : ℝ) * x j / (2 * Real.pi)) ∧
        2 * round ((n : ℝ) * x j / (2 * Real.pi)) < n) ∧
      Function.Injective fun j ↦ round ((n : ℝ) * x j / (2 * Real.pi))) ∧
    ∀ j, Tendsto (fun n : ℕ ↦
      2 * Real.pi * (round ((n : ℝ) * x j / (2 * Real.pi)) : ℝ) / n) atTop (𝓝 (x j)) := by
  have hπ := Real.pi_pos
  have hr : ∀ (n : ℕ) j, |(n : ℝ) * x j / (2 * Real.pi) -
      round ((n : ℝ) * x j / (2 * Real.pi))| ≤ 1 / 2 := fun n j ↦ abs_sub_round _
  have hev : ∀ c : ℝ, ∀ᶠ n : ℕ in atTop, c < n := fun c ↦
    tendsto_natCast_atTop_atTop.eventually_gt_atTop c
  refine ⟨?_, fun j ↦ ?_⟩
  · refine (Filter.eventually_all.2 fun j ↦ ?_).and ?_
    · filter_upwards [hev (Real.pi / x j), hev (Real.pi / (Real.pi - x j))] with n h1 h2
      have hj := abs_le.1 (hr n j)
      have hxj := hx0 j
      have hxj' : 0 < Real.pi - x j := sub_pos.2 (hxπ j)
      rw [div_lt_iff₀ hxj] at h1
      rw [div_lt_iff₀ hxj'] at h2
      have e1 : (n : ℝ) * x j / (2 * Real.pi) * (2 * Real.pi) = n * x j := by field_simp
      constructor
      · have : (0 : ℝ) < 2 * (round ((n : ℝ) * x j / (2 * Real.pi)) : ℝ) := by
          nlinarith
        exact_mod_cast this
      · have : 2 * (round ((n : ℝ) * x j / (2 * Real.pi)) : ℝ) < n := by nlinarith
        exact_mod_cast this
    · have hpair : ∀ᶠ n : ℕ in atTop, ∀ i j : Fin m, i ≠ j →
          round ((n : ℝ) * x i / (2 * Real.pi)) ≠ round ((n : ℝ) * x j / (2 * Real.pi)) := by
        refine Filter.eventually_all.2 fun i ↦ Filter.eventually_all.2 fun j ↦ ?_
        by_cases hij : i = j
        · exact Eventually.of_forall fun _ h ↦ absurd hij h
        have hd : 0 < |x i - x j| := abs_pos.2 (sub_ne_zero.2 (hx.ne hij))
        filter_upwards [hev (2 * Real.pi / |x i - x j|)] with n hn _ heq
        rw [div_lt_iff₀ hd] at hn
        have hi := abs_le.1 (hr n i)
        have hj := abs_le.1 (hr n j)
        have heq' : (round ((n : ℝ) * x i / (2 * Real.pi)) : ℝ) =
            round ((n : ℝ) * x j / (2 * Real.pi)) := by exact_mod_cast heq
        have hdiff : |(n : ℝ) * x i / (2 * Real.pi) - n * x j / (2 * Real.pi)| ≤ 1 := by
          rw [abs_le]; constructor <;> linarith
        have : |(n : ℝ) * x i / (2 * Real.pi) - n * x j / (2 * Real.pi)| =
            n * |x i - x j| / (2 * Real.pi) := by
          rw [← sub_div, ← mul_sub, abs_div, abs_mul, Nat.abs_cast,
            abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
        rw [this, div_le_one (by positivity)] at hdiff
        linarith
      filter_upwards [hpair] with n hn i j hij
      by_contra h
      exact hn i j h hij
  · have hb : ∀ n : ℕ, 0 < n → |2 * Real.pi * (round ((n : ℝ) * x j / (2 * Real.pi)) : ℝ) / n -
        x j| ≤ Real.pi / n := fun n hn ↦ by
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      have : 2 * Real.pi * (round ((n : ℝ) * x j / (2 * Real.pi)) : ℝ) / n - x j =
          -(2 * Real.pi / n) * ((n : ℝ) * x j / (2 * Real.pi) -
            round ((n : ℝ) * x j / (2 * Real.pi))) := by field_simp; ring
      rw [this, abs_mul, abs_neg, abs_of_pos (by positivity : 0 < 2 * Real.pi / n)]
      calc 2 * Real.pi / n * |(n : ℝ) * x j / (2 * Real.pi) -
            round ((n : ℝ) * x j / (2 * Real.pi))| ≤ 2 * Real.pi / n * (1 / 2) :=
            mul_le_mul_of_nonneg_left (hr n j) (by positivity)
        _ = Real.pi / n := by ring
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_
      (tendsto_const_div_atTop_nhds_zero_nat Real.pi)
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact hb n hn

/-- The cosine and sine sums of `tendstoInDistribution_fourierTrig_sum` recover the squared
modulus of the discrete Fourier transform at `ν = 2πk/n`:
`σ² (U₀² + U₁²)/2 = |∑_{t<n} z_t e^{-itν}|² / n`. -/
private theorem sq_norm_dft_eq_fourierTrig (z : ℕ → ℝ) {σsq : ℝ} (hσ : 0 < σsq) {n : ℕ}
    (hn : 0 < n) (k : ℤ) :
    ‖∑ t ∈ Finset.range n, (z t : ℂ) *
        Complex.exp (-((t : ℝ) * (2 * Real.pi * (k : ℝ) / n) : ℝ) * Complex.I)‖ ^ 2 / n =
      σsq * (((Real.sqrt (2 / (n * σsq)) * ∑ t ∈ Finset.range n,
          z t * fourierTrig 0 (2 * Real.pi * k * t / n)) ^ 2 +
        (Real.sqrt (2 / (n * σsq)) * ∑ t ∈ Finset.range n,
          z t * fourierTrig 1 (2 * Real.pi * k * t / n)) ^ 2) / 2) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have harg : ∀ t : ℕ, 2 * Real.pi * k * t / n = t * (2 * Real.pi * (k : ℝ) / n) := fun t ↦ by
    ring
  have hc : ∑ t ∈ Finset.range n, z t * fourierTrig 0 (2 * Real.pi * k * t / n) =
      ∑ t ∈ Finset.range n, z t * Real.cos (t * (2 * Real.pi * (k : ℝ) / n)) :=
    Finset.sum_congr rfl fun t _ ↦ by simp only [fourierTrig, ↓reduceIte]; rw [harg]
  have hs : ∑ t ∈ Finset.range n, z t * fourierTrig 1 (2 * Real.pi * k * t / n) =
      ∑ t ∈ Finset.range n, z t * Real.sin (t * (2 * Real.pi * (k : ℝ) / n)) :=
    Finset.sum_congr rfl fun t _ ↦ by simp only [fourierTrig, one_ne_zero, ↓reduceIte]; rw [harg]
  rw [hc, hs, sq_norm_sum_range_mul_cexp, mul_pow, mul_pow,
    Real.sq_sqrt (div_pos two_pos (mul_pos hn' hσ)).le]
  generalize ∑ t ∈ Finset.range n, z t * Real.cos (t * (2 * Real.pi * (k : ℝ) / n)) = C
  generalize ∑ t ∈ Finset.range n, z t * Real.sin (t * (2 * Real.pi * (k : ℝ) / n)) = S
  field_simp

/-- Fourier-frequency form of the limit law of the periodogram of a linear process: for iid
noise of variance `σ²`, `∑_j |ψ_j| < ∞`, integer frequencies `k_n(j)` with eventually
`0 < 2k_n(j) < n` distinct, `2πk_n(j)/n → x_j` and `ψ(e^{-ix_j}) ≠ 0`, the ratios
`I_n(2πk_n(j)/n) / f(x_j)` of the periodogram of `X_t = ∑_l ψ_l Z_{t-l}` to the spectral
density `f = σ² |ψ(e^{-i·})|² / (2π)` converge jointly in law to independent standard
exponential variables (Brockwell–Davis, Theorem 10.3.2). -/
theorem IsIIDNoise.tendstoInDistribution_periodogram_filter_div {Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {Z : ℤ → Ω → ℝ} {σsq : ℝ}
    (hZ : IsIIDNoise μ Z σsq) {ψ : ℤ → ℝ} (hψ : Summable fun j ↦ |ψ j|) {m : ℕ}
    (k : ℕ → Fin m → ℤ)
    (hk : ∀ᶠ n in atTop, (∀ j, 0 < 2 * k n j ∧ 2 * k n j < n) ∧ Function.Injective (k n))
    (x : Fin m → ℝ) (hkx : ∀ j, Tendsto (fun n : ℕ ↦ 2 * Real.pi * (k n j : ℝ) / n) atTop
      (𝓝 (x j)))
    (hT : ∀ j, ∑' l : ℤ, (ψ l : ℂ) * Complex.exp (-((l : ℝ) * x j : ℝ) * Complex.I) ≠ 0) :
    haveI := isProbabilityMeasure_expMeasure (r := 1) zero_lt_one
    TendstoInDistribution (fun (n : ℕ) ω ↦ WithLp.toLp 2 fun j : Fin m ↦
      (2 * Real.pi * n)⁻¹ * ‖∑ t ∈ Finset.range n, ((∑' l, ψ l * Z (t - l) ω : ℝ) : ℂ) *
          Complex.exp (-((t : ℝ) * (2 * Real.pi * (k n j : ℝ) / n) : ℝ) * Complex.I)‖ ^ 2 /
        (σsq / (2 * Real.pi) *
          ‖∑' l : ℤ, (ψ l : ℂ) * Complex.exp (-((l : ℝ) * x j : ℝ) * Complex.I)‖ ^ 2))
      atTop id (fun _ ↦ μ) ((Measure.pi fun _ : Fin m ↦ expMeasure 1).map (WithLp.toLp 2)) := by
  have := isProbabilityMeasure_expMeasure (r := 1) zero_lt_one
  have hσ := hZ.pos
  have hπ := Real.pi_pos
  set T : ℝ → ℂ := fun y ↦ ∑' l : ℤ, (ψ l : ℂ) * Complex.exp (-((l : ℝ) * y : ℝ) * Complex.I)
    with hTdef
  set U : ℕ → Ω → EuclideanSpace ℝ (Fin m × Fin 2) := fun n ω ↦ WithLp.toLp 2 fun p ↦
    Real.sqrt (2 / (n * σsq)) * ∑ t ∈ Finset.range n,
      Z t ω * fourierTrig p.2 (2 * Real.pi * k n p.1 * t / n) with hUdef
  have hU : TendstoInDistribution U atTop id (fun _ ↦ μ) _ :=
    tendstoInDistribution_fourierTrig_sum hZ k hk
  set Φ : EuclideanSpace ℝ (Fin m × Fin 2) → EuclideanSpace ℝ (Fin m) := fun u ↦
    WithLp.toLp 2 fun j ↦ (u (j, 0) ^ 2 + u (j, 1) ^ 2) / 2 with hΦdef
  have hΦ : Continuous Φ := by
    refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun j ↦ ?_)
    have h0 := (PiLp.continuous_apply 2 (fun _ : Fin m × Fin 2 ↦ ℝ) (j, 0))
    have h1 := (PiLp.continuous_apply 2 (fun _ : Fin m × Fin 2 ↦ ℝ) (j, 1))
    exact ((h0.pow 2).add (h1.pow 2)).div_const 2
  have hUm : ∀ n, Measurable (U n) := fun n ↦
    (WithLp.measurable_toLp 2 _).comp (measurable_pi_iff.2 fun p ↦
      measurable_const.mul (Finset.measurable_fun_sum _ fun t _ ↦
        (hZ.measurable _).mul_const _))
  have hlim : TendstoInDistribution (fun n ω ↦ Φ (U n ω)) atTop id (fun _ ↦ μ)
      ((Measure.pi fun _ : Fin m ↦ expMeasure 1).map (WithLp.toLp 2)) :=
    have hΦU := hU.continuous_comp hΦ
    tendstoInDistribution_of_map_eq hΦU aemeasurable_id
      (by rw [Measure.map_id, ← map_stdGaussian_half_sum_sq]; rfl)
  have hXm : ∀ t : ℤ, Measurable fun ω ↦ ∑' l, ψ l * Z (t - l) ω := fun t ↦
    Measurable.tsum fun l ↦ (hZ.measurable _).const_mul _
  have hZm := hZ.measurable
  refine tendstoInDistribution_of_tendstoInMeasure_sub_of_measurable μ
    (fun n ω ↦ Φ (U n ω)) _ (fun n ↦ hΦ.measurable.comp (hUm n))
    (fun n ↦ (WithLp.measurable_toLp 2 _).comp (measurable_pi_iff.2 fun j ↦ by fun_prop))
    hlim (tendstoInMeasure_euclidean_of_forall_apply _ fun j ↦ ?_)
  -- one coordinate
  set ν : ℕ → ℝ := fun n ↦ 2 * Real.pi * (k n j : ℝ) / n with hν
  set dX : ℕ → Ω → ℂ := fun n ω ↦ ∑ t ∈ Finset.range n,
    ((∑' l, ψ l * Z (t - l) ω : ℝ) : ℂ) * Complex.exp (-((t : ℝ) * ν n : ℝ) * Complex.I)
  set dZ : ℕ → Ω → ℂ := fun n ω ↦ ∑ t ∈ Finset.range n,
    (Z t ω : ℂ) * Complex.exp (-((t : ℝ) * ν n : ℝ) * Complex.I)
  set a : ℕ → Ω → ℂ := fun n ω ↦ (((Real.sqrt n)⁻¹ : ℝ) : ℂ) * dX n ω
  set b : ℕ → Ω → ℂ := fun n ω ↦ (((Real.sqrt n)⁻¹ : ℝ) : ℂ) * (T (ν n) * dZ n ω)
  set R : ℕ → Ω → ℝ := fun n ω ↦ (Real.sqrt n)⁻¹ * ‖dZ n ω‖
  have hsqrt : ∀ n : ℕ, ((Real.sqrt n)⁻¹) ^ 2 = (n : ℝ)⁻¹ := fun n ↦ by
    rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  -- the linear-process approximation
  have hab : TendstoInMeasure μ (fun n ω ↦ ‖a n ω - b n ω‖) atTop (fun _ ↦ 0) := by
    refine (hZ.tendstoInMeasure_dft_filter_sub hψ ν).congr (fun n ↦ ae_of_all _ fun ω ↦ ?_)
      (ae_of_all _ fun _ ↦ rfl)
    simp only [a, b, dX, dZ, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _))]
    rfl
  -- boundedness of `R`
  have hR : IsBoundedInProbability μ R := by
    set g : EuclideanSpace ℝ (Fin m × Fin 2) → ℝ := fun u ↦
      Real.sqrt (σsq * ((u (j, 0) ^ 2 + u (j, 1) ^ 2) / 2))
    have hg : Continuous g := by
      have h0 := (PiLp.continuous_apply 2 (fun _ : Fin m × Fin 2 ↦ ℝ) (j, 0))
      have h1 := (PiLp.continuous_apply 2 (fun _ : Fin m × Fin 2 ↦ ℝ) (j, 1))
      exact Real.continuous_sqrt.comp
        (continuous_const.mul (((h0.pow 2).add (h1.pow 2)).div_const 2))
    refine (isBoundedInProbability_of_tendstoInDistribution μ (fun n ↦ g ∘ U n)
      (hU.continuous_comp hg)).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    funext ω
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    simp only [Function.comp, g, R, hUdef]
    rw [← sq_norm_dft_eq_fourierTrig (fun t ↦ Z t ω) hσ hn, Real.sqrt_div' _ (Nat.cast_nonneg n),
      Real.sqrt_sq (norm_nonneg _), div_eq_inv_mul]
  -- the two error terms
  have h1 := tendstoInMeasure_sq_norm_sub_sq_norm a b R (∑' l, |ψ l|) hab (fun n ω ↦ by
    simp only [b, R, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _))]
    have := norm_tsum_mul_cexp_le hψ (ν n)
    calc (Real.sqrt n)⁻¹ * (‖T (ν n)‖ * ‖dZ n ω‖)
        ≤ (Real.sqrt n)⁻¹ * ((∑' l, |ψ l|) * ‖dZ n ω‖) := by gcongr
      _ = _ := by ring) hR
  set c : ℕ → ℝ := fun n ↦ ‖T (ν n)‖ ^ 2 - ‖T (x j)‖ ^ 2
  have hc : Tendsto c atTop (𝓝 0) := by
    have hT' : Tendsto (fun n ↦ T (ν n)) atTop (𝓝 (T (x j))) :=
      ((continuous_tsum_mul_cexp hψ).tendsto (x j)).comp (hkx j)
    have := (hT'.norm.pow 2).sub_const (‖T (x j)‖ ^ 2)
    rwa [sub_self] at this
  have h2 : TendstoInMeasure μ (fun n ω ↦ R n ω * (R n ω * c n)) atTop (fun _ ↦ 0) :=
    tendstoInMeasure_mul_zero_of_isBoundedInProbability μ R _ hR
      (tendstoInMeasure_mul_zero_of_isBoundedInProbability μ R _ hR
        (tendstoInMeasure_const_of_tendsto μ c hc))
  set K : ℝ := (σsq * ‖T (x j)‖ ^ 2)⁻¹
  have hTx : 0 < ‖T (x j)‖ := norm_pos_iff.2 (hT j)
  refine (tendstoInMeasure_add_zero μ _ _ (tendstoInMeasure_const_mul_zero μ _ K h1)
    (tendstoInMeasure_const_mul_zero μ _ K h2)).congr' ?_ (ae_of_all _ fun _ ↦ rfl)
  filter_upwards [eventually_gt_atTop 0] with n hn
  refine ae_of_all _ fun ω ↦ ?_
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hQ := sq_norm_dft_eq_fourierTrig (fun t ↦ Z t ω) hσ hn (k n j)
  simp only [PiLp.sub_apply, Φ, hUdef]
  have hQ' : ((Real.sqrt (2 / (n * σsq)) * ∑ t ∈ Finset.range n,
          Z t ω * fourierTrig 0 (2 * Real.pi * k n j * t / n)) ^ 2 +
        (Real.sqrt (2 / (n * σsq)) * ∑ t ∈ Finset.range n,
          Z t ω * fourierTrig 1 (2 * Real.pi * k n j * t / n)) ^ 2) / 2 =
      ‖dZ n ω‖ ^ 2 / n / σsq := (eq_div_iff hσ.ne').2 (by rw [hQ]; ring)
  rw [hQ']
  have e1 : ‖a n ω‖ ^ 2 = (n : ℝ)⁻¹ * ‖dX n ω‖ ^ 2 := by
    simp only [a, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, hsqrt]
  have e2 : ‖b n ω‖ ^ 2 = (n : ℝ)⁻¹ * (‖T (ν n)‖ ^ 2 * ‖dZ n ω‖ ^ 2) := by
    simp only [b, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, hsqrt]
  have e3 : R n ω * (R n ω * c n) = (n : ℝ)⁻¹ * ‖dZ n ω‖ ^ 2 * c n := by
    simp only [R]; rw [← hsqrt]; ring
  rw [e1, e2, e3]
  change _ = (2 * Real.pi * n)⁻¹ * ‖dX n ω‖ ^ 2 / (σsq / (2 * Real.pi) * ‖T (x j)‖ ^ 2) -
    ‖dZ n ω‖ ^ 2 / n / σsq
  simp only [c, K]
  generalize ‖dX n ω‖ = A
  generalize ‖dZ n ω‖ = B
  generalize ‖T (ν n)‖ = C
  generalize ‖T (x j)‖ = D at hTx ⊢
  field_simp
  ring

end CKSD
