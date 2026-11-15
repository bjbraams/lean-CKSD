module

public import CKSD.Asymptotics.Expansions
public import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.MeasureTheory.Measure.LevyConvergence
import TauCeti.MeasureTheory.Measure.ProductKernel
import CKSD.Bayes.Basic
public import CKSD.Asymptotics.Basic
import Mathlib.Probability.StrongLaw

/-!
# Bootstrap of the mean, the empirical distribution function and the studentized mean

Consistency of the nonparametric bootstrap of the mean in Kolmogorov distance,
`CKSD.tendstoInMeasure_bootstrap_mean_kolmogorovDistance` (GAPS 102.51). The proof follows the
classical argument of Bickel and Freedman (1981) and Singh (1981): along a sample path where the
strong law holds for `X` and `X²`, the bootstrap characteristic functions converge (Mathlib's
`Complex.tendsto_pow_exp_of_isLittleO_sub_add_div` and the Taylor bound `Complex.exp_bound`),
Lévy's continuity theorem (`ProbabilityMeasure.tendsto_iff_tendsto_charFun`) and the portmanteau
theorem give pointwise convergence of distribution functions, and Pólya's theorem
(`CKSD.tendsto_kolmogorovDistance_of_tendsto_cdf`) upgrades this to the Kolmogorov distance
using TauCeti's `Measure.continuous_cdf_of_noAtoms`. Measurability of the random Kolmogorov
distance uses TauCeti's `measurable_probabilityMeasure_pi_const_toMeasure`, and the strong law is
Mathlib's `strong_law_ae`.

The conditional expectation given the sample of a function of a nonparametric resample is the
exact average over the `n^n` index maps `Fin n → Fin n`; this avoids measurability questions
for functions on the nonseparable space of bounded functions. The bounded Lipschitz metric is
taken over functions on `ℝ → ℝ` that are bounded by one and `1`-Lipschitz for the extended
supremum distance. The `F`-Brownian bridge is `t ↦ W(F t) - F t · W 1` for a Brownian motion
`W` in the sense of Mathlib's `IsBrownianReal`.

The second-order accuracy of the studentized bootstrap is stated for the studentized mean in
dimension one, with the convention of `studentizedStatistic` that the statistic is zero when
the estimated standard deviation vanishes. Sources: GAPS 102.51, 102.52 and 102.60.

The finite-sample empirical distribution function `sampleEmpiricalCDF` and mean
`finiteSampleMean` are related to `CKSD.empiricalCDF` and `CKSD.empiricalMeasure` by
`empiricalCDF_eq_sampleEmpiricalCDF`, `sampleEmpiricalCDF_eq_cdf_empiricalMeasure` and
`finiteSampleMean_eq_integral_empiricalMeasure`; the empirical-measure integrals use
`CKSD.integral_empiricalMeasure_vector`.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace CKSD

/-- Empirical distribution function of a finite sample. -/
def sampleEmpiricalCDF {n : ℕ} (x : Fin n → ℝ) (t : ℝ) : ℝ :=
  (Finset.univ.filter fun i ↦ x i ≤ t).card / n

/-- Mean of a finite sample. -/
def finiteSampleMean {n : ℕ} (x : Fin n → ℝ) : ℝ := (∑ i, x i) / n

/-- Standard deviation of a finite sample with divisor `n`. -/
def finiteSampleSD {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Real.sqrt ((∑ i, (x i - finiteSampleMean x) ^ 2) / n)

/-- The empirical distribution function of the first `n` terms of a sequence is that of the
finite sample `(X i ω)_{i < n}`. -/
theorem empiricalCDF_eq_sampleEmpiricalCDF {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω)
    (t : ℝ) : empiricalCDF X n ω t = sampleEmpiricalCDF (fun i : Fin n ↦ X i ω) t := by
  rw [empiricalCDF_def, sampleEmpiricalCDF, Finset.card_filter, Finset.card_filter,
    Fin.sum_univ_eq_sum_range (fun i ↦ if X i ω ≤ t then 1 else 0) n]

/-- The empirical distribution function of a finite sample is the empirical measure of the
half-line `(-∞, t]`; both vanish for the empty sample. -/
theorem sampleEmpiricalCDF_eq_measureReal_empiricalMeasure {n : ℕ} (x : Fin n → ℝ) (t : ℝ) :
    sampleEmpiricalCDF x t = (empiricalMeasure n x).real (Iic t) := by
  rw [← integral_indicator_one measurableSet_Iic, integral_empiricalMeasure_vector,
    sampleEmpiricalCDF, smul_eq_mul, div_eq_inv_mul]
  congr 1
  simp [Set.indicator_apply, Finset.sum_boole]

/-- For a nonempty sample, the empirical distribution function is the distribution function
`ProbabilityTheory.cdf` of the empirical measure. -/
theorem sampleEmpiricalCDF_eq_cdf_empiricalMeasure {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ)
    (t : ℝ) : sampleEmpiricalCDF x t = cdf (empiricalMeasure n x) t := by
  have := isProbabilityMeasure_empiricalMeasure hn x
  rw [cdf_eq_real, sampleEmpiricalCDF_eq_measureReal_empiricalMeasure]

/-- The mean of a finite sample is the mean of its empirical measure; both vanish for the empty
sample. -/
theorem finiteSampleMean_eq_integral_empiricalMeasure {n : ℕ} (x : Fin n → ℝ) :
    finiteSampleMean x = ∫ y, y ∂empiricalMeasure n x := by
  rw [integral_empiricalMeasure_vector, finiteSampleMean, smul_eq_mul, div_eq_inv_mul]

/-- Extended supremum distance between real functions on the line. -/
def supEDist (u v : ℝ → ℝ) : ℝ≥0∞ := ⨆ t, ENNReal.ofReal |u t - v t|

/-- Test functions of the bounded Lipschitz metric: bounded by one and `1`-Lipschitz for the
supremum distance. -/
def IsBoundedLipschitzOne (h : (ℝ → ℝ) → ℝ) : Prop :=
  (∀ u, |h u| ≤ 1) ∧ ∀ u v, ENNReal.ofReal |h u - h v| ≤ supEDist u v

/-- The bootstrap empirical process `√n (F*ₙ - Fₙ)` of the resample `x ∘ σ`. -/
def bootstrapEmpiricalProcess {n : ℕ} (x : Fin n → ℝ) (σ : Fin n → Fin n) (t : ℝ) : ℝ :=
  Real.sqrt n * (sampleEmpiricalCDF (x ∘ σ) t - sampleEmpiricalCDF x t)

/-- Bounded Lipschitz distance between the conditional law of the bootstrap empirical process
given the sample `x` and the law of a process `Z` on `(Ω', P')`. The conditional expectation is
the average over all `n^n` resampling index maps. -/
def bootstrapBoundedLipschitzDistance {Ω' : Type*} [MeasurableSpace Ω'] {n : ℕ}
    (x : Fin n → ℝ) (Z : Ω' → ℝ → ℝ) (P' : Measure Ω') : ℝ :=
  ⨆ h : {h : (ℝ → ℝ) → ℝ // IsBoundedLipschitzOne h},
    |((Fintype.card (Fin n → Fin n) : ℝ))⁻¹ * ∑ σ, h.1 (bootstrapEmpiricalProcess x σ) -
      ∫ ω', h.1 (Z ω') ∂P'|

/-- GAPS 102.52: conditional convergence of the bootstrap empirical process. For iid real
observations with distribution function `F`, the bounded Lipschitz distance between the
conditional law of `√n (F*ₙ - Fₙ)` and the law of the `F`-Brownian bridge `B⁰ ∘ F` tends to zero
in outer probability. -/
theorem tendstoInProbability_bootstrapBoundedLipschitzDistance
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (P : Measure ℝ) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hiid : IsIndependentIdenticallyDistributed μ X P) (P' : Measure Ω')
    [IsProbabilityMeasure P'] (W : ℝ≥0 → Ω' → ℝ) (hW : IsBrownianReal W P') :
    let Z := fun (ω' : Ω') (t : ℝ) ↦ W (cdf P t).toNNReal ω' - cdf P t * W 1 ω';
    ∀ ε > 0, Tendsto (fun n ↦ μ.real {ω | ε <
      bootstrapBoundedLipschitzDistance (fun i : Fin n ↦ X i ω) Z P'}) atTop (𝓝 0) := by
  sorry

/-- GAPS 102.60, for the studentized mean in dimension one (`d = 1`, `g = id`). Assume all
moments are finite, the variance is positive, and Cramér's condition holds for `(X, X²)`.
With `T = √n (X̄ - μ)/σ̂` and its resampling analogue `T* = √n (X̄* - X̄)/σ̂*`:
the Kolmogorov distance between the conditional law of `T*` and the law of `T` is `O_P(n⁻¹)`;
the Kolmogorov distance between the law of `T` and `N(0,1)` is
`n^{-1/2} sup_x |p₁(x) φ(x)| + o(n^{-1/2})` with `p₁(x) = γ (2x² + 1)/6`, `γ` the skewness;
and the one-sided percentile-`t` interval `(-∞, X̄ - n^{-1/2} σ̂ v̂_α]` has coverage
`1 - α + O(n⁻¹)`. The coverage statements for the normal-theory, percentile, two-sided, and
symmetric intervals are outside this scope. -/
theorem studentized_bootstrap_mean_second_order_accuracy
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Measure ℝ) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hiid : IsIndependentIdenticallyDistributed μ X P)
    (hmom : ∀ k : ℕ, Integrable (fun x ↦ |x| ^ k) P) (hv : 0 < Var[id; P])
    (hcramer : SatisfiesCramerCondition
      (P.map fun x ↦ (WithLp.toLp 2 ![x, x ^ 2] : EuclideanSpace ℝ (Fin 2))))
    (α : ℝ) (hα : α ∈ Ioo 0 (1 / 2)) :
    let m := ∫ x, x ∂P;
    let γ := (∫ x, (x - m) ^ 3 ∂P) / Real.sqrt (Var[id; P]) ^ 3;
    let sample := fun (n : ℕ) (ω : Ω) (i : Fin n) ↦ X i ω;
    let T := fun (n : ℕ) (ω : Ω) ↦
      studentizedStatistic n (finiteSampleMean (sample n ω)) m (finiteSampleSD (sample n ω));
    let Tstar := fun (n : ℕ) (ω : Ω) ↦ bootstrapLaw (fun y : Fin n → ℝ ↦
      studentizedStatistic n (finiteSampleMean y) (finiteSampleMean (sample n ω))
        (finiteSampleSD y)) (sample n ω);
    let v := fun (n : ℕ) (ω : Ω) ↦ sInf {t : ℝ | α ≤ cdf (Tstar n ω) t};
    IsBoundedInProbability μ (fun n ω ↦ n * kolmogorovDistance (Tstar n ω) (μ.map (T n))) ∧
      Tendsto (fun n : ℕ ↦ Real.sqrt n *
          kolmogorovDistance (μ.map (T n)) (gaussianReal 0 1) -
            sSup (range fun x : ℝ ↦ |γ * (2 * x ^ 2 + 1) / 6 * gaussianPDFReal 0 1 x|))
        atTop (𝓝 0) ∧
      (fun n : ℕ ↦ μ.real {ω | m ≤ finiteSampleMean (sample n ω) -
          (Real.sqrt n)⁻¹ * finiteSampleSD (sample n ω) * v n ω} - (1 - α))
        =O[atTop] (fun n : ℕ ↦ (n : ℝ)⁻¹) := by
  sorry

section MeanBootstrap

attribute [local instance] Classical.propDecidable

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
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, integral_empiricalMeasure_vector]
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
    rw [abs_div, abs_mul, abs_of_nonneg (sq_nonneg s), abs_of_pos (by positivity : (0 : ℝ) < 2 * n),
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
  rw [kolmogorovDistance_def]
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
        simpa using (tendsto_const_nhds (x := t)).add
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
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
    simp only [empiricalMeasure_def, smul_apply, smul_eq_mul, FunLike.coe_sum, Finset.sum_apply]
    refine Measurable.const_mul (Finset.measurable_sum _ fun i _ ↦ ?_) _
    exact (Measure.measurable_coe hs).comp
      (Measure.measurable_dirac.comp ((measurable_pi_apply i).comp hx))
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

end MeanBootstrap

end CKSD
