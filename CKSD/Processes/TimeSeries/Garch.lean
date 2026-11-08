module

public import CKSD.Processes.Dependence
public import Mathlib.Probability.Independence.Integration

/-!
# Stationary GARCH(1,1) series and moments

For an iid noise `(ε_t)_{t ∈ ℤ}` with mean `0` and variance `1` and coefficients
`α₀ ≥ 0`, `α₁, β₁ ≥ 0` with `α₁ + β₁ < 1`, the series
`σ_t² = α₀ ∑_{n ≥ 0} ∏_{j < n} (β₁ + α₁ ε_{t-j-1}²)` converges almost surely and in `L¹`, solves
the GARCH recursion `σ_t² = α₀ + α₁ X_{t-1}² + β₁ σ_{t-1}²` with `X_t = σ_t ε_t`, and `(X_t)` is
weak white noise of variance `α₀ / (1 - α₁ - β₁)`. The products are functions of the strict
past of the noise, which gives the independence from `ε_t` used in all moment computations.

## Main definitions

* `CKSD.garchCoeff`, `CKSD.garchTerm`: the factors `β₁ + α₁ ε_{t-j-1}²` and their products.
* `CKSD.garchVariance`: the conditional variance series `σ_t²`.
* `CKSD.garchProcess`: the GARCH process `X_t = σ_t ε_t`.

## Main results (GAPS 106.18)

* `CKSD.ae_summable_garchTerm`, `CKSD.integrable_tsum_garchTerm`, `CKSD.integral_tsum_garchTerm`:
  the series converges almost surely, is integrable and has mean `(1 - (β₁ + α₁))⁻¹`.
* `CKSD.integral_garchVariance`: `𝔼 σ_t² = α₀ / (1 - α₁ - β₁)`.
* `CKSD.garchVariance_ae_eq`: the GARCH recursion holds almost surely.
* `CKSD.covariance_garchProcess`: `Cov(X_s, X_t) = α₀ / (1 - α₁ - β₁)` if `s = t` and `0`
  otherwise.

The strict-stationarity criterion `𝔼 log(β₁ + α₁ ε_0²) < 0` and uniqueness are not covered. In
the code `a₀ = α₀`, `a = α₁` and `b = β₁`.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace CKSD

/-- The GARCH coefficient `b + a ε_{t-j-1}²`. -/
def garchCoeff {Ω : Type*} (a b : ℝ) (ε : ℤ → Ω → ℝ) (t : ℤ) (j : ℕ) (ω : Ω) : ℝ :=
  b + a * ε (t - j - 1) ω ^ 2

/-- The GARCH product `∏_{j<n} (b + a ε_{t-j-1}²)`. -/
def garchTerm {Ω : Type*} (a b : ℝ) (ε : ℤ → Ω → ℝ) (t : ℤ) (n : ℕ) (ω : Ω) : ℝ :=
  ∏ j ∈ Finset.range n, garchCoeff a b ε t j ω

/-- The GARCH products are nonnegative. -/
theorem garchTerm_nonneg {Ω : Type*} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ε : ℤ → Ω → ℝ)
    (t : ℤ) (n : ℕ) (ω : Ω) : 0 ≤ garchTerm a b ε t n ω :=
  Finset.prod_nonneg fun j _ ↦ by unfold garchCoeff; positivity

/-- The GARCH product at time `t` is a function of the strict past of the noise. -/
theorem measurable_garchTerm {Ω : Type*} (a b : ℝ) (ε : ℤ → Ω → ℝ)
    (t : ℤ) (n : ℕ) : Measurable[pastSigmaAlgebra ε (t - 1)] (garchTerm a b ε t n) := by
  unfold garchTerm garchCoeff
  refine Finset.measurable_prod _ fun j _ ↦ ?_
  have := measurable_pastSigmaAlgebra_of_le (ε := ε) (s := t - j - 1) (t := t - 1) (by omega)
  exact measurable_const.add (measurable_const.mul (this.pow_const 2))

/-- The GARCH product at time `t` is measurable with respect to the noise at any set of times
containing `t - j - 1` for `j < n`. -/
theorem measurable_garchTerm_biSup {Ω : Type*} (a b : ℝ)
    (ε : ℤ → Ω → ℝ) (t : ℤ) (n : ℕ) {S : Set ℤ} (hS : ∀ j < n, t - j - 1 ∈ S) :
    Measurable[⨆ s ∈ S, MeasurableSpace.comap (ε s) inferInstance] (garchTerm a b ε t n) := by
  unfold garchTerm garchCoeff
  refine Finset.measurable_prod _ fun j hj ↦ ?_
  have : Measurable[⨆ s ∈ S, MeasurableSpace.comap (ε s) inferInstance] (ε (t - j - 1)) :=
    Measurable.of_comap_le (le_iSup₂_of_le (t - j - 1) (hS j (Finset.mem_range.1 hj)) le_rfl)
  exact measurable_const.add (measurable_const.mul (this.pow_const 2))

/-- The GARCH product of length `n` is integrable with mean `(b + a)^n`, by independence of the
noise at distinct times; the noise is iid with `𝔼 ε_0² = 1`. -/
private theorem integrable_garchTerm_and_integral_aux {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ε : ℤ → Ω → ℝ}
    (hm : ∀ t, Measurable (ε t)) (hind : iIndepFun ε μ)
    (hlaw : ∀ t, μ.map (ε t) = μ.map (ε 0))
    (h1 : (∫ ω, ε 0 ω ^ 2 ∂μ) = 1) (a b : ℝ) (t : ℤ) (n : ℕ) :
    Integrable (garchTerm a b ε t n) μ ∧ ∫ ω, garchTerm a b ε t n ω ∂μ = (b + a) ^ n := by
  have hsq : ∀ k, Integrable (fun ω ↦ ε k ω ^ 2) μ ∧ ∫ ω, ε k ω ^ 2 ∂μ = 1 := by
    intro k
    have hid : IdentDistrib (ε k) (ε 0) μ μ :=
      ⟨(hm k).aemeasurable, (hm 0).aemeasurable, hlaw k⟩
    have hid2 := hid.comp (measurable_id.pow_const 2)
    refine ⟨?_, ?_⟩
    · exact hid2.integrable_iff.2 (Integrable.of_integral_ne_zero (by
        simp only [Function.comp_def, id_eq]; rw [h1]; exact one_ne_zero))
    · rw [← h1]; exact hid2.integral_eq
  have hcoeff : ∀ j, Integrable (garchCoeff a b ε t j) μ ∧
      ∫ ω, garchCoeff a b ε t j ω ∂μ = b + a := by
    intro j
    obtain ⟨hi, he⟩ := hsq (t - j - 1)
    refine ⟨(integrable_const b).add (hi.const_mul a), ?_⟩
    simp only [garchCoeff]
    rw [integral_add (integrable_const b) (hi.const_mul a), integral_const_mul, he]
    simp
  induction n with
  | zero =>
    have : garchTerm a b ε t 0 = fun _ ↦ 1 := by funext ω; simp [garchTerm]
    rw [this]
    exact ⟨integrable_const _, by simp⟩
  | succ n ih =>
    have hfun : garchTerm a b ε t (n + 1) = garchTerm a b ε t n * garchCoeff a b ε t n := by
      funext ω; simp [garchTerm, Finset.prod_range_succ]
    have hY := measurable_garchTerm_biSup a b ε t n (S := {s | t - n ≤ s})
      (fun j hj ↦ by simp only [mem_ofPred_eq]; omega)
    have hindep : IndepFun (garchTerm a b ε t n) (garchCoeff a b ε t n) μ :=
      (indepFun_of_measurable_biSup_of_notMem hm hind (k := t - n - 1)
        (by simp only [mem_ofPred_eq]; omega) hY).comp measurable_id
          (measurable_const.add (measurable_const.mul (measurable_id.pow_const 2)) :
            Measurable fun x : ℝ ↦ b + a * x ^ 2)
    rw [hfun]
    refine ⟨hindep.integrable_mul ih.1 (hcoeff n).1, ?_⟩
    rw [IndepFun.integral_mul_eq_mul_integral hindep ih.1.aestronglyMeasurable
      (hcoeff n).1.aestronglyMeasurable, ih.2, (hcoeff n).2, pow_succ]

/-- The GARCH series `∑_n ∏_{j<n} (b + a ε_{t-j-1}²)`, when `a + b < 1`, converges almost
surely, is integrable, and has mean `(1 - (b + a))⁻¹`; the proof uses monotone convergence. -/
private theorem garchTsum_aux {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ε : ℤ → Ω → ℝ}
    (hm : ∀ t, Measurable (ε t)) (hind : iIndepFun ε μ)
    (hlaw : ∀ t, μ.map (ε t) = μ.map (ε 0))
    (h1 : (∫ ω, ε 0 ω ^ 2 ∂μ) = 1) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b < 1)
    (t : ℤ) :
    (∀ᵐ ω ∂μ, Summable fun n ↦ garchTerm a b ε t n ω) ∧
      Integrable (fun ω ↦ ∑' n, garchTerm a b ε t n ω) μ ∧
      ∫ ω, ∑' n, garchTerm a b ε t n ω ∂μ = (1 - (b + a))⁻¹ := by
  have hI := integrable_garchTerm_and_integral_aux hm hind hlaw h1 a b t
  have h0 := garchTerm_nonneg ha hb ε t
  have hmeas : ∀ n, Measurable (garchTerm a b ε t n) := fun n ↦
    (measurable_garchTerm a b ε t n).mono (pastSigmaAlgebra_le hm _) le_rfl
  have hgeo0 : 0 ≤ b + a := by linarith
  have hgeo1 : b + a < 1 := by linarith
  have hsum : Summable fun n : ℕ ↦ (b + a) ^ n := summable_geometric_of_lt_one hgeo0 hgeo1
  have hlin : ∫⁻ ω, ∑' n, ENNReal.ofReal (garchTerm a b ε t n ω) ∂μ =
      ENNReal.ofReal (∑' n : ℕ, (b + a) ^ n) := by
    rw [lintegral_tsum fun n ↦ (hmeas n).ennreal_ofReal.aemeasurable,
      ENNReal.ofReal_tsum_of_nonneg (fun n ↦ pow_nonneg hgeo0 n) hsum]
    congr 1
    funext n
    rw [← (hI n).2, ofReal_integral_eq_lintegral_ofReal (hI n).1 (ae_of_all _ (h0 n))]
  have hfin : ∀ᵐ ω ∂μ, ∑' n, ENNReal.ofReal (garchTerm a b ε t n ω) < ∞ :=
    ae_lt_top' (AEMeasurable.tsum fun n ↦ (hmeas n).ennreal_ofReal.aemeasurable)
      (by rw [hlin]; exact ENNReal.ofReal_ne_top)
  have hsumm : ∀ᵐ ω ∂μ, Summable fun n ↦ garchTerm a b ε t n ω := by
    filter_upwards [hfin] with ω hω
    have : Summable fun n ↦ ((garchTerm a b ε t n ω).toNNReal : ℝ) :=
      NNReal.summable_coe.2 (ENNReal.tsum_coe_ne_top_iff_summable.1 hω.ne)
    simpa only [Real.coe_toNNReal _ (h0 _ ω)] using this
  have hVmeas : Measurable fun ω ↦ ∑' n, garchTerm a b ε t n ω := Measurable.tsum hmeas
  refine ⟨hsumm, ⟨hVmeas.aestronglyMeasurable, ?_⟩, ?_⟩
  · rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun ω ↦ tsum_nonneg fun n ↦ h0 n ω)]
    calc ∫⁻ ω, ENNReal.ofReal (∑' n, garchTerm a b ε t n ω) ∂μ
        = ∫⁻ ω, ∑' n, ENNReal.ofReal (garchTerm a b ε t n ω) ∂μ := by
          refine lintegral_congr_ae ?_
          filter_upwards [hsumm] with ω hω
          exact ENNReal.ofReal_tsum_of_nonneg (fun n ↦ h0 n ω) hω
      _ < ∞ := by rw [hlin]; exact ENNReal.ofReal_lt_top
  · rw [← integral_tsum_of_summable_integral_norm (fun n ↦ (hI n).1)]
    · simp_rw [(hI _).2]
      exact tsum_geometric_of_lt_one hgeo0 hgeo1
    · refine hsum.congr fun n ↦ ?_
      rw [← (hI n).2]
      exact (integral_congr_ae (ae_of_all _ fun ω ↦ Real.norm_of_nonneg (h0 n ω))).symm


/-- GAPS 106.18: when `a + b < 1`, the GARCH series `∑_n ∏_{j<n} (b + a ε_{t-j-1}²)` converges
almost surely, for an iid noise with `𝔼 ε_0² = 1`. -/
theorem ae_summable_garchTerm {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ε : ℤ → Ω → ℝ}
    (hm : ∀ t, Measurable (ε t)) (hind : iIndepFun ε μ)
    (hlaw : ∀ t, μ.map (ε t) = μ.map (ε 0))
    (h1 : (∫ ω, ε 0 ω ^ 2 ∂μ) = 1) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b < 1)
    (t : ℤ) : ∀ᵐ ω ∂μ, Summable fun n ↦ garchTerm a b ε t n ω :=
  (garchTsum_aux hm hind hlaw h1 ha hb hab t).1

/-- When `a + b < 1`, the GARCH series is integrable. -/
theorem integrable_tsum_garchTerm {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ε : ℤ → Ω → ℝ}
    (hm : ∀ t, Measurable (ε t)) (hind : iIndepFun ε μ)
    (hlaw : ∀ t, μ.map (ε t) = μ.map (ε 0))
    (h1 : (∫ ω, ε 0 ω ^ 2 ∂μ) = 1) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b < 1)
    (t : ℤ) : Integrable (fun ω ↦ ∑' n, garchTerm a b ε t n ω) μ :=
  (garchTsum_aux hm hind hlaw h1 ha hb hab t).2.1

/-- When `a + b < 1`, the GARCH series has mean `(1 - (b + a))⁻¹`. -/
theorem integral_tsum_garchTerm {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ε : ℤ → Ω → ℝ}
    (hm : ∀ t, Measurable (ε t)) (hind : iIndepFun ε μ)
    (hlaw : ∀ t, μ.map (ε t) = μ.map (ε 0))
    (h1 : (∫ ω, ε 0 ω ^ 2 ∂μ) = 1) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b < 1)
    (t : ℤ) : ∫ ω, ∑' n, garchTerm a b ε t n ω ∂μ = (1 - (b + a))⁻¹ :=
  (garchTsum_aux hm hind hlaw h1 ha hb hab t).2.2

/-- The GARCH series at time `t` is a function of the strict past of the noise. -/
theorem measurable_tsum_garchTerm_past {Ω : Type*} (a b : ℝ) (ε : ℤ → Ω → ℝ) (t : ℤ) :
    Measurable[pastSigmaAlgebra ε (t - 1)] fun ω ↦ ∑' n, garchTerm a b ε t n ω := by
  let _ := pastSigmaAlgebra ε (t - 1)
  exact Measurable.tsum fun n ↦ measurable_garchTerm a b ε t n

/-- The GARCH conditional variance `σ_t² = a₀ ∑_n ∏_{j<n} (b + a ε_{t-j-1}²)`. -/
def garchVariance {Ω : Type*} (a₀ a b : ℝ) (ε : ℤ → Ω → ℝ) (t : ℤ) (ω : Ω) : ℝ :=
  a₀ * ∑' n, garchTerm a b ε t n ω

/-- The GARCH process `X_t = σ_t ε_t`. -/
def garchProcess {Ω : Type*} (a₀ a b : ℝ) (ε : ℤ → Ω → ℝ) (t : ℤ) (ω : Ω) : ℝ :=
  Real.sqrt (garchVariance a₀ a b ε t ω) * ε t ω

section Moments

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ε : ℤ → Ω → ℝ} {a₀ a b : ℝ}

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
/-- The GARCH conditional variance is nonnegative. -/
theorem garchVariance_nonneg (ha₀ : 0 ≤ a₀) (ha : 0 ≤ a) (hb : 0 ≤ b) (t : ℤ) (ω : Ω) :
    0 ≤ garchVariance a₀ a b ε t ω :=
  mul_nonneg ha₀ (tsum_nonneg fun n ↦ garchTerm_nonneg ha hb ε t n ω)

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
/-- The GARCH conditional variance at time `t` is a function of the strict past of the noise. -/
theorem measurable_garchVariance_past (t : ℤ) :
    Measurable[pastSigmaAlgebra ε (t - 1)] (garchVariance a₀ a b ε t) :=
  (measurable_tsum_garchTerm_past a b ε t).const_mul a₀

/-- GAPS 106.18: the GARCH conditional variance has mean `a₀ / (1 - a - b)`. -/
theorem integral_garchVariance (hε : IsIIDNoise μ ε 1) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b < 1) (t : ℤ) : ∫ ω, garchVariance a₀ a b ε t ω ∂μ = a₀ / (1 - a - b) := by
  simp only [garchVariance]
  rw [integral_const_mul, integral_tsum_garchTerm hε.measurable hε.iIndepFun hε.map_eq
    hε.integral_sq ha hb hab t, div_eq_mul_inv]
  ring_nf

/-- The GARCH conditional variance is integrable. -/
theorem integrable_garchVariance (hε : IsIIDNoise μ ε 1) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b < 1) (t : ℤ) : Integrable (garchVariance a₀ a b ε t) μ :=
  (integrable_tsum_garchTerm hε.measurable hε.iIndepFun hε.map_eq hε.integral_sq ha hb hab
    t).const_mul a₀

/-- GAPS 106.18: the GARCH recursion `σ_t² = a₀ + a X_{t-1}² + b σ_{t-1}²` holds almost surely. -/
theorem garchVariance_ae_eq (hε : IsIIDNoise μ ε 1) (ha₀ : 0 ≤ a₀) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b < 1) (t : ℤ) :
    ∀ᵐ ω ∂μ, garchVariance a₀ a b ε t ω = a₀ + a * garchProcess a₀ a b ε (t - 1) ω ^ 2 +
      b * garchVariance a₀ a b ε (t - 1) ω := by
  filter_upwards [ae_summable_garchTerm hε.measurable hε.iIndepFun hε.map_eq hε.integral_sq
    ha hb hab (t - 1)] with ω hω
  have hshift : ∀ n, garchTerm a b ε t (n + 1) ω =
      garchTerm a b ε (t - 1) n ω * (b + a * ε (t - 1) ω ^ 2) := by
    intro n
    simp only [garchTerm, Finset.prod_range_succ']
    congr 1
    · refine Finset.prod_congr rfl fun j _ ↦ ?_
      simp only [garchCoeff]
      rw [show t - ((j + 1 : ℕ) : ℤ) - 1 = t - 1 - (j : ℤ) - 1 by push_cast; ring]
    · simp [garchCoeff]
  have hsumt : Summable fun n ↦ garchTerm a b ε t n ω := by
    rw [← summable_nat_add_iff 1]
    simp_rw [hshift]
    exact hω.mul_right _
  have hX2 : garchProcess a₀ a b ε (t - 1) ω ^ 2 =
      garchVariance a₀ a b ε (t - 1) ω * ε (t - 1) ω ^ 2 := by
    simp only [garchProcess, mul_pow, Real.sq_sqrt (garchVariance_nonneg ha₀ ha hb _ _)]
  rw [hX2]
  simp only [garchVariance]
  rw [hsumt.tsum_eq_zero_add]
  simp_rw [hshift]
  rw [tsum_mul_right]
  simp only [garchTerm, Finset.range_zero, Finset.prod_empty]
  ring

/-- The GARCH process is square integrable. -/
theorem memLp_garchProcess (hε : IsIIDNoise μ ε 1) (ha₀ : 0 ≤ a₀) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b < 1) (t : ℤ) : MemLp (garchProcess a₀ a b ε t) 2 μ := by
  have hVmeas : Measurable (garchVariance a₀ a b ε t) :=
    (measurable_garchVariance_past t).mono (pastSigmaAlgebra_le hε.measurable _) le_rfl
  have hXmeas : Measurable (garchProcess a₀ a b ε t) :=
    (Real.continuous_sqrt.measurable.comp hVmeas).mul (hε.measurable t)
  have hindV2 : IndepFun (garchVariance a₀ a b ε t) (fun ω ↦ ε t ω ^ 2) μ :=
    (indepFun_of_measurable_pastSigmaAlgebra hε.measurable hε.iIndepFun t
      (measurable_garchVariance_past t)).comp measurable_id (measurable_id.pow_const 2)
  refine (memLp_two_iff_integrable_sq hXmeas.aestronglyMeasurable).2 ?_
  have := hindV2.integrable_mul (integrable_garchVariance hε ha hb hab t)
    (hε.memLp_two t).integrable_sq
  refine this.congr (ae_of_all _ fun ω ↦ ?_)
  simp only [garchProcess, Pi.mul_apply, mul_pow, Real.sq_sqrt (garchVariance_nonneg ha₀ ha hb _ _)]

/-- GAPS 106.18: the GARCH process with `a + b < 1` is weak white noise of variance
`a₀ / (1 - a - b)`: `Cov(X_s, X_t) = a₀ / (1 - a - b)` if `s = t` and `0` otherwise. -/
theorem covariance_garchProcess (hε : IsIIDNoise μ ε 1) (ha₀ : 0 ≤ a₀) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b < 1) (s t : ℤ) :
    covariance μ (garchProcess a₀ a b ε s) (garchProcess a₀ a b ε t) =
      if s = t then a₀ / (1 - a - b) else 0 := by
  set V := garchVariance a₀ a b ε
  set X := garchProcess a₀ a b ε
  have hm := hε.measurable
  have hind := hε.iIndepFun
  have hVmeasP : ∀ t, Measurable[pastSigmaAlgebra ε (t - 1)] (V t) := fun t ↦
    measurable_garchVariance_past t
  have hVmeas : ∀ t, Measurable (V t) := fun t ↦
    (hVmeasP t).mono (pastSigmaAlgebra_le hm _) le_rfl
  have hsqrtP : ∀ t, Measurable[pastSigmaAlgebra ε (t - 1)] fun ω ↦ Real.sqrt (V t ω) :=
    fun t ↦ Real.continuous_sqrt.measurable.comp (hVmeasP t)
  have hXP : ∀ s t, s < t → Measurable[pastSigmaAlgebra ε (t - 1)] (X s) := fun s t hst ↦
    (Real.continuous_sqrt.measurable.comp
      ((hVmeasP s).mono (pastSigmaAlgebra_mono ε (by omega)) le_rfl)).mul
      (measurable_pastSigmaAlgebra_of_le (by omega))
  have hEX : ∀ t, ∫ ω, X t ω ∂μ = 0 := fun t ↦ by
    have hind' := indepFun_of_measurable_pastSigmaAlgebra hm hind t (hsqrtP t)
    rw [show X t = (fun ω ↦ Real.sqrt (V t ω)) * ε t from rfl,
      IndepFun.integral_mul_eq_mul_integral hind'
        (Real.continuous_sqrt.measurable.comp (hVmeas t)).aestronglyMeasurable
        (hm t).aestronglyMeasurable, hε.integral_eq_zero' t, mul_zero]
  have hX2 : ∀ t, (fun ω ↦ X t ω * X t ω) = V t * fun ω ↦ ε t ω ^ 2 := fun t ↦ by
    funext ω
    simp only [X, V, garchProcess, Pi.mul_apply]
    rw [mul_mul_mul_comm, Real.mul_self_sqrt (garchVariance_nonneg ha₀ ha hb _ _), sq]
  have hindV2 : ∀ t, IndepFun (V t) (fun ω ↦ ε t ω ^ 2) μ := fun t ↦
    (indepFun_of_measurable_pastSigmaAlgebra hm hind t (hVmeasP t)).comp measurable_id
      (measurable_id.pow_const 2)
  have hEX2 : ∀ t, ∫ ω, X t ω * X t ω ∂μ = a₀ / (1 - a - b) := fun t ↦ by
    rw [hX2 t, IndepFun.integral_mul_eq_mul_integral (hindV2 t) (hVmeas t).aestronglyMeasurable
      ((hm t).pow_const 2).aestronglyMeasurable, integral_garchVariance hε ha hb hab,
      hε.integral_sq' t, mul_one]
  have hcross : ∀ s t, s < t → ∫ ω, X s ω * X t ω ∂μ = 0 := fun s t hst ↦ by
    have hmeasP : Measurable[pastSigmaAlgebra ε (t - 1)] fun ω ↦ X s ω * Real.sqrt (V t ω) :=
      (hXP s t hst).mul (hsqrtP t)
    have hind' := indepFun_of_measurable_pastSigmaAlgebra hm hind t hmeasP
    have hfun : (fun ω ↦ X s ω * X t ω) =
        (fun ω ↦ X s ω * Real.sqrt (V t ω)) * ε t := by
      funext ω; simp only [X, V, garchProcess, Pi.mul_apply]; ring
    rw [hfun, IndepFun.integral_mul_eq_mul_integral hind'
      ((hmeasP.mono (pastSigmaAlgebra_le hm _) le_rfl).aestronglyMeasurable)
      (hm t).aestronglyMeasurable, hε.integral_eq_zero' t, mul_zero]
  change ProbabilityTheory.covariance (X s) (X t) μ = _
  rw [covariance_eq_sub (memLp_garchProcess hε ha₀ ha hb hab s)
    (memLp_garchProcess hε ha₀ ha hb hab t), hEX s, hEX t, mul_zero, sub_zero]
  simp only [Pi.mul_apply]
  split_ifs with hst
  · subst hst; exact hEX2 s
  · rcases lt_or_gt_of_ne hst with h | h
    · exact hcross s t h
    · rw [← hcross t s h]
      exact integral_congr_ae (ae_of_all _ fun ω ↦ mul_comm _ _)

end Moments

end CKSD
