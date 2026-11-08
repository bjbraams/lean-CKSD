module

public import CKSD.Processes.Basic
public import CKSD.Asymptotics.Basic
public import CKSD.Nonparametric.Basic
public import CKSD.Processes.Dependence
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.MeasureTheory.Constructions.KolmogorovExtension
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Distributions.Gaussian.CharFun
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.Probability.Independence.Integration
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import TauCeti.Analysis.InnerProductSpace.LinearCombination

/-!
# Stationary GARCH series and moments

Products of lagged noise coefficients, past-measurability and independence, summability
of the stationary GARCH series, and its finite first/second moment identities.
The noise is indexed by all integers. Source: GAPS 106.18.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator
open scoped RealInnerProductSpace

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- A function measurable with respect to `σ(ε_s : s ∈ S)` is independent of `ε_k` for `k ∉ S`,
for an independent family `ε`. -/
theorem indepFun_of_measurable_iSup {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {ε : ℤ → Ω → ℝ} (hm : ∀ t, Measurable (ε t)) (hind : iIndepFun ε μ)
    {S : Set ℤ} {k : ℤ} (hk : k ∉ S) {Y : Ω → ℝ}
    (hY : Measurable[⨆ s ∈ S, MeasurableSpace.comap (ε s) inferInstance] Y) :
    IndepFun Y (ε k) μ := by
  have h := indep_iSup_of_disjoint (m := fun s ↦ MeasurableSpace.comap (ε s) inferInstance)
    (fun s ↦ (hm s).comap_le) hind.iIndep (S := S) (T := {k})
    (Set.disjoint_singleton_right.2 hk)
  rw [iSup_singleton] at h
  rw [IndepFun_iff_Indep]
  exact indep_of_indep_of_le_left h hY.comap_le

/-- A function of the strict past `σ(ε_s : s < t)` of an independent sequence is independent
of `ε_t`. -/
theorem indepFun_of_measurable_pastSigmaAlgebra {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {ε : ℤ → Ω → ℝ} (hm : ∀ t, Measurable (ε t)) (hind : iIndepFun ε μ)
    (t : ℤ) {Y : Ω → ℝ} (hY : Measurable[pastSigmaAlgebra ε (t - 1)] Y) :
    IndepFun Y (ε t) μ :=
  indepFun_of_measurable_iSup hm hind (S := {s | s ≤ t - 1}) (by simp) hY

/-- The coordinate `ε_s` is measurable with respect to the past `σ(ε_r : r ≤ t)` when `s ≤ t`. -/
theorem measurable_pastSigmaAlgebra_of_le {Ω : Type*}
    {ε : ℤ → Ω → ℝ} {s t : ℤ} (hst : s ≤ t) :
    Measurable[pastSigmaAlgebra ε t] (ε s) :=
  Measurable.of_comap_le (le_iSup₂_of_le s hst le_rfl)

/-- The past σ-algebras increase with time. -/
theorem pastSigmaAlgebra_mono {Ω : Type*} (ε : ℤ → Ω → ℝ) {s t : ℤ} (hst : s ≤ t) :
    pastSigmaAlgebra ε s ≤ pastSigmaAlgebra ε t :=
  iSup₂_le fun r hr ↦ le_iSup₂_of_le r (hr.trans hst) le_rfl

/-- The past σ-algebras of a measurable process are sub-σ-algebras. -/
theorem pastSigmaAlgebra_le {Ω : Type*} [MeasurableSpace Ω] {ε : ℤ → Ω → ℝ}
    (hm : ∀ t, Measurable (ε t)) (t : ℤ) : pastSigmaAlgebra ε t ≤ ‹MeasurableSpace Ω› :=
  iSup₂_le fun r _ ↦ (hm r).comap_le

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
theorem measurable_garchTerm_iSup {Ω : Type*} (a b : ℝ)
    (ε : ℤ → Ω → ℝ) (t : ℤ) (n : ℕ) {S : Set ℤ} (hS : ∀ j < n, t - j - 1 ∈ S) :
    Measurable[⨆ s ∈ S, MeasurableSpace.comap (ε s) inferInstance] (garchTerm a b ε t n) := by
  unfold garchTerm garchCoeff
  refine Finset.measurable_prod _ fun j hj ↦ ?_
  have : Measurable[⨆ s ∈ S, MeasurableSpace.comap (ε s) inferInstance] (ε (t - j - 1)) :=
    Measurable.of_comap_le (le_iSup₂_of_le (t - j - 1) (hS j (Finset.mem_range.1 hj)) le_rfl)
  exact measurable_const.add (measurable_const.mul (this.pow_const 2))

/-- The GARCH product of length `n` is integrable with mean `(b + a)^n`, by independence of the
noise at distinct times. -/
theorem integrable_garchTerm_and_integral {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ε : ℤ → Ω → ℝ}
    (hm : ∀ t, Measurable (ε t)) (hind : iIndepFun ε μ)
    (hlaw : ∀ t, μ.map (ε t) = μ.map (ε 0)) (h2 : MemLp (ε 0) 2 μ)
    (h1 : (∫ ω, ε 0 ω ^ 2 ∂μ) = 1) (a b : ℝ) (t : ℤ) (n : ℕ) :
    Integrable (garchTerm a b ε t n) μ ∧ ∫ ω, garchTerm a b ε t n ω ∂μ = (b + a) ^ n := by
  have hsq : ∀ k, Integrable (fun ω ↦ ε k ω ^ 2) μ ∧ ∫ ω, ε k ω ^ 2 ∂μ = 1 := by
    intro k
    have hid : IdentDistrib (ε k) (ε 0) μ μ :=
      ⟨(hm k).aemeasurable, (hm 0).aemeasurable, hlaw k⟩
    have hid2 := hid.comp (measurable_id.pow_const 2)
    refine ⟨?_, ?_⟩
    · exact hid2.integrable_iff.2 (h2.integrable_sq)
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
    have hY := measurable_garchTerm_iSup a b ε t n (S := {s | t - n ≤ s})
      (fun j hj ↦ by simp only [mem_ofPred_eq]; omega)
    have hindep : IndepFun (garchTerm a b ε t n) (garchCoeff a b ε t n) μ := by
      have := (indepFun_of_measurable_iSup hm hind (k := t - n - 1)
        (by simp only [mem_ofPred_eq]; omega) hY).comp measurable_id
          (measurable_const.add (measurable_const.mul (measurable_id.pow_const 2)) :
            Measurable fun x : ℝ ↦ b + a * x ^ 2)
      exact this
    rw [hfun]
    refine ⟨hindep.integrable_mul ih.1 (hcoeff n).1, ?_⟩
    rw [IndepFun.integral_mul_eq_mul_integral hindep ih.1.aestronglyMeasurable
      (hcoeff n).1.aestronglyMeasurable, ih.2, (hcoeff n).2, pow_succ]


/-- When `a + b < 1`, the GARCH series `∑_n ∏_{j<n} (b + a ε_{t-j-1}²)` converges almost surely,
is integrable, and has mean `(1 - (b + a))⁻¹`; the proof uses monotone convergence. -/
theorem garch_tsum_properties {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ε : ℤ → Ω → ℝ}
    (hm : ∀ t, Measurable (ε t)) (hind : iIndepFun ε μ)
    (hlaw : ∀ t, μ.map (ε t) = μ.map (ε 0)) (h2 : MemLp (ε 0) 2 μ)
    (h1 : (∫ ω, ε 0 ω ^ 2 ∂μ) = 1) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b < 1)
    (t : ℤ) :
    (∀ᵐ ω ∂μ, Summable fun n ↦ garchTerm a b ε t n ω) ∧
      Integrable (fun ω ↦ ∑' n, garchTerm a b ε t n ω) μ ∧
      ∫ ω, ∑' n, garchTerm a b ε t n ω ∂μ = (1 - (b + a))⁻¹ := by
  have hI := integrable_garchTerm_and_integral hm hind hlaw h2 h1 a b t
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


/-- First and second moments of the GARCH noise at every time. -/
theorem garch_noise_moments {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ε : ℤ → Ω → ℝ}
    (hm : ∀ t, Measurable (ε t)) (hlaw : ∀ t, μ.map (ε t) = μ.map (ε 0)) (h2 : MemLp (ε 0) 2 μ)
    (h0 : (∫ ω, ε 0 ω ∂μ) = 0) (h1 : (∫ ω, ε 0 ω ^ 2 ∂μ) = 1) (k : ℤ) :
    Integrable (ε k) μ ∧ ∫ ω, ε k ω ∂μ = 0 ∧
      Integrable (fun ω ↦ ε k ω ^ 2) μ ∧ ∫ ω, ε k ω ^ 2 ∂μ = 1 := by
  have hid : IdentDistrib (ε k) (ε 0) μ μ :=
    ⟨(hm k).aemeasurable, (hm 0).aemeasurable, hlaw k⟩
  have hid2 := hid.comp (measurable_id.pow_const 2)
  refine ⟨hid.integrable_iff.2 (h2.integrable one_le_two), by rw [← h0]; exact hid.integral_eq,
    hid2.integrable_iff.2 h2.integrable_sq, ?_⟩
  rw [← h1]; exact hid2.integral_eq

/-- The GARCH series at time `t` is a function of the strict past of the noise. -/
theorem measurable_tsum_garchTerm_past {Ω : Type*} (a b : ℝ) (ε : ℤ → Ω → ℝ) (t : ℤ) :
    Measurable[pastSigmaAlgebra ε (t - 1)] fun ω ↦ ∑' n, garchTerm a b ε t n ω := by
  let _ := pastSigmaAlgebra ε (t - 1)
  exact Measurable.tsum fun n ↦ measurable_garchTerm a b ε t n

/-- GAPS 106.18, finite-variance GARCH series when `alpha + beta < 1`. -/
theorem garch_series_summable_and_moments {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ε : ℤ → Ω → ℝ)
    (hm : ∀ t, Measurable (ε t)) (hind : iIndepFun ε μ)
    (hlaw : ∀ t, μ.map (ε t) = μ.map (ε 0)) (h2 : MemLp (ε 0) 2 μ)
    (h0 : (∫ ω, ε 0 ω ∂μ) = 0) (h1 : (∫ ω, ε 0 ω ^ 2 ∂μ) = 1)
    (a₀ a b : ℝ) (ha₀ : 0 < a₀) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b < 1) :
    let V := fun t ω ↦ a₀ * ∑' n : ℕ,
      ∏ j ∈ Finset.range n, (b + a * ε (t - j - 1) ω ^ 2);
    let X := fun t ω ↦ Real.sqrt (V t ω) * ε t ω;
    (∀ t, ∀ᵐ ω ∂μ, Summable (fun n : ℕ ↦
      ∏ j ∈ Finset.range n, (b + a * ε (t - j - 1) ω ^ 2))) ∧
      (∀ t, (∫ ω, V t ω ∂μ) = a₀ / (1 - a - b)) ∧
      (∀ t, ∀ᵐ ω ∂μ, V t ω = a₀ + a * X (t - 1) ω ^ 2 + b * V (t - 1) ω) ∧
      ∀ s t, covariance μ (X s) (X t) = if s = t then a₀ / (1 - a - b) else 0 := by
  intro V X
  have props := garch_tsum_properties hm hind hlaw h2 h1 ha hb hab
  have hV : ∀ t, V t = fun ω ↦ a₀ * ∑' n, garchTerm a b ε t n ω := fun t ↦ rfl
  have hab' : 1 - a - b ≠ 0 := by linarith
  have hVint : ∀ t, ∫ ω, V t ω ∂μ = a₀ / (1 - a - b) := fun t ↦ by
    rw [hV, integral_const_mul, (props t).2.2, div_eq_mul_inv]
    ring_nf
  have hVnn : ∀ t ω, 0 ≤ V t ω := fun t ω ↦
    mul_nonneg ha₀.le (tsum_nonneg fun n ↦ garchTerm_nonneg ha hb ε t n ω)
  refine ⟨fun t ↦ (props t).1, hVint, fun t ↦ ?_, fun s t ↦ ?_⟩
  · filter_upwards [(props (t - 1)).1] with ω hω
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
    have hX2 : X (t - 1) ω ^ 2 = V (t - 1) ω * ε (t - 1) ω ^ 2 := by
      simp only [X, mul_pow, Real.sq_sqrt (hVnn _ _)]
    rw [hX2, hV, hV]
    simp only
    rw [hsumt.tsum_eq_zero_add]
    simp_rw [hshift]
    rw [tsum_mul_right]
    simp only [garchTerm, Finset.range_zero, Finset.prod_empty]
    ring
  have hVmeasP : ∀ t, Measurable[pastSigmaAlgebra ε (t - 1)] (V t) := fun t ↦
    (measurable_tsum_garchTerm_past a b ε t).const_mul a₀
  have hVmeas : ∀ t, Measurable (V t) := fun t ↦
    (hVmeasP t).mono (pastSigmaAlgebra_le hm _) le_rfl
  have hVint' : ∀ t, Integrable (V t) μ := fun t ↦ (props t).2.1.const_mul a₀
  have hnoise := garch_noise_moments hm hlaw h2 h0 h1
  have hsqrtP : ∀ t, Measurable[pastSigmaAlgebra ε (t - 1)] fun ω ↦ Real.sqrt (V t ω) :=
    fun t ↦ Real.continuous_sqrt.measurable.comp (hVmeasP t)
  have hXmeas : ∀ t, Measurable (X t) := fun t ↦
    (Real.continuous_sqrt.measurable.comp (hVmeas t)).mul (hm t)
  have hXP : ∀ s t, s < t → Measurable[pastSigmaAlgebra ε (t - 1)] (X s) := fun s t hst ↦
    (Real.continuous_sqrt.measurable.comp
      ((hVmeasP s).mono (pastSigmaAlgebra_mono ε (by omega)) le_rfl)).mul
      (measurable_pastSigmaAlgebra_of_le (by omega))
  have hEX : ∀ t, ∫ ω, X t ω ∂μ = 0 := fun t ↦ by
    have hind' := indepFun_of_measurable_pastSigmaAlgebra hm hind t (hsqrtP t)
    rw [show X t = (fun ω ↦ Real.sqrt (V t ω)) * ε t from rfl,
      IndepFun.integral_mul_eq_mul_integral hind'
        (Real.continuous_sqrt.measurable.comp (hVmeas t)).aestronglyMeasurable
        (hm t).aestronglyMeasurable, (hnoise t).2.1, mul_zero]
  have hX2 : ∀ t, (fun ω ↦ X t ω * X t ω) = V t * fun ω ↦ ε t ω ^ 2 := fun t ↦ by
    funext ω
    simp only [X, Pi.mul_apply]
    rw [mul_mul_mul_comm, Real.mul_self_sqrt (hVnn _ _), sq]
  have hindV2 : ∀ t, IndepFun (V t) (fun ω ↦ ε t ω ^ 2) μ := fun t ↦
    (indepFun_of_measurable_pastSigmaAlgebra hm hind t (hVmeasP t)).comp measurable_id
      (measurable_id.pow_const 2)
  have hXL2 : ∀ t, MemLp (X t) 2 μ := fun t ↦ by
    refine (memLp_two_iff_integrable_sq (hXmeas t).aestronglyMeasurable).2 ?_
    have := (hindV2 t).integrable_mul (hVint' t) (hnoise t).2.2.1
    rw [← hX2 t] at this
    simpa only [sq] using this
  have hEX2 : ∀ t, ∫ ω, X t ω * X t ω ∂μ = a₀ / (1 - a - b) := fun t ↦ by
    rw [hX2 t, IndepFun.integral_mul_eq_mul_integral (hindV2 t) (hVmeas t).aestronglyMeasurable
      ((hm t).pow_const 2).aestronglyMeasurable, hVint, (hnoise t).2.2.2, mul_one]
  have hcross : ∀ s t, s < t → ∫ ω, X s ω * X t ω ∂μ = 0 := fun s t hst ↦ by
    have hmeasP : Measurable[pastSigmaAlgebra ε (t - 1)] fun ω ↦ X s ω * Real.sqrt (V t ω) :=
      (hXP s t hst).mul (hsqrtP t)
    have hind' := indepFun_of_measurable_pastSigmaAlgebra hm hind t hmeasP
    have hfun : (fun ω ↦ X s ω * X t ω) =
        (fun ω ↦ X s ω * Real.sqrt (V t ω)) * ε t := by
      funext ω; simp only [X, Pi.mul_apply]; ring
    rw [hfun, IndepFun.integral_mul_eq_mul_integral hind'
      ((hmeasP.mono (pastSigmaAlgebra_le hm _) le_rfl).aestronglyMeasurable)
      (hm t).aestronglyMeasurable, (hnoise t).2.1, mul_zero]
  change ProbabilityTheory.covariance (X s) (X t) μ = _
  rw [covariance_eq_sub (hXL2 s) (hXL2 t), hEX s, hEX t, mul_zero, sub_zero]
  simp only [Pi.mul_apply]
  split_ifs with hst
  · subst hst; exact hEX2 s
  · rcases lt_or_gt_of_ne hst with h | h
    · exact hcross s t h
    · simp_rw [mul_comm (X s _)]
      exact hcross t s h


end CKSD
