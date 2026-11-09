module

public import CKSD.Processes.RiskSetExpansion
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
public import TauCeti.Algebra.Order.BigOperators.ProdSubProd

/-!
# Nelson–Aalen and Kaplan–Meier estimators under random censoring

Central limit theorems at a fixed time for the Nelson–Aalen estimator of the cumulative hazard
and the Kaplan–Meier estimator of the survival function, from independent copies of a failure
time `T` with law `F` and an independent censoring time `C` with law `C₀`, both nonnegative.
The failure law has a Lebesgue density `f`, so that `Λ(t) = ∫_0^t f / (1 - F)` and the at-risk
probability is `y(s) = P(min(T, C) ≥ s) = (1 - F(s)) C₀[s, ∞)`.

## Main definitions

* `CKSD.IsRandomCensoringModel`: the observations `(T i, C i)` are iid with law `F ⊗ C₀`, and
  `F`, `C₀` are concentrated on `[0, ∞)`.

## Main results

* `CKSD.tendstoInDistribution_nelsonAalenEstimator` (GAPS 106.28):
  `√n (Λ̂_n(t) - Λ(t)) ⇒ N(0, ∫_0^t dΛ / y)`.
* `CKSD.tendstoInDistribution_kaplanMeierEstimator` (GAPS 106.29):
  `√n (Ŝ_n(t) - S(t)) ⇒ N(0, S(t)² ∫_0^t dΛ / y)`.

Auxiliary results on laws with a density: `CKSD.one_sub_cdf_eq_measureReal_Ici_of_hasDensity`,
`CKSD.cdf_eq_intervalIntegral_of_hasDensity`, and
`CKSD.one_sub_cdf_eq_exp_neg_integral_of_hasDensity` (`1 - F(t) = exp (-Λ(t))`, by the
fundamental theorem of calculus for absolutely continuous functions).

## Implementation notes

The Nelson–Aalen estimator is a risk-set sum `∑ A(Zᵢ) / #{j : x(Zⱼ) ≥ x(Zᵢ)}`, and its
central limit theorem is `CKSD.tendstoInDistribution_sqrt_mul_riskSetSum_sub` (a Hájek
expansion); the work here identifies the centring constant with `Λ(t)` and the variance of the
influence function with `∫_0^t dΛ / y`. The Kaplan–Meier theorem follows by the delta method
for `u ↦ exp (-u)`, since `|Ŝ_n(t) - exp (-Λ̂_n(t))| ≤ n / #{j : min(T j, C j) ≥ t}²`, which is
`O_P(1 / n)` by the law of large numbers.

The process-level convergence in the Skorokhod space `D[0, τ]` and Greenwood's variance
estimator are not stated.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace CKSD

/-- The random censoring model: the pairs `(T i, C i)` of failure and censoring times are
independent copies with law `F ⊗ C₀` (so failure and censoring are independent), and both laws
are concentrated on `[0, ∞)`. -/
structure IsRandomCensoringModel {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (F C₀ : Measure ℝ) (T C : ℕ → Ω → ℝ) : Prop where
  /-- The pairs `(T i, C i)` are iid with the product law `F ⊗ C₀`. -/
  iid : IsIndependentIdenticallyDistributed μ (fun i ω ↦ (T i ω, C i ω)) (F.prod C₀)
  /-- Failure times are nonnegative. -/
  failure_nonneg : F (Ici 0) = 1
  /-- Censoring times are nonnegative. -/
  censoring_nonneg : C₀ (Ici 0) = 1

/-- A law with a Lebesgue density has no atoms, so `1 - F(s) = F[s, ∞)`. -/
theorem one_sub_cdf_eq_measureReal_Ici_of_hasDensity (F : Measure ℝ) [IsProbabilityMeasure F]
    (f : ℝ → ℝ) (hf : HasDensity F volume f) (s : ℝ) : 1 - cdf F s = F.real (Ici s) := by
  have hsing : F {s} = 0 := by
    rw [hf.2.2, withDensity_apply _ (measurableSet_singleton s), Measure.restrict_singleton]
    simp
  have h1 : F.real (Iic s) + F.real (Ioi s) = 1 := by
    rw [← measureReal_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi, Iic_union_Ioi,
      probReal_univ]
  have h2 : F.real (Ici s) = F.real (Ioi s) := by
    exact measureReal_congr (Ioi_ae_eq_Ici' hsing).symm
  rw [cdf_eq_real, h2]
  linarith

/-- Integration against a law with a real density `f`: `∫ g dF = ∫ f g`. -/
theorem integral_eq_integral_mul_of_hasDensity (F : Measure ℝ) (f : ℝ → ℝ)
    (hf : HasDensity F volume f) (g : ℝ → ℝ) : ∫ s, g s ∂F = ∫ s, f s * g s := by
  rw [hf.2.2, integral_withDensity_eq_integral_toReal_smul hf.1.ennreal_ofReal
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  refine integral_congr_ae ?_
  filter_upwards [hf.2.1] with s hs
  simp [ENNReal.toReal_ofReal hs]

/-- Under random censoring, `∫ 1{T ≤ C} φ(T) d(F ⊗ C₀) = ∫ f(s) φ(s) C₀[s, ∞) ds` for a bounded
measurable `φ` and a density `f` of `F`. -/
theorem integral_ite_fst_le_snd_prod (F C₀ : Measure ℝ) [IsProbabilityMeasure F]
    [IsProbabilityMeasure C₀] (f : ℝ → ℝ) (hf : HasDensity F volume f) (φ : ℝ → ℝ)
    (hφ : Measurable φ) (M : ℝ) (hM : ∀ s, |φ s| ≤ M) :
    ∫ z, (if z.1 ≤ z.2 then φ z.1 else 0) ∂(F.prod C₀) =
      ∫ s, f s * (φ s * C₀.real (Ici s)) := by
  have hm : Measurable fun z : ℝ × ℝ ↦ if z.1 ≤ z.2 then φ z.1 else 0 :=
    Measurable.ite (measurableSet_le measurable_fst measurable_snd) (hφ.comp measurable_fst)
      measurable_const
  have hint : Integrable (fun z : ℝ × ℝ ↦ if z.1 ≤ z.2 then φ z.1 else 0) (F.prod C₀) :=
    Integrable.of_bound hm.aestronglyMeasurable M (ae_of_all _ fun z ↦ by
      rw [Real.norm_eq_abs]
      split_ifs
      · exact hM _
      · simpa using (abs_nonneg _).trans (hM 0))
  rw [integral_prod _ hint]
  have hinner (a : ℝ) : ∫ c, (if a ≤ c then φ a else 0) ∂C₀ = φ a * C₀.real (Ici a) := by
    have : (fun c ↦ if a ≤ c then φ a else 0) = (Ici a).indicator fun _ ↦ φ a := by
      funext c; simp [Set.indicator_apply]
    rw [this, integral_indicator_const _ measurableSet_Ici, smul_eq_mul, mul_comm]
  simp_rw [hinner]
  exact integral_eq_integral_mul_of_hasDensity F f hf _

/-- The at-risk probability under random censoring:
`P(min(T, C) ≥ s) = F[s, ∞) C₀[s, ∞)`. -/
theorem measureReal_le_min_prod (F C₀ : Measure ℝ) [IsProbabilityMeasure F]
    [IsProbabilityMeasure C₀] (s : ℝ) :
    (F.prod C₀).real {z | s ≤ min z.1 z.2} = F.real (Ici s) * C₀.real (Ici s) := by
  have : {z : ℝ × ℝ | s ≤ min z.1 z.2} = Ici s ×ˢ Ici s := by
    ext z; simp only [mem_ofPred_eq, le_min_iff, mem_prod, mem_Ici]
  rw [this, measureReal_prod_prod]

/-- A density of a law concentrated on `[0, ∞)` vanishes almost everywhere on `(-∞, 0)`. -/
theorem ae_eq_zero_of_hasDensity_of_measure_Ici (F : Measure ℝ) [IsProbabilityMeasure F]
    (f : ℝ → ℝ) (hf : HasDensity F volume f) (hF : F (Ici 0) = 1) :
    ∀ᵐ s, s < 0 → f s = 0 := by
  have hIio : F (Iio 0) = 0 := by
    rw [← compl_Ici, prob_compl_eq_zero_iff measurableSet_Ici]
    exact hF
  rw [hf.2.2, withDensity_apply _ measurableSet_Iio,
    setLIntegral_eq_zero_iff measurableSet_Iio hf.1.ennreal_ofReal] at hIio
  filter_upwards [hIio, hf.2.1] with s hs h0 hneg
  have := hs hneg
  rw [ENNReal.ofReal_eq_zero] at this
  linarith

/-- For an integrable `g` on `ℝ`, `(∫ g)² = 2 ∫ g(s) ∫_{r ≤ s} g(r) dr ds`: the square splits
into the two triangles `r ≤ s` and `s < r`, which agree after swapping the variables because
the diagonal is Lebesgue-null. -/
theorem sq_integral_eq_two_mul_integral_mul_integral_le (g : ℝ → ℝ) (hg : Integrable g) :
    (∫ s, g s) ^ 2 = 2 * ∫ s, g s * ∫ r, g r * (if r ≤ s then 1 else 0) := by
  have hgm := hg.aestronglyMeasurable
  have hprod : Integrable (fun p : ℝ × ℝ ↦ g p.1 * g p.2) (volume.prod volume) := hg.mul_prod hg
  have hI (G : ℝ × ℝ → ℝ) (hG : Measurable G) (hG1 : ∀ p, |G p| ≤ 1) :
      Integrable (fun p : ℝ × ℝ ↦ g p.1 * g p.2 * G p) (volume.prod volume) :=
    hprod.mul_bdd (c := 1) hG.aestronglyMeasurable (ae_of_all _ fun p ↦ by
      rw [Real.norm_eq_abs]; exact hG1 p) |>.congr (ae_of_all _ fun p ↦ rfl)
  have hJm : Measurable fun p : ℝ × ℝ ↦ (if p.1 < p.2 then (1 : ℝ) else 0) :=
    Measurable.ite (measurableSet_lt measurable_fst measurable_snd) measurable_const
      measurable_const
  have hJ1 (p : ℝ × ℝ) : |(if p.1 < p.2 then (1 : ℝ) else 0)| ≤ 1 := by split_ifs <;> simp
  -- split the square
  have hsplit : (∫ s, g s) ^ 2 = (∫ s, g s * ∫ r, g r * (if r ≤ s then 1 else 0)) +
      ∫ s, ∫ r, g s * g r * (if s < r then 1 else 0) := by
    have hIm : Measurable fun p : ℝ × ℝ ↦ (if p.2 ≤ p.1 then (1 : ℝ) else 0) :=
      Measurable.ite (measurableSet_le measurable_snd measurable_fst) measurable_const
        measurable_const
    have hI1 (p : ℝ × ℝ) : |(if p.2 ≤ p.1 then (1 : ℝ) else 0)| ≤ 1 := by split_ifs <;> simp
    have hA := (hI _ hIm hI1).integral_prod_left
    have hB := (hI _ hJm hJ1).integral_prod_left
    simp only at hA hB
    have hin (s : ℝ) (G : ℝ → ℝ) (hG : Measurable G) (hG1 : ∀ r, |G r| ≤ 1) :
        Integrable (fun r ↦ g s * g r * G r) :=
      (hg.const_mul (g s)).mul_bdd (c := 1) hG.aestronglyMeasurable
        (ae_of_all _ fun r ↦ by rw [Real.norm_eq_abs]; exact hG1 r)
    have hIs (s : ℝ) : Measurable fun r : ℝ ↦ (if r ≤ s then (1 : ℝ) else 0) :=
      Measurable.ite (measurableSet_le measurable_id measurable_const) measurable_const
        measurable_const
    have hJs (s : ℝ) : Measurable fun r : ℝ ↦ (if s < r then (1 : ℝ) else 0) :=
      Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_const
        measurable_const
    calc (∫ s, g s) ^ 2 = ∫ s, ∫ r, g s * g r := by
          rw [sq, ← integral_mul_const]
          exact integral_congr_ae (ae_of_all _ fun s ↦ (integral_const_mul _ _).symm)
      _ = ∫ s, ((∫ r, g s * g r * (if r ≤ s then 1 else 0)) +
            ∫ r, g s * g r * (if s < r then 1 else 0)) := by
          refine integral_congr_ae (ae_of_all _ fun s ↦ ?_)
          simp only
          rw [← integral_add (hin s _ (hIs s) fun r ↦ by split_ifs <;> simp)
            (hin s _ (hJs s) fun r ↦ by split_ifs <;> simp)]
          refine integral_congr_ae (ae_of_all _ fun r ↦ ?_)
          by_cases h : r ≤ s
          · simp [h, not_lt.2 h]
          · simp [h, lt_of_not_ge h]
      _ = (∫ s, ∫ r, g s * g r * (if r ≤ s then 1 else 0)) +
            ∫ s, ∫ r, g s * g r * (if s < r then 1 else 0) := integral_add hA hB
      _ = _ := by
          congr 1
          refine integral_congr_ae (ae_of_all _ fun s ↦ ?_)
          simp only
          rw [← integral_const_mul]
          exact integral_congr_ae (ae_of_all _ fun r ↦ by ring)
  -- swap the second triangle
  have hswap : ∫ s, ∫ r, g s * g r * (if s < r then (1 : ℝ) else 0) =
      ∫ s, g s * ∫ r, g r * (if r ≤ s then 1 else 0) := by
    rw [integral_integral_swap (f := fun s r ↦ g s * g r * (if s < r then (1 : ℝ) else 0))
      (hI _ hJm hJ1)]
    refine integral_congr_ae (ae_of_all _ fun s ↦ ?_)
    simp only
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    have hne : ∀ᵐ r : ℝ, r ≠ s := by
      simp [ae_iff]
    filter_upwards [hne] with r hr
    by_cases h : r < s
    · simp [h, h.le, mul_comm]
    · have h' : ¬ r ≤ s := fun h'' ↦ h (lt_of_le_of_ne h'' hr)
      simp [h, h']
  rw [hsplit, hswap]
  ring

/-- For an integrable measurable `k` and `c(u) = ∫_{s ≤ u} k`, the second moment of `c(x)` under
a probability measure `P` is `2 ∫ k(s) P(x ≥ s) c(s) ds`. -/
theorem integral_sq_integral_mul_ite_le {E : Type*} [MeasurableSpace E] (P : Measure E)
    [IsProbabilityMeasure P] (x : E → ℝ) (hx : Measurable x) (k : ℝ → ℝ) (hkm : Measurable k)
    (hk : Integrable k) :
    ∫ z, (∫ s, k s * (if s ≤ x z then 1 else 0)) ^ 2 ∂P =
      2 * ∫ s, k s * P.real {z | s ≤ x z} * ∫ r, k r * (if r ≤ s then 1 else 0) := by
  set c : ℝ → ℝ := fun s ↦ ∫ r, k r * (if r ≤ s then 1 else 0) with hc
  have hcm : Measurable c := by
    have hm : Measurable fun p : ℝ × ℝ ↦ k p.2 * (if p.2 ≤ p.1 then (1 : ℝ) else 0) :=
      (hkm.comp measurable_snd).mul (Measurable.ite (measurableSet_le measurable_snd
        measurable_fst) measurable_const measurable_const)
    exact (StronglyMeasurable.integral_prod_right' (ν := volume) hm.stronglyMeasurable).measurable
  set K := ∫ r, |k r| with hK
  have hcb (s : ℝ) : |c s| ≤ K := by
    refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
      (ae_of_all _ fun _ ↦ abs_nonneg _) hk.abs (ae_of_all _ fun r ↦ ?_))
    simp only [abs_mul]
    split_ifs <;> simp
  -- the square for a fixed `z`
  have hpt (z : E) : (∫ s, k s * (if s ≤ x z then 1 else 0)) ^ 2 =
      2 * ∫ s, k s * (if s ≤ x z then 1 else 0) * c s := by
    have hgi : Integrable fun s ↦ k s * (if s ≤ x z then (1 : ℝ) else 0) :=
      hk.mul_bdd (c := 1) (Measurable.ite (measurableSet_le measurable_id measurable_const)
        measurable_const measurable_const).aestronglyMeasurable
        (ae_of_all _ fun s ↦ by split_ifs <;> simp)
    rw [sq_integral_eq_two_mul_integral_mul_integral_le _ hgi]
    congr 1
    refine integral_congr_ae (ae_of_all _ fun s ↦ ?_)
    by_cases hs : s ≤ x z
    · simp only [hs, ↓reduceIte, mul_one, hc]
      congr 1
      refine integral_congr_ae (ae_of_all _ fun r ↦ ?_)
      by_cases hr : r ≤ s
      · simp [hr, hr.trans hs]
      · simp [hr]
    · simp [hs]
  simp_rw [hpt]
  rw [integral_const_mul]
  congr 1
  have hFm : Measurable fun p : E × ℝ ↦ k p.2 * (if p.2 ≤ x p.1 then (1 : ℝ) else 0) * c p.2 :=
    ((hkm.comp measurable_snd).mul (Measurable.ite (measurableSet_le measurable_snd
      (hx.comp measurable_fst)) measurable_const measurable_const)).mul (hcm.comp measurable_snd)
  have hFi : Integrable (fun p : E × ℝ ↦ k p.2 * (if p.2 ≤ x p.1 then (1 : ℝ) else 0) * c p.2)
      (P.prod volume) := by
    refine Integrable.mono' (((integrable_const (1 : ℝ)).mul_prod hk.abs).mul_const K)
      hFm.aestronglyMeasurable (ae_of_all _ fun p ↦ ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, one_mul]
    refine mul_le_mul ?_ (hcb _) (abs_nonneg _) (abs_nonneg _)
    split_ifs <;> simp
  rw [integral_integral_swap (f := fun z s ↦ k s * (if s ≤ x z then (1 : ℝ) else 0) * c s) hFi]
  refine integral_congr_ae (ae_of_all _ fun s ↦ ?_)
  have hS : MeasurableSet {z | s ≤ x z} := measurableSet_le measurable_const hx
  have hind : (fun z ↦ (if s ≤ x z then (1 : ℝ) else 0)) = {z | s ≤ x z}.indicator 1 := by
    funext z; simp [Set.indicator_apply]
  simp only
  simp_rw [mul_comm (k s), mul_assoc]
  rw [integral_mul_const, hind, integral_indicator_one hS]

/-- For a density `f` of a law on `[0, ∞)` and `t ≥ 0`,
`∫ 1{s ≤ t} f(s) G(s) ds = ∫_0^t f G`. -/
theorem integral_ite_le_mul_eq_intervalIntegral (F : Measure ℝ) [IsProbabilityMeasure F]
    (f : ℝ → ℝ) (hf : HasDensity F volume f) (hF : F (Ici 0) = 1) (G : ℝ → ℝ) (t : ℝ)
    (ht : 0 ≤ t) :
    ∫ s, (if s ≤ t then f s * G s else 0) = ∫ s in (0 : ℝ)..t, f s * G s := by
  rw [intervalIntegral.integral_of_le ht, ← integral_indicator measurableSet_Ioc]
  have h0 := ae_eq_zero_of_hasDensity_of_measure_Ici F f hf hF
  have hne : ∀ᵐ s : ℝ, s ≠ 0 := by simp [ae_iff]
  refine integral_congr_ae ?_
  filter_upwards [h0, hne] with s hs hs0
  by_cases hst : s ≤ t
  · by_cases hpos : 0 < s
    · simp [hst, hpos]
    · have hneg : s < 0 := lt_of_le_of_ne (not_lt.1 hpos) hs0
      simp [hst, hpos, hs hneg]
  · simp [hst]
/-- Positivity and monotonicity of the at-risk probabilities `F[s, ∞)`, `C₀[s, ∞)` and of
`y(s) = F[s, ∞) C₀[s, ∞)` up to a time `t` with `F[t, ∞) C₀[t, ∞) > 0`. -/
private theorem atRisk_bounds (F C₀ : Measure ℝ) [IsProbabilityMeasure F]
    [IsProbabilityMeasure C₀] {t : ℝ} (hrisk : 0 < F (Ici t) * C₀ (Ici t)) :
    0 < F.real (Ici t) * C₀.real (Ici t) ∧ ∀ s ≤ t, 0 < F.real (Ici s) ∧ 0 < C₀.real (Ici s) ∧
      F.real (Ici t) * C₀.real (Ici t) ≤ F.real (Ici s) * C₀.real (Ici s) := by
  rcases ENNReal.mul_pos_iff.1 hrisk with ⟨h1, h2⟩
  have hFt : 0 < F.real (Ici t) := ENNReal.toReal_pos h1.ne' (measure_ne_top _ _)
  have hCt : 0 < C₀.real (Ici t) := ENNReal.toReal_pos h2.ne' (measure_ne_top _ _)
  refine ⟨mul_pos hFt hCt, fun s hs ↦ ?_⟩
  have hF : F.real (Ici t) ≤ F.real (Ici s) := measureReal_mono (Ici_subset_Ici.2 hs)
  have hC : C₀.real (Ici t) ≤ C₀.real (Ici s) := measureReal_mono (Ici_subset_Ici.2 hs)
  exact ⟨hFt.trans_le hF, hCt.trans_le hC, mul_le_mul hF hC hCt.le measureReal_nonneg⟩

/-- In the random censoring model, integrals of `A(z) Φ(min(z₁, z₂))`, with `A` the indicator
of an observed failure by time `t`, are integrals against the failure density:
`∫ A Φ(x) d(F ⊗ C₀) = ∫ f(s) 1{s ≤ t} Φ(s) C₀[s, ∞) ds` for `Φ` bounded on `(-∞, t]`. -/
private theorem integral_failureIndicator_mul (F C₀ : Measure ℝ) [IsProbabilityMeasure F]
    [IsProbabilityMeasure C₀] (f : ℝ → ℝ) (hf : HasDensity F volume f) (t : ℝ) (Φ : ℝ → ℝ)
    (hΦ : Measurable Φ) (M : ℝ) (hM : ∀ s, s ≤ t → |Φ s| ≤ M) :
    ∫ z, (if z.1 ≤ z.2 ∧ z.1 ≤ t then (1 : ℝ) else 0) * Φ (min z.1 z.2) ∂(F.prod C₀) =
      ∫ s, f s * ((if s ≤ t then Φ s else 0) * C₀.real (Ici s)) := by
  have hpt : (fun z : ℝ × ℝ ↦ (if z.1 ≤ z.2 ∧ z.1 ≤ t then (1 : ℝ) else 0) * Φ (min z.1 z.2)) =
      fun z : ℝ × ℝ ↦ if z.1 ≤ z.2 then (if z.1 ≤ t then Φ z.1 else 0) else 0 := by
    funext z
    by_cases h1 : z.1 ≤ z.2
    · simp only [h1, true_and, min_eq_left h1, ↓reduceIte]
      split_ifs <;> simp
    · simp [h1]
  rw [hpt]
  refine integral_ite_fst_le_snd_prod F C₀ f hf _ (Measurable.ite (measurableSet_le
    measurable_id measurable_const) hΦ measurable_const) (max M 0) fun s ↦ ?_
  split_ifs with hs
  · exact (hM s hs).trans (le_max_left _ _)
  · simp

/-- The kernel `f(s) 1{s ≤ t} C₀[s, ∞) / y(s)²` of the Nelson–Aalen variance, with
`y(s) = F[s, ∞) C₀[s, ∞)` and `y(t) > 0`, is integrable. -/
private theorem integrable_atRiskKernel (F C₀ : Measure ℝ) [IsProbabilityMeasure F]
    [IsProbabilityMeasure C₀] (f : ℝ → ℝ) (hf : HasDensity F volume f) {t : ℝ}
    (hrisk : 0 < F (Ici t) * C₀ (Ici t))
    (hm : AEStronglyMeasurable (fun s ↦ f s * ((if s ≤ t then
      ((F.real (Ici s) * C₀.real (Ici s)) ^ 2)⁻¹ else 0) * C₀.real (Ici s))) volume) :
    Integrable fun s ↦ f s * ((if s ≤ t then
      ((F.real (Ici s) * C₀.real (Ici s)) ^ 2)⁻¹ else 0) * C₀.real (Ici s)) := by
  obtain ⟨hyt, hbd⟩ := atRisk_bounds F C₀ hrisk
  set yt := F.real (Ici t) * C₀.real (Ici t)
  refine ((integrable_of_hasDensity F f hf).mul_const (1 / yt ^ 2)).mono' hm ?_
  filter_upwards [hf.2.1] with s hs
  have hC1 : C₀.real (Ici s) ≤ 1 := measureReal_le_one
  have hC0 : 0 ≤ C₀.real (Ici s) := measureReal_nonneg
  have hite : 0 ≤ (if s ≤ t then ((F.real (Ici s) * C₀.real (Ici s)) ^ 2)⁻¹ else 0) ∧
      (if s ≤ t then ((F.real (Ici s) * C₀.real (Ici s)) ^ 2)⁻¹ else 0) ≤ 1 / yt ^ 2 := by
    split_ifs with hst
    · refine ⟨by positivity, ?_⟩
      rw [one_div]
      exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hyt.le (hbd s hst).2.2 2)
    · exact ⟨le_rfl, by positivity⟩
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hs (mul_nonneg hite.1 hC0))]
  exact mul_le_mul_of_nonneg_left ((mul_le_of_le_one_right hite.1 hC1).trans hite.2) hs

/-- The Nelson–Aalen variance `∫_0^t f / ((1 - F)² C₀[s, ∞))` as the integral of the kernel
`f(s) 1{s ≤ t} C₀[s, ∞) / y(s)²` with `y(s) = F[s, ∞) C₀[s, ∞)`. -/
private theorem intervalIntegral_eq_integral_atRiskKernel (F C₀ : Measure ℝ)
    [IsProbabilityMeasure F] [IsProbabilityMeasure C₀] (f : ℝ → ℝ) (hf : HasDensity F volume f)
    (hF : F (Ici 0) = 1) {t : ℝ} (ht : 0 ≤ t) (hrisk : 0 < F (Ici t) * C₀ (Ici t)) :
    ∫ s in (0 : ℝ)..t, f s / ((1 - cdf F s) ^ 2 * C₀.real (Ici s)) =
      ∫ s, f s * ((if s ≤ t then ((F.real (Ici s) * C₀.real (Ici s)) ^ 2)⁻¹ else 0) *
        C₀.real (Ici s)) := by
  obtain ⟨-, hbd⟩ := atRisk_bounds F C₀ hrisk
  simp only [div_eq_mul_inv]
  rw [← integral_ite_le_mul_eq_intervalIntegral F f hf hF _ t ht]
  refine integral_congr_ae (ae_of_all _ fun s ↦ ?_)
  by_cases hs : s ≤ t
  · have := (hbd s hs).1
    have := (hbd s hs).2.1
    simp only [hs, ↓reduceIte, one_sub_cdf_eq_measureReal_Ici_of_hasDensity F f hf s]
    field_simp
  · simp [hs]

/-- The asymptotic variance of the Nelson–Aalen estimator: for the random censoring model
with observed time `x = min(T, C)`, failure-by-`t` indicator `A`, and at-risk probability
`y(s) = F[s, ∞) C₀[s, ∞)`, the variance `∫ ψ²` of the influence function
`ψ(z) = A(z) / y(x z) - θ - ∫ A(z₁) / y(x z₁)² (1{x z₁ ≤ x z} - y(x z₁)) dP(z₁)` equals
`∫_0^t f / ((1 - F)² C₀[s, ∞))`. -/
private theorem nelsonAalenVariance_eq_integral_sq (F C₀ : Measure ℝ) [IsProbabilityMeasure F]
    [IsProbabilityMeasure C₀] (f : ℝ → ℝ) (hf : HasDensity F volume f) (hF : F (Ici 0) = 1)
    (t : ℝ) (ht : 0 ≤ t) (hrisk : 0 < F (Ici t) * C₀ (Ici t)) :
    let x : ℝ × ℝ → ℝ := fun z ↦ min z.1 z.2
    let A : ℝ × ℝ → ℝ := fun z ↦ if z.1 ≤ z.2 ∧ z.1 ≤ t then 1 else 0
    let y : ℝ → ℝ := fun s ↦ F.real (Ici s) * C₀.real (Ici s)
    let v := ∫ s in (0 : ℝ)..t, f s / ((1 - cdf F s) ^ 2 * C₀.real (Ici s))
    v = ∫ z, (A z / y (x z) - ∫ z, A z / y (x z) ∂(F.prod C₀) -
      ∫ z₁, A z₁ / y (x z₁) ^ 2 * ((if x z₁ ≤ x z then 1 else 0) - y (x z₁)) ∂(F.prod C₀)) ^ 2
        ∂(F.prod C₀) := by
  intro x A y v
  have hxdef : x = fun z ↦ min z.1 z.2 := rfl
  have hAdef : A = fun z ↦ if z.1 ≤ z.2 ∧ z.1 ≤ t then 1 else 0 := rfl
  have hydef : y = fun s ↦ F.real (Ici s) * C₀.real (Ici s) := rfl
  set P := F.prod C₀ with hP
  have hx : Measurable x := measurable_fst.min measurable_snd
  have hA : Measurable A := Measurable.ite ((measurableSet_le measurable_fst measurable_snd).inter
    (measurableSet_le measurable_fst measurable_const)) measurable_const measurable_const
  have hA0 (z : ℝ × ℝ) : 0 ≤ A z := by simp only [hAdef]; split_ifs <;> norm_num
  have hA1 (z : ℝ × ℝ) : A z ≤ 1 := by simp only [hAdef]; split_ifs <;> norm_num
  have hAt (z : ℝ × ℝ) (hz : A z ≠ 0) : x z ≤ t := by
    simp only [hAdef, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_not] at hz
    exact (min_le_left _ _).trans hz.2
  have hy (s : ℝ) : y s = P.real {z | s ≤ x z} := (measureReal_le_min_prod F C₀ s).symm
  obtain ⟨hyt', hbd⟩ := atRisk_bounds F C₀ hrisk
  have hyt : 0 < y t := hyt'
  have hFanti : Antitone fun s ↦ F.real (Ici s) := fun s s' h ↦
    measureReal_mono (Ici_subset_Ici.2 h)
  have hCanti : Antitone fun s ↦ C₀.real (Ici s) := fun s s' h ↦
    measureReal_mono (Ici_subset_Ici.2 h)
  have hym : Measurable y := hFanti.measurable.mul hCanti.measurable
  have hys (s : ℝ) (hs : s ≤ t) : y t ≤ y s := (hbd s hs).2.2
  have hyspos (s : ℝ) (hs : s ≤ t) : 0 < y s := hyt.trans_le (hys s hs)
  have hAx (Φ : ℝ → ℝ) (hΦ : Measurable Φ) (M : ℝ) (hM : ∀ s, s ≤ t → |Φ s| ≤ M) :
      ∫ z, A z * Φ (x z) ∂P = ∫ s, f s * ((if s ≤ t then Φ s else 0) * C₀.real (Ici s)) :=
    integral_failureIndicator_mul F C₀ f hf t Φ hΦ M hM
  set kt : ℝ → ℝ := fun s ↦ f s * ((if s ≤ t then (y s ^ 2)⁻¹ else 0) * C₀.real (Ici s))
    with hkt
  have hktm : Measurable kt := hf.1.mul ((Measurable.ite (measurableSet_le measurable_id
    measurable_const) (hym.pow_const 2).inv measurable_const).mul hCanti.measurable)
  have hktint : Integrable kt :=
    integrable_atRiskKernel F C₀ f hf hrisk hktm.aestronglyMeasurable
  set c : ℝ → ℝ := fun u ↦ ∫ s, kt s * (if s ≤ u then 1 else 0) with hc
  have hcm : Measurable c := by
    have hm : Measurable fun p : ℝ × ℝ ↦ kt p.2 * (if p.2 ≤ p.1 then (1 : ℝ) else 0) :=
      (hktm.comp measurable_snd).mul (Measurable.ite (measurableSet_le measurable_snd
        measurable_fst) measurable_const measurable_const)
    exact (StronglyMeasurable.integral_prod_right' (ν := volume) hm.stronglyMeasurable).measurable
  set K := ∫ r, |kt r| with hK
  have hcb (u : ℝ) : |c u| ≤ K := by
    refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
      (ae_of_all _ fun _ ↦ abs_nonneg _) hktint.abs (ae_of_all _ fun r ↦ ?_))
    simp only [abs_mul]
    split_ifs <;> simp
  have hy0 (s : ℝ) : 0 ≤ y s := mul_nonneg measureReal_nonneg measureReal_nonneg
  have hy1 (s : ℝ) : y s ≤ 1 := by rw [hy]; exact measureReal_le_one
  have hbdd (G : ℝ × ℝ → ℝ) (hG : Measurable G) (M : ℝ) (hM : ∀ z, |G z| ≤ M) :
      Integrable G P :=
    Integrable.of_bound hG.aestronglyMeasurable M (ae_of_all _ fun z ↦ by
      rw [Real.norm_eq_abs]; exact hM z)
  have hAyle (z : ℝ × ℝ) (hz : A z ≠ 0) : y t ≤ y (x z) := hys _ (hAt z hz)
  have ha1m : Measurable fun z ↦ A z / y (x z) := hA.div (hym.comp hx)
  have ha2m : Measurable fun z ↦ A z / y (x z) ^ 2 := hA.div ((hym.comp hx).pow_const 2)
  have hAyb (z : ℝ × ℝ) : |A z / y (x z)| ≤ 1 / y t := by
    by_cases hz : A z = 0
    · simp [hz, hyt.le]
    rw [abs_of_nonneg (div_nonneg (hA0 z) (hy0 _))]
    exact div_le_div₀ zero_le_one (hA1 z) hyt (hAyle z hz)
  have hAy2b (z : ℝ × ℝ) : |A z / y (x z) ^ 2| ≤ 1 / y t ^ 2 := by
    by_cases hz : A z = 0
    · simp [hz]; positivity
    rw [abs_of_nonneg (div_nonneg (hA0 z) (sq_nonneg _))]
    exact div_le_div₀ zero_le_one (hA1 z) (by positivity)
      (pow_le_pow_left₀ hyt.le (hAyle z hz) 2)
  -- the projection term is `c(x) - θ`
  have hb (z' : ℝ × ℝ) : ∫ z, A z / y (x z) ^ 2 * ((if x z ≤ x z' then 1 else 0) - y (x z)) ∂P =
      c (x z') - ∫ z, A z / y (x z) ∂P := by
    have hI : Measurable fun z : ℝ × ℝ ↦ (if x z ≤ x z' then (1 : ℝ) else 0) :=
      Measurable.ite (measurableSet_le hx measurable_const) measurable_const measurable_const
    have h1 := hbdd (fun z ↦ A z / y (x z) ^ 2 * (if x z ≤ x z' then (1 : ℝ) else 0))
      (ha2m.mul hI) (1 / y t ^ 2) fun z ↦ by
      rw [abs_mul]
      exact (mul_le_of_le_one_right (abs_nonneg _) (by split_ifs <;> simp)).trans (hAy2b z)
    have h2 := hbdd (fun z ↦ A z / y (x z) ^ 2 * y (x z)) (ha2m.mul (hym.comp hx))
      (1 / y t ^ 2) fun z ↦ by
      rw [abs_mul]
      exact (mul_le_of_le_one_right (abs_nonneg _) (by
        rw [abs_of_nonneg (hy0 _)]; exact hy1 _)).trans (hAy2b z)
    simp_rw [mul_sub]
    rw [integral_sub h1 h2]
    congr 1
    · have hΦ : Measurable fun s ↦ (y s ^ 2)⁻¹ * (if s ≤ x z' then (1 : ℝ) else 0) :=
        (hym.pow_const 2).inv.mul (Measurable.ite (measurableSet_le measurable_id
          measurable_const) measurable_const measurable_const)
      have := hAx _ hΦ (1 / y t ^ 2) fun s hs ↦ by
        rw [abs_mul, abs_of_pos (inv_pos.2 (pow_pos (hyspos s hs) 2)), one_div]
        exact (mul_le_of_le_one_right (inv_pos.2 (pow_pos (hyspos s hs) 2)).le
          (by split_ifs <;> simp)).trans (inv_anti₀ (by positivity)
            (pow_le_pow_left₀ hyt.le (hys s hs) 2))
      convert this using 1
      · exact integral_congr_ae (ae_of_all _ fun z ↦ by simp only; ring)
      · refine integral_congr_ae (ae_of_all _ fun s ↦ ?_)
        simp only [hkt]
        split_ifs <;> ring
    · refine integral_congr_ae (ae_of_all _ fun z ↦ ?_)
      by_cases hyz : y (x z) = 0
      · simp [hyz]
      · simp only
        field_simp
  have hψ (z : ℝ × ℝ) : A z / y (x z) - ∫ z, A z / y (x z) ∂P -
      ∫ z₁, A z₁ / y (x z₁) ^ 2 * ((if x z₁ ≤ x z then 1 else 0) - y (x z₁)) ∂P =
        A z / y (x z) - c (x z) := by
    rw [hb]; ring
  simp_rw [hψ]
  -- expand the square
  have hp := hbdd (fun z ↦ (A z / y (x z)) ^ 2) (ha1m.pow_const 2) ((1 / y t) ^ 2) fun z ↦ by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hAyb z) 2
  have hpq := hbdd (fun z ↦ A z / y (x z) * c (x z)) (ha1m.mul (hcm.comp hx)) (1 / y t * K)
    fun z ↦ by rw [abs_mul]; exact mul_le_mul (hAyb z) (hcb _) (abs_nonneg _) (by positivity)
  have hq := hbdd (fun z ↦ c (x z) ^ 2) ((hcm.comp hx).pow_const 2) (K ^ 2) fun z ↦ by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hcb _) 2
  have hexp : (fun z ↦ (A z / y (x z) - c (x z)) ^ 2) =
      fun z ↦ (A z / y (x z)) ^ 2 - 2 * (A z / y (x z) * c (x z)) + c (x z) ^ 2 := by
    funext z; ring
  rw [hexp, integral_add (f := fun z ↦ (A z / y (x z)) ^ 2 - 2 * (A z / y (x z) * c (x z)))
      (g := fun z ↦ c (x z) ^ 2) (hp.sub (hpq.const_mul 2)) hq,
    integral_sub (f := fun z ↦ (A z / y (x z)) ^ 2)
      (g := fun z ↦ 2 * (A z / y (x z) * c (x z))) hp (hpq.const_mul 2), integral_const_mul]
  -- the three terms
  have hT1 : ∫ z, (A z / y (x z)) ^ 2 ∂P = ∫ s, kt s := by
    have h := hAx (fun s ↦ (y s ^ 2)⁻¹) (hym.pow_const 2).inv (1 / y t ^ 2) fun s hs ↦ by
      rw [abs_of_pos (inv_pos.2 (pow_pos (hyspos s hs) 2)), one_div]
      exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hyt.le (hys s hs) 2)
    rw [← h]
    refine integral_congr_ae (ae_of_all _ fun z ↦ ?_)
    simp only [hAdef]
    split_ifs <;> simp
  have hT2 : ∫ z, A z / y (x z) * c (x z) ∂P = ∫ s, kt s * y s * c s := by
    have hΦ : Measurable fun s ↦ c s / y s := hcm.div hym
    have h := hAx (fun s ↦ c s / y s) hΦ (K / y t) fun s hs ↦ by
      rw [abs_div, abs_of_pos (hyspos s hs)]
      exact div_le_div₀ (by positivity) (hcb s) hyt (hys s hs)
    rw [show (fun z ↦ A z / y (x z) * c (x z)) = fun z ↦ A z * (c (x z) / y (x z)) from by
      funext z; ring, h]
    refine integral_congr_ae (ae_of_all _ fun s ↦ ?_)
    simp only [hkt]
    by_cases hs : s ≤ t
    · have := hyspos s hs
      simp only [hs, ↓reduceIte]
      field_simp
    · simp [hs]
  have hT3 : ∫ z, c (x z) ^ 2 ∂P = 2 * ∫ s, kt s * y s * c s := by
    have h := integral_sq_integral_mul_ite_le P x hx kt hktm hktint
    simp_rw [← hy] at h
    exact h
  have hT0 : v = ∫ s, kt s := intervalIntegral_eq_integral_atRiskKernel F C₀ f hf hF ht hrisk
  rw [hT1, hT2, hT3, hT0]
  ring

/-- GAPS 106.28, fixed-time Nelson–Aalen central limit theorem: in the random censoring model
with a failure law `F` of density `f` and `P(min(T, C) ≥ t) > 0`,
`√n (Λ̂_n(t) - Λ(t)) ⇒ N(0, v)` with `Λ(t) = ∫_0^t f / (1 - F)` and
`v = ∫_0^t f / ((1 - F)² C₀[s, ∞))`. -/
theorem tendstoInDistribution_nelsonAalenEstimator {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F C₀ : Measure ℝ)
    [IsProbabilityMeasure F] [IsProbabilityMeasure C₀]
    (T C : ℕ → Ω → ℝ) (hcens : IsRandomCensoringModel μ F C₀ T C)
    (f : ℝ → ℝ) (hf : HasDensity F volume f)
    (t : ℝ) (ht : 0 ≤ t) (hrisk : 0 < F (Ici t) * C₀ (Ici t)) :
    let Λ := ∫ s in (0 : ℝ)..t, f s / (1 - cdf F s);
    let v := ∫ s in (0 : ℝ)..t, f s / ((1 - cdf F s) ^ 2 * C₀.real (Ici s));
    TendstoInDistribution (fun (n : ℕ) ω ↦ Real.sqrt n * (nelsonAalenEstimator T C n ω t - Λ))
      atTop id (fun _ ↦ μ)
      (gaussianReal 0 (Real.toNNReal v)) := by
  intro Λ v
  set P := F.prod C₀ with hP
  set x : ℝ × ℝ → ℝ := fun z ↦ min z.1 z.2 with hxdef
  have hx : Measurable x := measurable_fst.min measurable_snd
  set A : ℝ × ℝ → ℝ := fun z ↦ if z.1 ≤ z.2 ∧ z.1 ≤ t then 1 else 0 with hAdef
  have hA : Measurable A := Measurable.ite ((measurableSet_le measurable_fst measurable_snd).inter
    (measurableSet_le measurable_fst measurable_const)) measurable_const measurable_const
  have hA0 (z : ℝ × ℝ) : 0 ≤ A z := by simp only [hAdef]; split_ifs <;> norm_num
  have hA1 (z : ℝ × ℝ) : A z ≤ 1 := by simp only [hAdef]; split_ifs <;> norm_num
  have hAt (z : ℝ × ℝ) (hz : A z ≠ 0) : x z ≤ t := by
    simp only [hAdef, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_not] at hz
    exact (min_le_left _ _).trans hz.2
  set y : ℝ → ℝ := fun s ↦ F.real (Ici s) * C₀.real (Ici s) with hydef
  have hy (s : ℝ) : y s = P.real {z | s ≤ x z} := (measureReal_le_min_prod F C₀ s).symm
  have hyt : 0 < y t := by
    rcases ENNReal.mul_pos_iff.1 hrisk with ⟨h1, h2⟩
    exact mul_pos (ENNReal.toReal_pos h1.ne' (measure_ne_top _ _))
      (ENNReal.toReal_pos h2.ne' (measure_ne_top _ _))
  have hmain := tendstoInDistribution_sqrt_mul_riskSetSum_sub μ P (fun i ω ↦ (T i ω, C i ω))
    hcens.iid x hx A hA hA0 hA1 t hAt y hy hyt
  simp only at hmain
  -- properties of the at-risk probability
  have hFanti : Antitone fun s ↦ F.real (Ici s) := fun s s' h ↦
    measureReal_mono (Ici_subset_Ici.2 h)
  have hCanti : Antitone fun s ↦ C₀.real (Ici s) := fun s s' h ↦
    measureReal_mono (Ici_subset_Ici.2 h)
  have hym : Measurable y := hFanti.measurable.mul hCanti.measurable
  have hFt : 0 < F.real (Ici t) := by
    rcases ENNReal.mul_pos_iff.1 hrisk with ⟨h1, -⟩
    exact ENNReal.toReal_pos h1.ne' (measure_ne_top _ _)
  have hCt : 0 < C₀.real (Ici t) := by
    rcases ENNReal.mul_pos_iff.1 hrisk with ⟨-, h2⟩
    exact ENNReal.toReal_pos h2.ne' (measure_ne_top _ _)
  have hFs (s : ℝ) (hs : s ≤ t) : 0 < F.real (Ici s) := hFt.trans_le (hFanti hs)
  have hCs (s : ℝ) (hs : s ≤ t) : 0 < C₀.real (Ici s) := hCt.trans_le (hCanti hs)
  have hys (s : ℝ) (hs : s ≤ t) : y t ≤ y s :=
    mul_le_mul (hFanti hs) (hCanti hs) hCt.le measureReal_nonneg
  have hcdf (s : ℝ) : 1 - cdf F s = F.real (Ici s) :=
    one_sub_cdf_eq_measureReal_Ici_of_hasDensity F f hf s
  -- the centring constant
  have hθ : ∫ z, A z / y (x z) ∂P = Λ := by
    have hpt : (fun z ↦ A z / y (x z)) = fun z : ℝ × ℝ ↦
        if z.1 ≤ z.2 then (if z.1 ≤ t then (y z.1)⁻¹ else 0) else 0 := by
      funext z
      simp only [hAdef, hxdef]
      by_cases h1 : z.1 ≤ z.2
      · simp [h1]
        split_ifs <;> simp
      · simp [h1]
    have hφm : Measurable fun s ↦ if s ≤ t then (y s)⁻¹ else 0 :=
      Measurable.ite (measurableSet_le measurable_id measurable_const) hym.inv measurable_const
    have hφb (s : ℝ) : |if s ≤ t then (y s)⁻¹ else 0| ≤ 1 / y t := by
      split_ifs with hs
      · rw [abs_of_pos (inv_pos.2 (hyt.trans_le (hys s hs))), one_div]
        exact inv_anti₀ hyt (hys s hs)
      · simp [hyt.le]
    rw [hpt, integral_ite_fst_le_snd_prod F C₀ f hf _ hφm (1 / y t) hφb]
    have hΛ : Λ = ∫ s in (0 : ℝ)..t, f s * (1 - cdf F s)⁻¹ := by
      simp only [Λ, div_eq_mul_inv]
    rw [hΛ, ← integral_ite_le_mul_eq_intervalIntegral F f hf hcens.failure_nonneg _ t ht]
    refine integral_congr_ae (ae_of_all _ fun s ↦ ?_)
    by_cases hs : s ≤ t
    · simp only [hs, ↓reduceIte, hcdf, hydef]
      have := hCs s hs
      have := hFs s hs
      field_simp
    · simp [hs]
  have hNA (n : ℕ) (ω : Ω) : nelsonAalenEstimator T C n ω t = ∑ i ∈ Finset.range n,
      A (T i ω, C i ω) / (((Finset.range n).filter fun j ↦
        x (T i ω, C i ω) ≤ x (T j ω, C j ω)).card : ℝ) := by
    unfold nelsonAalenEstimator riskSetSize
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [hAdef, hxdef]
    split_ifs <;> simp
  have hfun : (fun (n : ℕ) ω ↦ Real.sqrt n * (nelsonAalenEstimator T C n ω t - Λ)) =
      fun (n : ℕ) ω ↦ Real.sqrt n * (∑ i ∈ Finset.range n, A (T i ω, C i ω) /
        (((Finset.range n).filter fun j ↦ x (T i ω, C i ω) ≤ x (T j ω, C j ω)).card : ℝ) -
          ∫ z, A z / y (x z) ∂P) := by
    funext n ω; rw [hNA, hθ]
  rw [hfun]
  convert hmain using 3
  exact nelsonAalenVariance_eq_integral_sq F C₀ f hf hcens.failure_nonneg t ht hrisk

/-- For a law on `[0, ∞)` with density `f`, `F(s) = ∫_0^s f` for `s ≥ 0`. -/
theorem cdf_eq_intervalIntegral_of_hasDensity (F : Measure ℝ) [IsProbabilityMeasure F]
    (f : ℝ → ℝ) (hf : HasDensity F volume f) (hF : F (Ici 0) = 1) (s : ℝ) (hs : 0 ≤ s) :
    cdf F s = ∫ u in (0 : ℝ)..s, f u := by
  have h := integral_ite_le_mul_eq_intervalIntegral F f hf hF (fun _ ↦ 1) s hs
  simp only [mul_one] at h
  rw [← h, cdf_eq_real, ← integral_indicator_one measurableSet_Iic,
    integral_eq_integral_mul_of_hasDensity F f hf]
  refine integral_congr_ae (ae_of_all _ fun u ↦ ?_)
  by_cases hu : u ≤ s <;> simp [hu]

/-- For a law on `[0, ∞)` with density `f` and `F(t) < 1`, the survival function is the
exponential of minus the cumulative hazard: `1 - F(t) = exp (-∫_0^t f / (1 - F))`. -/
theorem one_sub_cdf_eq_exp_neg_integral_of_hasDensity (F : Measure ℝ) [IsProbabilityMeasure F]
    (f : ℝ → ℝ) (hf : HasDensity F volume f) (hF : F (Ici 0) = 1) (t : ℝ) (ht : 0 ≤ t)
    (hpos : 0 < 1 - cdf F t) :
    1 - cdf F t = Real.exp (-∫ s in (0 : ℝ)..t, f s / (1 - cdf F s)) := by
  set Φ : ℝ → ℝ := fun s ↦ ∫ u in (0 : ℝ)..s, f u with hΦ
  have hfi : Integrable f := integrable_of_hasDensity F f hf
  have hut : uIcc 0 t = Icc 0 t := uIcc_of_le ht
  have hcdfΦ (s : ℝ) (hs : s ∈ uIcc 0 t) : cdf F s = Φ s := by
    rw [hut] at hs
    exact cdf_eq_intervalIntegral_of_hasDensity F f hf hF s hs.1
  have hle (s : ℝ) (hs : s ∈ uIcc 0 t) : Φ s ≤ cdf F t := by
    rw [← hcdfΦ s hs]
    rw [hut] at hs
    exact (cdf F).mono hs.2
  have hlow (s : ℝ) (hs : s ∈ uIcc 0 t) : 1 - cdf F t ≤ 1 - Φ s := by linarith [hle s hs]
  have htmem : t ∈ uIcc 0 t := by simp
  have hcongr : ∫ s in (0 : ℝ)..t, f s / (1 - cdf F s) = ∫ s in (0 : ℝ)..t, f s / (1 - Φ s) :=
    intervalIntegral.integral_congr fun s hs ↦ by simp only [hcdfΦ s hs]
  rw [hcongr, hcdfΦ t htmem]
  have hpos' : 0 < 1 - Φ t := by rw [← hcdfΦ t htmem]; exact hpos
  have hΦc : Continuous Φ := intervalIntegral.continuous_primitive (fun _ _ ↦
    hfi.intervalIntegrable) 0
  -- the integrand is interval integrable
  have hgi : IntervalIntegrable (fun s ↦ f s / (1 - Φ s)) volume 0 t := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht]
    refine Integrable.mono'
      ((MeasureTheory.Integrable.div_const hfi.abs (1 - cdf F t)).integrableOn)
      ((hf.1.div (continuous_const.sub hΦc).measurable).aestronglyMeasurable.restrict) ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun s hs ↦ ?_)
    have hs' : s ∈ uIcc 0 t := by rw [hut]; exact Ioc_subset_Icc_self hs
    have h1 := hlow s hs'
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (hpos.trans_le h1)]
    exact div_le_div_of_nonneg_left (abs_nonneg _) hpos h1
  -- `log (1 - ·)` is Lipschitz on `(-∞, F(t)]`
  have hlip : LipschitzOnWith (Real.toNNReal (1 / (1 - cdf F t)))
      (fun u ↦ Real.log (1 - u)) (Iic (cdf F t)) := by
    refine (convex_Iic _).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (f' := fun u ↦ -1 / (1 - u)) (fun u hu ↦ ?_) (fun u hu ↦ ?_)
    · have hu' : 1 - u ≠ 0 := by
        have : u ≤ cdf F t := hu
        linarith
      have := ((hasDerivAt_id u).const_sub 1).log hu'
      simpa using this.hasDerivWithinAt
    · have hu' : 1 - cdf F t ≤ 1 - u := by
        have : u ≤ cdf F t := hu
        linarith
      rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ (by positivity),
        Real.norm_eq_abs, abs_div, abs_neg, abs_one, abs_of_pos (hpos.trans_le hu')]
      exact one_div_le_one_div_of_le hpos hu'
  set Ψ : ℝ → ℝ := fun s ↦ Real.log (1 - Φ s) + ∫ u in (0 : ℝ)..s, f u / (1 - Φ u) with hΨ
  have hΦac : AbsolutelyContinuousOnInterval Φ 0 t :=
    hfi.intervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have hΨac : AbsolutelyContinuousOnInterval Ψ 0 t :=
    (hlip.comp_absolutelyContinuousOnInterval (fun s hs ↦ hle s hs) hΦac).add
      (hgi.absolutelyContinuousOnInterval_intervalIntegral (by simp))
  have hder : ∀ᵐ s, s ∈ uIcc 0 t → HasDerivAt Ψ 0 s := by
    filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hfi.locallyIntegrable,
      hgi.ae_hasDerivAt_integral]
      with s h1 h2 hs
    have hs1 : 1 - Φ s ≠ 0 := (hpos.trans_le (hlow s hs)).ne'
    have hd := (((h1 0).const_sub 1).log hs1).add (h2 hs 0 (by simp))
    convert hd using 1
    change (0 : ℝ) = -f s / (1 - Φ s) + f s / (1 - Φ s)
    ring
  obtain ⟨c, hc⟩ := hΨac.const_of_ae_hasDerivAt_zero hder
  have hΨ0 : Ψ 0 = 0 := by simp [hΨ, hΦ]
  have hΨt : Ψ t = 0 := by rw [hc t htmem, ← hc 0 (by simp), hΨ0]
  have hlog : Real.log (1 - Φ t) = -∫ u in (0 : ℝ)..t, f u / (1 - Φ u) := by
    simp only [hΨ] at hΨt
    linarith
  rw [← hlog, Real.exp_log hpos']

/-- The Kaplan–Meier estimator is close to the exponential of minus the Nelson–Aalen estimator:
`|Ŝ(t) - exp (-Λ̂(t))| ≤ n / K²` with `K = max(1, #{j < n : min(T j, C j) ≥ t})`, since every
risk set of an observed failure by time `t` has at least `K` members. -/
private theorem abs_kaplanMeierEstimator_sub_exp_neg_le {Ω : Type*} (T C : ℕ → Ω → ℝ) (n : ℕ)
    (ω : Ω) (t : ℝ) :
    |kaplanMeierEstimator T C n ω t - Real.exp (-nelsonAalenEstimator T C n ω t)| ≤
      n * (((max ((Finset.range n).filter fun j ↦ t ≤ min (T j ω) (C j ω)).card 1 : ℕ) : ℝ)⁻¹)
        ^ 2 := by
  set K : ℝ := ((max ((Finset.range n).filter fun j ↦ t ≤ min (T j ω) (C j ω)).card 1 : ℕ) : ℝ)
    with hKdef
  have hK : 1 ≤ K := by rw [hKdef]; exact_mod_cast le_max_right _ _
  have hN (i : ℕ) (hi : i ∈ Finset.range n) (hE : T i ω ≤ C i ω ∧ T i ω ≤ t) :
      K ≤ (riskSetSize T C n i ω : ℝ) := by
    rw [hKdef]
    refine Nat.cast_le.2 (max_le (Finset.card_le_card fun j hj ↦ ?_) ?_)
    · rw [Finset.mem_filter] at hj ⊢
      exact ⟨hj.1, ((min_le_left _ _).trans hE.2).trans hj.2⟩
    · exact Finset.card_pos.2 ⟨i, Finset.mem_filter.2 ⟨hi, le_rfl⟩⟩
  have hexp : Real.exp (-nelsonAalenEstimator T C n ω t) = ∏ i ∈ Finset.range n,
      if T i ω ≤ C i ω ∧ T i ω ≤ t then Real.exp (-(riskSetSize T C n i ω : ℝ)⁻¹) else 1 := by
    unfold nelsonAalenEstimator
    rw [← Finset.sum_neg_distrib, Real.exp_sum]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    split_ifs <;> simp
  have hu (i : ℕ) (hi : i ∈ Finset.range n) (hE : T i ω ≤ C i ω ∧ T i ω ≤ t) :
      0 ≤ (riskSetSize T C n i ω : ℝ)⁻¹ ∧ (riskSetSize T C n i ω : ℝ)⁻¹ ≤ K⁻¹ ∧ K⁻¹ ≤ 1 := by
    have h1 := hN i hi hE
    refine ⟨inv_nonneg.2 (by positivity), inv_anti₀ (by linarith) h1, inv_le_one_of_one_le₀ hK⟩
  unfold kaplanMeierEstimator
  rw [hexp]
  refine (TauCeti.abs_prod_sub_prod_le_sum_abs_sub _ (fun i hi ↦ ?_) (fun i hi ↦ ?_)).trans ?_
  · split_ifs with hE
    · obtain ⟨h0, h1, h2⟩ := hu i hi hE
      rw [abs_le]
      constructor <;> linarith
    · simp
  · split_ifs with hE
    · obtain ⟨h0, -, -⟩ := hu i hi hE
      rw [abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.2 (by linarith)
    · simp
  calc ∑ i ∈ Finset.range n, |(if T i ω ≤ C i ω ∧ T i ω ≤ t then
          1 - (riskSetSize T C n i ω : ℝ)⁻¹ else 1) -
        (if T i ω ≤ C i ω ∧ T i ω ≤ t then Real.exp (-(riskSetSize T C n i ω : ℝ)⁻¹) else 1)|
      ≤ ∑ i ∈ Finset.range n, K⁻¹ ^ 2 := by
        refine Finset.sum_le_sum fun i hi ↦ ?_
        split_ifs with hE
        · obtain ⟨h0, h1, h2⟩ := hu i hi hE
          set u := (riskSetSize T C n i ω : ℝ)⁻¹
          have hb := Real.abs_exp_sub_one_sub_id_le (x := -u)
            (by rw [abs_neg, abs_of_nonneg h0]; linarith)
          rw [show 1 - u - Real.exp (-u) = -(Real.exp (-u) - 1 - -u) by ring, abs_neg]
          refine hb.trans ?_
          rw [neg_sq]
          exact pow_le_pow_left₀ h0 h1 2
        · simp only [sub_self, abs_zero]
          positivity
    _ = n * K⁻¹ ^ 2 := by simp

/-- In the random censoring model, the risk-set sizes, the Nelson–Aalen estimator and the
Kaplan–Meier estimator are measurable functions of the sample. -/
private theorem measurable_nelsonAalenEstimator_kaplanMeierEstimator {Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} {F C₀ : Measure ℝ} {T C : ℕ → Ω → ℝ}
    (hcens : IsRandomCensoringModel μ F C₀ T C) (n : ℕ) (t : ℝ) :
    Measurable (fun ω ↦ nelsonAalenEstimator T C n ω t) ∧
      Measurable (fun ω ↦ kaplanMeierEstimator T C n ω t) := by
  have hT (i : ℕ) : Measurable (T i) := (hcens.iid.1 i).fst
  have hC (i : ℕ) : Measurable (C i) := (hcens.iid.1 i).snd
  have hR (i : ℕ) : Measurable fun ω ↦ (riskSetSize T C n i ω : ℝ) := by
    have h : (fun ω ↦ (riskSetSize T C n i ω : ℝ)) = fun ω ↦ ∑ j ∈ Finset.range n,
        if min (T i ω) (C i ω) ≤ min (T j ω) (C j ω) then (1 : ℝ) else 0 := by
      funext ω
      rw [riskSetSize, Finset.natCast_card_filter]
    rw [h]
    exact Finset.measurable_fun_sum _ fun j _ ↦ Measurable.ite
      (measurableSet_le ((hT i).min (hC i)) ((hT j).min (hC j))) measurable_const
      measurable_const
  have hE (i : ℕ) : MeasurableSet {ω | T i ω ≤ C i ω ∧ T i ω ≤ t} :=
    (measurableSet_le (hT i) (hC i)).inter (measurableSet_le (hT i) measurable_const)
  refine ⟨?_, ?_⟩
  · unfold nelsonAalenEstimator
    exact Finset.measurable_fun_sum _ fun i _ ↦ Measurable.ite (hE i) (hR i).inv
      measurable_const
  · unfold kaplanMeierEstimator
    exact Finset.measurable_prod _ fun i _ ↦ Measurable.ite (hE i)
      (measurable_const.sub (hR i).inv) measurable_const

/-- GAPS 106.29, fixed-time Kaplan–Meier central limit theorem: under the assumptions of
`tendstoInDistribution_nelsonAalenEstimator`, `√n (Ŝ_n(t) - S(t)) ⇒ N(0, S(t)² v)` with
`S(t) = 1 - F(t)` and `v` the Nelson–Aalen asymptotic variance (Greenwood's formula). -/
theorem tendstoInDistribution_kaplanMeierEstimator {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F C₀ : Measure ℝ)
    [IsProbabilityMeasure F] [IsProbabilityMeasure C₀]
    (T C : ℕ → Ω → ℝ) (hcens : IsRandomCensoringModel μ F C₀ T C)
    (f : ℝ → ℝ) (hf : HasDensity F volume f)
    (t : ℝ) (ht : 0 ≤ t) (hrisk : 0 < F (Ici t) * C₀ (Ici t)) :
    let S := 1 - cdf F t;
    let v := S ^ 2 * ∫ s in (0 : ℝ)..t, f s / ((1 - cdf F s) ^ 2 * C₀.real (Ici s));
    TendstoInDistribution (fun (n : ℕ) ω ↦ Real.sqrt n * (kaplanMeierEstimator T C n ω t - S))
      atTop id (fun _ ↦ μ)
      (gaussianReal 0 (Real.toNNReal v)) := by
  intro S v
  set Λ := ∫ s in (0 : ℝ)..t, f s / (1 - cdf F s) with hΛ
  set w := ∫ s in (0 : ℝ)..t, f s / ((1 - cdf F s) ^ 2 * C₀.real (Ici s)) with hw
  have hNA := tendstoInDistribution_nelsonAalenEstimator μ F C₀ T C hcens f hf t ht hrisk
  simp only at hNA
  rw [← hΛ, ← hw] at hNA
  have hFt : 0 < F.real (Ici t) := by
    rcases ENNReal.mul_pos_iff.1 hrisk with ⟨h1, -⟩
    exact ENNReal.toReal_pos h1.ne' (measure_ne_top _ _)
  have hCt : 0 < C₀.real (Ici t) := by
    rcases ENNReal.mul_pos_iff.1 hrisk with ⟨-, h2⟩
    exact ENNReal.toReal_pos h2.ne' (measure_ne_top _ _)
  have hSpos : 0 < S := by
    simp only [S, one_sub_cdf_eq_measureReal_Ici_of_hasDensity F f hf]; exact hFt
  have hS : S = Real.exp (-Λ) :=
    one_sub_cdf_eq_exp_neg_integral_of_hasDensity F f hf hcens.failure_nonneg t ht hSpos
  have hmeas := measurable_nelsonAalenEstimator_kaplanMeierEstimator hcens
  -- delta method for `u ↦ exp (-u)`
  have hd : HasDerivAt (fun u : ℝ ↦ Real.exp (-u)) (-Real.exp (-Λ)) Λ := by
    simpa using (hasDerivAt_neg Λ).exp
  have hdelta := (tendstoInDistribution_delta_method μ (fun n ω ↦ nelsonAalenEstimator T C n ω t)
    (fun n ↦ (hmeas n t).1) Λ (fun u : ℝ ↦ Real.exp (-u)) (by fun_prop)
    (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (-Real.exp (-Λ))) hd.hasFDerivAt
    (by simpa only [smul_eq_mul] using hNA)).1
  have hlaw : (gaussianReal 0 v.toNNReal).map id = (gaussianReal 0 w.toNNReal).map
      ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (-Real.exp (-Λ))) ∘ id) := by
    have hfun : ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (-Real.exp (-Λ))) ∘ id) =
        fun u ↦ -Real.exp (-Λ) * u := by
      funext u; simp [mul_comm]
    rw [hfun, gaussianReal_map_const_mul, Measure.map_id, mul_zero]
    congr 1
    rw [Real.toNNReal_mul (sq_nonneg _)]
    congr 1
    ext
    simp [hS, sq_nonneg]
  have hX := tendstoInDistribution_of_map_eq hdelta aemeasurable_id hlaw
  refine tendstoInDistribution_of_tendstoInMeasure_sub_of_measurable μ _ _
    (fun n ↦ (((hmeas n t).1.neg.exp).sub_const _).const_mul _)
    (fun n ↦ ((hmeas n t).2.sub_const _).const_mul _) hX ?_
  -- the at-risk proportion at `t` obeys the law of large numbers
  set y := F.real (Ici t) * C₀.real (Ici t) with hydef
  have hy : 0 < y := mul_pos hFt hCt
  set r : ℝ × ℝ → ℝ := fun z ↦ if t ≤ min z.1 z.2 then 1 else 0 with hrdef
  have hrm : Measurable r := Measurable.ite
    (measurableSet_le measurable_const (measurable_fst.min measurable_snd)) measurable_const
    measurable_const
  have hri : Integrable r (F.prod C₀) := (integrable_const (1 : ℝ)).mono'
    hrm.aestronglyMeasurable (ae_of_all _ fun z ↦ by simp only [hrdef]; split_ifs <;> simp)
  have hrint : ∫ z, r z ∂(F.prod C₀) = y := by
    have : r = {z : ℝ × ℝ | t ≤ min z.1 z.2}.indicator 1 := by
      funext z; simp [hrdef, Set.indicator_apply]
    rw [this, integral_indicator_one
      (measurableSet_le measurable_const (measurable_fst.min measurable_snd)),
      measureReal_le_min_prod]
  have hW := tendstoInMeasure_sampleMean_of_iid μ (F.prod C₀) (fun i ω ↦ (T i ω, C i ω))
    hcens.iid r hrm hri
  have hU : TendstoInMeasure μ (fun (n : ℕ) ω ↦
      (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, r (T i ω, C i ω) - y) atTop (fun _ ↦ 0) := by
    rw [tendstoInMeasure_iff_dist] at hW ⊢
    intro ε hε
    simpa only [Real.dist_eq, sub_zero, hrint] using hW ε hε
  have hlim : Tendsto (fun n : ℕ ↦ 4 / (y ^ 2 * Real.sqrt n)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((Real.tendsto_sqrt_atTop.comp
      tendsto_natCast_atTop_atTop).const_mul_atTop (by positivity))
  refine tendstoInMeasure_zero_of_abs_le μ (fun n _ ↦ 4 / (y ^ 2 * Real.sqrt n)) _ _
    (half_pos hy) ?_ (tendstoInMeasure_const_of_tendsto μ _ hlim) hU
  filter_upwards [eventually_ge_atTop 1] with n hn
  refine ae_of_all _ fun ω hω ↦ ?_
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set M := ((Finset.range n).filter fun j ↦ t ≤ min (T j ω) (C j ω)).card with hMdef
  have hMcast : (M : ℝ) = ∑ i ∈ Finset.range n, r (T i ω, C i ω) := by
    rw [hMdef, Finset.natCast_card_filter]
  have hMlow : y / 2 * n < M := by
    have h1 := (abs_lt.1 hω).1
    have h2 : y / 2 < (n : ℝ)⁻¹ * M := by rw [hMcast]; linarith
    rwa [inv_mul_eq_div, lt_div_iff₀ hn'] at h2
  have hK : (M : ℝ) ≤ ((max M 1 : ℕ) : ℝ) := by exact_mod_cast le_max_left _ _
  have hb := abs_kaplanMeierEstimator_sub_exp_neg_le T C n ω t
  rw [← hMdef] at hb
  have hr0 : 0 < Real.sqrt n := Real.sqrt_pos.2 hn'
  have hr2 : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn'.le
  change |Real.sqrt n * (kaplanMeierEstimator T C n ω t - S) -
    Real.sqrt n * (Real.exp (-nelsonAalenEstimator T C n ω t) - Real.exp (-Λ))| ≤
      |4 / (y ^ 2 * Real.sqrt n)|
  rw [← hS, ← mul_sub, show kaplanMeierEstimator T C n ω t - S -
      (Real.exp (-nelsonAalenEstimator T C n ω t) - S) =
      kaplanMeierEstimator T C n ω t - Real.exp (-nelsonAalenEstimator T C n ω t) by ring,
    abs_mul, abs_of_pos hr0, abs_of_pos (show (0 : ℝ) < 4 / (y ^ 2 * Real.sqrt n) by positivity)]
  have hKinv : ((max M 1 : ℕ) : ℝ)⁻¹ ≤ 2 / (y * n) := by
    rw [← one_div]
    calc 1 / ((max M 1 : ℕ) : ℝ) ≤ 1 / (y / 2 * n) :=
          one_div_le_one_div_of_le (by positivity) (hMlow.le.trans hK)
      _ = 2 / (y * n) := by field_simp
  calc Real.sqrt n * |kaplanMeierEstimator T C n ω t -
        Real.exp (-nelsonAalenEstimator T C n ω t)|
      ≤ Real.sqrt n * (n * ((max M 1 : ℕ) : ℝ)⁻¹ ^ 2) := mul_le_mul_of_nonneg_left hb hr0.le
    _ ≤ Real.sqrt n * (n * (2 / (y * n)) ^ 2) := by gcongr
    _ = 4 / (y ^ 2 * Real.sqrt n) := by
      generalize Real.sqrt n = R at hr0 hr2 ⊢
      rw [← hr2]
      field_simp
      ring

end CKSD
