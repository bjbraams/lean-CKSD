module
public import CKSD.LinearModels.GammaRatioAsymptotics
public import TauCeti.Probability.Distributions.Beta.Basic
public import TauCeti.Probability.Distributions.Gamma.Basic
public import TauCeti.Probability.Moments.WeakConvergence
public import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Cdf
/-!
# Gamma limits of Beta logarithms

A Beta variable with first shape `a` tending to infinity satisfies
`-a * log B ⇒ Gamma(b, 1)`. Raising the Beta variable to `a` first gives laws supported on the
unit interval. Their moments converge by the Gamma quotient asymptotic, so TauCeti's proved
method of moments gives weak convergence to an exponentiated negative Gamma law. Finally,
portmanteau on positive closed tails transfers the limit to the logarithms.

Mathlib supplies probability measure convergence and portmanteau; TauCeti supplies the Beta
moments, Gamma moment-generating function, and method of moments. The Gamma quotient
asymptotic is local project code.
-/

@[expose] public section
noncomputable section
open Filter Set Real MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace CKSD

/-- The positive real-power moment of a Beta variable. -/
theorem integral_rpow_betaMeasure {a b q : ℝ} (ha : 0 < a) (hb : 0 < b) (hq : 0 ≤ q) :
    (∫ x, x ^ q ∂betaMeasure a b) =
      Real.Gamma (a + q) * Real.Gamma (a + b) / (Real.Gamma a * Real.Gamma (a + b + q)) := by
  have h := TauCeti.Probability.integral_rpow_mul_one_sub_rpow_betaMeasure ha hb
    (show 0 < a + q by linarith) (show 0 < b + (0 : ℝ) by simpa using hb)
  simp only [Real.rpow_zero, mul_one, add_zero] at h
  rw [h, ProbabilityTheory.beta, ProbabilityTheory.beta]
  rw [show a + q + b = a + b + q by ring]
  field_simp [(Real.Gamma_pos_of_pos hb).ne']

/-- A growing-shape Beta variable raised to its first shape has the moments of an exponentiated
negative Gamma variable in the limit. -/
theorem tendsto_integral_beta_rpow_pow {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    (hatop : Tendsto a atTop atTop) {b : ℝ} (hb : 0 < b) (k : ℕ) :
    Tendsto (fun n ↦ ∫ x, (x ^ (a n)) ^ k ∂betaMeasure (a n) b) atTop
      (𝓝 ((1 + (k : ℝ)) ^ (-b))) := by
  let c := 1 + (k : ℝ)
  have hc : 0 < c := by dsimp [c]; positivity
  let R : ℝ → ℝ := fun x ↦ Real.Gamma (x + b) / (Real.Gamma x * x ^ b)
  have hR : Tendsto R atTop (𝓝 1) := tendsto_Gamma_add_div_mul_rpow hb
  have hlim := ((hR.comp hatop).div (hR.comp (hatop.const_mul_atTop hc)) one_ne_zero).mul_const (c ^ (-b))
  simp only [div_self one_ne_zero, one_mul] at hlim
  apply hlim.congr'
  exact Eventually.of_forall fun n ↦ by
    have hmoment : (∫ x, (x ^ (a n)) ^ k ∂betaMeasure (a n) b) =
        Real.Gamma (c * a n) * Real.Gamma (a n + b) /
          (Real.Gamma (a n) * Real.Gamma (c * a n + b)) := by
      calc _ = ∫ x, x ^ (a n * k) ∂betaMeasure (a n) b := by
              apply integral_congr_ae
              filter_upwards [TauCeti.Probability.ae_mem_Ioo_betaMeasure (a n) b] with x hx
              rw [← Real.rpow_natCast, ← Real.rpow_mul hx.1.le]
        _ = _ := by
          rw [integral_rpow_betaMeasure (ha n) hb (mul_nonneg (ha n).le (Nat.cast_nonneg k)),
            show a n + a n * k = c * a n by dsimp [c]; ring,
            show a n + b + a n * k = c * a n + b by dsimp [c]; ring]
    dsimp only
    change (R (a n) / R (c * a n)) * c ^ (-b) = _
    rw [hmoment]
    dsimp [R]
    rw [Real.mul_rpow hc.le (ha n).le, Real.rpow_neg hc.le]
    field_simp [(Real.Gamma_pos_of_pos (ha n)).ne',
      (Real.Gamma_pos_of_pos (mul_pos hc (ha n))).ne',
      (Real.Gamma_pos_of_pos (add_pos (mul_pos hc (ha n)) hb)).ne',
      (Real.rpow_pos_of_pos (ha n) b).ne', (Real.rpow_pos_of_pos hc b).ne']

/-- The transformed growing-shape Beta variables converge weakly to an exponentiated Gamma law. -/
theorem tendstoInDistribution_beta_rpow {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    (hatop : Tendsto a atTop atTop) {b : ℝ} (hb : 0 < b) :
    let : ∀ n, IsProbabilityMeasure (betaMeasure (a n) b) := fun n ↦ isProbabilityMeasureBeta (ha n) hb;
    let : IsProbabilityMeasure (gammaMeasure b 1) := ProbabilityTheory.isProbabilityMeasure_gammaMeasure hb zero_lt_one;
    TendstoInDistribution (fun (n : ℕ) (x : ℝ) ↦ x ^ (a n)) atTop (fun y : ℝ ↦ Real.exp (-y))
      (fun n ↦ betaMeasure (a n) b) (gammaMeasure b 1) := by
  let : ∀ n, IsProbabilityMeasure (betaMeasure (a n) b) := fun n ↦ isProbabilityMeasureBeta (ha n) hb
  let : IsProbabilityMeasure (gammaMeasure b 1) := ProbabilityTheory.isProbabilityMeasure_gammaMeasure hb zero_lt_one
  have hmap (n : ℕ) : Measurable (fun x : ℝ ↦ x ^ (a n)) := measurable_id.pow_const _
  have hlim : Measurable (fun y : ℝ ↦ Real.exp (-y)) := by fun_prop
  refine ⟨fun n ↦ (hmap n).aemeasurable, hlim.aemeasurable, ?_⟩
  have hνsupport : ∀ᵐ x ∂(gammaMeasure b 1).map (fun y : ℝ ↦ Real.exp (-y)), x ∈ Icc (0 : ℝ) 1 := by
    apply (ae_map_iff hlim.aemeasurable measurableSet_Icc).2
    filter_upwards [TauCeti.Probability.ae_pos_gammaMeasure b 1] with y hy
    exact ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.2 (by linarith)⟩
  have hμsupport (n : ℕ) : ∀ᵐ x ∂(betaMeasure (a n) b).map (fun x : ℝ ↦ x ^ (a n)), x ∈ Icc (0 : ℝ) 1 := by
    apply (ae_map_iff (hmap n).aemeasurable measurableSet_Icc).2
    filter_upwards [TauCeti.Probability.ae_mem_Icc_betaMeasure (a n) b] with x hx
    exact ⟨Real.rpow_nonneg hx.1 _, Real.rpow_le_one hx.1 hx.2 (ha n).le⟩
  let μs : ℕ → ProbabilityMeasure ℝ := fun n ↦ ⟨(betaMeasure (a n) b).map (fun x : ℝ ↦ x ^ (a n)), by infer_instance⟩
  let ν : ProbabilityMeasure ℝ := ⟨(gammaMeasure b 1).map (fun y : ℝ ↦ Real.exp (-y)), by infer_instance⟩
  change Tendsto μs atTop (𝓝 ν)
  apply ProbabilityMeasure.tendsto_of_tendsto_integral_pow (μs := μs) (μ := ν) isCompact_Icc
    (by change ((gammaMeasure b 1).map (fun y : ℝ ↦ Real.exp (-y))) (Icc (0 : ℝ) 1)ᶜ = 0; exact ae_iff.1 hνsupport)
  · intro k
    refine Eventually.of_forall fun n ↦ ?_
    change Integrable (fun x : ℝ ↦ x ^ k) ((betaMeasure (a n) b).map (fun x : ℝ ↦ x ^ (a n)))
    exact Integrable.of_bound (by fun_prop) 1 ((hμsupport n).mono fun x hx ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hx.1 _)]
        exact pow_le_one₀ hx.1 hx.2)
  · intro k
    have hνmoment : (∫ x, x ^ k ∂(gammaMeasure b 1).map (fun y : ℝ ↦ Real.exp (-y))) =
        (1 + (k : ℝ)) ^ (-b) := by
      rw [integral_map hlim.aemeasurable (by fun_prop)]
      have hmgf := TauCeti.Probability.mgf_id_gammaMeasure hb zero_lt_one (t := -(k : ℝ)) (by have := Nat.cast_nonneg (α := ℝ) k; linarith)
      rw [mgf] at hmgf
      convert hmgf using 1 <;> simp only [id_eq, div_one, sub_neg_eq_add]
      congr 1
      funext x
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    change Tendsto (fun n ↦ ∫ x : ℝ, x ^ k ∂(betaMeasure (a n) b).map (fun x : ℝ ↦ x ^ (a n))) atTop
      (𝓝 (∫ x : ℝ, x ^ k ∂(gammaMeasure b 1).map (fun y : ℝ ↦ Real.exp (-y))))
    rw [hνmoment]
    convert tendsto_integral_beta_rpow_pow ha hatop hb k using 1
    funext n
    rw [integral_map (hmap n).aemeasurable (by fun_prop)]

/-- Convergence of exponentiated negative variables to an exponentiated Gamma law implies
convergence of the variables themselves; positive closed tails handle the logarithmic endpoint. -/
theorem tendstoInDistribution_of_exp_neg_gamma {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] (μ : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (X : (n : ℕ) → Ω n → ℝ) (hX : ∀ n, Measurable (X n)) {b : ℝ} (hb : 0 < b) :
    let : IsProbabilityMeasure (gammaMeasure b 1) := isProbabilityMeasure_gammaMeasure hb zero_lt_one;
    TendstoInDistribution (fun n ω ↦ Real.exp (-X n ω)) atTop (fun y : ℝ ↦ Real.exp (-y)) μ (gammaMeasure b 1) →
      TendstoInDistribution X atTop id μ (gammaMeasure b 1) := by
  let : IsProbabilityMeasure (gammaMeasure b 1) := isProbabilityMeasure_gammaMeasure hb zero_lt_one
  dsimp only
  intro hpow
  have hm (n : ℕ) : Measurable (fun ω ↦ Real.exp (-X n ω)) := (hX n).neg.exp
  have he : Measurable (fun y : ℝ ↦ Real.exp (-y)) := by fun_prop
  let μs : ℕ → ProbabilityMeasure ℝ := fun n ↦ ⟨(μ n).map (fun ω ↦ Real.exp (-X n ω)), by infer_instance⟩
  let ν : ProbabilityMeasure ℝ := ⟨(gammaMeasure b 1).map (fun y : ℝ ↦ Real.exp (-y)), by infer_instance⟩
  have hweak : Tendsto μs atTop (𝓝 ν) := hpow.tendsto
  apply TendstoInDistribution.of_tendsto_cdf (fun n ↦ (hX n).aemeasurable) measurable_id.aemeasurable
  intro x
  have hboundary : (ν : Measure ℝ) (frontier (Ici (Real.exp (-x)))) = 0 := by
    change ((gammaMeasure b 1).map (fun y : ℝ ↦ Real.exp (-y))) (frontier (Ici (Real.exp (-x)))) = 0
    rw [frontier_Ici, Measure.map_apply he (measurableSet_singleton _)]
    have hs : (fun y : ℝ ↦ Real.exp (-y)) ⁻¹' {Real.exp (-x)} = {x} := by
      ext y
      simp only [mem_preimage, mem_singleton_iff, Real.exp_eq_exp, neg_inj]
    rw [hs, measure_singleton]
  have htail := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hweak hboundary
  have hr := (ENNReal.continuousAt_toReal (measure_ne_top (ν : Measure ℝ) _)).tendsto.comp htail
  have hlim : (ν : Measure ℝ) (Ici (Real.exp (-x))) = gammaMeasure b 1 (Iic x) := by
    change ((gammaMeasure b 1).map (fun y : ℝ ↦ Real.exp (-y))) (Ici (Real.exp (-x))) = _
    rw [Measure.map_apply he measurableSet_Ici]
    congr 1
    ext y
    simp only [mem_preimage, mem_Ici, mem_Iic, Real.exp_le_exp, neg_le_neg_iff]
  have hn (n : ℕ) : cdf ((μ n).map (X n)) x = ((μs n : Measure ℝ) (Ici (Real.exp (-x)))).toReal := by
    rw [cdf_eq_real, Measure.real, Measure.map_apply (hX n) measurableSet_Iic]
    change ((μ n) ((X n) ⁻¹' Iic x)).toReal =
      (((μ n).map (fun ω ↦ Real.exp (-X n ω))) (Ici (Real.exp (-x)))).toReal
    rw [Measure.map_apply (hm n) measurableSet_Ici]
    congr 1
    congr 1
    ext ω
    simp only [mem_preimage, mem_Iic, mem_Ici, Real.exp_le_exp, neg_le_neg_iff]
  simp only [Measure.map_id, cdf_eq_real, Measure.real, hlim] at hr ⊢
  convert hr using 1
  funext n
  simpa only [cdf_eq_real, Measure.real, Function.comp_apply] using hn n

/-- Growing-shape Beta logarithms have a Gamma limit with the exact unit rate. -/
theorem tendstoInDistribution_neg_mul_log_beta {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    (hatop : Tendsto a atTop atTop) {b : ℝ} (hb : 0 < b) :
    let : ∀ n, IsProbabilityMeasure (betaMeasure (a n) b) := fun n ↦ isProbabilityMeasureBeta (ha n) hb;
    let : IsProbabilityMeasure (gammaMeasure b 1) := isProbabilityMeasure_gammaMeasure hb zero_lt_one;
    TendstoInDistribution (fun (n : ℕ) (x : ℝ) ↦ -(a n) * Real.log x) atTop id
      (fun n ↦ betaMeasure (a n) b) (gammaMeasure b 1) := by
  let : ∀ n, IsProbabilityMeasure (betaMeasure (a n) b) := fun n ↦ isProbabilityMeasureBeta (ha n) hb
  let : IsProbabilityMeasure (gammaMeasure b 1) := isProbabilityMeasure_gammaMeasure hb zero_lt_one
  apply tendstoInDistribution_of_exp_neg_gamma _ _ (fun n ↦ by fun_prop) hb
  apply (tendstoInDistribution_beta_rpow ha hatop hb).congr _ (EventuallyEq.rfl)
  intro n
  filter_upwards [TauCeti.Probability.ae_mem_Ioo_betaMeasure (a n) b] with z hz
  rw [Real.rpow_def_of_pos hz.1]
  congr 1
  ring

end CKSD
