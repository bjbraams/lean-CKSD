module

public import CKSD.LinearModels.BetaLogLimit
public import Mathlib.MeasureTheory.Integral.Pi
/-!
# Gamma limits of finite Beta-product likelihood ratios

Independent Beta factors with growing first shapes and a common asymptotically equal
scale have a logarithmic product converging to a Gamma law. The limiting shape is exactly
the sum of the fixed second shapes. The proof computes moments after exponentiation,
uses the compact method of moments, and then transfers back through positive closed tails.

Mathlib supplies finite-product integration and weak-convergence operations; TauCeti
supplies Beta and Gamma laws and moment determinacy. The scalar asymptotics and inverse
exponential convergence argument are local project code.
-/

@[expose] public section
noncomputable section
open Filter Set Real MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace CKSD

/-- The growing-shape Beta power moment limit permits any asymptotically equal power scale. -/
theorem tendsto_integral_beta_rpow_pow_of_ratio {a t : ℕ → ℝ}
    (ha : ∀ n, 0 < a n) (ht : ∀ n, 0 < t n) (hatop : Tendsto a atTop atTop)
    (hratio : Tendsto (fun n ↦ t n / a n) atTop (𝓝 1)) {b : ℝ} (hb : 0 < b) (k : ℕ) :
    Tendsto (fun n ↦ ∫ x, (x ^ (t n)) ^ k ∂betaMeasure (a n) b) atTop
      (𝓝 ((1 + (k : ℝ)) ^ (-b))) := by
  let c : ℕ → ℝ := fun n ↦ a n + t n * k
  have hc (n : ℕ) : 0 < c n := add_pos_of_pos_of_nonneg (ha n) (mul_nonneg (ht n).le (Nat.cast_nonneg k))
  have hctop : Tendsto c atTop atTop := tendsto_atTop_mono
    (fun n ↦ le_add_of_nonneg_right (mul_nonneg (ht n).le (Nat.cast_nonneg k))) hatop
  have hcratio : Tendsto (fun n ↦ c n / a n) atTop (𝓝 (1 + (k : ℝ))) := by
    have heq : (fun n ↦ c n / a n) = (fun n ↦ 1 + (t n / a n) * k) := by
      funext n
      dsimp [c]
      field_simp [(ha n).ne']
    rw [heq]
    simpa only [mul_one, one_mul] using tendsto_const_nhds.add (hratio.mul_const (k : ℝ))
  have hpower := (Real.continuousAt_rpow_const (1 + (k : ℝ)) (-b) (Or.inl (by positivity))).tendsto.comp hcratio
  let R : ℝ → ℝ := fun x ↦ Real.Gamma (x + b) / (Real.Gamma x * x ^ b)
  have hR : Tendsto R atTop (𝓝 1) := tendsto_gamma_add_div_mul_rpow hb
  have hlim := ((hR.comp hatop).div (hR.comp hctop) one_ne_zero).mul hpower
  simp only [div_self one_ne_zero, one_mul] at hlim
  apply hlim.congr'
  exact Eventually.of_forall fun n ↦ by
    dsimp only
    change (R (a n) / R (c n)) * (c n / a n) ^ (-b) = _
    have hmoment : (∫ x, (x ^ (t n)) ^ k ∂betaMeasure (a n) b) =
        Real.Gamma (c n) * Real.Gamma (a n + b) /
          (Real.Gamma (a n) * Real.Gamma (c n + b)) := by
      calc _ = ∫ x, x ^ (t n * k) ∂betaMeasure (a n) b := by
              apply integral_congr_ae
              filter_upwards [TauCeti.Probability.ae_mem_Ioo_betaMeasure (a n) b] with x hx
              rw [← Real.rpow_natCast, ← Real.rpow_mul hx.1.le]
        _ = _ := by
          rw [integral_rpow_beta_measure (ha n) hb (mul_nonneg (ht n).le (Nat.cast_nonneg k))]
          rw [show a n + b + t n * k = c n + b by dsimp [c]; ring]
    rw [hmoment]
    dsimp [R]
    rw [Real.rpow_neg (div_pos (hc n) (ha n)).le, Real.div_rpow (hc n).le (ha n).le]
    field_simp [(Real.Gamma_pos_of_pos (ha n)).ne', (Real.Gamma_pos_of_pos (hc n)).ne',
      (Real.Gamma_pos_of_pos (add_pos (hc n) hb)).ne',
      (Real.rpow_pos_of_pos (ha n) b).ne', (Real.rpow_pos_of_pos (hc n) b).ne']

/-- Positive Beta factors give a probability measure on their finite product. -/
theorem is_probability_measure_pi_beta {ι : Type*} [Fintype ι] (a b : ι → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) :
    IsProbabilityMeasure (Measure.pi fun i ↦ betaMeasure (a i) (b i)) := by
  let : ∀ i, IsProbabilityMeasure (betaMeasure (a i) (b i)) := fun i ↦ isProbabilityMeasureBeta (ha i) (hb i)
  infer_instance

/-- Finite products of asymptotically equal-scale Beta powers have an exponentiated Gamma limit. -/
theorem tendsto_in_distribution_beta_product_rpow {ι : Type*} [Fintype ι] [Nonempty ι]
    (a : ι → ℕ → ℝ) (b : ι → ℝ) (t : ℕ → ℝ)
    (ha : ∀ i n, 0 < a i n) (hb : ∀ i, 0 < b i) (ht : ∀ n, 0 < t n)
    (hatop : ∀ i, Tendsto (a i) atTop atTop)
    (hratio : ∀ i, Tendsto (fun n ↦ t n / a i n) atTop (𝓝 1)) :
    let : ∀ n, IsProbabilityMeasure (Measure.pi fun i ↦ betaMeasure (a i n) (b i)) :=
      fun n ↦ is_probability_measure_pi_beta _ _ (fun i ↦ ha i n) hb;
    let : IsProbabilityMeasure (gammaMeasure (∑ i, b i) 1) :=
      isProbabilityMeasure_gammaMeasure (Finset.sum_pos (fun i _ ↦ hb i) Finset.univ_nonempty) zero_lt_one;
    TendstoInDistribution (fun (n : ℕ) (x : ι → ℝ) ↦ ∏ i, x i ^ (t n)) atTop
      (fun y : ℝ ↦ Real.exp (-y)) (fun n ↦ Measure.pi fun i ↦ betaMeasure (a i n) (b i))
      (gammaMeasure (∑ i, b i) 1) := by
  have hbS : 0 < ∑ i, b i := Finset.sum_pos (fun i _ ↦ hb i) Finset.univ_nonempty
  let : ∀ n, IsProbabilityMeasure (Measure.pi fun i ↦ betaMeasure (a i n) (b i)) :=
    fun n ↦ is_probability_measure_pi_beta _ _ (fun i ↦ ha i n) hb
  let : ∀ n i, IsProbabilityMeasure (betaMeasure (a i n) (b i)) := fun n i ↦ isProbabilityMeasureBeta (ha i n) (hb i)
  let : IsProbabilityMeasure (gammaMeasure (∑ i, b i) 1) := isProbabilityMeasure_gammaMeasure hbS zero_lt_one
  let U : ℕ → (ι → ℝ) → ℝ := fun n x ↦ ∏ i, x i ^ (t n)
  let μprod : ℕ → Measure (ι → ℝ) := fun n ↦ Measure.pi fun i ↦ betaMeasure (a i n) (b i)
  have hUm (n : ℕ) : Measurable (U n) := Finset.measurable_fun_prod _ fun i _ ↦ (measurable_pi_apply i).pow_const _
  have he : Measurable (fun y : ℝ ↦ Real.exp (-y)) := by fun_prop
  refine ⟨fun n ↦ (hUm n).aemeasurable, he.aemeasurable, ?_⟩
  let μs : ℕ → ProbabilityMeasure ℝ := fun n ↦ ⟨(μprod n).map (U n), by infer_instance⟩
  let ν : ProbabilityMeasure ℝ := ⟨(gammaMeasure (∑ i, b i) 1).map (fun y : ℝ ↦ Real.exp (-y)), by infer_instance⟩
  change Tendsto μs atTop (𝓝 ν)
  have hμsupport (n : ℕ) : ∀ᵐ z ∂(μprod n).map (U n), z ∈ Icc (0 : ℝ) 1 := by
    apply (ae_map_iff (hUm n).aemeasurable measurableSet_Icc).2
    have hs : ∀ᵐ x ∂μprod n, ∀ i, x i ∈ Icc (0 : ℝ) 1 := ae_all_iff.2 fun i ↦
      Measure.tendsto_eval_ae_ae.eventually (TauCeti.Probability.ae_mem_Icc_betaMeasure (a i n) (b i))
    filter_upwards [hs] with x hx
    have hp (i : ι) : x i ^ (t n) ∈ Icc (0 : ℝ) 1 :=
      ⟨Real.rpow_nonneg (hx i).1 _, Real.rpow_le_one (hx i).1 (hx i).2 (ht n).le⟩
    exact ⟨Finset.prod_nonneg fun i _ ↦ (hp i).1, Finset.prod_le_one₀ (fun i _ ↦ (hp i).1) (fun i _ ↦ (hp i).2)⟩
  have hνsupport : ∀ᵐ z ∂(gammaMeasure (∑ i, b i) 1).map (fun y : ℝ ↦ Real.exp (-y)), z ∈ Icc (0 : ℝ) 1 := by
    apply (ae_map_iff he.aemeasurable measurableSet_Icc).2
    filter_upwards [TauCeti.Probability.ae_pos_gammaMeasure (∑ i, b i) 1] with y hy
    exact ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.2 (by linarith)⟩
  apply ProbabilityMeasure.tendsto_of_tendsto_integral_pow (μs := μs) (μ := ν) isCompact_Icc
    (by change ((gammaMeasure (∑ i, b i) 1).map (fun y : ℝ ↦ Real.exp (-y))) (Icc (0 : ℝ) 1)ᶜ = 0; exact ae_iff.1 hνsupport)
  · intro k
    refine Eventually.of_forall fun n ↦ ?_
    change Integrable (fun z : ℝ ↦ z ^ k) ((μprod n).map (U n))
    exact Integrable.of_bound (by fun_prop) 1 ((hμsupport n).mono fun z hz ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hz.1 _)]
      exact pow_le_one₀ hz.1 hz.2)
  · intro k
    change Tendsto (fun n ↦ ∫ z : ℝ, z ^ k ∂(μprod n).map (U n)) atTop
      (𝓝 (∫ z : ℝ, z ^ k ∂(gammaMeasure (∑ i, b i) 1).map (fun y : ℝ ↦ Real.exp (-y))))
    have hνmoment : (∫ z : ℝ, z ^ k ∂(gammaMeasure (∑ i, b i) 1).map (fun y : ℝ ↦ Real.exp (-y))) =
        (1 + (k : ℝ)) ^ (-(∑ i, b i)) := by
      rw [integral_map he.aemeasurable (by fun_prop)]
      have hmgf := TauCeti.Probability.mgf_id_gammaMeasure hbS zero_lt_one (t := -(k : ℝ))
        (by have := Nat.cast_nonneg (α := ℝ) k; linarith)
      rw [mgf] at hmgf
      convert hmgf using 1 <;> simp only [id_eq, div_one, sub_neg_eq_add]
      congr 1
      funext x
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [hνmoment]
    have hlim := tendsto_finsetProd (Finset.univ : Finset ι) (fun i _ ↦
      tendsto_integral_beta_rpow_pow_of_ratio (ha i) ht (hatop i) (hratio i) (hb i) k)
    have hprod : ∏ i, (1 + (k : ℝ)) ^ (-b i) = (1 + (k : ℝ)) ^ (-(∑ i, b i)) := by
      rw [← Real.rpow_sum_of_pos (by positivity) _ _, Finset.sum_neg_distrib]
    rw [hprod] at hlim
    apply hlim.congr'
    exact Eventually.of_forall fun n ↦ by
      dsimp only
      rw [integral_map (hUm n).aemeasurable (by fun_prop)]
      dsimp only [U, μprod]
      rw [← integral_fintype_prod_eq_prod (fun (i : ι) (x : ℝ) ↦ (x ^ (t n)) ^ k)]
      congr 1
      funext x
      exact Finset.prod_pow _ _ _

/-- The logarithm of a finite independent Beta product converges to a Gamma law when the
first shapes share a growing common scale; the limiting shape is the sum of second shapes. -/
theorem tendsto_in_distribution_neg_mul_log_beta_product {ι : Type*} [Fintype ι] [Nonempty ι]
    (a : ι → ℕ → ℝ) (b : ι → ℝ) (t : ℕ → ℝ)
    (ha : ∀ i n, 0 < a i n) (hb : ∀ i, 0 < b i) (ht : ∀ n, 0 < t n)
    (hatop : ∀ i, Tendsto (a i) atTop atTop)
    (hratio : ∀ i, Tendsto (fun n ↦ t n / a i n) atTop (𝓝 1)) :
    let : ∀ n, IsProbabilityMeasure (Measure.pi fun i ↦ betaMeasure (a i n) (b i)) :=
      fun n ↦ is_probability_measure_pi_beta _ _ (fun i ↦ ha i n) hb;
    let : IsProbabilityMeasure (gammaMeasure (∑ i, b i) 1) :=
      isProbabilityMeasure_gammaMeasure (Finset.sum_pos (fun i _ ↦ hb i) Finset.univ_nonempty) zero_lt_one;
    TendstoInDistribution (fun (n : ℕ) (x : ι → ℝ) ↦ -(t n) * Real.log (∏ i, x i)) atTop id
      (fun n ↦ Measure.pi fun i ↦ betaMeasure (a i n) (b i)) (gammaMeasure (∑ i, b i) 1) := by
  have hbS : 0 < ∑ i, b i := Finset.sum_pos (fun i _ ↦ hb i) Finset.univ_nonempty
  let : ∀ n, IsProbabilityMeasure (Measure.pi fun i ↦ betaMeasure (a i n) (b i)) :=
    fun n ↦ is_probability_measure_pi_beta _ _ (fun i ↦ ha i n) hb
  let : ∀ n i, IsProbabilityMeasure (betaMeasure (a i n) (b i)) := fun n i ↦ isProbabilityMeasureBeta (ha i n) (hb i)
  let : IsProbabilityMeasure (gammaMeasure (∑ i, b i) 1) := isProbabilityMeasure_gammaMeasure hbS zero_lt_one
  have hXm (n : ℕ) : Measurable (fun x : ι → ℝ ↦ -(t n) * Real.log (∏ i, x i)) := by fun_prop
  apply tendsto_in_distribution_of_exp_neg_gamma _ _ hXm hbS
  apply (tendsto_in_distribution_beta_product_rpow a b t ha hb ht hatop hratio).congr _ (EventuallyEq.rfl)
  intro n
  have hs : ∀ᵐ x ∂Measure.pi (fun i ↦ betaMeasure (a i n) (b i)), ∀ i, x i ∈ Ioo (0 : ℝ) 1 :=
    ae_all_iff.2 fun i ↦ Measure.tendsto_eval_ae_ae.eventually
      (TauCeti.Probability.ae_mem_Ioo_betaMeasure (a i n) (b i))
  filter_upwards [hs] with x hx
  have hprodlog : Real.log (∏ i, x i) = ∑ i, Real.log (x i) := Real.log_prod (fun i _ ↦ (hx i).1.ne')
  rw [hprodlog]
  have he : -(-(t n) * ∑ i, Real.log (x i)) = ∑ i, (t n) * Real.log (x i) := by
    rw [← Finset.mul_sum]
    ring
  rw [he, Real.exp_sum]
  apply Finset.prod_congr rfl
  intro i _
  rw [Real.rpow_def_of_pos (hx i).1]
  congr 1
  ring

end CKSD
