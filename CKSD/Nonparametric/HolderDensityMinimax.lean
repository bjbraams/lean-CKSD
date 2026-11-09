module

public import CKSD.Nonparametric.SmoothingRates

/-!
# Pointwise minimax rate for Hölder density estimation

The minimax rate `n^(-2β/(2β+1))` for pointwise estimation of a probability density on the line
in the Hölder class of order `β ∈ (0, 1]` (GAPS 103.26). The upper bound is attained by a kernel
density estimator; minimax risks are infima over measurable estimators of suprema of
`ℝ≥0∞`-valued risks.

## Main definitions

* `CKSD.holderDensityClass β L`: probability densities on `ℝ` with
  `|f x - f y| ≤ L |x - y|^β`; `CKSD.mem_holderDensityClass_iff` identifies it with Mathlib's
  `HolderWith`.
* `CKSD.densityLaw`, `CKSD.holderDensityPointwiseMinimaxRisk`: the law with a given density
  and the pointwise minimax squared risk.

## Main results

* `CKSD.finiteKernelDensityEstimator_risk_le`: the upper bound for the kernel density estimator.
* `CKSD.holderDensityPointwiseMinimaxRisk_lower_bound`: the matching lower bound. It is Le Cam's
  two-point method: a Cauchy density of large scale against its perturbation by two opposite
  tents of height of order `h^β` and width `h = n^(-1/(2β+1)) / 2`, with the Kullback–Leibler
  divergence of the `n`-fold products bounded through the chi-square integral and Statlib's
  tensorization.
* `CKSD.klDiv_densityLaw_le`: `KL(f₁, f₀) ≤ ∫ (f₁ - f₀)² / f₀` for a positive density `f₀`.
* `CKSD.ofReal_mul_measureReal_le_lintegral_sq`: Markov's inequality for the squared error.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace CKSD

/-- Probability densities on the line with the Hölder bound `|f x - f y| ≤ L |x - y|^β`.
Integrability is implied by `∫ f = 1`. -/
def holderDensityClass (β L : ℝ) : Set (ℝ → ℝ) :=
  {f | Measurable f ∧ (∀ x, 0 ≤ f x) ∧ (∫ x, f x) = 1 ∧
    ∀ x y, |f x - f y| ≤ L * Real.rpow |x - y| β}

/-- A member of the Hölder density class is integrable. -/
theorem integrable_of_mem_holderDensityClass {β L : ℝ} {f : ℝ → ℝ}
    (hf : f ∈ holderDensityClass β L) : Integrable f volume :=
  Integrable.of_integral_ne_zero (by rw [hf.2.2.1]; norm_num)

/-- For nonnegative parameters, the Hölder density class consists of the measurable
probability densities satisfying Mathlib's `HolderWith L β`. -/
theorem mem_holderDensityClass_iff {β L : ℝ≥0} {f : ℝ → ℝ} :
    f ∈ holderDensityClass β L ↔
      Measurable f ∧ (∀ x, 0 ≤ f x) ∧ (∫ x, f x) = 1 ∧ HolderWith L β f := by
  simp only [holderDensityClass, mem_ofPred_eq, Real.rpow_eq_pow, ← holderOnWith_univ,
    holderOnWith_iff_abs_sub_le, mem_univ, true_imp_iff]

/-- The probability law represented by a real density. -/
def densityLaw (f : ℝ → ℝ) : Measure ℝ :=
  volume.withDensity (fun x ↦ ENNReal.ofReal (f x))

/-- Pointwise minimax risk for density estimation on a Hölder class. -/
def holderDensityPointwiseMinimaxRisk (n : ℕ) (β L x : ℝ) : ℝ≥0∞ :=
  ⨅ T : {T : (Fin n → ℝ) → ℝ // Measurable T},
    ⨆ f : holderDensityClass β L,
      ∫⁻ sample, ENNReal.ofReal ((T.val sample - f.val x) ^ 2)
        ∂(Measure.pi fun _ : Fin n ↦ densityLaw f.val)

/-- Mean squared error of a sample mean under a product law: bias squared plus at most the
second moment divided by the sample size. -/
theorem integral_sq_sampleMean_sub_le {P : Measure ℝ} [IsProbabilityMeasure P] {n : ℕ}
    (hn : 0 < n) {g : ℝ → ℝ} (hg : MemLp g 2 P) (a : ℝ) :
    MemLp (fun ω : Fin n → ℝ ↦ (∑ i, g (ω i)) / n - a) 2 (Measure.pi fun _ ↦ P) ∧
    ∫ ω, ((∑ i, g (ω i)) / n - a) ^ 2 ∂(Measure.pi fun _ : Fin n ↦ P) ≤
      (∫ y, g y ∂P - a) ^ 2 + (∫ y, g y ^ 2 ∂P) / n := by
  set μ := Measure.pi fun _ : Fin n ↦ P with hμ
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hXi : ∀ i : Fin n, MemLp (fun ω : Fin n → ℝ ↦ g (ω i)) 2 μ := fun i ↦
    hg.comp_measurePreserving (measurePreserving_eval _ i)
  have hS : MemLp (fun ω : Fin n → ℝ ↦ ∑ i, g (ω i)) 2 μ := memLp_finsetSum _ fun i _ ↦ hXi i
  have hW : MemLp (fun ω : Fin n → ℝ ↦ (∑ i, g (ω i)) / n - a) 2 μ := by
    have e : (fun ω : Fin n → ℝ ↦ (∑ i, g (ω i)) / n - a) =
        fun ω ↦ (1 / (n : ℝ)) * (∑ i, g (ω i)) - a := by funext ω; ring
    rw [e]
    exact (hS.const_mul _).sub (memLp_const a)
  refine ⟨hW, ?_⟩
  have hEi : ∀ i : Fin n, ∫ ω, g (ω i) ∂μ = ∫ y, g y ∂P := fun i ↦ by
    have hmap := (measurePreserving_eval (fun _ : Fin n ↦ P) i).map_eq
    calc ∫ ω, g (ω i) ∂μ = ∫ y, g y ∂(μ.map (fun ω ↦ ω i)) :=
          (integral_map (measurable_pi_apply i).aemeasurable
            (by rw [hμ, hmap]; exact hg.aestronglyMeasurable)).symm
      _ = _ := by rw [hμ, hmap]
  have hES : ∫ ω, (∑ i, g (ω i)) ∂μ = n * ∫ y, g y ∂P := by
    rw [integral_finsetSum _ fun i _ ↦ (hXi i).integrable one_le_two]
    simp [hEi]
  have hEW : ∫ ω, ((∑ i, g (ω i)) / n - a) ∂μ = ∫ y, g y ∂P - a := by
    rw [integral_sub ((hS.integrable one_le_two).div_const _) (integrable_const a), integral_div,
      hES, integral_const]
    simp only [probReal_univ, smul_eq_mul, one_mul]
    field_simp
  have hVS : Var[fun ω : Fin n → ℝ ↦ ∑ i, g (ω i); μ] = n * Var[g; P] := by
    have := variance_sum_pi (μ := fun _ : Fin n ↦ P) (X := fun _ ↦ g) (fun _ ↦ hg)
    rw [hμ]
    convert this using 2
    · ext ω; simp
    · simp
  have hVW : Var[fun ω : Fin n → ℝ ↦ (∑ i, g (ω i)) / n - a; μ] = Var[g; P] / n := by
    rw [variance_sub_const ((hS.const_mul (1 / (n : ℝ))).aestronglyMeasurable.congr
      (Filter.Eventually.of_forall fun ω ↦ by simp only; ring))]
    have : (fun ω : Fin n → ℝ ↦ (∑ i, g (ω i)) / n) =
        fun ω ↦ (1 / (n : ℝ)) * ∑ i, g (ω i) := by ext ω; ring
    rw [this, variance_const_mul, hVS]
    field_simp
  have hV := variance_eq_sub hW
  rw [hVW] at hV
  have hle := variance_le_expectation_sq hg.aestronglyMeasurable
  have e : ∫ ω, ((∑ i, g (ω i)) / n - a) ^ 2 ∂μ =
      Var[g; P] / n + (∫ y, g y ∂P - a) ^ 2 := by
    rw [← hEW]
    have : μ[(fun ω : Fin n → ℝ ↦ (∑ i, g (ω i)) / n - a) ^ 2] =
        ∫ ω, ((∑ i, g (ω i)) / n - a) ^ 2 ∂μ := rfl
    linarith
  rw [e]
  have : Var[g; P] / n ≤ (∫ y, g y ^ 2 ∂P) / n := by
    apply div_le_div_of_nonneg_right _ hnR.le
    exact hle
  linarith

/-- A Hölder probability density of order `β ∈ (0, 1]` is bounded by `1 / 2 + L`. -/
theorem le_of_mem_holderDensityClass {β L : ℝ} (hβ : 0 < β) {f : ℝ → ℝ}
    (hf : f ∈ holderDensityClass β L) (x : ℝ) : f x ≤ 1 / 2 + L := by
  have hfi := integrable_of_mem_holderDensityClass hf
  obtain ⟨hfm, hf0, hf1, hfh⟩ := hf
  have hle : ∀ y ∈ Icc (x - 1) (x + 1), f x - L ≤ f y := by
    intro y hy
    have h1 : |x - y| ≤ 1 := abs_le.mpr ⟨by linarith [hy.2], by linarith [hy.1]⟩
    have h2 : Real.rpow |x - y| β ≤ 1 := Real.rpow_le_one (abs_nonneg _) h1 hβ.le
    have h3 := hfh x y
    have hL : 0 ≤ L := by
      have := hfh x (x + 1)
      have h0 : (0 : ℝ) < Real.rpow |x - (x + 1)| β := by
        simp only [sub_add_cancel_left, abs_neg, abs_one]; norm_num
      by_contra hneg; push Not at hneg
      have : L * Real.rpow |x - (x + 1)| β < 0 := mul_neg_of_neg_of_pos hneg h0
      linarith [abs_nonneg (f x - f (x + 1))]
    have := abs_le.mp h3
    nlinarith [this.1]
  have hmono := intervalIntegral.integral_mono_on (by linarith : x - 1 ≤ x + 1)
    (intervalIntegrable_const (c := f x - L)) hfi.intervalIntegrable hle
  rw [intervalIntegral.integral_const, smul_eq_mul,
    intervalIntegral.integral_of_le (by linarith : x - 1 ≤ x + 1)] at hmono
  have hint : ∫ y in Ioc (x - 1) (x + 1), f y ≤ ∫ y, f y :=
    setIntegral_le_integral hfi (Filter.Eventually.of_forall hf0)
  rw [hf1] at hint
  have : x + 1 - (x - 1) = 2 := by ring
  rw [this] at hmono
  linarith

/-- The law with a probability density is a probability measure. -/
theorem isProbabilityMeasure_densityLaw {f : ℝ → ℝ} (hf0 : ∀ x, 0 ≤ f x)
    (hfi : Integrable f volume) (hf1 : ∫ x, f x = 1) : IsProbabilityMeasure (densityLaw f) := by
  refine ⟨?_⟩
  rw [densityLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hfi (Filter.Eventually.of_forall hf0), hf1,
    ENNReal.ofReal_one]

/-- Integrals against a density law. -/
theorem integral_densityLaw {f : ℝ → ℝ} (hfm : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (φ : ℝ → ℝ) : ∫ y, φ y ∂densityLaw f = ∫ y, f y * φ y := by
  rw [densityLaw, integral_withDensity_eq_integral_toReal_smul hfm.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
  simp only [ENNReal.toReal_ofReal (hf0 y), smul_eq_mul]

/-- Integrability against a density law. -/
theorem integrable_densityLaw_iff {f : ℝ → ℝ} (hfm : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (φ : ℝ → ℝ) : Integrable φ (densityLaw f) ↔ Integrable (fun y ↦ f y * φ y) := by
  rw [densityLaw, integrable_withDensity_iff_integrable_smul' hfm.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  refine integrable_congr (Filter.Eventually.of_forall fun y ↦ ?_)
  simp only [ENNReal.toReal_ofReal (hf0 y), smul_eq_mul]

/-- Change of variables `u = (x - y) / h` on the line. -/
theorem integral_comp_sub_div {h : ℝ} (hh : 0 < h) (x : ℝ) (ψ : ℝ → ℝ) :
    ∫ y, ψ ((x - y) / h) = h * ∫ u, ψ u := by
  rw [integral_sub_left_eq_self (fun z ↦ ψ (z / h)) volume x, Measure.integral_comp_div ψ h,
    abs_of_pos hh, smul_eq_mul]

/-- GAPS 103.26: the kernel upper bound for pointwise Hölder density risk with `0<β≤1`.
The moment condition is the order-zero kernel condition appropriate in this range. -/
theorem finiteKernelDensityEstimator_risk_le (β L c : ℝ)
    (hβ : β ∈ Ioc (0 : ℝ) 1) (hL : 0 < L) (hc : 0 < c)
    (K : ℝ → ℝ) (hK : Measurable K) (hK1 : (∫ x, K x) = 1) (hK2 : MemLp K 2 volume)
    (hKm : Integrable (fun x ↦ Real.rpow |x| β * |K x|) volume) :
    ∃ C > (0 : ℝ), ∀ n : ℕ, 0 < n → ∀ f ∈ holderDensityClass β L, ∀ x : ℝ,
      (∫⁻ sample, ENNReal.ofReal
        ((finiteKernelDensityEstimator K (c * Real.rpow (n : ℝ) (-1 / (2 * β + 1))) sample x -
          f x) ^ 2) ∂(Measure.pi fun _ : Fin n ↦ densityLaw f)) ≤
      ENNReal.ofReal (C * Real.rpow (n : ℝ) (-2 * β / (2 * β + 1))) := by
  obtain ⟨hβ0, -⟩ := hβ
  have hKi : Integrable K volume := Integrable.of_integral_ne_zero (by rw [hK1]; norm_num)
  simp only [Real.rpow_eq_pow] at hKm ⊢
  set MK := ∫ u, |u| ^ β * |K u| with hMK
  set K2 := ∫ u, K u ^ 2 with hK2def
  set B := 1 / 2 + L with hB
  have hMK0 : 0 ≤ MK :=
    integral_nonneg fun u ↦ mul_nonneg (Real.rpow_nonneg (abs_nonneg u) β) (abs_nonneg _)
  have hK20 : 0 ≤ K2 := integral_nonneg fun u ↦ sq_nonneg _
  have hB0 : 0 < B := by linarith
  have hKsq : Integrable (fun u ↦ K u ^ 2) volume := hK2.integrable_sq
  refine ⟨L ^ 2 * c ^ (2 * β) * MK ^ 2 + B * K2 / c + 1, by positivity, ?_⟩
  intro n hn f hf x
  have hfB : ∀ y, f y ≤ B := le_of_mem_holderDensityClass hβ0 hf
  have hfi := integrable_of_mem_holderDensityClass hf
  obtain ⟨hfm, hf0, hf1, hfh⟩ := hf
  simp only [Real.rpow_eq_pow] at hfh
  have := isProbabilityMeasure_densityLaw hf0 hfi hf1
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set e := (n : ℝ) ^ (-1 / (2 * β + 1)) with he
  set r := (n : ℝ) ^ (-2 * β / (2 * β + 1)) with hr
  have he0 : 0 < e := Real.rpow_pos_of_pos hnR _
  have hr0 : 0 < r := Real.rpow_pos_of_pos hnR _
  set h := c * e with hh
  have hh0 : 0 < h := mul_pos hc he0
  set g : ℝ → ℝ := fun y ↦ K ((x - y) / h) / h with hg
  have hgm : Measurable g :=
    (hK.comp ((measurable_const.sub measurable_id).div_const h)).div_const h
  -- second moment
  have hR : Integrable (fun y ↦ K ((x - y) / h) ^ 2) volume :=
    (hKsq.comp_div hh0.ne').comp_sub_left x
  have hbound2 : ∀ y, f y * g y ^ 2 ≤ B / h ^ 2 * K ((x - y) / h) ^ 2 := by
    intro y
    simp only [hg, div_pow]
    rw [mul_div_assoc', div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hfB y) (sq_nonneg _))
      (by positivity)
  have hg2int : Integrable (fun y ↦ f y * g y ^ 2) volume := by
    refine (hR.const_mul (B / h ^ 2)).mono' (hfm.mul (hgm.pow_const 2)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hf0 y) (sq_nonneg _))]
    exact hbound2 y
  have hg2le : ∫ y, f y * g y ^ 2 ≤ B * K2 / h := by
    calc ∫ y, f y * g y ^ 2 ≤ ∫ y, B / h ^ 2 * K ((x - y) / h) ^ 2 :=
          integral_mono hg2int (hR.const_mul _) hbound2
      _ = B / h ^ 2 * (h * K2) := by
          rw [integral_const_mul, integral_comp_sub_div hh0 x (fun u ↦ K u ^ 2)]
      _ = B * K2 / h := by field_simp
  have hgL2 : MemLp g 2 (densityLaw f) := by
    rw [memLp_two_iff_integrable_sq hgm.aestronglyMeasurable,
      integrable_densityLaw_iff hfm hf0]
    exact hg2int
  -- bias
  have hψ : Integrable (fun u ↦ f (x - h * u) * K u) volume :=
    hKi.bdd_mul
      (hfm.comp (measurable_const.sub (measurable_const.mul measurable_id))).aestronglyMeasurable
      (c := B) (Filter.Eventually.of_forall fun u ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (hf0 _)]; exact hfB _)
  have hmean : ∫ y, g y ∂densityLaw f = ∫ u, f (x - h * u) * K u := by
    rw [integral_densityLaw hfm hf0]
    have e1 : ∀ y, f y * g y = 1 / h * (fun u ↦ f (x - h * u) * K u) ((x - y) / h) := by
      intro y
      simp only [hg]
      have : x - h * ((x - y) / h) = y := by field_simp; ring
      rw [this]; ring
    simp_rw [e1]
    have hcv := integral_comp_sub_div hh0 x (fun u ↦ f (x - h * u) * K u)
    rw [integral_const_mul, hcv]
    field_simp
  have hbias : |∫ y, g y ∂densityLaw f - f x| ≤ L * h ^ β * MK := by
    rw [hmean]
    have e2 : (∫ u, f (x - h * u) * K u) - f x = ∫ u, (f (x - h * u) - f x) * K u := by
      have h3 : ∫ u, (f (x - h * u) - f x) * K u =
          (∫ u, f (x - h * u) * K u) - ∫ u, f x * K u := by
        rw [← integral_sub hψ (hKi.const_mul (f x))]; congr 1; ext u; ring
      rw [h3, integral_const_mul, hK1, mul_one]
    rw [e2]
    have hb : ∀ u, ‖(f (x - h * u) - f x) * K u‖ ≤ L * h ^ β * (|u| ^ β * |K u|) := by
      intro u
      rw [Real.norm_eq_abs, abs_mul]
      have h1 := hfh (x - h * u) x
      have h2 : |x - h * u - x| = h * |u| := by
        rw [show x - h * u - x = -(h * u) by ring, abs_neg, abs_mul, abs_of_pos hh0]
      rw [h2, Real.mul_rpow hh0.le (abs_nonneg u)] at h1
      calc |f (x - h * u) - f x| * |K u| ≤ L * (h ^ β * |u| ^ β) * |K u| :=
            mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
        _ = _ := by ring
    calc |∫ u, (f (x - h * u) - f x) * K u| ≤ ∫ u, L * h ^ β * (|u| ^ β * |K u|) :=
          norm_integral_le_of_norm_le (hKm.const_mul _) (Filter.Eventually.of_forall hb)
      _ = L * h ^ β * MK := integral_const_mul _ _
  obtain ⟨hWL2, hmse⟩ := integral_sq_sampleMean_sub_le hn hgL2 (f x)
  have hest : ∀ sample : Fin n → ℝ,
      finiteKernelDensityEstimator K h sample x = (∑ i, g (sample i)) / n := by
    intro sample
    simp only [finiteKernelDensityEstimator, hg]
    rw [← Finset.sum_div]
    field_simp
  simp_rw [hest]
  rw [← ofReal_integral_eq_lintegral_ofReal hWL2.integrable_sq
    (Filter.Eventually.of_forall fun _ ↦ sq_nonneg _)]
  refine ENNReal.ofReal_le_ofReal (hmse.trans ?_)
  rw [integral_densityLaw hfm hf0 (fun y ↦ g y ^ 2)]
  have hb2 : (∫ y, g y ∂densityLaw f - f x) ^ 2 ≤ (L * h ^ β * MK) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hbias 2
  have hpow : (h ^ β) ^ 2 = c ^ (2 * β) * r := sq_bandwidth_rpow_eq hn hβ0 hc
  have hner : (n : ℝ) * e * r = 1 := natCast_mul_bandwidth_mul_rate_eq_one hn hβ0
  have hvar : (∫ y, f y * g y ^ 2) / n ≤ B * K2 / c * r := by
    have hr' : r = 1 / (n * e) := by
      rw [eq_div_iff (by positivity)]; linarith [hner]
    have : B * K2 / h / n = B * K2 / c * r := by
      rw [hr', hh]
      field_simp
    calc (∫ y, f y * g y ^ 2) / n ≤ B * K2 / h / n :=
          div_le_div_of_nonneg_right hg2le hnR.le
      _ = _ := this
  calc (∫ y, g y ∂densityLaw f - f x) ^ 2 + (∫ y, f y * g y ^ 2) / n
      ≤ (L * h ^ β * MK) ^ 2 + B * K2 / c * r := add_le_add hb2 hvar
    _ = (L ^ 2 * c ^ (2 * β) * MK ^ 2 + B * K2 / c) * r := by
        rw [mul_pow, mul_pow, hpow]; ring
    _ ≤ (L ^ 2 * c ^ (2 * β) * MK ^ 2 + B * K2 / c + 1) * r := by
        nlinarith

/-- `klFun t ≤ (t - 1)²` for `t ≥ 0`, from `log t ≤ t - 1`. -/
private theorem klFun_le_sq_of_nonneg {t : ℝ} (ht : 0 ≤ t) :
    InformationTheory.klFun t ≤ (t - 1) ^ 2 := by
  rw [InformationTheory.klFun_apply]
  rcases ht.eq_or_lt with h | h
  · subst h; simp
  have := Real.log_le_sub_one_of_pos h
  nlinarith

/-- Kullback–Leibler divergence between laws with densities, bounded by the chi-square
integral: `KL(f₁, f₀) ≤ ∫ (f₁ - f₀)² / f₀` for a positive density `f₀`. -/
theorem klDiv_densityLaw_le {f₀ f₁ : ℝ → ℝ} (hm₀ : Measurable f₀) (hm₁ : Measurable f₁)
    (hpos : ∀ y, 0 < f₀ y) (h₁ : ∀ y, 0 ≤ f₁ y)
    [IsFiniteMeasure (densityLaw f₀)] [IsFiniteMeasure (densityLaw f₁)] :
    InformationTheory.klDiv (densityLaw f₁) (densityLaw f₀) ≤
      ∫⁻ y, ENNReal.ofReal ((f₁ y - f₀ y) ^ 2 / f₀ y) := by
  set r : ℝ → ℝ := fun y ↦ f₁ y / f₀ y with hr
  have hrm : Measurable r := hm₁.div hm₀
  have heq : densityLaw f₁ = (densityLaw f₀).withDensity fun y ↦ ENNReal.ofReal (r y) := by
    rw [densityLaw, densityLaw, ← withDensity_mul _ hm₀.ennreal_ofReal hrm.ennreal_ofReal]
    congr 1
    funext y
    simp only [Pi.mul_apply, hr]
    rw [← ENNReal.ofReal_mul (hpos y).le, mul_div_cancel₀ _ (hpos y).ne']
  have hac : densityLaw f₁ ≪ densityLaw f₀ := by
    rw [heq]; exact withDensity_absolutelyContinuous _ _
  rw [InformationTheory.klDiv_eq_lintegral_klFun_of_ac hac]
  have hrn : (densityLaw f₁).rnDeriv (densityLaw f₀) =ᵐ[densityLaw f₀]
      fun y ↦ ENNReal.ofReal (r y) := by
    rw [heq]; exact Measure.rnDeriv_withDensity _ hrm.ennreal_ofReal
  calc ∫⁻ y, ENNReal.ofReal (InformationTheory.klFun
        ((densityLaw f₁).rnDeriv (densityLaw f₀) y).toReal) ∂densityLaw f₀
      = ∫⁻ y, ENNReal.ofReal (InformationTheory.klFun (r y)) ∂densityLaw f₀ := by
        refine lintegral_congr_ae (hrn.mono fun y hy ↦ ?_)
        simp only at hy ⊢
        rw [hy, ENNReal.toReal_ofReal (div_nonneg (h₁ y) (hpos y).le)]
    _ ≤ ∫⁻ y, ENNReal.ofReal ((r y - 1) ^ 2) ∂densityLaw f₀ :=
        lintegral_mono fun y ↦ ENNReal.ofReal_le_ofReal
          (klFun_le_sq_of_nonneg (div_nonneg (h₁ y) (hpos y).le))
    _ = ∫⁻ y, ENNReal.ofReal ((f₁ y - f₀ y) ^ 2 / f₀ y) := by
        rw [densityLaw, lintegral_withDensity_eq_lintegral_mul _ hm₀.ennreal_ofReal
          (by fun_prop)]
        refine lintegral_congr fun y ↦ ?_
        simp only [Pi.mul_apply, hr]
        rw [← ENNReal.ofReal_mul (hpos y).le]
        congr 1
        have := (hpos y).ne'
        field_simp

/-- A function with oscillation at most `1` and Lipschitz constant `1` is `β`-Hölder with
constant `1` for `β ∈ (0, 1]`. -/
private theorem abs_sub_le_rpow_of_le_one_of_le {β a d : ℝ} (hβ : β ∈ Ioc (0 : ℝ) 1)
    (h1 : a ≤ 1) (h2 : a ≤ d) (hd : 0 ≤ d) : a ≤ d ^ β := by
  rcases le_total d 1 with h | h
  · exact h2.trans (Real.self_le_rpow_of_le_one hd h hβ.2)
  · exact h1.trans (Real.one_le_rpow h hβ.1.le)

/-- The unit tent `u ↦ (1 - |u|)₊`. -/
private def unitTent (u : ℝ) : ℝ := max 0 (1 - |u|)

/-- The tent is continuous. -/
private theorem continuous_tentFun : Continuous unitTent := by unfold unitTent; fun_prop

/-- The tent is nonnegative. -/
private theorem tentFun_nonneg (u : ℝ) : 0 ≤ unitTent u := le_max_left _ _

/-- The tent is at most one. -/
private theorem tentFun_le_one (u : ℝ) : unitTent u ≤ 1 :=
  max_le zero_le_one (by linarith [abs_nonneg u])

/-- The tent vanishes outside `(-1, 1)`. -/
private theorem tentFun_eq_zero {u : ℝ} (hu : 1 ≤ |u|) : unitTent u = 0 :=
  max_eq_left (by linarith)

/-- The tent is `1`-Lipschitz. -/
private theorem abs_tentFun_sub_le (u v : ℝ) : |unitTent u - unitTent v| ≤ |u - v| := by
  unfold unitTent
  rw [max_comm 0, max_comm 0]
  calc |max (1 - |u|) 0 - max (1 - |v|) 0| ≤ |(1 - |u|) - (1 - |v|)| :=
        abs_max_sub_max_le_abs _ _ _
    _ = |(|v| - |u|)| := by rw [sub_sub_sub_cancel_left]
    _ ≤ |v - u| := abs_abs_sub_abs_le_abs_sub _ _
    _ = |u - v| := abs_sub_comm _ _

/-- The tent has oscillation at most one. -/
private theorem abs_tentFun_sub_le_one (u v : ℝ) : |unitTent u - unitTent v| ≤ 1 := by
  rw [abs_le]; constructor <;> linarith [tentFun_nonneg u, tentFun_nonneg v, tentFun_le_one u,
    tentFun_le_one v]

/-- The Cauchy profile `u ↦ (1 + u²)⁻¹` is `1`-Lipschitz. -/
private theorem abs_inv_one_add_sq_sub_le (u v : ℝ) :
    |(1 + u ^ 2)⁻¹ - (1 + v ^ 2)⁻¹| ≤ |u - v| := by
  have hu : 0 < 1 + u ^ 2 := by positivity
  have hv : 0 < 1 + v ^ 2 := by positivity
  rw [inv_sub_inv hu.ne' hv.ne', abs_div, abs_of_pos (mul_pos hu hv),
    div_le_iff₀ (mul_pos hu hv), show 1 + v ^ 2 - (1 + u ^ 2) = (v - u) * (v + u) by ring,
    abs_mul, abs_sub_comm v u]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  have h1 : |v + u| ≤ |v| + |u| := abs_add_le _ _
  nlinarith [sq_nonneg (|u| - 1 / 2), sq_nonneg (|v| - 1 / 2), sq_abs u, sq_abs v,
    mul_nonneg (sq_nonneg u) (sq_nonneg v)]

/-- The Cauchy profile has oscillation at most one. -/
private theorem abs_inv_one_add_sq_sub_le_one (u v : ℝ) :
    |(1 + u ^ 2)⁻¹ - (1 + v ^ 2)⁻¹| ≤ 1 := by
  have hu : (1 + u ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg u])
  have hv : (1 + v ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg v])
  have hu0 : 0 ≤ (1 + u ^ 2)⁻¹ := by positivity
  have hv0 : 0 ≤ (1 + v ^ 2)⁻¹ := by positivity
  rw [abs_le]; constructor <;> linarith

/-- The Cauchy density with center `x` and scale `w`. -/
private def cauchyDensity (x w y : ℝ) : ℝ := (Real.pi * w)⁻¹ * (1 + (w⁻¹ * (y - x)) ^ 2)⁻¹

/-- The Cauchy density is continuous. -/
private theorem continuous_cauchyDensity (x w : ℝ) : Continuous (cauchyDensity x w) := by
  unfold cauchyDensity
  exact continuous_const.mul (Continuous.inv₀ (f := fun y ↦ 1 + (w⁻¹ * (y - x)) ^ 2)
    (by fun_prop) fun y ↦ by positivity)

/-- The Cauchy density is positive. -/
private theorem cauchyDensity_pos (x : ℝ) {w : ℝ} (hw : 0 < w) (y : ℝ) :
    0 < cauchyDensity x w y := by
  unfold cauchyDensity; have := Real.pi_pos; positivity

/-- The Cauchy density is integrable. -/
private theorem integrable_cauchyDensity (x : ℝ) {w : ℝ} (hw : 0 < w) :
    Integrable (cauchyDensity x w) := by
  unfold cauchyDensity
  exact ((integrable_inv_one_add_mul_sq (inv_ne_zero hw.ne')).comp_sub_right x).const_mul _

/-- The Cauchy density integrates to one. -/
private theorem integral_cauchyDensity (x : ℝ) {w : ℝ} (hw : 0 < w) :
    ∫ y, cauchyDensity x w y = 1 := by
  unfold cauchyDensity
  rw [integral_const_mul, integral_sub_right_eq_self (fun y ↦ (1 + (w⁻¹ * y) ^ 2)⁻¹) x,
    integral_univ_inv_one_add_mul_sq, abs_inv, abs_of_pos hw]
  have := Real.pi_pos
  field_simp

/-- For `w ≥ 1` the Cauchy density of scale `w` is `β`-Hölder with constant `(π w)⁻¹`. -/
private theorem abs_cauchyDensity_sub_le {β : ℝ} (hβ : β ∈ Ioc (0 : ℝ) 1) (x : ℝ) {w : ℝ}
    (hw : 1 ≤ w) (y z : ℝ) :
    |cauchyDensity x w y - cauchyDensity x w z| ≤ (Real.pi * w)⁻¹ * |y - z| ^ β := by
  have hw0 : 0 < w := by linarith
  unfold cauchyDensity
  rw [← mul_sub, abs_mul, abs_of_pos (by have := Real.pi_pos; positivity)]
  gcongr
  set d := |w⁻¹ * (y - x) - w⁻¹ * (z - x)|
  have hd : d ≤ |y - z| := by
    simp only [d]
    rw [← mul_sub, show y - x - (z - x) = y - z by ring, abs_mul, abs_of_pos (inv_pos.mpr hw0)]
    exact mul_le_of_le_one_left (abs_nonneg _) (inv_le_one_of_one_le₀ hw)
  refine (abs_sub_le_rpow_of_le_one_of_le hβ (abs_inv_one_add_sq_sub_le_one _ _)
    (abs_inv_one_add_sq_sub_le _ _) (abs_nonneg _)).trans ?_
  exact Real.rpow_le_rpow (abs_nonneg _) hd hβ.1.le

/-- For `w ≥ 3` the Cauchy density of scale `w` is at least `(2 π w)⁻¹` within distance `3`
of its center. -/
private theorem inv_two_mul_le_cauchyDensity (x : ℝ) {w : ℝ} (hw : 3 ≤ w) {y : ℝ}
    (hy : |y - x| ≤ 3) :
    (2 * Real.pi * w)⁻¹ ≤ cauchyDensity x w y := by
  have hw0 : 0 < w := by linarith
  unfold cauchyDensity
  have hsq : (w⁻¹ * (y - x)) ^ 2 ≤ 1 := by
    rw [mul_pow, ← sq_abs (y - x), inv_pow]
    rw [inv_mul_le_iff₀ (by positivity), mul_one]
    exact pow_le_pow_left₀ (abs_nonneg _) (hy.trans hw) 2
  have := Real.pi_pos
  rw [show (2 * Real.pi * w)⁻¹ = (Real.pi * w)⁻¹ * 2⁻¹ by
    rw [mul_inv, mul_inv, mul_inv]; ring]
  gcongr
  linarith

/-- The zero-mean perturbation: an upward tent of height `κ h^β` at `x` and a downward one at
`x + 2h`. -/
private def tentPerturbation (β κ h x y : ℝ) : ℝ :=
  κ * h ^ β * (unitTent ((y - x) / h) - unitTent ((y - x) / h - 2))

/-- The tent perturbation is continuous. -/
private theorem continuous_tentPerturbation (β κ h x : ℝ) :
    Continuous (tentPerturbation β κ h x) := by
  unfold tentPerturbation
  have := continuous_tentFun
  fun_prop

/-- The tent perturbation has height `κ h^β` at its center. -/
private theorem tentPerturbation_self {β κ h : ℝ} (x : ℝ) :
    tentPerturbation β κ h x x = κ * h ^ β := by
  simp [tentPerturbation, unitTent]

/-- The tent perturbation vanishes at distance at least `3 h` from `x`. -/
private theorem tentPerturbation_eq_zero {β κ h x y : ℝ} (hh : 0 < h) (hy : 3 * h ≤ |y - x|) :
    tentPerturbation β κ h x y = 0 := by
  have h1 : 3 ≤ |(y - x) / h| := by
    rw [abs_div, abs_of_pos hh, le_div_iff₀ hh]; linarith
  rw [tentPerturbation, tentFun_eq_zero (by linarith), tentFun_eq_zero]
  · ring
  · have := abs_sub_abs_le_abs_sub ((y - x) / h) 2
    rw [abs_two] at this; linarith

/-- The tent perturbation is bounded by `κ h^β`. -/
private theorem abs_tentPerturbation_le {β κ h : ℝ} (hκ : 0 ≤ κ) (hh : 0 < h) (x y : ℝ) :
    |tentPerturbation β κ h x y| ≤ κ * h ^ β := by
  rw [tentPerturbation, abs_mul, abs_of_nonneg (by positivity)]
  exact mul_le_of_le_one_right (by positivity) (abs_tentFun_sub_le_one _ _)

/-- The tent perturbation is `β`-Hölder with constant `2 κ`. -/
private theorem abs_tentPerturbation_sub_le {β κ h : ℝ} (hβ : β ∈ Ioc (0 : ℝ) 1) (hκ : 0 ≤ κ)
    (hh : 0 < h) (x y z : ℝ) :
    |tentPerturbation β κ h x y - tentPerturbation β κ h x z| ≤ 2 * κ * |y - z| ^ β := by
  have hT : ∀ u v : ℝ, |unitTent u - unitTent v| ≤ |u - v| ^ β := fun u v ↦
    abs_sub_le_rpow_of_le_one_of_le hβ (abs_tentFun_sub_le_one _ _) (abs_tentFun_sub_le _ _)
      (abs_nonneg _)
  have hd1 : |(y - x) / h - (z - x) / h| = |y - z| / h := by
    rw [← sub_div, show y - x - (z - x) = y - z by ring, abs_div, abs_of_pos hh]
  have hd2 : |((y - x) / h - 2) - ((z - x) / h - 2)| = |y - z| / h := by
    rw [sub_sub_sub_cancel_right, hd1]
  have hpow : (|y - z| / h) ^ β = |y - z| ^ β / h ^ β :=
    Real.div_rpow (abs_nonneg _) hh.le _
  have hhβ : 0 < h ^ β := Real.rpow_pos_of_pos hh β
  unfold tentPerturbation
  rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity)]
  have h1 := hT ((y - x) / h) ((z - x) / h)
  have h2 := hT ((y - x) / h - 2) ((z - x) / h - 2)
  rw [hd1, hpow] at h1
  rw [hd2, hpow] at h2
  have h3 : |unitTent ((y - x) / h) - unitTent ((y - x) / h - 2) -
      (unitTent ((z - x) / h) - unitTent ((z - x) / h - 2))| ≤ 2 * (|y - z| ^ β / h ^ β) := by
    have := abs_sub (unitTent ((y - x) / h) - unitTent ((z - x) / h))
      (unitTent ((y - x) / h - 2) - unitTent ((z - x) / h - 2))
    rw [show unitTent ((y - x) / h) - unitTent ((y - x) / h - 2) -
      (unitTent ((z - x) / h) - unitTent ((z - x) / h - 2)) =
      (unitTent ((y - x) / h) - unitTent ((z - x) / h)) -
      (unitTent ((y - x) / h - 2) - unitTent ((z - x) / h - 2)) by ring]
    linarith
  calc κ * h ^ β * |unitTent ((y - x) / h) - unitTent ((y - x) / h - 2) -
        (unitTent ((z - x) / h) - unitTent ((z - x) / h - 2))|
      ≤ κ * h ^ β * (2 * (|y - z| ^ β / h ^ β)) := by gcongr
    _ = 2 * κ * |y - z| ^ β := by field_simp

/-- Rescaled and translated tents are integrable. -/
private theorem integrable_tentFun_comp {h : ℝ} (hh : 0 < h) (x c : ℝ) :
    Integrable fun y ↦ unitTent ((y - x) / h - c) := by
  have hcs : HasCompactSupport unitTent := by
    refine HasCompactSupport.intro (isCompact_Icc (a := -1) (b := 1)) fun u hu ↦ ?_
    apply tentFun_eq_zero
    simp only [mem_Icc, not_and_or, not_le] at hu
    rcases hu with hu | hu
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  have hT : Integrable unitTent := continuous_tentFun.integrable_of_hasCompactSupport hcs
  have := ((hT.comp_sub_right c).comp_div hh.ne').comp_sub_right x
  refine this.congr (ae_of_all _ fun y ↦ ?_)
  simp

/-- The tent perturbation has integral zero. -/
private theorem integral_tentPerturbation {β κ h : ℝ} (hh : 0 < h) (x : ℝ) :
    ∫ y, tentPerturbation β κ h x y = 0 := by
  unfold tentPerturbation
  rw [integral_const_mul, integral_sub (by simpa using integrable_tentFun_comp hh x 0)
    (integrable_tentFun_comp hh x 2)]
  have : ∫ y, unitTent ((y - x) / h - 2) = ∫ y, unitTent ((y - x) / h) := by
    rw [← integral_sub_right_eq_self (fun y ↦ unitTent ((y - x) / h)) (2 * h)]
    congr 1; funext y; congr 1; field_simp; ring
  rw [this, sub_self, mul_zero]

/-- Markov's inequality for the squared error. -/
theorem ofReal_mul_measureReal_le_lintegral_sq {X : Type*} [MeasurableSpace X] (P : Measure X)
    [IsFiniteMeasure P] {T : X → ℝ} (hT : Measurable T) (θ : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    ENNReal.ofReal (s ^ 2 * P.real {ω | s ≤ dist (T ω) θ}) ≤
      ∫⁻ ω, ENNReal.ofReal ((T ω - θ) ^ 2) ∂P := by
  have hA : MeasurableSet {ω | s ≤ dist (T ω) θ} :=
    measurableSet_le measurable_const ((continuous_id.dist continuous_const).measurable.comp hT)
  rw [ENNReal.ofReal_mul (by positivity), ofReal_measureReal (measure_ne_top _ _),
    ← lintegral_indicator_const hA]
  refine lintegral_mono fun ω ↦ ?_
  by_cases hω : ω ∈ {ω | s ≤ dist (T ω) θ}
  · rw [Set.indicator_of_mem hω]
    apply ENNReal.ofReal_le_ofReal
    have : s ≤ |T ω - θ| := hω
    rw [← sq_abs (T ω - θ)]
    exact pow_le_pow_left₀ hs this 2
  · rw [Set.indicator_of_notMem hω]; positivity

/-- The two hypotheses of the density lower bound: a Cauchy density of scale `w ≥ 3` with
`(π w)⁻¹ ≤ L / 2`, and its perturbation by the tents of height `κ h^β ≤ κ`, both lie in the
Hölder density class. -/
private theorem mem_holderDensityClass_cauchyDensity_add {β L : ℝ} (hβ : β ∈ Ioc (0 : ℝ) 1)
    {w κ h : ℝ} (x : ℝ)
    (hw3 : 3 ≤ w) (hπw : (Real.pi * w)⁻¹ ≤ L / 2) (hκ0 : 0 < κ) (hκL : κ ≤ L / 4)
    (hκw : κ ≤ 1 / (7 * w)) (hh0 : 0 < h) (hh1 : h ≤ 1) :
    cauchyDensity x w ∈ holderDensityClass β L ∧
      (fun y ↦ cauchyDensity x w y + tentPerturbation β κ h x y) ∈ holderDensityClass β L := by
  have hβ0 := hβ.1
  have hpi := Real.pi_gt_three
  have hpi' := Real.pi_lt_d2
  have hw0 : 0 < w := by linarith
  have hhβ1 : h ^ β ≤ 1 := Real.rpow_le_one hh0.le hh1 hβ0.le
  set f₀ := cauchyDensity x w with hf₀
  set g := tentPerturbation β κ h x with hg
  set f₁ : ℝ → ℝ := fun y ↦ f₀ y + g y with hf₁
  have hf₀m : Measurable f₀ := (continuous_cauchyDensity x w).measurable
  have hf₁m : Measurable f₁ :=
    ((continuous_cauchyDensity x w).add (continuous_tentPerturbation β κ h x)).measurable
  have hf₀pos : ∀ y, 0 < f₀ y := cauchyDensity_pos x hw0
  have hf₀hold : ∀ y z, |f₀ y - f₀ z| ≤ L / 2 * |y - z| ^ β := fun y z ↦
    (abs_cauchyDensity_sub_le hβ x (by linarith) y z).trans
      (mul_le_mul_of_nonneg_right hπw (by positivity))
  have hf₀int : Integrable f₀ := integrable_cauchyDensity x hw0
  have hgint : Integrable g := by
    have h1 := integrable_tentFun_comp hh0 x 0
    have h2 := integrable_tentFun_comp hh0 x 2
    simp only [sub_zero] at h1
    exact (h1.sub h2).const_mul _
  have hf₀mem : f₀ ∈ holderDensityClass β L := by
    refine ⟨hf₀m, fun y ↦ (hf₀pos y).le, integral_cauchyDensity x hw0, fun y z ↦ ?_⟩
    rw [Real.rpow_eq_pow]
    exact (hf₀hold y z).trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  have hf₁nonneg : ∀ y, 0 ≤ f₁ y := by
    intro y
    rcases le_or_gt (3 * h) |y - x| with hy | hy
    · simp only [hf₁, hg, tentPerturbation_eq_zero hh0 hy, add_zero]; exact (hf₀pos y).le
    · have h1 := inv_two_mul_le_cauchyDensity x hw3 (y := y) (by linarith)
      have h2 := abs_tentPerturbation_le hκ0.le hh0 (β := β) x y
      have h3 : κ * h ^ β ≤ (2 * Real.pi * w)⁻¹ := by
        calc κ * h ^ β ≤ κ := mul_le_of_le_one_right hκ0.le hhβ1
          _ ≤ 1 / (7 * w) := hκw
          _ ≤ (2 * Real.pi * w)⁻¹ := by
              rw [one_div]; exact inv_anti₀ (by positivity) (by nlinarith)
      simp only [hf₁, hg]
      have := neg_abs_le (tentPerturbation β κ h x y)
      linarith
  have hf₁mem : f₁ ∈ holderDensityClass β L := by
    refine ⟨hf₁m, hf₁nonneg, ?_, fun y z ↦ ?_⟩
    · simp only [hf₁]
      rw [integral_add hf₀int hgint, integral_cauchyDensity x hw0, hg,
        integral_tentPerturbation hh0, add_zero]
    · rw [Real.rpow_eq_pow]
      have h1 := hf₀hold y z
      have h2 := abs_tentPerturbation_sub_le hβ hκ0.le hh0 x y z
      have h3 : f₁ y - f₁ z = (f₀ y - f₀ z) + (g y - g z) := by simp only [hf₁]; ring
      rw [h3]
      refine (abs_add_le _ _).trans ?_
      have : 2 * κ * |y - z| ^ β ≤ L / 2 * |y - z| ^ β :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      simp only [hg] at *
      linarith
  exact ⟨hf₀mem, hf₁mem⟩

/-- The Kullback–Leibler divergence between the two hypotheses of the density lower bound is at
most `2 π w (κ h^β)² · 6 h`. -/
private theorem klDiv_densityLaw_cauchyDensity_add_le {β L : ℝ} (hβ : β ∈ Ioc (0 : ℝ) 1)
    {w κ h : ℝ} (x : ℝ)
    (hw3 : 3 ≤ w) (hπw : (Real.pi * w)⁻¹ ≤ L / 2) (hκ0 : 0 < κ) (hκL : κ ≤ L / 4)
    (hκw : κ ≤ 1 / (7 * w)) (hh0 : 0 < h) (hh1 : h ≤ 1) :
    InformationTheory.klDiv (densityLaw fun y ↦ cauchyDensity x w y + tentPerturbation β κ h x y)
      (densityLaw (cauchyDensity x w)) ≤
      ENNReal.ofReal (2 * Real.pi * w * (κ * h ^ β) ^ 2 * (6 * h)) := by
  have hpi := Real.pi_gt_three
  have hw0 : 0 < w := by linarith
  obtain ⟨hf₀mem, hf₁mem⟩ := mem_holderDensityClass_cauchyDensity_add hβ x hw3 hπw hκ0 hκL
    hκw hh0 hh1
  set f₀ := cauchyDensity x w with hf₀
  set g := tentPerturbation β κ h x with hg
  set f₁ : ℝ → ℝ := fun y ↦ f₀ y + g y with hf₁
  have hf₀m : Measurable f₀ := (continuous_cauchyDensity x w).measurable
  have hf₁m : Measurable f₁ := hf₁mem.1
  have hf₀pos : ∀ y, 0 < f₀ y := cauchyDensity_pos x hw0
  have hf₁nonneg : ∀ y, 0 ≤ f₁ y := hf₁mem.2.1
  have hf₀int : Integrable f₀ := integrable_cauchyDensity x hw0
  have hP₀ : IsProbabilityMeasure (densityLaw f₀) :=
    isProbabilityMeasure_densityLaw (fun y ↦ (hf₀pos y).le) hf₀int (integral_cauchyDensity x hw0)
  have hP₁ : IsProbabilityMeasure (densityLaw f₁) :=
    isProbabilityMeasure_densityLaw hf₁nonneg (integrable_of_mem_holderDensityClass hf₁mem)
      hf₁mem.2.2.1
  -- the Kullback–Leibler divergence of one observation
  set B : ℝ := 2 * Real.pi * w * (κ * h ^ β) ^ 2 with hB
  have hKL1 : InformationTheory.klDiv (densityLaw f₁) (densityLaw f₀) ≤
      ENNReal.ofReal (B * (6 * h)) := by
    refine (klDiv_densityLaw_le hf₀m hf₁m hf₀pos hf₁nonneg).trans ?_
    have hpt : ∀ y, ENNReal.ofReal ((f₁ y - f₀ y) ^ 2 / f₀ y) ≤
        (Icc (x - 3 * h) (x + 3 * h)).indicator (fun _ ↦ ENNReal.ofReal B) y := by
      intro y
      have hfg : f₁ y - f₀ y = g y := by simp only [hf₁]; ring
      rw [hfg]
      by_cases hy : y ∈ Icc (x - 3 * h) (x + 3 * h)
      · rw [Set.indicator_of_mem hy]
        apply ENNReal.ofReal_le_ofReal
        have hyx : |y - x| ≤ 3 * h := by
          rw [abs_le]; constructor <;> linarith [hy.1, hy.2]
        have h1 := inv_two_mul_le_cauchyDensity x hw3 (y := y) (by linarith)
        have h2 : g y ^ 2 ≤ (κ * h ^ β) ^ 2 := by
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (abs_tentPerturbation_le hκ0.le hh0 x y) 2
        rw [div_le_iff₀ (hf₀pos y), hB]
        have h3 : 1 ≤ 2 * Real.pi * w * f₀ y := by
          rw [← inv_le_iff_one_le_mul₀' (by positivity)]
          exact h1
        nlinarith [sq_nonneg (κ * h ^ β)]
      · rw [Set.indicator_of_notMem hy]
        have hyx : 3 * h ≤ |y - x| := by
          simp only [mem_Icc, not_and_or, not_le] at hy
          rcases hy with hy | hy
          · rw [abs_of_neg (by linarith)]; linarith
          · rw [abs_of_pos (by linarith)]; linarith
        simp [hg, tentPerturbation_eq_zero hh0 hyx]
    refine (lintegral_mono hpt).trans (le_of_eq ?_)
    rw [lintegral_indicator_const measurableSet_Icc, Real.volume_Icc,
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1; ring
  exact hKL1

/-- GAPS 103.26: the matching pointwise minimax lower bound for Hölder orders at most one. -/
theorem holderDensityPointwiseMinimaxRisk_lower_bound (β L : ℝ)
    (hβ : β ∈ Ioc (0 : ℝ) 1) (hL : 0 < L) :
    ∃ c > (0 : ℝ), ∀ n : ℕ, 0 < n → ∀ x : ℝ,
      ENNReal.ofReal (c * Real.rpow (n : ℝ) (-2 * β / (2 * β + 1))) ≤
        holderDensityPointwiseMinimaxRisk n β L x := by
  have hβ0 := hβ.1
  have hpi := Real.pi_gt_three
  have hpi' := Real.pi_lt_d2
  set w : ℝ := 3 + 1 / L with hw
  have hw3 : 3 ≤ w := by rw [hw]; linarith [one_div_pos.mpr hL]
  have hw0 : 0 < w := by linarith
  have hwL : 1 / L ≤ w := by rw [hw]; linarith
  set κ : ℝ := min (L / 4) (1 / (7 * w)) with hκ
  have hκ0 : 0 < κ := lt_min (by positivity) (by positivity)
  have hκL : κ ≤ L / 4 := min_le_left _ _
  have hκw : κ ≤ 1 / (7 * w) := min_le_right _ _
  refine ⟨κ ^ 2 * (1 / 2) ^ (2 * β) / 16, by positivity, fun n hn x ↦ ?_⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set h : ℝ := 1 / 2 * (n : ℝ) ^ (-1 / (2 * β + 1)) with hhdef
  have hh0 : 0 < h := by positivity
  have hh1 : h ≤ 1 := by
    have : (n : ℝ) ^ (-1 / (2 * β + 1)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn)
        (div_nonpos_of_nonpos_of_nonneg (by norm_num) (by linarith))
    rw [hhdef]; linarith
  have hhβ1 : h ^ β ≤ 1 := Real.rpow_le_one hh0.le hh1 hβ0.le
  have hhβ0 : 0 < h ^ β := Real.rpow_pos_of_pos hh0 β
  set f₀ := cauchyDensity x w with hf₀
  set g := tentPerturbation β κ h x with hg
  set f₁ : ℝ → ℝ := fun y ↦ f₀ y + g y with hf₁
  have hπw : (Real.pi * w)⁻¹ ≤ L / 2 := by
    rw [inv_le_iff_one_le_mul₀ (by positivity)]
    have : 1 ≤ L * w := by rw [div_le_iff₀ hL] at hwL; linarith
    nlinarith
  obtain ⟨hf₀mem, hf₁mem⟩ := mem_holderDensityClass_cauchyDensity_add hβ x hw3 hπw hκ0 hκL
    hκw hh0 hh1
  have hKL1 := klDiv_densityLaw_cauchyDensity_add_le hβ x hw3 hπw hκ0 hκL hκw hh0 hh1
  set B : ℝ := 2 * Real.pi * w * (κ * h ^ β) ^ 2 with hB
  have hf₀pos : ∀ y, 0 < f₀ y := cauchyDensity_pos x hw0
  have hf₀int : Integrable f₀ := integrable_cauchyDensity x hw0
  have hf₁nonneg : ∀ y, 0 ≤ f₁ y := hf₁mem.2.1
  have hP₀ : IsProbabilityMeasure (densityLaw f₀) :=
    isProbabilityMeasure_densityLaw (fun y ↦ (hf₀pos y).le) hf₀int (integral_cauchyDensity x hw0)
  have hP₁ : IsProbabilityMeasure (densityLaw f₁) :=
    isProbabilityMeasure_densityLaw hf₁nonneg (integrable_of_mem_holderDensityClass hf₁mem)
      hf₁mem.2.2.1
  -- `n` observations
  have hnh : (n : ℝ) * h * (h ^ β) ^ 2 ≤ 1 / 2 := by
    have h1 := sq_bandwidth_rpow_eq hn hβ0 (c := 1 / 2) (by norm_num)
    have h2 := natCast_mul_bandwidth_mul_rate_eq_one hn hβ0
    have h3 : (1 / 2 : ℝ) ^ (2 * β) ≤ 1 :=
      Real.rpow_le_one (by norm_num) (by norm_num) (by linarith)
    rw [← hhdef] at h1
    rw [h1, hhdef]
    have : (n : ℝ) * (1 / 2 * (n : ℝ) ^ (-1 / (2 * β + 1))) *
        ((1 / 2) ^ (2 * β) * (n : ℝ) ^ (-2 * β / (2 * β + 1))) =
        1 / 2 * (1 / 2) ^ (2 * β) *
          ((n : ℝ) * (n : ℝ) ^ (-1 / (2 * β + 1)) * (n : ℝ) ^ (-2 * β / (2 * β + 1))) := by ring
    rw [this, h2]
    linarith
  have hKLn : InformationTheory.klDiv (Measure.pi fun _ : Fin n ↦ densityLaw f₁)
      (Measure.pi fun _ : Fin n ↦ densityLaw f₀) ≤ ENNReal.ofReal (1 / 2) := by
    rw [klDiv_pi_const, Fintype.card_fin]
    calc (n : ℝ≥0∞) * InformationTheory.klDiv (densityLaw f₁) (densityLaw f₀)
        ≤ (n : ℝ≥0∞) * ENNReal.ofReal (B * (6 * h)) := by gcongr
      _ = ENNReal.ofReal (n * (B * (6 * h))) := by
          rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal (1 / 2) := by
          apply ENNReal.ofReal_le_ofReal
          have hwκ : w * κ ^ 2 ≤ 1 / 49 := by
            have : κ * (7 * w) ≤ 1 := by rw [le_div_iff₀ (by positivity)] at hκw; linarith
            nlinarith
          have : (n : ℝ) * (B * (6 * h)) =
              12 * Real.pi * (w * κ ^ 2) * ((n : ℝ) * h * (h ^ β) ^ 2) := by
            rw [hB]; ring
          rw [this]
          have h0 : 0 ≤ (n : ℝ) * h * (h ^ β) ^ 2 := by positivity
          nlinarith [mul_le_mul hwκ hnh h0 (by norm_num : (0 : ℝ) ≤ 1 / 49)]
  have hfin : InformationTheory.klDiv (Measure.pi fun _ : Fin n ↦ densityLaw f₁)
      (Measure.pi fun _ : Fin n ↦ densityLaw f₀) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hKLn
  have hTV : totalVariationDistance (Measure.pi fun _ : Fin n ↦ densityLaw f₁)
      (Measure.pi fun _ : Fin n ↦ densityLaw f₀) ≤ 1 / 2 := by
    refine (totalVariationDistance_le_sqrt_toReal_klDiv _ _ hfin).trans ?_
    rw [Real.sqrt_le_left (by norm_num)]
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hKLn
    rw [ENNReal.toReal_ofReal (by norm_num)] at this
    linarith
  -- Le Cam's two-point bound
  set s := κ * h ^ β / 2 with hs
  have hsep : 2 * s ≤ dist (f₁ x) (f₀ x) := by
    rw [Real.dist_eq, show f₁ x - f₀ x = g x by simp only [hf₁]; ring, hg,
      tentPerturbation_self, abs_of_pos (by positivity), hs]
    linarith
  have hc : κ ^ 2 * (1 / 2) ^ (2 * β) / 16 * Real.rpow (n : ℝ) (-2 * β / (2 * β + 1)) =
      s ^ 2 / 4 := by
    have h1 := sq_bandwidth_rpow_eq hn hβ0 (c := 1 / 2) (by norm_num)
    rw [← hhdef] at h1
    rw [hs, div_pow, mul_pow, h1, Real.rpow_eq_pow]; ring
  refine le_iInf fun T ↦ ?_
  have hLC := one_sub_totalVariationDistance_div_two_le_max_measureReal
    (Measure.pi fun _ : Fin n ↦ densityLaw f₁) (Measure.pi fun _ : Fin n ↦ densityLaw f₀)
    (f₁ x) (f₀ x) s hsep T.val T.2
  have hs0 : 0 ≤ s := by positivity
  have hR₀ := ofReal_mul_measureReal_le_lintegral_sq (Measure.pi fun _ : Fin n ↦ densityLaw f₀)
    T.2 (f₀ x) hs0
  have hR₁ := ofReal_mul_measureReal_le_lintegral_sq (Measure.pi fun _ : Fin n ↦ densityLaw f₁)
    T.2 (f₁ x) hs0
  have hsup₀ := le_iSup (fun f : holderDensityClass β L ↦ ∫⁻ sample,
    ENNReal.ofReal ((T.val sample - f.val x) ^ 2) ∂(Measure.pi fun _ : Fin n ↦ densityLaw f.val))
    ⟨f₀, hf₀mem⟩
  have hsup₁ := le_iSup (fun f : holderDensityClass β L ↦ ∫⁻ sample,
    ENNReal.ofReal ((T.val sample - f.val x) ^ 2) ∂(Measure.pi fun _ : Fin n ↦ densityLaw f.val))
    ⟨f₁, hf₁mem⟩
  rw [hc]
  rcases le_total ((Measure.pi fun _ : Fin n ↦ densityLaw f₁).real
    {ω | s ≤ dist (T.val ω) (f₁ x)})
    ((Measure.pi fun _ : Fin n ↦ densityLaw f₀).real {ω | s ≤ dist (T.val ω) (f₀ x)}) with hm | hm
  · rw [max_eq_right hm] at hLC
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) (hR₀.trans hsup₀)
    have : s ^ 2 / 4 ≤ s ^ 2 * ((1 - 1 / 2) / 2) := by nlinarith [sq_nonneg s]
    refine this.trans (mul_le_mul_of_nonneg_left (le_trans ?_ hLC) (sq_nonneg s))
    linarith
  · rw [max_eq_left hm] at hLC
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) (hR₁.trans hsup₁)
    have : s ^ 2 / 4 ≤ s ^ 2 * ((1 - 1 / 2) / 2) := by nlinarith [sq_nonneg s]
    refine this.trans (mul_le_mul_of_nonneg_left (le_trans ?_ hLC) (sq_nonneg s))
    linarith

end CKSD
