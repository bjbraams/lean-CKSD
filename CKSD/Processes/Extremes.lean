module

public import CKSD.Processes.Basic
public import Mathlib.Probability.Distributions.Poisson.PoissonLimitThm
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import TauCeti.Probability.Distributions.PoissonBinomial.Count
public import TauCeti.Probability.Quantile

/-!
# Maxima and exceedances of independent observations

For iid real observations `X 0, X 1, …` with distribution function `F`, the maximum of the first
`n` observations satisfies `P(max_{i<n} X_i ≤ c) = F(c)^n`, and the number of exceedances of a
level `u` is binomial with success probability `1 - F(u)`.

## Main definitions

* `CKSD.tailQuantile`: the tail quantile `U(t) = F^←(1 - 1/t)`, TauCeti's quantile at level
  `1 - 1/t`.
* `CKSD.HasRegularlyVaryingTail`: `1 - F` is positive everywhere and regularly varying at
  infinity with index `-1/γ`.

## Main results

* `CKSD.tendsto_maximum_of_hasRegularlyVaryingTail` (GAPS 106.46): if `1 - F` is regularly
  varying with index `-1/γ`, `γ > 0`, then `P(max_{i<n} X_i ≤ U(n) x) → exp(-x^{-1/γ})`, the
  Fréchet limit, for every `x > 0`.
* `CKSD.tendsto_measureReal_forall_le_of_tendsto_mul` (GAPS 106.48, independent case): if
  `n (1 - F(u_n)) → τ` then `P(max_{i<n} X_i ≤ u_n) → e^{-τ}`.
* `CKSD.tendstoInDistribution_card_exceedances` (GAPS 106.50): under the same condition the
  number of exceedances of `u_n` converges in law to the Poisson law with mean `τ`.

## Implementation notes

The exceedance count is binomial by TauCeti's `iIndepFun.hasLaw_card_filter_mem` and
`poissonBinomialMeasure_const`, which also give the law `F(c)^n` of the maximum. The limit
`(1 - p_n)^n → e^{-τ}` is Mathlib's `Real.tendsto_one_add_pow_exp_of_tendsto`. The Poisson
limit of the binomial laws combines Mathlib's `tendsto_choose_mul_pow_of_tendsto_mul_atTop` with
Tannery's theorem. The Fréchet limit compares `n (1 - F(U(n)))` with `1` through the regular
variation of the tail at the quantiles `U(n)`, using TauCeti's quantile inequalities
`MeasureTheory.Measure.le_cdf_quantile` and `MeasureTheory.Measure.lt_quantile_iff`.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators unitInterval Nat

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- Poisson limit of the binomial law tested against bounded functions: if `n p_n → τ`, then
`∫ f d Bin(n, p_n) → ∫ f d Po(τ)`. The pointwise limit of the probabilities is Mathlib's
`tendsto_choose_mul_pow_of_tendsto_mul_atTop`; the bound `C (sup_n n p_n)^k / k!` allows
Tannery's theorem. -/
theorem tendsto_integral_binomial_poissonMeasure (p : ℕ → I) (τ : ℝ≥0)
    (h : Tendsto (fun n : ℕ ↦ (n : ℝ) * (p n : ℝ)) atTop (𝓝 (τ : ℝ))) (f : ℕ → ℝ)
    (hf : ∃ C, ∀ k, |f k| ≤ C) :
    Tendsto (fun n ↦ ∫ k, f k ∂binomial n (p n)) atTop (𝓝 (∫ k, f k ∂poissonMeasure τ)) := by
  obtain ⟨C, hC⟩ := hf
  obtain ⟨M, hM⟩ := h.bddAbove_range
  have hM' : ∀ n : ℕ, (n : ℝ) * (p n : ℝ) ≤ M := fun n ↦ hM ⟨n, rfl⟩
  have hM0 : 0 ≤ M := le_trans (by simp) (hM' 0)
  let g : ℕ → ℕ → ℝ := fun n k ↦ (n.choose k * (p n : ℝ) ^ k * (1 - p n) ^ (n - k)) * f k
  have hint : ∀ n, ∫ k, f k ∂binomial n (p n) = ∑' k, g n k := by
    intro n
    rw [integral_binomial, tsum_eq_sum (s := Finset.Iic n)]
    · rfl
    · intro k hk
      simp only [Finset.mem_Iic, not_le] at hk
      simp [g, Nat.choose_eq_zero_of_lt hk]
  rw [integral_poissonMeasure]
  simp_rw [hint, smul_eq_mul]
  refine tendsto_tsum_of_dominated_convergence (bound := fun k ↦ C * (M ^ k / k !))
    ((Real.summable_pow_div_factorial M).mul_left C) (fun k ↦ ?_)
    (Eventually.of_forall fun n k ↦ ?_)
  · exact (tendsto_choose_mul_pow_of_tendsto_mul_atTop k h).mul_const (f k)
  · have hp0 : 0 ≤ (p n : ℝ) := (p n).2.1
    have hp1 : (p n : ℝ) ≤ 1 := (p n).2.2
    have hb0 : 0 ≤ (n.choose k : ℝ) * (p n : ℝ) ^ k * (1 - p n) ^ (n - k) := by
      have : (0 : ℝ) ≤ 1 - p n := by linarith
      positivity
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hb0, mul_comm]
    refine mul_le_mul (hC k) ?_ hb0 ((abs_nonneg _).trans (hC k))
    calc (n.choose k : ℝ) * (p n : ℝ) ^ k * (1 - p n) ^ (n - k)
        ≤ (n.choose k : ℝ) * (p n : ℝ) ^ k * 1 := by
          gcongr
          exact pow_le_one₀ (by linarith) (by linarith)
      _ ≤ (n : ℝ) ^ k / k ! * (p n : ℝ) ^ k := by
          rw [mul_one]; gcongr; exact Nat.choose_le_pow_div k n
      _ = ((n : ℝ) * p n) ^ k / k ! := by ring
      _ ≤ M ^ k / k ! := by
          gcongr
          exact hM' n


/-- Counting indices in `Fin n` and in `range n` agree. -/
theorem card_filter_univ_fin_eq_card_filter_range (n : ℕ) (q : ℕ → Prop) [DecidablePred q] :
    (Finset.univ.filter fun i : Fin n ↦ q i).card = ((Finset.range n).filter q).card := by
  rw [Finset.card_filter, Finset.card_filter]
  exact Fin.sum_univ_eq_sum_range (fun i ↦ if q i then 1 else 0) n

/-- The number of exceedances of a level among the first `n` iid observations is binomial, by
TauCeti's Poisson-binomial law of counts of independent events. -/
theorem hasLaw_card_exceedances_binomial {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (P : Measure ℝ) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hiid : IsIndependentIdenticallyDistributed μ X P) (n : ℕ) (u : ℝ) :
    HasLaw (fun ω ↦ ((Finset.range n).filter (fun i ↦ u < X i ω)).card)
      (binomial n ⟨P.real (Ioi u), by simp⟩) μ := by
  have hind : iIndepFun (fun i : Fin n ↦ X i) μ := hiid.2.1.precomp Fin.val_injective
  have h := iIndepFun.hasLaw_card_filter_mem (μ := fun _ : Fin n ↦ P) hind
    (fun i ↦ ⟨(hiid.1 i).aemeasurable, hiid.2.2 i⟩) (s := fun _ ↦ Ioi u)
    (fun _ ↦ measurableSet_Ioi)
  have e := TauCeti.Probability.poissonBinomialMeasure_const (ι := Fin n)
    (⟨P.real (Ioi u), by simp⟩ : I)
  rw [Fintype.card_fin] at e
  rw [← e]
  refine h.congr (ae_of_all _ fun ω ↦ ?_)
  simp only [mem_Ioi]
  exact (card_filter_univ_fin_eq_card_filter_range n (fun i ↦ u < X i ω)).symm


/-- The tail of a probability measure on the line is the mass of the open upper ray:
`1 - F(c) = P(c, ∞)`. -/
theorem one_sub_cdf_eq_measureReal_Ioi (P : Measure ℝ) [IsProbabilityMeasure P] (c : ℝ) :
    1 - cdf P c = P.real (Ioi c) := by
  rw [cdf, ← compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic]

/-- The probability that the first `n` iid observations do not exceed `c` is `F(c)^n`, written
as `(1 - (1 - F(c)))^n`. -/
theorem measureReal_forall_le_eq_pow {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (P : Measure ℝ) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hiid : IsIndependentIdenticallyDistributed μ X P) (n : ℕ) (c : ℝ) :
    μ.real {ω | ∀ i < n, X i ω ≤ c} = (1 - (1 - cdf P c)) ^ n := by
  have hlaw := hasLaw_card_exceedances_binomial μ P X hiid n c
  have hset : {ω | ∀ i < n, X i ω ≤ c} =
      (fun ω ↦ ((Finset.range n).filter (fun i ↦ c < X i ω)).card) ⁻¹' {0} := by
    ext ω
    simp [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rw [hset, measureReal_def, ← Measure.map_apply_of_aemeasurable hlaw.aemeasurable
    (measurableSet_singleton 0), hlaw.map_eq, ← measureReal_def, binomial_real_zero,
    one_sub_cdf_eq_measureReal_Ioi]

/-- If `n (1 - F(u_n)) → τ`, the probability that none of the first `n` iid observations exceeds
`u_n` tends to `e^{-τ}`. -/
theorem tendsto_measureReal_forall_le_of_tendsto_mul {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (P : Measure ℝ) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hiid : IsIndependentIdenticallyDistributed μ X P) (u : ℕ → ℝ) (τ : ℝ)
    (htail : Tendsto (fun n : ℕ ↦ (n : ℝ) * (1 - cdf P (u n))) atTop (𝓝 τ)) :
    Tendsto (fun n ↦ μ.real {ω | ∀ i < n, X i ω ≤ u n}) atTop (𝓝 (Real.exp (-τ))) := by
  have h := Real.tendsto_one_add_pow_exp_of_tendsto (g := fun n ↦ -(1 - cdf P (u n)))
    (by simpa only [mul_neg] using htail.neg)
  refine h.congr fun n ↦ ?_
  rw [measureReal_forall_le_eq_pow μ P X hiid n (u n), ← sub_eq_add_neg]

/-- The tail quantile `U(t) = F^←(1 - 1/t)`, TauCeti's quantile of `P` at level `1 - 1/t`; it is
used for `t > 1`. -/
def tailQuantile (P : Measure ℝ) (t : ℝ) : ℝ :=
  P.quantile (1 - 1 / t)

/-- At the tail quantile the tail mass is at most `1/t`. -/
theorem one_sub_cdf_tailQuantile_le (P : Measure ℝ) [IsProbabilityMeasure P] {t : ℝ}
    (ht : 1 < t) : 1 - cdf P (tailQuantile P t) ≤ t⁻¹ := by
  have h1 : 1 - 1 / t < 1 := sub_lt_self 1 (by positivity)
  have h := P.le_cdf_quantile h1
  rw [cdf_eq_real] at h
  rw [tailQuantile, cdf, ← one_div]
  linarith

/-- Below the tail quantile the tail mass exceeds `1/t`. -/
theorem lt_one_sub_cdf_of_lt_tailQuantile (P : Measure ℝ) [IsProbabilityMeasure P] {t x : ℝ}
    (ht : 1 < t) (hx : x < tailQuantile P t) : t⁻¹ < 1 - cdf P x := by
  have h0 : 0 < 1 - 1 / t := by
    rw [sub_pos, div_lt_one (by linarith)]; exact ht
  have h := (P.lt_quantile_iff h0 (sub_lt_self 1 (by positivity))).1 hx
  rw [cdf_eq_real, one_div] at h
  rw [cdf]
  linarith

/-- The tail `1 - F` is positive everywhere (the upper endpoint is infinite) and regularly
varying at infinity with index `-1/γ`: `(1 - F(tx)) / (1 - F(t)) → x^{-1/γ}` for every `x > 0`. -/
def HasRegularlyVaryingTail (P : Measure ℝ) (γ : ℝ) : Prop :=
  (∀ t : ℝ, cdf P t < 1) ∧ ∀ x > 0,
    Tendsto (fun t ↦ (1 - cdf P (t * x)) / (1 - cdf P t)) atTop
      (𝓝 (Real.rpow x (-1 / γ)))

/-- Under an everywhere positive tail, the tail quantiles `U(n)` tend to infinity. -/
theorem tendsto_tailQuantile_atTop (P : Measure ℝ) [IsProbabilityMeasure P]
    (hpos : ∀ t : ℝ, cdf P t < 1) :
    Tendsto (fun n : ℕ ↦ tailQuantile P n) atTop atTop := by
  refine tendsto_atTop.2 fun M ↦ ?_
  have hlim : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_nhds_zero_nat
  filter_upwards [eventually_ge_atTop 2, hlim.eventually (gt_mem_nhds (sub_pos.2 (hpos M)))]
    with n hn hnM
  by_contra h
  have h1 := one_sub_cdf_tailQuantile_le P (t := n) (by exact_mod_cast hn)
  have h2 : cdf P (tailQuantile P n) ≤ cdf P M := by
    rw [cdf, cdf]
    exact measureReal_mono (Iic_subset_Iic.2 (not_le.1 h).le)
  linarith

/-- If `1 - F` is regularly varying with index `-1/γ`, `γ > 0`, then `n (1 - F(U(n))) → 1`. -/
theorem tendsto_mul_one_sub_cdf_tailQuantile (P : Measure ℝ) [IsProbabilityMeasure P] {γ : ℝ}
    (hγ : 0 < γ) (hrv : HasRegularlyVaryingTail P γ) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) * (1 - cdf P (tailQuantile P n))) atTop (𝓝 1) := by
  set a : ℕ → ℝ := fun n ↦ tailQuantile P n
  set Fb : ℝ → ℝ := fun t ↦ 1 - cdf P t with hFb
  have hFb_pos : ∀ t, 0 < Fb t := fun t ↦ sub_pos.2 (hrv.1 t)
  have ha_top : Tendsto a atTop atTop := tendsto_tailQuantile_atTop P hrv.1
  have hcast : ∀ n : ℕ, 2 ≤ n → (1 : ℝ) < n := fun n hn ↦ by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  refine tendsto_order.2 ⟨fun b hb ↦ ?_, fun b hb ↦ ?_⟩
  · set z := (max b 0 + 1) / 2 with hz
    have hz0 : 0 < z := by have := le_max_right b 0; linarith
    have hz1 : z < 1 := by have := max_lt hb one_pos; linarith
    have hbz : b < z := by have := le_max_left b 0; linarith
    set y := z ^ γ with hy
    have hy0 : 0 < y := Real.rpow_pos_of_pos hz0 γ
    have hy1 : y < 1 := Real.rpow_lt_one hz0.le hz1 hγ
    have hlimy : Real.rpow y (-1 / γ) = z⁻¹ := by
      change (z ^ γ) ^ (-1 / γ) = z⁻¹
      rw [← Real.rpow_mul hz0.le, show γ * (-1 / γ) = -1 by field_simp, Real.rpow_neg_one]
    have hinv : Tendsto (fun n ↦ Fb (a n) / Fb (a n * y)) atTop (𝓝 z) := by
      have := ((hrv.2 y hy0).comp ha_top).inv₀ (by rw [hlimy]; positivity)
      rw [hlimy, inv_inv] at this
      simpa only [Function.comp_def, inv_div] using this
    filter_upwards [hinv.eventually (lt_mem_nhds hbz), eventually_ge_atTop 2,
      ha_top.eventually (eventually_gt_atTop 0)] with n h1 hn ha0
    have hlt : a n * y < a n := mul_lt_of_lt_one_right ha0 hy1
    have h2 := lt_one_sub_cdf_of_lt_tailQuantile P (hcast n hn) hlt
    have hn0 : (0 : ℝ) < n := by linarith [hcast n hn]
    have h3 : 1 < n * Fb (a n * y) := by
      have := mul_lt_mul_of_pos_left h2 hn0
      rwa [mul_inv_cancel₀ hn0.ne'] at this
    have h4 : Fb (a n) / Fb (a n * y) ≤ n * Fb (a n) := by
      rw [div_le_iff₀ (hFb_pos _)]
      nlinarith [hFb_pos (a n)]
    linarith
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hn0 : (0 : ℝ) < n := by linarith [hcast n hn]
    calc (n : ℝ) * Fb (a n) ≤ n * (n : ℝ)⁻¹ := by
          gcongr; exact one_sub_cdf_tailQuantile_le P (hcast n hn)
      _ = 1 := mul_inv_cancel₀ hn0.ne'
      _ < b := hb

/-- GAPS 106.46, sufficient condition for the Fréchet limit: if `1 - F` is regularly varying
with index `-1/γ`, `γ > 0`, then `P(max_{i<n} X_i ≤ U(n) x) → exp(-x^{-1/γ})` for every
`x > 0`, with `U` the tail quantile. -/
theorem tendsto_maximum_of_hasRegularlyVaryingTail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (P : Measure ℝ) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hiid : IsIndependentIdenticallyDistributed μ X P) (γ : ℝ) (hγ : 0 < γ)
    (hrv : HasRegularlyVaryingTail P γ) (x : ℝ) (hx : 0 < x) :
    Tendsto (fun n : ℕ ↦ μ.real {ω | ∀ i < n, X i ω ≤ tailQuantile P n * x}) atTop
      (𝓝 (Real.exp (-Real.rpow x (-1 / γ)))) := by
  refine tendsto_measureReal_forall_le_of_tendsto_mul μ P X hiid _ _ ?_
  have hratio := (hrv.2 x hx).comp (tendsto_tailQuantile_atTop P hrv.1)
  have := (tendsto_mul_one_sub_cdf_tailQuantile P hγ hrv).mul hratio
  rw [one_mul] at this
  refine this.congr fun n ↦ ?_
  have := (sub_pos.2 (hrv.1 (tailQuantile P n))).ne'
  simp only [Function.comp_apply]
  field_simp

/-- GAPS 106.50, finite-intensity exceedance limit (also the independent case of GAPS 106.48):
if `n (1 - F(u_n)) → τ`, the number of exceedances of `u_n` among the first `n` iid
observations converges in law to the Poisson law with mean `τ`. -/
theorem tendstoInDistribution_card_exceedances {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure ℝ) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hiid : IsIndependentIdenticallyDistributed μ X P) (u : ℕ → ℝ) (τ : ℝ≥0)
    (htail : Tendsto (fun n : ℕ ↦ (n : ℝ) * (1 - cdf P (u n))) atTop (𝓝 (τ : ℝ))) :
    TendstoInDistribution μ (fun n ω ↦ ((Finset.range n).filter (fun i ↦ u n < X i ω)).card)
      (poissonMeasure τ) := by
  let p : ℕ → I := fun n ↦ ⟨P.real (Ioi (u n)), by simp⟩
  have hpt : Tendsto (fun n : ℕ ↦ (n : ℝ) * (p n : ℝ)) atTop (𝓝 (τ : ℝ)) := by
    simpa only [one_sub_cdf_eq_measureReal_Ioi] using htail
  have hlaw := fun n ↦ hasLaw_card_exceedances_binomial μ P X hiid n (u n)
  refine TendstoWeakly.of_forall_integral_tendsto (fun f ↦ ?_)
  simp_rw [fun n ↦ (hlaw n).map_eq]
  exact tendsto_integral_binomial_poissonMeasure p τ hpt f ⟨‖f‖, fun k ↦ by
    simpa [Real.norm_eq_abs] using f.norm_coe_le_norm k⟩

end CKSD
