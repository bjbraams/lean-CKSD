module

public import CKSD.Processes.Basic
public import CKSD.Asymptotics.Basic
public import CKSD.Nonparametric.Basic
public import Mathlib.Probability.Distributions.Poisson.PoissonLimitThm
public import Mathlib.Analysis.Normed.Group.Tannery
public import TauCeti.Probability.Distributions.PoissonBinomial.Count

/-!
# Processes: Extremes

Sources: `GAPS.md`, `SYNOPSIS106.md`, and `STRUCTURE106.md`.
Declarations adapted from this project's section drafts.
The exceedance count is binomial by TauCeti's `iIndepFun.hasLaw_card_filter_mem` and
`poissonBinomialMeasure_const`, which also give the law `F(c)^n` of the maximum. The Poisson
limit combines Mathlib's Poisson limit theorem `tendsto_choose_mul_pow_of_tendsto_mul_atTop`
with Tannery's theorem. The Fréchet limit compares `n (1 - F(a_n))` with `1` through the
regular variation of the tail at the quantiles `a_n`.
The docstrings specify the scope of each result; `sorry` marks unfinished proofs.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator unitInterval Nat

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


/-- The generalized quantile `sInf {t | c ≤ F t}` of a level `c ∈ (0, 1)` satisfies
`c ≤ F(sInf …)`, by right continuity, and `F t < c` below it. -/
theorem cdf_sInf_setOf_le_cdf (P : Measure ℝ) [IsProbabilityMeasure P] {c : ℝ} (hc0 : 0 < c)
    (hc1 : c < 1) :
    c ≤ cdf P (sInf {t | c ≤ cdf P t}) ∧ ∀ t < sInf {t | c ≤ cdf P t}, cdf P t < c := by
  set S := {t | c ≤ cdf P t}
  have hF : ∀ t, cdf P t = ProbabilityTheory.cdf P t := fun t ↦ (cdf_eq_real P t).symm
  have hne : S.Nonempty := by
    obtain ⟨t, ht⟩ := ((tendsto_cdf_atTop (μ := P)).eventually (lt_mem_nhds hc1)).exists
    exact ⟨t, by simp only [S, mem_ofPred_eq, hF]; exact ht.le⟩
  have hbdd : BddBelow S := by
    obtain ⟨t₀, ht₀⟩ := (eventually_atBot.1 ((tendsto_cdf_atBot (μ := P)).eventually
      (gt_mem_nhds hc0)))
    refine ⟨t₀, fun s hs ↦ ?_⟩
    by_contra h
    have := ht₀ s (not_le.1 h).le
    simp only [S, mem_ofPred_eq, hF] at hs
    linarith
  have hlt : ∀ t < sInf S, cdf P t < c := fun t ht ↦ by
    by_contra h
    exact absurd (csInf_le hbdd (show t ∈ S from not_lt.1 h)) (not_le.2 ht)
  refine ⟨?_, hlt⟩
  rw [hF]
  have hrc : Tendsto (ProbabilityTheory.cdf P) (𝓝[>] (sInf S)) (𝓝 (ProbabilityTheory.cdf P (sInf S))) :=
    ((ProbabilityTheory.cdf P).right_continuous (sInf S)).mono Ioi_subset_Ici_self
  refine ge_of_tendsto hrc ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  obtain ⟨s, hs, hst⟩ := exists_lt_of_csInf_lt hne ht
  simp only [S, mem_ofPred_eq, hF] at hs
  exact hs.trans ((ProbabilityTheory.cdf P).mono hst.le)


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
    (measurableSet_singleton 0), hlaw.map_eq, ← measureReal_def, binomial_real_zero]
  simp only [cdf]
  rw [← compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic]

/-- GAPS 106.46, the regularly varying positive-tail sufficient condition for a Fréchet limit. -/
theorem tendsto_maximum_of_regularly_varying_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (P : Measure ℝ) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hiid : IsIndependentIdenticallyDistributed μ X P) (γ : ℝ) (hγ : 0 < γ)
    (hpos : ∀ t : ℝ, cdf P t < 1)
    (hrv : ∀ x > 0, Tendsto (fun t ↦ (1 - cdf P (t * x)) / (1 - cdf P t))
      atTop (𝓝 (Real.rpow x (-1 / γ)))) :
    let a := fun n : ℕ ↦ sInf {t | 1 - (n : ℝ)⁻¹ ≤ cdf P t};
    ∀ x > 0, Tendsto (fun n ↦ μ.real {ω | ∀ i < n, X i ω ≤ a n * x}) atTop
      (𝓝 (Real.exp (-Real.rpow x (-1 / γ)))) := by
  intro a x hx
  set Fb : ℝ → ℝ := fun t ↦ 1 - cdf P t with hFb
  have hFb_pos : ∀ t, 0 < Fb t := fun t ↦ sub_pos.2 (hpos t)
  have hF : ∀ t, cdf P t = ProbabilityTheory.cdf P t := fun t ↦ (cdf_eq_real P t).symm
  have hmono : Monotone (cdf P) := fun s t hst ↦ by
    rw [hF, hF]; exact (ProbabilityTheory.cdf P).mono hst
  -- properties of `a n` for `n ≥ 2`
  have hprop : ∀ n : ℕ, 2 ≤ n → Fb (a n) ≤ (n : ℝ)⁻¹ ∧ ∀ t < a n, (n : ℝ)⁻¹ < Fb t := by
    intro n hn
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hinv : (n : ℝ)⁻¹ ≤ 1 / 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    have hinv0 : 0 < (n : ℝ)⁻¹ := by positivity
    obtain ⟨h1, h2⟩ := cdf_sInf_setOf_le_cdf P (c := 1 - (n : ℝ)⁻¹) (by linarith) (by linarith)
    exact ⟨by simp only [Fb]; linarith, fun t ht ↦ by have := h2 t ht; simp only [Fb]; linarith⟩
  have ha_top : Tendsto a atTop atTop := by
    refine tendsto_atTop.2 fun M ↦ ?_
    have hlim : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_nhds_zero_nat
    filter_upwards [eventually_ge_atTop 2, hlim.eventually (gt_mem_nhds (hFb_pos M))]
      with n hn hnM
    by_contra h
    have h1 := (hprop n hn).1
    have h2 := hmono (not_le.1 h).le
    simp only [Fb] at h1 hnM
    linarith
  have hratio : ∀ y > 0, Tendsto (fun n ↦ Fb (a n * y) / Fb (a n)) atTop
      (𝓝 (Real.rpow y (-1 / γ))) := fun y hy ↦ (hrv y hy).comp ha_top
  have hnF : Tendsto (fun n : ℕ ↦ (n : ℝ) * Fb (a n)) atTop (𝓝 1) := by
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
        have := (hratio y hy0).inv₀ (by rw [hlimy]; positivity)
        rw [hlimy, inv_inv] at this
        simpa only [inv_div] using this
      filter_upwards [hinv.eventually (lt_mem_nhds hbz), eventually_ge_atTop 2,
        ha_top.eventually (eventually_gt_atTop 0)] with n h1 hn ha0
      have hlt : a n * y < a n := mul_lt_of_lt_one_right ha0 hy1
      have h2 := (hprop n hn).2 _ hlt
      have hn0 : (0 : ℝ) < n := by have : (2 : ℝ) ≤ n := by exact_mod_cast hn
                                   linarith
      have h3 : 1 < n * Fb (a n * y) := by
        have := mul_lt_mul_of_pos_left h2 hn0
        rwa [mul_inv_cancel₀ hn0.ne'] at this
      have h4 : Fb (a n) / Fb (a n * y) ≤ n * Fb (a n) := by
        rw [div_le_iff₀ (hFb_pos _)]
        nlinarith [hFb_pos (a n)]
      linarith
    · filter_upwards [eventually_ge_atTop 2] with n hn
      have hn0 : (0 : ℝ) < n := by have : (2 : ℝ) ≤ n := by exact_mod_cast hn
                                   linarith
      calc (n : ℝ) * Fb (a n) ≤ n * (n : ℝ)⁻¹ := by gcongr; exact (hprop n hn).1
        _ = 1 := mul_inv_cancel₀ hn0.ne'
        _ < b := hb
  have hq : Tendsto (fun n : ℕ ↦ (n : ℝ) * Fb (a n * x)) atTop (𝓝 (Real.rpow x (-1 / γ))) := by
    have := hnF.mul (hratio x hx)
    rw [one_mul] at this
    refine this.congr fun n ↦ ?_
    have := (hFb_pos (a n)).ne'
    field_simp
  have h0 := tendsto_choose_mul_pow_of_tendsto_mul_atTop 0 hq
  simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, one_mul, Nat.sub_zero,
    Nat.factorial_zero, div_one, mul_one] at h0
  exact h0.congr fun n ↦ (measureReal_forall_le_eq_pow μ P X hiid n (a n * x)).symm

/-- GAPS 106.48 (independent scope) and GAPS 106.50, finite-intensity exceedance limit; also the
independent part of 106.48. -/
theorem tendsto_maximum_and_exceedance_count_of_tail_limit {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure ℝ) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hiid : IsIndependentIdenticallyDistributed μ X P) (u : ℕ → ℝ) (τ : ℝ≥0)
    (htail : Tendsto (fun n : ℕ ↦ (n : ℝ) * (1 - cdf P (u n))) atTop (𝓝 (τ : ℝ))) :
    Tendsto (fun n ↦ μ.real {ω | ∀ i < n, X i ω ≤ u n}) atTop (𝓝 (Real.exp (-τ))) ∧
      TendstoInDistribution μ (fun n ω ↦ ((Finset.range n).filter (fun i ↦ u n < X i ω)).card)
        (poissonMeasure τ) := by
  let p : ℕ → I := fun n ↦ ⟨P.real (Ioi (u n)), by simp⟩
  have hp : ∀ n, 1 - cdf P (u n) = (p n : ℝ) := fun n ↦ by
    simp only [p, cdf]
    rw [← compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic]
  have hpt : Tendsto (fun n : ℕ ↦ (n : ℝ) * (p n : ℝ)) atTop (𝓝 (τ : ℝ)) := by
    simpa only [hp] using htail
  have hlaw := fun n ↦ hasLaw_card_exceedances_binomial μ P X hiid n (u n)
  refine ⟨?_, TendstoWeakly.of_forall_integral_tendsto (fun f ↦ ?_)⟩
  · have h0 := tendsto_choose_mul_pow_of_tendsto_mul_atTop 0 hpt
    simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, one_mul, Nat.sub_zero,
      Nat.factorial_zero, div_one, mul_one] at h0
    refine h0.congr fun n ↦ ?_
    rw [measureReal_forall_le_eq_pow μ P X hiid n (u n), hp n]
  · simp_rw [fun n ↦ (hlaw n).map_eq]
    exact tendsto_integral_binomial_poissonMeasure p τ hpt f ⟨‖f‖, fun k ↦ by
      simpa [Real.norm_eq_abs] using f.norm_coe_le_norm k⟩


end CKSD
