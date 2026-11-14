module

public import CKSD.Processes.Basic
public import Mathlib.Analysis.Normed.Group.Tannery


/-!
# Long-run variance of a sample mean

For a square-integrable process `(X_t)_{t ∈ ℤ}` with autocovariance
`Cov(X_s, X_t) = γ(s - t)` and `∑_h |γ(h)| < ∞`, `n Var(X̄_n) → ∑_h γ(h)`. The proof regroups
the double sum of covariances by lag, with weights `#{(i, j) : i, j < n, i - j = h} / n` that
tend to `1`, and passes to the limit by Tannery's theorem.

## Main definitions

* `CKSD.lagCountWeight`: the lag-counting weight `#{(i, j) : i, j < n, i - j = h} / n`.

## Main results

* `CKSD.sum_sum_eq_tsum_lag_count_weight`: regrouping by lag.
* `CKSD.tendsto_lag_count_weight`: the weights tend to `1` at each fixed lag.
* `CKSD.tendsto_mul_variance_sample_average` (GAPS 106.12): `n Var(X̄_n) → ∑_h γ(h)`.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- The lag-counting weight `#{(i, j) : i, j < n, i - j = h} / n`. -/
def lagCountWeight (n : ℕ) (h : ℤ) : ℝ :=
  (((Finset.range n ×ˢ Finset.range n).filter fun p : ℕ × ℕ ↦ (p.1 : ℤ) - p.2 = h).card : ℝ) / n

/-- A normalized double sum over `i, j < n` of a function of `i - j`, regrouped by lag. -/
theorem sum_sum_eq_tsum_lag_count_weight (γ : ℤ → ℝ) (n : ℕ) :
    (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, γ ((i : ℤ) - j) =
      ∑' h : ℤ, lagCountWeight n h * γ h := by
  classical
  let s := Finset.range n ×ˢ Finset.range n
  let g : ℕ × ℕ → ℤ := fun p ↦ (p.1 : ℤ) - p.2
  have hsupp : ∀ h ∉ s.image g, lagCountWeight n h * γ h = 0 := by
    intro h hh
    have : (s.filter fun p ↦ g p = h) = ∅ := by
      ext p
      simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
      intro hp hgp
      exact hh (Finset.mem_image.2 ⟨p, hp, hgp⟩)
    simp [lagCountWeight, s, g, this]
  have hfib : ∑ p ∈ s, γ (g p) =
      ∑ h ∈ s.image g, ((s.filter fun p ↦ g p = h).card : ℝ) * γ h := by
    rw [← Finset.sum_fiberwise_of_maps_to (fun p hp ↦ Finset.mem_image_of_mem g hp)]
    refine Finset.sum_congr rfl fun h _ ↦ ?_
    rw [Finset.sum_congr rfl (g := fun _ ↦ γ h) (fun p hp ↦ by
      show γ (g p) = γ h
      rw [(Finset.mem_filter.1 hp).2])]
    simp
  rw [tsum_eq_sum hsupp, ← Finset.sum_product']
  change (n : ℝ)⁻¹ * ∑ p ∈ s, γ (g p) = _
  rw [hfib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun h _ ↦ ?_
  simp only [lagCountWeight, s, g]
  ring

/-- Lag-counting weights are nonnegative. -/
theorem lag_count_weight_nonneg (n : ℕ) (h : ℤ) : 0 ≤ lagCountWeight n h := by
  unfold lagCountWeight; positivity

/-- Lag-counting weights are at most one. -/
theorem lag_count_weight_le_one (n : ℕ) (h : ℤ) : lagCountWeight n h ≤ 1 := by
  unfold lagCountWeight
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [div_le_one (by exact_mod_cast hn)]
  have : ((Finset.range n ×ˢ Finset.range n).filter fun p : ℕ × ℕ ↦ (p.1 : ℤ) - p.2 = h).card
      ≤ (Finset.range n).card := by
    refine Finset.card_le_card_of_injOn Prod.snd (fun p hp ↦ ?_) ?_
    · simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_range] at hp
      simpa using hp.1.2
    · intro p hp q hq hpq
      simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hp hq
      have : (p.1 : ℤ) = q.1 := by rw [← hpq] at hq; linarith [hp.2, hq.2]
      exact Prod.ext (by exact_mod_cast this) hpq
  simpa using (Nat.cast_le (α := ℝ)).2 this

/-- The lower bound `(n - |h|)/n` for the lag-counting weight. -/
theorem le_lag_count_weight (n : ℕ) (h : ℤ) :
    ((n - (h.toNat + (-h).toNat) : ℕ) : ℝ) / n ≤ lagCountWeight n h := by
  unfold lagCountWeight
  gcongr
  refine (Finset.card_range _).symm.le.trans ?_
  refine Finset.card_le_card_of_injOn (fun j ↦ (j + h.toNat, j + (-h).toNat)) (fun j hj ↦ ?_) ?_
  · simp only [Finset.coe_range, Set.mem_Iio] at hj
    simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_range, Set.mem_ofPred_eq]
    refine ⟨⟨by omega, by omega⟩, by push_cast; omega⟩
  · intro a _ b _ hab
    simp only [Prod.mk.injEq] at hab
    omega

/-- Lag-counting weights tend to one at each fixed lag. -/
theorem tendsto_lag_count_weight (h : ℤ) : Tendsto (fun n ↦ lagCountWeight n h) atTop (𝓝 1) := by
  set a := h.toNat + (-h).toNat
  have hlow : Tendsto (fun n : ℕ ↦ ((n - a : ℕ) : ℝ) / n) atTop (𝓝 1) := by
    have h1 : Tendsto (fun n : ℕ ↦ 1 - (a : ℝ) / n) atTop (𝓝 1) := by
      simpa using (tendsto_const_div_atTop_nhds_zero_nat (a : ℝ)).const_sub 1
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop (a + 1)] with n hn
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    rw [Nat.cast_sub (by omega)]
    field_simp
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
    (fun n ↦ le_lag_count_weight n h) (fun n ↦ lag_count_weight_le_one n h)


/-- GAPS 106.12, long-run variance from summable autocovariances: if the autocovariance
`Cov(X_s, X_t) = γ(s - t)` is absolutely summable, then `n Var(X̄_n) → ∑_h γ(h)`, with `X̄_n` the
mean of `X 0, …, X (n - 1)`. -/
theorem tendsto_mul_variance_sample_average {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℤ → Ω → ℝ)
    (h2 : ∀ t, MemLp (X t) 2 μ) (γ : ℤ → ℝ) (hγ : Summable (fun t ↦ |γ t|))
    (hcov : ∀ s t, cov[X s, X t; μ] = γ (s - t)) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) * Var[sampleAverage (fun j ↦ X j) n; μ])
      atTop (𝓝 (∑' h : ℤ, γ h)) := by
  have hrepr : ∀ n : ℕ, 0 < n → (n : ℝ) * Var[sampleAverage (fun j ↦ X j) n; μ] =
      ∑' h : ℤ, lagCountWeight n h * γ h := by
    intro n hn
    rw [← sum_sum_eq_tsum_lag_count_weight]
    have havg : sampleAverage (fun j : ℕ ↦ X j) n =
        fun ω ↦ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, X i ω := by
      funext ω; simp [sampleAverage, smul_eq_mul]
    have hvar : Var[sampleAverage (fun j : ℕ ↦ X j) n; μ] =
        ProbabilityTheory.covariance (sampleAverage (fun j : ℕ ↦ X j) n)
          (sampleAverage (fun j : ℕ ↦ X j) n) μ := by
      refine (covariance_self ?_).symm
      rw [havg]
      exact aemeasurable_const.mul (Finset.aemeasurable_fun_sum _ fun i _ ↦ (h2 i).aemeasurable)
    rw [hvar, havg, covariance_const_mul_left, covariance_const_mul_right,
      covariance_fun_sum_fun_sum' (X := fun i : ℕ ↦ X i) (Y := fun i : ℕ ↦ X i)
      (fun i _ ↦ h2 i) (fun i _ ↦ h2 i)]
    simp only [show ∀ s t, ProbabilityTheory.covariance (X s) (X t) μ = γ (s - t) from hcov]
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    field_simp
  have hlim := tendsto_tsum_of_dominated_convergence (f := fun n h ↦ lagCountWeight n h * γ h)
    (g := γ) (bound := fun h ↦ |γ h|) hγ
    (fun h ↦ by simpa using (tendsto_lag_count_weight h).mul_const (γ h))
    (Eventually.of_forall fun n h ↦ by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (lag_count_weight_nonneg n h)]
      exact mul_le_of_le_one_left (abs_nonneg _) (lag_count_weight_le_one n h))
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn using (hrepr n hn).symm

end CKSD
