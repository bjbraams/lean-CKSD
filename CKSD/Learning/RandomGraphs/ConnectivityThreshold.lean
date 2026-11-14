module

public import Mathlib.Probability.Combinatorics.BinomialRandomGraph.Defs
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Algebra.Order.Field.GeomSum
public import Mathlib.Probability.Distributions.Poisson.PoissonLimitThm
public import CKSD.Learning.RandomGraphs.Connectivity


/-!
# Limits at the connectivity threshold of the binomial random graph

For `p = (log n + xₙ)/n` (clamped to `[0,1]`) the binomial random graph `G(n, p)` is connected
with probability tending to one if `xₙ → ∞`, has an isolated vertex with probability tending to
one if `xₙ → -∞`, and for constant `xₙ = x` is connected with probability tending to
`exp (-e^{-x})` (Erdős–Rényi). The finite-`n` estimates are those of
`CKSD.Learning.RandomGraphs.Connectivity`; here `Sⱼ → e^{-jx}/j!` gives the Poisson limit.

## Main results

* `CKSD.tendsto_isolated_moment_threshold`: the limits of the factorial moments of the number of
  isolated vertices.
* `CKSD.tendsto_binomial_random_connected_of_tendsto_at_top`,
  `CKSD.tendsto_binomial_random_exists_isolated_of_tendsto_at_bot`,
  `CKSD.tendsto_binomial_random_connected_threshold`: the three parts of the connectivity
  threshold (GAPS 107.47).

The Poisson-limit lemma `ProbabilityTheory.tendsto_choose_mul_pow_atTop` and the exponential
series are Mathlib's.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set unitInterval
open scoped ENNReal NNReal Topology BigOperators

namespace CKSD

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- For `p ≤ 1/2`: `exp(-np - 2np²) ≤ (1 - p)^n`. -/
private theorem exp_le_one_sub_pow {p : ℝ} (hp : p ≤ 1 / 2) (n : ℕ) :
    Real.exp (-(n * p) - 2 * n * p ^ 2) ≤ (1 - p) ^ n := by
  have hq : 0 < 1 - p := by linarith
  have hlog : -p - 2 * p ^ 2 ≤ Real.log (1 - p) := by
    refine le_trans ?_ (Real.one_sub_inv_le_log_of_pos hq)
    rw [show 1 - (1 - p)⁻¹ = -p / (1 - p) by field_simp; ring]
    rw [le_div_iff₀ hq]
    nlinarith
  rw [← Real.exp_log (pow_pos hq n), Real.log_pow]
  apply Real.exp_le_exp.mpr
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

/-! ### Limits along the threshold sequence -/

/-- Elementary facts about the clamped edge probability `p = max 0 (min 1 r)`: `n p ≥ min n (n r)`
and `p ≤ max 0 r`. -/
private theorem proj_icc_bounds (n : ℕ) (r : ℝ) :
    min (n : ℝ) (n * r) ≤ n * (Set.projIcc (0 : ℝ) 1 zero_le_one r : ℝ) ∧
      (Set.projIcc (0 : ℝ) 1 zero_le_one r : ℝ) ≤ max 0 r := by
  rw [Set.coe_projIcc]
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  constructor
  · rcases le_total r 0 with h | h
    · rw [max_eq_left (by simp [h])]
      have : (n : ℝ) * r ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hn h
      simp only [mul_zero]
      exact (min_le_right _ _).trans this
    · rcases le_total r 1 with h' | h'
      · rw [min_eq_right h', max_eq_right h]
        exact min_le_right _ _
      · rw [min_eq_left h', max_eq_right zero_le_one, mul_one]
        exact min_le_left _ _
  · exact max_le_max le_rfl (min_le_right _ _)

/-- `log n / n → 0` along the integers, together with its square variant. -/
private theorem tendsto_log_pow_div (k : ℕ) :
    Tendsto (fun n : ℕ ↦ Real.log n ^ k / n) atTop (𝓝 0) := by
  have := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 k one_ne_zero).comp
    tendsto_natCast_atTop_atTop
  refine this.congr fun n ↦ ?_
  simp

/-- The partial sums `∑_{j ≤ M} (-1)^j μ^j / j!` converge to `exp (-μ)`. -/
private theorem tendsto_alternating_exp_partial_sum (μ : ℝ) :
    Tendsto (fun M : ℕ ↦ ∑ j ∈ Finset.range (M + 1), (-1 : ℝ) ^ j * (μ ^ j / j.factorial))
      atTop (𝓝 (Real.exp (-μ))) := by
  have h := NormedSpace.expSeries_div_hasSum_exp (-μ)
  rw [← Real.exp_eq_exp_ℝ] at h
  have h' := h.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  refine h'.congr fun M ↦ ?_
  simp only [Function.comp_apply]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [neg_pow, mul_div_assoc]

/-- Bonferroni squeeze: if the alternating partial sums of `Sⱼ(n)` bound `P n` alternately and
`Sⱼ(n) → μ^j / j!` for each `j`, then `P n → exp (-μ)`. -/
private theorem tendsto_of_bonferroni (P : ℕ → ℝ) (S : ℕ → ℕ → ℝ) (μ : ℝ)
    (hB : ∀ M n, 0 ≤ (-1 : ℝ) ^ M * ((∑ j ∈ Finset.range (M + 1), (-1 : ℝ) ^ j * S j n) - P n))
    (hS : ∀ j, Tendsto (S j) atTop (𝓝 (μ ^ j / j.factorial))) :
    Tendsto P atTop (𝓝 (Real.exp (-μ))) := by
  have hA := tendsto_alternating_exp_partial_sum μ
  rw [Metric.tendsto_atTop] at hA ⊢
  intro ε hε
  obtain ⟨M₀, hM₀⟩ := hA (ε / 2) (by positivity)
  set M := 2 * M₀
  have hpart : ∀ L, Tendsto (fun n ↦ ∑ j ∈ Finset.range (L + 1), (-1 : ℝ) ^ j * S j n) atTop
      (𝓝 (∑ j ∈ Finset.range (L + 1), (-1 : ℝ) ^ j * (μ ^ j / j.factorial))) := fun L ↦
    tendsto_finsetSum _ fun j _ ↦ (hS j).const_mul _
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.mp (hpart M) (ε / 2) (by positivity)
  obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.mp (hpart (M + 1)) (ε / 2) (by positivity)
  refine ⟨max N₁ N₂, fun n hn ↦ ?_⟩
  have h1 := hN₁ n (le_of_max_le_left hn)
  have h2 := hN₂ n (le_of_max_le_right hn)
  have h3 := hM₀ M (by omega)
  have h4 := hM₀ (M + 1) (by omega)
  have hup := hB M n
  have hlow := hB (M + 1) n
  have hev : (-1 : ℝ) ^ M = 1 := by rw [pow_mul]; norm_num
  rw [hev, one_mul] at hup
  rw [pow_succ, hev] at hlow
  rw [Real.dist_eq] at h1 h2 h3 h4 ⊢
  rw [abs_lt] at h1 h2 h3 h4 ⊢
  constructor <;> linarith

/-- For fixed `x`, the threshold value `r n = (log n + x) / n` tends to zero. -/
private theorem tendsto_threshold_zero (x : ℝ) :
    Tendsto (fun n : ℕ ↦ (Real.log n + x) / n) atTop (𝓝 0) := by
  have h1 := tendsto_log_pow_div 1
  have h2 := tendsto_const_div_atTop_nhds_zero_nat x
  simpa [add_div] using h1.add h2

/-- For fixed `x`, the clamped threshold probability eventually equals `(log n + x) / n`. -/
private theorem eventually_proj_icc_threshold_eq (x : ℝ) :
    ∀ᶠ n : ℕ in atTop, (Set.projIcc (0 : ℝ) 1 zero_le_one ((Real.log n + x) / n) : ℝ) =
      (Real.log n + x) / n ∧ (Real.log n + x) / n ≤ 1 / 2 := by
  have hlog : Tendsto (fun n : ℕ ↦ Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually_ge_atTop (-x),
    (tendsto_threshold_zero x).eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))]
    with n h1 h2
  refine ⟨?_, h2⟩
  have h0 : 0 ≤ (Real.log n + x) / n := div_nonneg (by linarith) (Nat.cast_nonneg n)
  rw [Set.coe_projIcc, min_eq_right (by linarith), max_eq_right h0]

/-- For fixed `x`, `n (1 - (log n + x)/n)^n → exp (-x)`. -/
private theorem tendsto_mul_one_sub_threshold_pow (x : ℝ) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) * (1 - (Real.log n + x) / n) ^ n) atTop
      (𝓝 (Real.exp (-x))) := by
  have hsq : Tendsto (fun n : ℕ ↦ (Real.log n + x) ^ 2 / n) atTop (𝓝 0) := by
    have h := ((tendsto_log_pow_div 2).add ((tendsto_log_pow_div 1).const_mul (2 * x))).add
      (tendsto_const_div_atTop_nhds_zero_nat (x ^ 2))
    simp only [mul_zero, add_zero] at h
    refine h.congr fun n ↦ ?_
    ring
  have hlow : Tendsto (fun n : ℕ ↦ Real.exp (-x - 2 * ((Real.log n + x) ^ 2 / n))) atTop
      (𝓝 (Real.exp (-x))) := by
    have := ((hsq.const_mul 2).const_sub (-x)).rexp
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_proj_icc_threshold_eq x, eventually_ge_atTop 1] with n hn h1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast h1
    have h := exp_le_one_sub_pow hn.2 n
    have he : Real.exp (-x - 2 * ((Real.log n + x) ^ 2 / n)) =
        n * Real.exp (-(n * ((Real.log n + x) / n)) - 2 * n * ((Real.log n + x) / n) ^ 2) := by
      rw [show (n : ℝ) * Real.exp (-(n * ((Real.log n + x) / n)) -
          2 * n * ((Real.log n + x) / n) ^ 2) = Real.exp (Real.log n +
          (-(n * ((Real.log n + x) / n)) - 2 * n * ((Real.log n + x) / n) ^ 2)) by
        rw [Real.exp_add, Real.exp_log hn0]]
      congr 1
      field_simp
      ring
    rw [he]
    exact mul_le_mul_of_nonneg_left h hn0.le
  · filter_upwards [eventually_proj_icc_threshold_eq x, eventually_ge_atTop 1] with n hn h1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast h1
    have hr1 : (Real.log n + x) / n ≤ 1 := by linarith [hn.2]
    have h := one_sub_pow_le_exp hr1 n
    have he : n * Real.exp (-((Real.log n + x) / n * n)) = Real.exp (-x) := by
      nth_rewrite 1 [← Real.exp_log hn0]
      rw [← Real.exp_add]
      congr 1
      field_simp
      ring
    rw [← he]
    exact mul_le_mul_of_nonneg_left h hn0.le

/-- For fixed `x`, the `j`-th factorial moment of the number of isolated vertices of
`G(n, (log n + x)/n)` tends to `e^{-jx} / j!`. -/
theorem tendsto_isolated_moment_threshold (x : ℝ) (j : ℕ) :
    Tendsto (fun n : ℕ ↦ isolatedMoment (V := Fin n)
        (Set.projIcc (0 : ℝ) 1 zero_le_one ((Real.log n + x) / n)) j) atTop
      (𝓝 (Real.exp (-x) ^ j / j.factorial)) := by
  set q : ℕ → ℝ := fun n ↦
    1 - (Set.projIcc (0 : ℝ) 1 zero_le_one ((Real.log n + x) / n) : ℝ) with hq
  have hqn : Tendsto (fun n : ℕ ↦ (n : ℝ) * q n ^ n) atTop (𝓝 (Real.exp (-x))) := by
    refine (tendsto_mul_one_sub_threshold_pow x).congr' ?_
    filter_upwards [eventually_proj_icc_threshold_eq x] with n hn
    simp only [hq, hn.1]
  have hq1 : Tendsto q atTop (𝓝 1) := by
    have := (tendsto_threshold_zero x).const_sub 1
    rw [sub_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_proj_icc_threshold_eq x] with n hn
    simp only [hq, hn.1]
  have hL := ProbabilityTheory.tendsto_choose_mul_pow_atTop (p := fun n ↦ q n ^ n) j hqn
  have hqpos : ∀ᶠ n : ℕ in atTop, 0 < q n := by
    filter_upwards [eventually_proj_icc_threshold_eq x] with n hn
    simp only [hq, hn.1]
    linarith [hn.2]
  have hU : Tendsto (fun n : ℕ ↦ (n.choose j : ℝ) * (q n ^ n) ^ j * (q n ^ (j * j))⁻¹) atTop
      (𝓝 (Real.exp (-x) ^ j / j.factorial)) := by
    have := hL.mul ((hq1.pow (j * j)).inv₀ (by simp))
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hL hU ?_ ?_
  · refine Eventually.of_forall fun n ↦ ?_
    have h := (isolated_moment_mem_icc (V := Fin n)
      (Set.projIcc (0 : ℝ) 1 zero_le_one ((Real.log n + x) / n)) j).1
    rw [Fintype.card_fin] at h
    refine le_trans (le_of_eq ?_) h
    simp only [hq]
    rw [← pow_mul, mul_comm n j]
  · filter_upwards [hqpos, eventually_ge_atTop j] with n hpos hjn
    have h := (isolated_moment_mem_icc (V := Fin n)
      (Set.projIcc (0 : ℝ) 1 zero_le_one ((Real.log n + x) / n)) j).2
    rw [Fintype.card_fin] at h
    refine h.trans (le_of_eq ?_)
    have hsplit : q n ^ (j * (n - j)) * q n ^ (j * j) = (q n ^ n) ^ j := by
      rw [← pow_add, ← pow_mul, ← Nat.mul_add, Nat.sub_add_cancel hjn, mul_comm]
    rw [← hsplit, mul_assoc, mul_assoc, mul_inv_cancel₀ (pow_pos hpos _).ne', mul_one]

/-- GAPS 107.47, connectivity at `p = (log n + x)/n`: the probability that `G(n, p)` is connected
tends to `exp (-e^{-x})`. -/
theorem tendsto_binomial_random_connected_threshold (x : ℝ) :
    Tendsto (fun n : ℕ ↦ (SimpleGraph.binomialRandom (Fin n)
        (Set.projIcc (0 : ℝ) 1 zero_le_one ((Real.log n + x) / n))).real {G | G.Connected})
      atTop (𝓝 (Real.exp (-Real.exp (-x)))) := by
  set p : ℕ → I := fun n ↦ Set.projIcc (0 : ℝ) 1 zero_le_one ((Real.log n + x) / n) with hp
  have hiso : Tendsto (fun n : ℕ ↦ (SimpleGraph.binomialRandom (Fin n) (p n)).real
      {G | isolatedVertices G = ∅}) atTop (𝓝 (Real.exp (-Real.exp (-x)))) :=
    tendsto_of_bonferroni _ (fun j n ↦ isolatedMoment (V := Fin n) (p n) j) _
      (fun M n ↦ bonferroni_isolated_vertices (p n) M)
      (fun j ↦ tendsto_isolated_moment_threshold x j)
  have hT := tendsto_disconn_sum p |x| (by
    filter_upwards [eventually_proj_icc_threshold_eq x, eventually_ge_atTop 1] with n hn h1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast h1
    simp only [hp, hn.1]
    rw [mul_div_cancel₀ _ hn0.ne']
    linarith [neg_abs_le x])
  have hlow := hiso.sub hT
  rw [sub_zero] at hlow
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hiso ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have h := (binomial_random_real_connected_mem_icc (V := Fin n) (by simpa using hn) (p n)).1
    simpa only [Fintype.card_fin] using h
  · filter_upwards [eventually_ge_atTop 2] with n hn
    exact (binomial_random_real_connected_mem_icc (V := Fin n) (by simpa using hn) (p n)).2

/-- First-moment bound: `P(no isolated vertex) ≥ 1 - S₁`. -/
theorem one_sub_isolated_moment_one_le (p : I) :
    1 - isolatedMoment (V := V) p 1 ≤
      (SimpleGraph.binomialRandom V p).real {G | isolatedVertices G = ∅} := by
  have h := bonferroni_isolated_vertices (V := V) p 1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, isolated_moment_zero, pow_zero,
    pow_one, zero_add, one_mul] at h
  linarith

/-- If `xₙ → ∞`, the probability that `G(n, (log n + xₙ)/n)` has no isolated vertex tends to
one; more precisely `S₁ → 0`. -/
private theorem tendsto_isolated_moment_one_of_tendsto_at_top (x : ℕ → ℝ)
    (hx : Tendsto x atTop atTop) :
    Tendsto (fun n : ℕ ↦ isolatedMoment (V := Fin n)
        (Set.projIcc (0 : ℝ) 1 zero_le_one ((Real.log n + x n) / n)) 1) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ ↦ (n : ℝ) * Real.exp (-(n : ℝ))) atTop (𝓝 0) := by
    have := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp tendsto_natCast_atTop_atTop
    refine this.congr fun n ↦ ?_
    simp
  have h2 : Tendsto (fun n ↦ Real.exp (-x n)) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hx
  have hlim := (h1.add h2).const_mul (Real.exp 1)
  rw [add_zero, mul_zero] at hlim
  refine squeeze_zero' (Eventually.of_forall fun n ↦ ?_) ?_ hlim
  · exact Finset.sum_nonneg fun J _ ↦ pow_nonneg (by
      linarith [(Set.projIcc (0 : ℝ) 1 zero_le_one ((Real.log n + x n) / n)).2.2]) _
  filter_upwards [eventually_ge_atTop 1] with n hn
  set pn := Set.projIcc (0 : ℝ) 1 zero_le_one ((Real.log n + x n) / n)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hS := (isolated_moment_mem_icc (V := Fin n) pn 1).2
  rw [Fintype.card_fin, Nat.choose_one_right, one_mul] at hS
  have hq := one_sub_pow_le_exp pn.2.2 (n - 1)
  rw [Nat.cast_sub hn, Nat.cast_one] at hq
  have hmin := (proj_icc_bounds n ((Real.log n + x n) / n)).1
  rw [mul_div_cancel₀ _ hn0.ne'] at hmin
  have hkey : (n : ℝ) * Real.exp (-(n * (pn : ℝ))) ≤ n * Real.exp (-(n : ℝ)) + Real.exp (-x n) := by
    rcases le_total (n : ℝ) (Real.log n + x n) with h | h
    · rw [min_eq_left h] at hmin
      have : (n : ℝ) * Real.exp (-(n * (pn : ℝ))) ≤ n * Real.exp (-(n : ℝ)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hn0.le
      linarith [Real.exp_pos (-x n)]
    · rw [min_eq_right h] at hmin
      have : (n : ℝ) * Real.exp (-(n * (pn : ℝ))) ≤ n * Real.exp (-(Real.log n + x n)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hn0.le
      have he : (n : ℝ) * Real.exp (-(Real.log n + x n)) = Real.exp (-x n) := by
        rw [show -(Real.log n + x n) = -Real.log n + -x n by ring, Real.exp_add, Real.exp_neg,
          Real.exp_log hn0]
        field_simp
      have := mul_pos hn0 (Real.exp_pos (-(n : ℝ)))
      linarith
  calc isolatedMoment (V := Fin n) pn 1 ≤ n * (1 - (pn : ℝ)) ^ (n - 1) := hS
    _ ≤ n * Real.exp (-((pn : ℝ) * (n - 1))) := mul_le_mul_of_nonneg_left hq hn0.le
    _ = Real.exp 1 * (n * Real.exp (-(n * (pn : ℝ)))) * Real.exp ((pn : ℝ) - 1) := by
        rw [mul_comm (Real.exp 1), mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add]
        ring_nf
    _ ≤ Real.exp 1 * (n * Real.exp (-(n * (pn : ℝ)))) * 1 := by
        gcongr
        exact Real.exp_le_one_iff.mpr (by linarith [pn.2.2])
    _ ≤ Real.exp 1 * (n * Real.exp (-(n : ℝ)) + Real.exp (-x n)) := by
        rw [mul_one]; gcongr

/-- GAPS 107.47: if `xₙ → ∞`, then `G(n, (log n + xₙ)/n)` is connected with probability tending
to one. -/
theorem tendsto_binomial_random_connected_of_tendsto_at_top (x : ℕ → ℝ)
    (hx : Tendsto x atTop atTop) :
    Tendsto (fun n : ℕ ↦ (SimpleGraph.binomialRandom (Fin n)
        (Set.projIcc (0 : ℝ) 1 zero_le_one ((Real.log n + x n) / n))).real {G | G.Connected})
      atTop (𝓝 1) := by
  set p : ℕ → I := fun n ↦ Set.projIcc (0 : ℝ) 1 zero_le_one ((Real.log n + x n) / n) with hp
  have hS := tendsto_isolated_moment_one_of_tendsto_at_top x hx
  have hT := tendsto_disconn_sum p 0 (by
    filter_upwards [hx.eventually_ge_atTop 0, eventually_ge_atTop 1] with n hxn h1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast h1
    have hmin := (proj_icc_bounds n ((Real.log n + x n) / n)).1
    rw [mul_div_cancel₀ _ hn0.ne'] at hmin
    have hlogn : Real.log n ≤ n := (Real.log_le_sub_one_of_pos hn0).trans (by linarith)
    simp only [hp, sub_zero]
    exact le_trans (le_min hlogn (by linarith)) hmin)
  have hlow := (hS.const_sub 1).sub hT
  rw [sub_zero, sub_zero] at hlow
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have h := (binomial_random_real_connected_mem_icc (V := Fin n) (by simpa using hn) (p n)).1
    simp only [Fintype.card_fin] at h
    have h' := one_sub_isolated_moment_one_le (V := Fin n) (p n)
    linarith
  · exact Eventually.of_forall fun n ↦ measureReal_le_one

/-- GAPS 107.47: if `xₙ → -∞`, then `G(n, (log n + xₙ)/n)` has an isolated vertex with
probability tending to one (second-moment method). -/
theorem tendsto_binomial_random_exists_isolated_of_tendsto_at_bot (x : ℕ → ℝ)
    (hx : Tendsto x atTop atBot) :
    Tendsto (fun n : ℕ ↦ (SimpleGraph.binomialRandom (Fin n)
        (Set.projIcc (0 : ℝ) 1 zero_le_one ((Real.log n + x n) / n))).real
          {G | ∃ v, ∀ w, ¬ G.Adj v w}) atTop (𝓝 1) := by
  set p : ℕ → I := fun n ↦ Set.projIcc (0 : ℝ) 1 zero_le_one ((Real.log n + x n) / n) with hp
  set q : ℕ → ℝ := fun n ↦ 1 - (p n : ℝ) with hq
  have hlog : Tendsto (fun n : ℕ ↦ Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hl1 := tendsto_log_pow_div 1
  simp only [pow_one] at hl1
  have hl2 := tendsto_log_pow_div 2
  -- eventually `0 ≤ pₙ ≤ log n / n ≤ 1/2`
  have hpb : ∀ᶠ n : ℕ in atTop, (p n : ℝ) ≤ Real.log n / n ∧ Real.log n / n ≤ 1 / 2 ∧
      n * (p n : ℝ) ≤ max 0 (Real.log n + x n) := by
    filter_upwards [hx.eventually_le_atBot 0, eventually_ge_atTop 1,
      hl1.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with n hxn h1 hhalf
    have hn0 : (0 : ℝ) < n := by exact_mod_cast h1
    have hlog0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast h1)
    have hmax := (proj_icc_bounds n ((Real.log n + x n) / n)).2
    refine ⟨hmax.trans (max_le (div_nonneg hlog0 hn0.le) ?_), hhalf, ?_⟩
    · exact div_le_div_of_nonneg_right (by linarith) hn0.le
    · calc n * (p n : ℝ) ≤ n * max 0 ((Real.log n + x n) / n) :=
            mul_le_mul_of_nonneg_left hmax hn0.le
        _ = max 0 (Real.log n + x n) := by
            rw [mul_max_of_nonneg _ _ hn0.le, mul_zero, mul_div_cancel₀ _ hn0.ne']
  have hp0 : Tendsto (fun n ↦ (p n : ℝ)) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun n ↦ (p n).2.1) ?_ hl1
    filter_upwards [hpb] with n h
    exact h.1
  have hq1 : Tendsto q atTop (𝓝 1) := by
    simpa using hp0.const_sub 1
  -- `n qₙ^n → ∞`
  have hnq : Tendsto (fun n : ℕ ↦ (n : ℝ) * q n ^ n) atTop atTop := by
    have hmin : Tendsto (fun n : ℕ ↦ min (Real.log n) (-x n) - 2) atTop atTop :=
      tendsto_atTop_add_const_right _ _ (tendsto_atTop.2 fun b ↦
        ((hlog.eventually_ge_atTop b).and
          ((tendsto_neg_atBot_atTop.comp hx).eventually_ge_atTop b)).mono
          fun n h ↦ le_min h.1 h.2)
    refine tendsto_atTop_mono' atTop ?_ (Real.tendsto_exp_atTop.comp hmin)
    filter_upwards [hpb, eventually_ge_atTop 1,
      hl2.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1))] with n h h1 hsq
    have hn0 : (0 : ℝ) < n := by exact_mod_cast h1
    have hlow := exp_le_one_sub_pow (h.1.trans h.2.1) n
    have hsq' : (n : ℝ) * (p n : ℝ) ^ 2 ≤ 1 := by
      have hp2 : (p n : ℝ) ^ 2 ≤ (Real.log n / n) ^ 2 :=
        pow_le_pow_left₀ (p n).2.1 h.1 2
      calc (n : ℝ) * (p n : ℝ) ^ 2 ≤ n * (Real.log n / n) ^ 2 :=
            mul_le_mul_of_nonneg_left hp2 hn0.le
        _ = Real.log n ^ 2 / n := by field_simp
        _ ≤ 1 := hsq
    have hexp : min (Real.log n) (-x n) - 2 ≤
        Real.log n + (-(n * (p n : ℝ)) - 2 * n * (p n : ℝ) ^ 2) := by
      have h3 := h.2.2
      rcases le_total 0 (Real.log n + x n) with h4 | h4
      · rw [max_eq_right h4] at h3
        have := min_le_right (Real.log n) (-x n)
        nlinarith
      · rw [max_eq_left h4] at h3
        have := min_le_left (Real.log n) (-x n)
        nlinarith
    calc Real.exp (min (Real.log n) (-x n) - 2)
        ≤ Real.exp (Real.log n + (-(n * (p n : ℝ)) - 2 * n * (p n : ℝ) ^ 2)) :=
          Real.exp_le_exp.mpr hexp
      _ = n * Real.exp (-(n * (p n : ℝ)) - 2 * n * (p n : ℝ) ^ 2) := by
          rw [Real.exp_add, Real.exp_log hn0]
      _ ≤ n * q n ^ n := mul_le_mul_of_nonneg_left hlow hn0.le
  -- the second-moment bound
  set P0 : ℕ → ℝ := fun n ↦ (SimpleGraph.binomialRandom (Fin n) (p n)).real
    {G | isolatedVertices G = ∅} with hP0
  have hbound : Tendsto (fun n : ℕ ↦ ((n : ℝ) * q n ^ n)⁻¹ + (q n ^ 4)⁻¹ - 1) atTop (𝓝 0) := by
    have := (hnq.inv_tendsto_atTop.add ((hq1.pow 4).inv₀ (by norm_num))).sub_const 1
    simpa using this
  have hP0lim : Tendsto P0 atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun n ↦ measureReal_nonneg) ?_ hbound
    filter_upwards [hpb, eventually_ge_atTop 2] with n h h2
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hqpos : 0 < q n := by simp only [hq]; linarith [h.1.trans h.2.1]
    have hS1 := (isolated_moment_mem_icc (V := Fin n) (p n) 1).1
    have hS2 := (isolated_moment_mem_icc (V := Fin n) (p n) 2).2
    rw [Fintype.card_fin, Nat.choose_one_right, one_mul] at hS1
    rw [Fintype.card_fin, Nat.cast_choose_two] at hS2
    have hsm := binomial_random_real_isolated_vertices_eq_empty_mul_le (V := Fin n) (p n)
    set S1 := isolatedMoment (V := Fin n) (p n) 1
    set S2 := isolatedMoment (V := Fin n) (p n) 2
    set a := (n : ℝ) * q n ^ n with ha
    have ha0 : 0 < a := mul_pos hn0 (pow_pos hqpos n)
    have hS1a : a ≤ S1 := hS1
    have hS10 : 0 < S1 := ha0.trans_le hS1a
    -- `2 S₂ ≤ S₁² q⁻⁴`
    have hq4 : q n ^ (2 * (n - 2)) * q n ^ 4 = (q n ^ n) ^ 2 := by
      rw [← pow_add, ← pow_mul]; congr 1; omega
    have h2S2 : 2 * S2 ≤ S1 ^ 2 * (q n ^ 4)⁻¹ := by
      have : 2 * S2 ≤ (n : ℝ) ^ 2 * q n ^ (2 * (n - 2)) := by
        have hq0 : 0 ≤ q n ^ (2 * (n - 2)) := pow_nonneg hqpos.le _
        nlinarith
      refine this.trans ?_
      rw [le_mul_inv_iff₀ (pow_pos hqpos 4), mul_assoc, hq4]
      have : a ^ 2 ≤ S1 ^ 2 := pow_le_pow_left₀ ha0.le hS1a 2
      calc (n : ℝ) ^ 2 * (q n ^ n) ^ 2 = a ^ 2 := by rw [ha]; ring
        _ ≤ S1 ^ 2 := this
    have hmain : P0 n * S1 ^ 2 ≤ S1 + S1 ^ 2 * ((q n ^ 4)⁻¹ - 1) := by
      have := hsm
      simp only [hP0]
      nlinarith
    have hdiv : P0 n ≤ S1⁻¹ + (q n ^ 4)⁻¹ - 1 := by
      have hS1sq : 0 < S1 ^ 2 := by positivity
      rw [← mul_le_mul_iff_left₀ hS1sq]
      calc P0 n * S1 ^ 2 ≤ S1 + S1 ^ 2 * ((q n ^ 4)⁻¹ - 1) := hmain
        _ = (S1⁻¹ + (q n ^ 4)⁻¹ - 1) * S1 ^ 2 := by field_simp; ring
    calc P0 n ≤ S1⁻¹ + (q n ^ 4)⁻¹ - 1 := hdiv
      _ ≤ a⁻¹ + (q n ^ 4)⁻¹ - 1 := by gcongr
  have hcompl : ∀ n : ℕ, {G : SimpleGraph (Fin n) | ∃ v, ∀ w, ¬ G.Adj v w} =
      {G | isolatedVertices G = ∅}ᶜ := by
    intro n
    ext G
    simp [isolatedVertices, Finset.eq_empty_iff_forall_notMem]
  have := hP0lim.const_sub 1
  rw [sub_zero] at this
  refine this.congr fun n ↦ ?_
  simp only [hP0]
  rw [hcompl, probReal_compl_eq_one_sub (DiscreteMeasurableSpace.forall_measurableSet _)]

end CKSD
