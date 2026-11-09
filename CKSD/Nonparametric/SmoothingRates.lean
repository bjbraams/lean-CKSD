module

public import CKSD.Nonparametric.Models
public import Mathlib.Topology.MetricSpace.Holder

/-!
# Regression smoothers and one-dimensional Hölder rates

Stone's consistency theorem for the Nadaraya–Watson estimator, and the minimax rates
`n^(-2β/(2β+1))` for fixed-design regression and pointwise density estimation over Hölder
classes of order `β ∈ (0, 1]`, with the upper bounds attained by box-kernel local averaging and
by kernel density estimation. The fixed design samples at `(i + 1) / n`. Minimax risks are
infima over measurable estimators of suprema of `ℝ≥0∞`-valued risks. The higher-order
local-polynomial and Sobolev parts of the catalogue entries are outside these statements.

## Main definitions

* `CKSD.holderRegressionClass β L`, `CKSD.holderDensityClass β L`: measurable functions with
  `|f x - f y| ≤ L |x - y|^β` on `[0, 1]`, and probability densities with this bound on `ℝ`;
  `CKSD.mem_holderRegressionClass_iff` and `CKSD.mem_holderDensityClass_iff` identify them with
  Mathlib's `HolderOnWith` and `HolderWith`.
* `CKSD.fixedDesignRegressionLaw`, `CKSD.fixedDesignRegressionRisk`,
  `CKSD.holderRegressionMinimaxRisk`: the Gaussian fixed-design regression experiment, the mean
  integrated squared error, and its minimax value.
* `CKSD.fixedDesignLocalConstant`: the box-kernel local average.
* `CKSD.densityLaw`, `CKSD.holderDensityPointwiseMinimaxRisk`: the law with a given density
  and the pointwise minimax squared risk.

## Main results

* `CKSD.tendsto_nadarayaWatson_prediction_error_probability` (Stone's theorem).
* `CKSD.fixedDesignLocalConstant_risk_le`: the upper bound for the regression risk. The
  matching lower bound and the two-sided rate `CKSD.holderRegressionMinimaxRisk_bounds` are in
  `CKSD.Nonparametric.HolderRegressionMinimax`.
* `CKSD.finiteKernelDensityEstimator_risk_le`,
  `CKSD.holderDensityPointwiseMinimaxRisk_lower_bound`.

Sources: GAPS 103.7, 103.22, and 103.26.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- The finite-sample Nadaraya–Watson predictor formed from paired observations. -/
def nadarayaWatsonSample {d n : ℕ} (K : EuclideanSpace ℝ (Fin d) → ℝ) (h : ℝ)
    (sample : Fin n → EuclideanSpace ℝ (Fin d) × ℝ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  nadarayaWatson K h (fun i ↦ (sample i).1) (fun i ↦ (sample i).2) x

/-- GAPS 103.7: universal prediction consistency of the Nadaraya–Watson estimator.
The regression mean is given as a version of conditional expectation, with its `L²` property
explicit. The kernel has upper and positive local lower ball bounds. -/
theorem tendsto_nadarayaWatson_prediction_error_probability
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Measure (EuclideanSpace ℝ (Fin d) × ℝ)) [IsProbabilityMeasure P]
    (X : ℕ → Ω → EuclideanSpace ℝ (Fin d) × ℝ)
    (hiid : IsIndependentIdenticallyDistributed μ X P) (hY : MemLp Prod.snd 2 P)
    (m : EuclideanSpace ℝ (Fin d) → ℝ) (hm : Measurable m)
    (hm2 : MemLp m 2 (P.map Prod.fst))
    (hmean : P[(fun z ↦ z.2) |
      (inferInstance : MeasurableSpace (EuclideanSpace ℝ (Fin d))).comap Prod.fst] =ᵐ[P]
        fun z ↦ m z.1)
    (K : EuclideanSpace ℝ (Fin d) → ℝ) (hK : Measurable K)
    (a b r R : ℝ) (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) (hR : r ≤ R)
    (hlower : ∀ x, ‖x‖ ≤ r → a ≤ K x)
    (hupper : ∀ x, 0 ≤ K x ∧ K x ≤ b)
    (hsupp : ∀ x, R < ‖x‖ → K x = 0)
    (h : ℕ → ℝ) (hpos : ∀ n, 0 < h n) (hh : Tendsto h atTop (𝓝 0))
    (hnh : Tendsto (fun n : ℕ ↦ (n : ℝ) * h n ^ d) atTop atTop) :
    ∀ ε > (0 : ℝ), Tendsto (fun n ↦ μ.real {ω |
      ENNReal.ofReal ε < regressionPredictionError (P.map Prod.fst) m
        (nadarayaWatsonSample K (h n) (fun i : Fin n ↦ X i.val ω))}) atTop (𝓝 0) := by
  sorry

/-- Measurable functions on the line with the Hölder bound `|f x - f y| ≤ L |x - y|^β` on the
unit interval. There is no bound on an additive constant. -/
def holderRegressionClass (β L : ℝ) : Set (ℝ → ℝ) :=
  {f | Measurable f ∧ ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
    |f x - f y| ≤ L * Real.rpow |x - y| β}

/-- Mathlib's Hölder condition for real functions on a set of reals, in terms of absolute
values. -/
theorem holderOnWith_iff_abs_sub_le {C r : ℝ≥0} {f : ℝ → ℝ} {s : Set ℝ} :
    HolderOnWith C r f s ↔ ∀ x ∈ s, ∀ y ∈ s, |f x - f y| ≤ C * |x - y| ^ (r : ℝ) := by
  refine ⟨fun h x hx y hy ↦ by simpa [Real.dist_eq] using h.dist_le hx hy, fun h x hx y hy ↦ ?_⟩
  rw [edist_dist, edist_dist, Real.dist_eq, Real.dist_eq,
    ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) r.coe_nonneg, ← ENNReal.ofReal_coe_nnreal,
    ← ENNReal.ofReal_mul C.coe_nonneg]
  exact ENNReal.ofReal_le_ofReal (h x hx y hy)

/-- For nonnegative parameters, the Hölder regression class consists of the measurable
functions satisfying Mathlib's `HolderOnWith L β` on `[0, 1]`. -/
theorem mem_holderRegressionClass_iff {β L : ℝ≥0} {f : ℝ → ℝ} :
    f ∈ holderRegressionClass β L ↔ Measurable f ∧ HolderOnWith L β f (Icc 0 1) := by
  simp only [holderRegressionClass, mem_ofPred_eq, Real.rpow_eq_pow, holderOnWith_iff_abs_sub_le]

/-- Fixed-design Gaussian regression law with noise standard deviation `σ`. -/
def fixedDesignRegressionLaw (n : ℕ) (f : ℝ → ℝ) (σ : ℝ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun i ↦ gaussianReal (f (((i.val + 1 : ℕ) : ℝ) / n))
    (Real.toNNReal (σ ^ 2)))

/-- Mean integrated squared error of a predictor under the fixed-design Gaussian experiment. -/
def fixedDesignRegressionRisk {n : ℕ} (f : ℝ → ℝ) (σ : ℝ)
    (estimate : (Fin n → ℝ) → ℝ → ℝ) : ℝ≥0∞ :=
  ∫⁻ y, (∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal ((estimate y t - f t) ^ 2))
    ∂fixedDesignRegressionLaw n f σ

/-- Fixed-design Hölder minimax mean integrated squared risk over jointly measurable estimators. -/
def holderRegressionMinimaxRisk (n : ℕ) (β L σ : ℝ) : ℝ≥0∞ :=
  ⨅ T : {T : (Fin n → ℝ) → ℝ → ℝ // Measurable (Function.uncurry T)},
    ⨆ f : holderRegressionClass β L, fixedDesignRegressionRisk f.val σ T.val

/-- Box-kernel local-constant regression on the fixed design. -/
def fixedDesignLocalConstant {n : ℕ} (h : ℝ) (y : Fin n → ℝ) (t : ℝ) : ℝ :=
  let w := fun i : Fin n ↦ if |t - ((i.val + 1 : ℕ) : ℝ) / n| ≤ h then (1 : ℝ) else 0
  (∑ i, w i * y i) / (∑ i, w i)

/-- Mean squared error of a linear statistic of independent Gaussian observations with common
variance `v`: the variance `v ∑ aᵢ²` plus the squared bias. -/
theorem integral_sq_linear_gaussian {n : ℕ} (m : Fin n → ℝ) (v : ℝ≥0) (a : Fin n → ℝ)
    (b : ℝ) :
    MemLp (fun y : Fin n → ℝ ↦ ∑ i, a i * y i - b) 2
        (Measure.pi fun i ↦ gaussianReal (m i) v) ∧
    ∫ y, (∑ i, a i * y i - b) ^ 2 ∂(Measure.pi fun i ↦ gaussianReal (m i) v) =
      v * ∑ i, a i ^ 2 + (∑ i, a i * m i - b) ^ 2 := by
  set μ := Measure.pi fun i ↦ gaussianReal (m i) v with hμ
  have hX : ∀ i, MemLp (fun z : ℝ ↦ a i * z) 2 (gaussianReal (m i) v) := fun i ↦
    (memLp_id_gaussianReal 2).const_mul (a i)
  have hXi : ∀ i, MemLp (fun y : Fin n → ℝ ↦ a i * y i) 2 μ := fun i ↦
    (hX i).comp_measurePreserving (measurePreserving_eval _ i)
  have hS : MemLp (fun y : Fin n → ℝ ↦ ∑ i, a i * y i) 2 μ := memLp_finsetSum _ fun i _ ↦ hXi i
  have hZ : MemLp (fun y : Fin n → ℝ ↦ ∑ i, a i * y i - b) 2 μ := hS.sub (memLp_const b)
  refine ⟨hZ, ?_⟩
  have hEi : ∀ i, ∫ y, a i * y i ∂μ = a i * m i := fun i ↦ by
    have hmap := (measurePreserving_eval (fun i ↦ gaussianReal (m i) v) i).map_eq
    calc ∫ y, a i * y i ∂μ = ∫ z, a i * z ∂(μ.map (fun y ↦ y i)) :=
          (integral_map (measurable_pi_apply i).aemeasurable
            (by rw [hμ, hmap]; exact (hX i).aestronglyMeasurable)).symm
      _ = a i * m i := by rw [hμ, hmap, integral_const_mul, integral_id_gaussianReal]
  have hEZ : ∫ y, (∑ i, a i * y i - b) ∂μ = ∑ i, a i * m i - b := by
    rw [integral_sub (hS.integrable one_le_two) (integrable_const b),
      integral_finsetSum _ fun i _ ↦ (hXi i).integrable one_le_two, integral_const]
    simp [hEi]
  have hVS : Var[fun y : Fin n → ℝ ↦ ∑ i, a i * y i; μ] = ∑ i, a i ^ 2 * v := by
    have := variance_sum_pi (μ := fun i ↦ gaussianReal (m i) v)
      (X := fun i z ↦ a i * z) hX
    rw [hμ]
    rw [show (fun y : Fin n → ℝ ↦ ∑ i, a i * y i) = ∑ i, fun y : Fin n → ℝ ↦ a i * y i by
      ext y; simp, this]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [variance_const_mul, variance_fun_id_gaussianReal]
  have hVZ : Var[fun y : Fin n → ℝ ↦ ∑ i, a i * y i - b; μ] = ∑ i, a i ^ 2 * v := by
    rw [variance_sub_const hS.aestronglyMeasurable, hVS]
  have hV := variance_eq_sub hZ
  rw [hVZ] at hV
  have : μ[(fun y : Fin n → ℝ ↦ ∑ i, a i * y i - b) ^ 2] =
      ∫ y, (∑ i, a i * y i - b) ^ 2 ∂μ := rfl
  rw [Finset.mul_sum]
  have e : ∑ i, a i ^ 2 * (v : ℝ) = ∑ i, (v : ℝ) * a i ^ 2 :=
    Finset.sum_congr rfl fun i _ ↦ mul_comm _ _
  rw [← hEZ]
  linarith

/-- On the grid `(i + 1) / n`, a window of half-width `h ≥ 1 / n` around a point of `[0, 1]`
contains at least `n min(h, 1) / 2` design points. -/
theorem card_fixedDesign_window_ge {n : ℕ} (hn : 0 < n) {h t : ℝ} (hh : 1 / (n : ℝ) ≤ h)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (n : ℝ) * min h 1 / 2 ≤ ((Finset.univ : Finset (Fin n)).filter
      fun i ↦ |t - ((i.val + 1 : ℕ) : ℝ) / n| ≤ h).card := by
  classical
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set ℓ := min h 1 with hℓ
  have hℓh : ℓ ≤ h := min_le_left _ _
  have hℓ1 : ℓ ≤ 1 := min_le_right _ _
  have hnℓ : 1 ≤ (n : ℝ) * ℓ := by
    have h1n : 1 / (n : ℝ) ≤ 1 := by rw [div_le_one hnR]; exact_mod_cast hn
    have : 1 / (n : ℝ) ≤ ℓ := le_min hh h1n
    rw [div_le_iff₀ hnR] at this; linarith
  obtain ⟨u, hu0, hu1, hut⟩ : ∃ u : ℝ, 0 ≤ u ∧ u + ℓ ≤ 1 ∧
      ∀ s, u ≤ s → s ≤ u + ℓ → |t - s| ≤ h := by
    by_cases hc : t + ℓ ≤ 1
    · refine ⟨t, ht0, hc, fun s hs1 hs2 ↦ ?_⟩
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
    · push Not at hc
      refine ⟨1 - ℓ, by linarith, by linarith, fun s hs1 hs2 ↦ ?_⟩
      rw [abs_le]; constructor <;> linarith
  set M := ⌊(n : ℝ) * ℓ⌋₊ with hM
  have hM1 : 1 ≤ M := Nat.le_floor (by exact_mod_cast hnℓ)
  have hMle : (M : ℝ) ≤ n * ℓ := Nat.floor_le (by linarith)
  have hMgt : (n : ℝ) * ℓ < M + 1 := Nat.lt_floor_add_one _
  set k₀ := ⌊(n : ℝ) * u⌋₊ with hk₀
  have hk₀le : (k₀ : ℝ) ≤ n * u := Nat.floor_le (by positivity)
  have hk₀gt : (n : ℝ) * u < k₀ + 1 := Nat.lt_floor_add_one _
  have hidx : ∀ j < M, k₀ + j < n := by
    intro j hj
    have : (k₀ : ℝ) + j + 1 ≤ n := by
      have hj' : (j : ℝ) + 1 ≤ M := by exact_mod_cast hj
      nlinarith
    exact_mod_cast (show ((k₀ + j : ℕ) : ℝ) < n by push_cast; linarith)
  have hcard : M ≤ ((Finset.univ : Finset (Fin n)).filter
      fun i ↦ |t - ((i.val + 1 : ℕ) : ℝ) / n| ≤ h).card := by
    calc M = (Finset.range M).card := (Finset.card_range M).symm
      _ ≤ _ := by
          refine Finset.card_le_card_of_injOn
            (fun j ↦ if hj : j < M then (⟨k₀ + j, hidx j hj⟩ : Fin n) else ⟨0, hn⟩) ?_ ?_
          · intro j hj
            have hj' : j < M := Finset.mem_range.mp hj
            simp only [hj', dite_true, Finset.coe_filter, Finset.mem_univ, true_and,
              mem_ofPred_eq]
            apply hut
            · rw [le_div_iff₀ hnR]; push_cast; nlinarith
            · rw [div_le_iff₀ hnR]; push_cast
              have : (j : ℝ) + 1 ≤ M := by exact_mod_cast hj'
              nlinarith
          · intro j hj j' hj' heq
            have h1 : j < M := Finset.mem_range.mp hj
            have h2 : j' < M := Finset.mem_range.mp hj'
            simp only [h1, h2, dite_true, Fin.mk.injEq] at heq
            omega
  have : (n : ℝ) * ℓ / 2 ≤ M := by
    have : (1 : ℝ) ≤ M := by exact_mod_cast hM1
    linarith
  exact this.trans (by exact_mod_cast hcard)

/-- The bandwidth `n^(-1/(2β+1))` balances the variance `1/(n h)` against the rate
`n^(-2β/(2β+1))`: `n · n^(-1/(2β+1)) · n^(-2β/(2β+1)) = 1`. -/
private theorem natCast_mul_rpow_mul_rpow_eq_one {n : ℕ} (hn : 0 < n) {β : ℝ} (hβ : 0 < β) :
    (n : ℝ) * (n : ℝ) ^ (-1 / (2 * β + 1)) * (n : ℝ) ^ (-2 * β / (2 * β + 1)) = 1 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hden : (2 * β + 1) ≠ 0 := by linarith
  have h3 : (n : ℝ) * (n : ℝ) ^ (-1 / (2 * β + 1)) * (n : ℝ) ^ (-2 * β / (2 * β + 1)) =
      (n : ℝ) ^ ((1 : ℝ) + -1 / (2 * β + 1) + -2 * β / (2 * β + 1)) := by
    rw [Real.rpow_add hnR, Real.rpow_add hnR, Real.rpow_one]
  rw [h3, show (1 : ℝ) + -1 / (2 * β + 1) + -2 * β / (2 * β + 1) = 0 by field_simp; ring,
    Real.rpow_zero]

/-- The squared bias `(h^β)²` of the bandwidth `h = c n^(-1/(2β+1))` is
`c^(2β) n^(-2β/(2β+1))`. -/
private theorem mul_rpow_rpow_sq_eq {n : ℕ} (hn : 0 < n) {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) :
    ((c * (n : ℝ) ^ (-1 / (2 * β + 1))) ^ β) ^ 2 =
      c ^ (2 * β) * (n : ℝ) ^ (-2 * β / (2 * β + 1)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hden : (2 * β + 1) ≠ 0 := by linarith
  rw [Real.mul_rpow hc.le (Real.rpow_nonneg hnR.le _), mul_pow, ← Real.rpow_mul hnR.le,
    ← Real.rpow_natCast, ← Real.rpow_natCast (_ ^ _), ← Real.rpow_mul hc.le,
    ← Real.rpow_mul hnR.le]
  congr 2
  · push_cast; ring
  · push_cast; field_simp

/-- GAPS 103.22: a box-kernel local-constant estimator attains the `L²` rate for `0<β≤1`. -/
theorem fixedDesignLocalConstant_risk_le (β L σ c : ℝ)
    (hβ : β ∈ Ioc (0 : ℝ) 1) (hL : 0 < L) (hσ : 0 < σ) (hc : 1 ≤ c) :
    ∃ C > (0 : ℝ), ∀ n : ℕ, 0 < n → ∀ f ∈ holderRegressionClass β L,
      fixedDesignRegressionRisk (n := n) f σ
        (fixedDesignLocalConstant (n := n) (c * Real.rpow (n : ℝ) (-1 / (2 * β + 1)))) ≤
        ENNReal.ofReal (C * Real.rpow (n : ℝ) (-2 * β / (2 * β + 1))) := by
  classical
  obtain ⟨hβ0, -⟩ := hβ
  have hc0 : 0 < c := by linarith
  refine ⟨L ^ 2 * c ^ (2 * β) + 2 * σ ^ 2 * (1 / c + 1) + 1, by positivity, ?_⟩
  intro n hn f hf
  obtain ⟨hfm, hfh⟩ := hf
  simp only [Real.rpow_eq_pow] at hfh ⊢
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set e := (n : ℝ) ^ (-1 / (2 * β + 1)) with he
  set r := (n : ℝ) ^ (-2 * β / (2 * β + 1)) with hr
  have he0 : 0 < e := Real.rpow_pos_of_pos hnR _
  have hr0 : 0 < r := Real.rpow_pos_of_pos hnR _
  set h := c * e with hh
  have hh0 : 0 < h := mul_pos hc0 he0
  have hden : (2 * β + 1) ≠ 0 := by linarith
  have hden' : 0 < 2 * β + 1 := by linarith
  have hner : (n : ℝ) * e * r = 1 := natCast_mul_rpow_mul_rpow_eq_one hn hβ0
  have hpow : (h ^ β) ^ 2 = c ^ (2 * β) * r := mul_rpow_rpow_sq_eq hn hβ0 hc0
  have hrn : 1 / (n : ℝ) ≤ r := by
    rw [hr, one_div, ← Real.rpow_neg_one]
    refine Real.rpow_le_rpow_of_exponent_le hn1 ?_
    rw [le_div_iff₀ hden']; linarith
  have hen : 1 / (n : ℝ) ≤ e := by
    rw [he, one_div, ← Real.rpow_neg_one]
    refine Real.rpow_le_rpow_of_exponent_le hn1 ?_
    rw [le_div_iff₀ hden']; linarith
  have hh1n : 1 / (n : ℝ) ≤ h := hen.trans (le_mul_of_one_le_left he0.le hc)
  set x : Fin n → ℝ := fun i ↦ ((i.val + 1 : ℕ) : ℝ) / n with hx
  have hx01 : ∀ i, x i ∈ Icc (0 : ℝ) 1 := by
    intro i
    refine ⟨by positivity, ?_⟩
    rw [hx, div_le_one hnR]
    exact_mod_cast i.isLt
  set Bd := L ^ 2 * c ^ (2 * β) + 2 * σ ^ 2 * (1 / c + 1) + 1 with hBd
  have hpt : ∀ t ∈ Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal ((fixedDesignLocalConstant h y t -
      f t) ^ 2) ∂fixedDesignRegressionLaw n f σ ≤ ENNReal.ofReal (Bd * r) := by
    intro t ht
    set w : Fin n → ℝ := fun i ↦ if |t - x i| ≤ h then 1 else 0 with hw
    set N := ∑ i, w i with hN
    have hNcard : N = ((Finset.univ : Finset (Fin n)).filter
        fun i ↦ |t - ((i.val + 1 : ℕ) : ℝ) / n| ≤ h).card := by
      rw [hN, Finset.card_filter, Nat.cast_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      simp only [hw, hx]
      split_ifs <;> simp
    have hNge : (n : ℝ) * min h 1 / 2 ≤ N :=
      hNcard ▸ card_fixedDesign_window_ge hn hh1n ht.1 ht.2
    have hmin0 : 0 < min h 1 := lt_min hh0 one_pos
    have hNpos : 0 < N := lt_of_lt_of_le (by positivity) hNge
    set a : Fin n → ℝ := fun i ↦ w i / N with ha
    have hest : ∀ y : Fin n → ℝ, fixedDesignLocalConstant h y t = ∑ i, a i * y i := by
      intro y
      simp only [fixedDesignLocalConstant, ha, hw, hN, hx]
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      ring
    obtain ⟨hZ, hmse⟩ := integral_sq_linear_gaussian (fun i ↦ f (x i)) (σ ^ 2).toNNReal a (f t)
    simp_rw [hest]
    rw [fixedDesignRegressionLaw, ← ofReal_integral_eq_lintegral_ofReal hZ.integrable_sq
      (Filter.Eventually.of_forall fun _ ↦ sq_nonneg _), hmse]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [Real.coe_toNNReal _ (sq_nonneg σ)]
    have hw01 : ∀ i, w i = 0 ∨ (w i = 1 ∧ |t - x i| ≤ h) := by
      intro i
      simp only [hw]
      split_ifs with h' <;> simp [h']
    have hw2 : ∀ i, w i ^ 2 = w i := by
      intro i; rcases hw01 i with h' | ⟨h', -⟩ <;> rw [h'] <;> norm_num
    have hsuma2 : ∑ i, a i ^ 2 = 1 / N := by
      simp only [ha, div_pow, hw2, ← Finset.sum_div, ← hN]
      field_simp
    have hsuma : ∑ i, a i = 1 := by
      simp only [ha, ← Finset.sum_div, ← hN]
      field_simp
    have ha0 : ∀ i, 0 ≤ a i := fun i ↦ by
      rcases hw01 i with h' | ⟨h', -⟩ <;> simp only [ha, h'] <;> positivity
    have hbias : |∑ i, a i * f (x i) - f t| ≤ L * h ^ β := by
      have e1 : ∑ i, a i * f (x i) - f t = ∑ i, a i * (f (x i) - f t) := by
        simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsuma, one_mul]
      rw [e1]
      calc |∑ i, a i * (f (x i) - f t)| ≤ ∑ i, |a i * (f (x i) - f t)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i, a i * (L * h ^ β) := by
            refine Finset.sum_le_sum fun i _ ↦ ?_
            rw [abs_mul, abs_of_nonneg (ha0 i)]
            rcases hw01 i with h' | ⟨-, hd⟩
            · simp [ha, h']
            · refine mul_le_mul_of_nonneg_left ?_ (ha0 i)
              refine (hfh (x i) (hx01 i) t ht).trans ?_
              refine mul_le_mul_of_nonneg_left ?_ hL.le
              rw [abs_sub_comm]
              exact Real.rpow_le_rpow (abs_nonneg _) hd hβ0.le
        _ = L * h ^ β := by rw [← Finset.sum_mul, hsuma, one_mul]
    have hb2 : (∑ i, a i * f (x i) - f t) ^ 2 ≤ L ^ 2 * c ^ (2 * β) * r := by
      rw [← sq_abs]
      calc |∑ i, a i * f (x i) - f t| ^ 2 ≤ (L * h ^ β) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) hbias 2
        _ = L ^ 2 * c ^ (2 * β) * r := by rw [mul_pow, hpow]; ring
    have hinvN : 1 / N ≤ 2 * (1 / c + 1) * r := by
      have h1 : 1 / N ≤ 2 / ((n : ℝ) * min h 1) := by
        rw [div_le_div_iff₀ hNpos (by positivity)]; linarith
      have h2 : 1 / min h 1 ≤ 1 / h + 1 := by
        rcases le_total h 1 with h' | h'
        · rw [min_eq_left h']; linarith [one_pos (α := ℝ)]
        · rw [min_eq_right h', div_one]; linarith [(one_div_pos.mpr hh0).le]
      have h3 : 1 / ((n : ℝ) * h) = r / c := by
        rw [hh]; field_simp; linarith [hner]
      calc 1 / N ≤ 2 / ((n : ℝ) * min h 1) := h1
        _ = 2 * (1 / n) * (1 / min h 1) := by field_simp
        _ ≤ 2 * (1 / n) * (1 / h + 1) := by gcongr
        _ = 2 * (1 / ((n : ℝ) * h) + 1 / n) := by field_simp
        _ ≤ 2 * (r / c + r) := by rw [h3]; gcongr
        _ = 2 * (1 / c + 1) * r := by ring
    rw [hsuma2]
    have hσ2 : σ ^ 2 * (1 / N) ≤ σ ^ 2 * (2 * (1 / c + 1) * r) :=
      mul_le_mul_of_nonneg_left hinvN (sq_nonneg σ)
    rw [hBd]
    nlinarith
  have hmeasT : Measurable (fun p : (Fin n → ℝ) × ℝ ↦ fixedDesignLocalConstant h p.1 p.2) := by
    unfold fixedDesignLocalConstant
    have hwm : ∀ i : Fin n, Measurable (fun p : (Fin n → ℝ) × ℝ ↦
        if |p.2 - ((i.val + 1 : ℕ) : ℝ) / n| ≤ h then (1 : ℝ) else 0) := fun i ↦
      Measurable.ite (measurableSet_le (continuous_abs.measurable.comp
        (measurable_snd.sub_const _)) measurable_const) measurable_const measurable_const
    exact (Finset.measurable_sum _ fun i _ ↦ (hwm i).mul
      ((measurable_pi_apply i).comp measurable_fst)).div (Finset.measurable_sum _ fun i _ ↦ hwm i)
  have : IsProbabilityMeasure (fixedDesignRegressionLaw n f σ) := by
    unfold fixedDesignRegressionLaw; infer_instance
  unfold fixedDesignRegressionRisk
  rw [lintegral_lintegral_swap
    (((hmeasT.sub (hfm.comp measurable_snd)).pow_const 2).ennreal_ofReal.aemeasurable)]
  calc ∫⁻ t in Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal ((fixedDesignLocalConstant h y t - f t) ^ 2)
        ∂fixedDesignRegressionLaw n f σ
      ≤ ∫⁻ _t in Icc (0 : ℝ) 1, ENNReal.ofReal (Bd * r) := setLIntegral_mono' measurableSet_Icc hpt
    _ = ENNReal.ofReal (Bd * r) := by
        rw [setLIntegral_const, Real.volume_Icc, sub_zero, ENNReal.ofReal_one, mul_one]

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
  have hpow : (h ^ β) ^ 2 = c ^ (2 * β) * r := mul_rpow_rpow_sq_eq hn hβ0 hc
  have hner : (n : ℝ) * e * r = 1 := natCast_mul_rpow_mul_rpow_eq_one hn hβ0
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

/-- GAPS 103.26: the matching pointwise minimax lower bound for Hölder orders at most one. -/
theorem holderDensityPointwiseMinimaxRisk_lower_bound (β L : ℝ)
    (hβ : β ∈ Ioc (0 : ℝ) 1) (hL : 0 < L) :
    ∃ c > (0 : ℝ), ∀ n : ℕ, 0 < n → ∀ x : ℝ,
      ENNReal.ofReal (c * Real.rpow (n : ℝ) (-2 * β / (2 * β + 1))) ≤
        holderDensityPointwiseMinimaxRisk n β L x := by
  sorry

/-- A Nadaraya–Watson predictor is nonnegative when observations and weights are nonnegative. -/
theorem nadarayaWatson_nonneg {d n : ℕ} (K : EuclideanSpace ℝ (Fin d) → ℝ)
    (hK : ∀ x, 0 ≤ K x) (h : ℝ) (x : Fin n → EuclideanSpace ℝ (Fin d))
    (y : Fin n → ℝ) (hy : ∀ i, 0 ≤ y i) (t : EuclideanSpace ℝ (Fin d)) :
    0 ≤ nadarayaWatson K h x y t := by
  exact div_nonneg (Finset.sum_nonneg fun i _ ↦ mul_nonneg (hK _) (hy i))
    (Finset.sum_nonneg fun i _ ↦ hK _)

/-- A nonempty normalized set of kernel weights reproduces a constant response. -/
theorem nadarayaWatson_const {d n : ℕ} (K : EuclideanSpace ℝ (Fin d) → ℝ)
    (h : ℝ) (x : Fin n → EuclideanSpace ℝ (Fin d)) (c : ℝ)
    (t : EuclideanSpace ℝ (Fin d))
    (hden : (∑ i, K (h⁻¹ • (x i - t))) ≠ 0) :
    nadarayaWatson K h x (fun _ ↦ c) t = c := by
  unfold nadarayaWatson
  rw [← Finset.sum_mul, mul_div_cancel_left₀ _ hden]

end CKSD
