module

public import CKSD.Nonparametric.SmoothingRates
public import CKSD.Nonparametric.LowerBounds.Testing
public import CKSD.Nonparametric.LowerBounds.Gaussian

/-!
# The fixed-design Hölder regression minimax rate

For Hölder orders `0 < β ≤ 1`, the minimax mean integrated squared error of fixed-design
Gaussian regression over the Hölder class `CKSD.holderRegressionClass β L` is of exact order
`n^(-2β/(2β+1))`.

The upper bound is attained by the box-kernel local average `CKSD.fixedDesignLocalConstant`
with bandwidth `n^(-1/(2β+1))` (`CKSD.fixedDesignLocalConstant_risk_le`). The lower bound is
Assouad's lemma (`CKSD.mul_one_sub_div_two_le_sSup_integral_hammingDist`) applied to the
hypercube of alternatives `t ↦ L dist(t, S_w)^β`, sums of Hölder tents over a subfamily of the
`m ≍ n^(1/(2β+1))` cells `(j/m, (j + 1)/m)`. Neighbouring alternatives are compared by the
Gaussian total variation bound `CKSD.totalVariationDistance_pi_gaussianReal_le`, and estimates
are reduced to sign patterns by a cellwise minimum-distance decoder.

## Main results

* `CKSD.measurable_uncurry_fixedDesignLocalConstant`: the local average is an admissible
  (jointly measurable) estimator.
* `CKSD.holderRegressionMinimaxRisk_le`, `CKSD.holderRegressionMinimaxRisk_ge`: the upper and
  lower bounds.
* `CKSD.holderRegressionMinimaxRisk_bounds`: both bounds together.

Sources: GAPS 103.22.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- The box-kernel local average `(y, t) ↦ fixedDesignLocalConstant h y t` is jointly measurable
in the observations and the evaluation point, so it is an admissible estimator in
`CKSD.holderRegressionMinimaxRisk`. -/
theorem measurable_uncurry_fixedDesignLocalConstant (n : ℕ) (h : ℝ) :
    Measurable (Function.uncurry (fixedDesignLocalConstant (n := n) h)) := by
  have hw : ∀ i : Fin n, Measurable fun p : (Fin n → ℝ) × ℝ ↦
      if |p.2 - ((i.val + 1 : ℕ) : ℝ) / n| ≤ h then (1 : ℝ) else 0 := fun i ↦
    Measurable.ite (measurableSet_le (by fun_prop) measurable_const) measurable_const
      measurable_const
  have e : Function.uncurry (fixedDesignLocalConstant (n := n) h) = fun p : (Fin n → ℝ) × ℝ ↦
    (∑ i : Fin n, (if |p.2 - ((i.val + 1 : ℕ) : ℝ) / n| ≤ h then (1 : ℝ) else 0) * p.1 i) /
      ∑ i : Fin n, (if |p.2 - ((i.val + 1 : ℕ) : ℝ) / n| ≤ h then (1 : ℝ) else 0) := by
    funext p; simp only [Function.uncurry_def, fixedDesignLocalConstant]
  rw [e]
  exact (Finset.measurable_sum _ fun i _ ↦ (hw i).mul (by fun_prop)).div
    (Finset.measurable_sum _ fun i _ ↦ hw i)

/-- Upper half of GAPS 103.22: for `0 < β ≤ 1`, the fixed-design Hölder minimax mean integrated
squared risk is at most `C n^(-2β/(2β+1))`, attained by the box-kernel local average with
bandwidth `n^(-1/(2β+1))` (`CKSD.fixedDesignLocalConstant_risk_le`). -/
theorem holderRegressionMinimaxRisk_le (β L σ : ℝ)
    (hβ : β ∈ Ioc (0 : ℝ) 1) (hL : 0 < L) (hσ : 0 < σ) :
    ∃ C > (0 : ℝ), ∀ n : ℕ, 0 < n →
      holderRegressionMinimaxRisk n β L σ ≤
        ENNReal.ofReal (C * Real.rpow (n : ℝ) (-2 * β / (2 * β + 1))) := by
  obtain ⟨C, hC, hrisk⟩ := fixedDesignLocalConstant_risk_le β L σ 1 hβ hL hσ le_rfl
  refine ⟨C, hC, fun n hn ↦ ?_⟩
  unfold holderRegressionMinimaxRisk
  refine iInf_le_of_le ⟨_, measurable_uncurry_fixedDesignLocalConstant n
    (1 * Real.rpow (n : ℝ) (-1 / (2 * β + 1)))⟩ ?_
  exact iSup_le fun f ↦ hrisk n hn f.val f.property

/-- For a sign pattern `w ∈ {0,1}^m`, the complement in `ℝ` of the open cells
`((j / m), (j + 1) / m)` with `w j = true`; it contains every grid point `k / m`. -/
private def bumpSet (m : ℕ) (w : Fin m → Bool) : Set ℝ :=
  {t | ∀ j : Fin m, w j = true → t ∉ Ioo ((j : ℝ) / m) ((j + 1 : ℝ) / m)}

/-- The hypercube alternative `t ↦ L dist(t, bumpSet m w)^β`: a sum of Hölder tents of height
`L (2m)^(-β)` on the cells `j` with `w j = true`, vanishing elsewhere. -/
private def bumpFun (β L : ℝ) (m : ℕ) (w : Fin m → Bool) (t : ℝ) : ℝ :=
  L * Metric.infDist t (bumpSet m w) ^ β

/-- The Hölder tent `t ↦ L min(t - j/m, (j + 1)/m - t)^β` on the cell `(j/m, (j + 1)/m)`. -/
private def tentFun (β L : ℝ) (m j : ℕ) (t : ℝ) : ℝ :=
  L * min (t - j / m) ((j + 1) / m - t) ^ β

/-- Every grid point `k / m` lies in `bumpSet m w`, since no open cell contains it. -/
private theorem natCast_div_mem_bumpSet {m : ℕ} (hm : 0 < m) (w : Fin m → Bool) (k : ℕ) :
    (k : ℝ) / m ∈ bumpSet m w := by
  intro j _ ⟨h1, h2⟩
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  rw [div_lt_div_iff_of_pos_right hmR] at h1 h2
  have h1' : (j : ℕ) < k := by exact_mod_cast h1
  have h2' : k < (j : ℕ) + 1 := by exact_mod_cast h2
  omega

/-- The open cells `(j/m, (j + 1)/m)` are pairwise disjoint: a point in two of them determines
the cell index. -/
private theorem eq_of_mem_Ioo_of_mem_Ioo {m j k : ℕ} {t : ℝ}
    (hj : t ∈ Ioo ((j : ℝ) / m) ((j + 1 : ℝ) / m)) (hk : t ∈ Ioo ((k : ℝ) / m) ((k + 1 : ℝ) / m)) :
    j = k := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp at hj
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have a1 : (j : ℝ) < k + 1 := by
    have := hj.1.trans hk.2; rwa [div_lt_div_iff_of_pos_right hmR] at this
  have a2 : (k : ℝ) < j + 1 := by
    have := hk.1.trans hj.2; rwa [div_lt_div_iff_of_pos_right hmR] at this
  have b1 : j < k + 1 := by exact_mod_cast a1
  have b2 : k < j + 1 := by exact_mod_cast a2
  omega

/-- Hölder continuity of `x ↦ x^β` on `[0, ∞)` for `0 ≤ β ≤ 1`:
`|a^β - b^β| ≤ |a - b|^β`, from the subadditivity of `x ↦ x^β`. -/
private theorem abs_rpow_sub_rpow_le {a b β : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hβ : 0 ≤ β)
    (hβ1 : β ≤ 1) :
    |a ^ β - b ^ β| ≤ |a - b| ^ β := by
  wlog hab : b ≤ a generalizing a b
  · rw [abs_sub_comm, abs_sub_comm a b]; exact this hb ha (le_of_not_ge hab)
  have h := Real.rpow_add_le_add_rpow (sub_nonneg.mpr hab) hb hβ hβ1
  rw [sub_add_cancel] at h
  rw [abs_of_nonneg (sub_nonneg.mpr hab), abs_of_nonneg (sub_nonneg.mpr
    (Real.rpow_le_rpow hb hab hβ))]
  linarith

/-- Each hypercube alternative lies in the Hölder class: `x ↦ dist(x, S)` is `1`-Lipschitz and
`x ↦ x^β` is `β`-Hölder with constant one, so `L dist(·, S)^β` satisfies the `(β, L)` bound. -/
private theorem bumpFun_mem_holderRegressionClass {β L : ℝ} (hβ : β ∈ Ioc (0 : ℝ) 1) (hL : 0 ≤ L)
    {m : ℕ} (hm : 0 < m) (w : Fin m → Bool) : bumpFun β L m w ∈ holderRegressionClass β L := by
  have hne : (bumpSet m w).Nonempty := ⟨_, natCast_div_mem_bumpSet hm w 0⟩
  refine ⟨?_, fun x _ y _ ↦ ?_⟩
  · unfold bumpFun
    exact (measurable_const.mul ((Metric.continuous_infDist_pt _).rpow_const
      fun _ ↦ Or.inr hβ.1.le).measurable)
  · unfold bumpFun
    rw [← mul_sub, abs_mul, abs_of_nonneg hL]
    refine mul_le_mul_of_nonneg_left ?_ hL
    refine (abs_rpow_sub_rpow_le Metric.infDist_nonneg Metric.infDist_nonneg hβ.1.le hβ.2).trans ?_
    rw [Real.rpow_eq_pow]
    apply Real.rpow_le_rpow (abs_nonneg _) _ hβ.1.le
    have h1 := Metric.infDist_le_infDist_add_dist (x := x) (y := y) (s := bumpSet m w)
    have h2 := Metric.infDist_le_infDist_add_dist (x := y) (y := x) (s := bumpSet m w)
    rw [Real.dist_eq] at h1 h2
    rw [abs_sub_comm y x] at h2
    exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩

/-- On the cell `(j/m, (j + 1)/m)`, the alternative equals the tent when `w j = true` and
vanishes otherwise. -/
private theorem bumpFun_of_mem_Ioo {β L : ℝ} (hβ : 0 < β) {m : ℕ} (w : Fin m → Bool) {j : Fin m}
    {t : ℝ}
    (ht : t ∈ Ioo ((j : ℝ) / m) ((j + 1 : ℝ) / m)) :
    bumpFun β L m w t = if w j then tentFun β L m j t else 0 := by
  have hm : 0 < m := j.pos
  unfold bumpFun
  split_ifs with hw
  · unfold tentFun
    congr 2
    have hne : (bumpSet m w).Nonempty := ⟨_, natCast_div_mem_bumpSet hm w 0⟩
    have hl : ((j : ℕ) : ℝ) / m ∈ bumpSet m w := natCast_div_mem_bumpSet hm w j
    have hr : (((j : ℕ) + 1 : ℕ) : ℝ) / m ∈ bumpSet m w := natCast_div_mem_bumpSet hm w (j + 1)
    push_cast at hr
    refine le_antisymm (le_min ?_ ?_) ((Metric.le_infDist hne).mpr fun y hy ↦ ?_)
    · refine (Metric.infDist_le_dist_of_mem hl).trans_eq ?_
      rw [Real.dist_eq, abs_of_pos (by linarith [ht.1])]
    · refine (Metric.infDist_le_dist_of_mem hr).trans_eq ?_
      rw [Real.dist_eq, abs_of_neg (by linarith [ht.2])]; ring
    · have hy' := hy j hw
      simp only [mem_Ioo, not_and_or, not_lt] at hy'
      rw [Real.dist_eq]
      rcases hy' with h | h
      · exact (min_le_left _ _).trans (by rw [abs_of_pos (by linarith [ht.1])]; linarith)
      · exact (min_le_right _ _).trans (by
          rw [abs_of_neg (by linarith [ht.2])]; linarith)
  · have hmem : t ∈ bumpSet m w := by
      intro k hk htk
      have := eq_of_mem_Ioo_of_mem_Ioo ht htk
      rw [Fin.ext this] at hw
      exact hw hk
    rw [Metric.infDist_zero_of_mem hmem, Real.zero_rpow hβ.ne', mul_zero]

/-- Every point of `[0, 1]` is either a grid point `k / m` or lies in one of the open cells
`(j/m, (j + 1)/m)` with `j < m`. -/
private theorem grid_or_mem_Ioo {m : ℕ} (hm : 0 < m) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (∃ k : ℕ, t = k / m) ∨ ∃ j : Fin m, t ∈ Ioo ((j : ℝ) / m) ((j + 1 : ℝ) / m) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  set k := ⌊t * m⌋₊ with hk
  have hfl := Nat.floor_le (mul_nonneg ht.1 hmR.le)
  have hlt := Nat.lt_floor_add_one (t * m)
  rcases hfl.lt_or_eq with h | h
  · have hkm : k < m := by
      have : (k : ℝ) < m := by nlinarith [ht.2]
      exact_mod_cast this
    right
    refine ⟨⟨k, hkm⟩, ?_, ?_⟩
    · rw [div_lt_iff₀ hmR]; exact h
    · rw [lt_div_iff₀ hmR]; exact hlt
  · left
    exact ⟨k, by rw [h]; field_simp⟩

/-- The hypercube alternatives vanish at every grid point `k / m`. -/
private theorem bumpFun_natCast_div {β L : ℝ} (hβ : 0 < β) {m : ℕ} (hm : 0 < m) (w : Fin m → Bool)
    (k : ℕ) : bumpFun β L m w (k / m) = 0 := by
  rw [bumpFun, Metric.infDist_zero_of_mem (natCast_div_mem_bumpSet hm w k),
    Real.zero_rpow hβ.ne', mul_zero]

/-- On its cell the tent takes values in `[0, L (1/m)^β]`. -/
private theorem tentFun_nonneg_le {β L : ℝ} (hβ : 0 < β) (hL : 0 ≤ L) {m : ℕ} (hm : 0 < m) {j : ℕ}
    {t : ℝ} (ht : t ∈ Ioo ((j : ℝ) / m) ((j + 1 : ℝ) / m)) :
    0 ≤ tentFun β L m j t ∧ tentFun β L m j t ≤ L * (1 / (m : ℝ)) ^ β := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have h0 : 0 ≤ min (t - j / m) ((j + 1) / m - t) :=
    le_min (by linarith [ht.1]) (by linarith [ht.2])
  have h1 : min (t - j / m) ((j + 1) / m - t) ≤ 1 / m := by
    refine (min_le_left _ _).trans ?_
    have : t < (j + 1 : ℝ) / m := ht.2
    rw [add_div] at this; linarith
  unfold tentFun
  exact ⟨mul_nonneg hL (Real.rpow_nonneg h0 _),
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow h0 h1 hβ.le) hL⟩

/-- Lower bound for the squared `L²` mass of a tent: on the middle half of its cell the tent is
at least `L (1/(4m))^β`, so `∫ tent² ≥ L² (1/(4m))^(2β) / (2m)`. -/
private theorem ofReal_le_lintegral_tentFun_sq {β L : ℝ} (hβ : 0 < β) (hL : 0 ≤ L) {m : ℕ}
    (hm : 0 < m) (j : ℕ) :
    ENNReal.ofReal (L ^ 2 * ((1 / (4 * m : ℝ)) ^ β) ^ 2 * (1 / (2 * m))) ≤
      ∫⁻ t in Ioo ((j : ℝ) / m) ((j + 1 : ℝ) / m), ENNReal.ofReal (tentFun β L m j t ^ 2) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  set a : ℝ := j / m
  have hsub : Icc (a + 1 / (4 * m)) (a + 3 / (4 * m)) ⊆ Ioo ((j : ℝ) / m) ((j + 1 : ℝ) / m) := by
    intro t ht
    have e : (j + 1 : ℝ) / m = a + 1 / m := by simp only [a]; ring
    rw [e]
    have : 0 < 1 / (4 * (m : ℝ)) := by positivity
    have : 3 / (4 * (m : ℝ)) < 1 / m := by
      rw [div_lt_div_iff₀ (by positivity) hmR]; linarith
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  refine le_trans ?_ (lintegral_mono_set hsub)
  have hpt : ∀ t ∈ Icc (a + 1 / (4 * m)) (a + 3 / (4 * m)),
      ENNReal.ofReal (L ^ 2 * ((1 / (4 * m : ℝ)) ^ β) ^ 2) ≤
        ENNReal.ofReal (tentFun β L m j t ^ 2) := by
    intro t ht
    apply ENNReal.ofReal_le_ofReal
    have hmin : 1 / (4 * m : ℝ) ≤ min (t - j / m) ((j + 1) / m - t) := by
      have e : (j + 1 : ℝ) / m = a + 1 / m := by simp only [a]; ring
      rw [e]
      have : 3 / (4 * (m : ℝ)) = 1 / m - 1 / (4 * m) := by field_simp; ring
      exact le_min (by linarith [ht.1]) (by linarith [ht.2])
    have h1 : L * (1 / (4 * m : ℝ)) ^ β ≤ tentFun β L m j t :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hmin hβ.le) hL
    have h0 : 0 ≤ L * (1 / (4 * m : ℝ)) ^ β := by positivity
    nlinarith
  refine le_trans ?_ (setLIntegral_mono' measurableSet_Icc hpt)
  rw [setLIntegral_const, Real.volume_Icc, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  apply le_of_eq
  congr 1
  field_simp
  ring

/-- The open cell `(j/m, (j + 1)/m)` of the partition of `[0, 1]` into `m` intervals. -/
private def bumpIoo (m : ℕ) (j : ℕ) : Set ℝ := Ioo ((j : ℝ) / m) ((j + 1 : ℝ) / m)

/-- The minimum-distance decoder: from a regression estimate `g`, guess `w j = true` exactly when
`g` is closer in `L²` on cell `j` to the tent than to zero. -/
private def regDecode (β L : ℝ) (m : ℕ) (g : ℝ → ℝ) (j : Fin m) : Bool :=
  decide ((∫⁻ t in bumpIoo m j, ENNReal.ofReal ((g t - tentFun β L m j t) ^ 2)) <
    ∫⁻ t in bumpIoo m j, ENNReal.ofReal (g t ^ 2))

/-- The per-cell loss `L² (1/(4m))^(2β) / (8m)`, a quarter of the tent mass lower bound. -/
private def bumpLoss (β L : ℝ) (m : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (L ^ 2 * ((1 / (4 * m : ℝ)) ^ β) ^ 2 * (1 / (2 * m))) / 4

/-- If the decoder errs on cell `j`, the squared `L²` error of `g` on that cell against the
alternative `bumpFun w` is at least `bumpLoss`; this is the triangle inequality
`∫ tent² ≤ 2 ∫ (g - tent)² + 2 ∫ g²` applied to the closer of the two candidates. -/
private theorem bumpLoss_le_of_regDecode_ne {β L : ℝ} (hβ : 0 < β) (hL : 0 ≤ L) {m : ℕ}
    {g : ℝ → ℝ} (hg : Measurable g) (w : Fin m → Bool) (j : Fin m)
    (hne : regDecode β L m g j ≠ w j) :
    bumpLoss β L m ≤ ∫⁻ t in bumpIoo m j, ENNReal.ofReal ((g t - bumpFun β L m w t) ^ 2) := by
  have hm : 0 < m := j.pos
  set A := ∫⁻ t in bumpIoo m j, ENNReal.ofReal ((g t - tentFun β L m j t) ^ 2)
  set Z := ∫⁻ t in bumpIoo m j, ENNReal.ofReal (g t ^ 2)
  have hB : ENNReal.ofReal (L ^ 2 * ((1 / (4 * m : ℝ)) ^ β) ^ 2 * (1 / (2 * m))) ≤
      2 * A + 2 * Z := by
    refine (ofReal_le_lintegral_tentFun_sq hβ hL hm j).trans ?_
    calc ∫⁻ t in bumpIoo m j, ENNReal.ofReal (tentFun β L m j t ^ 2)
        ≤ ∫⁻ t in bumpIoo m j, (2 * ENNReal.ofReal ((g t - tentFun β L m j t) ^ 2) +
            2 * ENNReal.ofReal (g t ^ 2)) := by
          refine lintegral_mono fun t ↦ ?_
          rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num),
            ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity)
            (by positivity)]
          apply ENNReal.ofReal_le_ofReal
          norm_num
          nlinarith [sq_nonneg (g t - tentFun β L m j t + g t)]
      _ = 2 * A + 2 * Z := by
          have htent : Measurable (tentFun β L m j) := by
            unfold tentFun
            exact measurable_const.mul ((Continuous.rpow_const (by fun_prop)
              fun _ ↦ Or.inr hβ.le).measurable)
          rw [lintegral_add_left (by fun_prop), lintegral_const_mul _ (by fun_prop),
            lintegral_const_mul _ (by fun_prop)]
  have hcongr : ∫⁻ t in bumpIoo m j, ENNReal.ofReal ((g t - bumpFun β L m w t) ^ 2) =
      if w j then A else Z := by
    split_ifs with hw
    · exact setLIntegral_congr_fun measurableSet_Ioo fun t ht ↦ by
        simp only [bumpFun_of_mem_Ioo hβ w ht, hw, ↓reduceIte]
    · exact setLIntegral_congr_fun measurableSet_Ioo fun t ht ↦ by
        simp only [bumpFun_of_mem_Ioo hβ w ht, hw, ↓reduceIte, sub_zero, Bool.false_eq_true]
  rw [hcongr, bumpLoss]
  apply ENNReal.div_le_of_le_mul
  by_cases hAZ : A < Z
  · have hd : regDecode β L m g j = true := decide_eq_true hAZ
    rw [hd] at hne
    have hw : w j = false := by simpa using hne.symm
    simp only [hw, Bool.false_eq_true, ↓reduceIte]
    calc _ ≤ 2 * A + 2 * Z := hB
      _ ≤ 2 * Z + 2 * Z := by gcongr
      _ = Z * 4 := by ring
  · have hd : regDecode β L m g j = false := decide_eq_false hAZ
    rw [hd] at hne
    have hw : w j = true := by simpa using hne.symm
    simp only [hw, ↓reduceIte]
    push Not at hAZ
    calc _ ≤ 2 * A + 2 * Z := hB
      _ ≤ 2 * A + 2 * A := by gcongr
      _ = A * 4 := by ring

/-- Reduction of estimation to Hamming loss: the `L²[0, 1]` error of `g` against `bumpFun w`
is at least `bumpLoss` times the Hamming distance between the decoded pattern and `w`. -/
private theorem hammingDist_regDecode_mul_le {β L : ℝ} (hβ : 0 < β) (hL : 0 ≤ L) {m : ℕ}
    {g : ℝ → ℝ} (hg : Measurable g) (w : Fin m → Bool) :
    (hammingDist (regDecode β L m g) w : ℝ≥0∞) * bumpLoss β L m ≤
      ∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal ((g t - bumpFun β L m w t) ^ 2) := by
  have hdisj : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint
      fun j ↦ bumpIoo m j := by
    intro j _ k _ hjk
    rw [Function.onFun, Set.disjoint_left]
    intro t htj htk
    exact hjk (Fin.ext (eq_of_mem_Ioo_of_mem_Ioo htj htk))
  have hsub : (⋃ j ∈ (Finset.univ : Finset (Fin m)), bumpIoo m j) ⊆ Icc (0 : ℝ) 1 := by
    intro t ht
    simp only [Finset.mem_univ, iUnion_true, mem_iUnion] at ht
    obtain ⟨j, hj⟩ := ht
    have hmR : (0 : ℝ) < m := by exact_mod_cast j.pos
    have hj1 : ((j : ℕ) + 1 : ℝ) ≤ m := by exact_mod_cast j.isLt
    refine ⟨le_trans (by positivity) hj.1.le, hj.2.le.trans ?_⟩
    rw [div_le_one hmR]; exact hj1
  have hham : (hammingDist (regDecode β L m g) w : ℝ≥0∞) * bumpLoss β L m =
      ∑ j, (if regDecode β L m g j ≠ w j then bumpLoss β L m else 0) := by
    rw [hammingDist, Finset.card_filter, Nat.cast_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    split_ifs <;> simp
  rw [hham]
  calc ∑ j, (if regDecode β L m g j ≠ w j then bumpLoss β L m else 0)
      ≤ ∑ j : Fin m, ∫⁻ t in bumpIoo m j, ENNReal.ofReal ((g t - bumpFun β L m w t) ^ 2) := by
        refine Finset.sum_le_sum fun j _ ↦ ?_
        split_ifs with h
        · exact bumpLoss_le_of_regDecode_ne hβ hL hg w j h
        · exact zero_le
    _ = ∫⁻ t in ⋃ j ∈ (Finset.univ : Finset (Fin m)), bumpIoo m j,
          ENNReal.ofReal ((g t - bumpFun β L m w t) ^ 2) :=
        (lintegral_biUnion_finset hdisj (fun _ _ ↦ measurableSet_Ioo) _).symm
    _ ≤ _ := lintegral_mono_set hsub

/-- For a jointly measurable estimator `T`, the decoded pattern `y ↦ regDecode (T y)` is a
measurable function of the observations. -/
private theorem measurable_regDecode_comp {β L : ℝ} (hβ : 0 < β) {m n : ℕ}
    {T : (Fin n → ℝ) → ℝ → ℝ} (hT : Measurable (Function.uncurry T)) :
    Measurable fun y ↦ regDecode β L m (T y) := by
  have htent : ∀ j : ℕ, Measurable (tentFun β L m j) := fun j ↦ by
    unfold tentFun
    exact measurable_const.mul ((Continuous.rpow_const (by fun_prop)
      fun _ ↦ Or.inr hβ.le).measurable)
  rw [measurable_pi_iff]
  intro j
  apply measurable_to_bool
  show MeasurableSet {y | regDecode β L m (T y) j = true}
  simp only [regDecode, decide_eq_true_eq]
  refine measurableSet_lt ?_ ?_
  · refine Measurable.lintegral_prod_right' (f := fun p : (Fin n → ℝ) × ℝ ↦
      ENNReal.ofReal ((T p.1 p.2 - tentFun β L m j p.2) ^ 2)) ?_
    exact ENNReal.measurable_ofReal.comp ((hT.sub ((htent j).comp measurable_snd)).pow_const 2)
  · refine Measurable.lintegral_prod_right' (f := fun p : (Fin n → ℝ) × ℝ ↦
      ENNReal.ofReal ((T p.1 p.2) ^ 2)) ?_
    exact ENNReal.measurable_ofReal.comp (hT.pow_const 2)

/-- At most `n/m + 1` design points `(i + 1)/n` fall in a cell `(j/m, (j + 1)/m)`. -/
private theorem card_design_mem_bumpIoo_le {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (j : ℕ) :
    ((Finset.univ.filter fun i : Fin n ↦ ((i.val + 1 : ℕ) : ℝ) / n ∈ bumpIoo m j).card : ℝ) ≤
      n / m + 1 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  set k₀ := ⌊(n : ℝ) * (j / m)⌋₊
  set N := ⌈(n : ℝ) / m⌉₊
  have hsub : (Finset.univ.filter fun i : Fin n ↦ ((i.val + 1 : ℕ) : ℝ) / n ∈ bumpIoo m j).map
      Fin.valEmbedding ⊆ Finset.Ico k₀ (k₀ + N) := by
    intro k hk
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply] at hk
    obtain ⟨i, hi, rfl⟩ := hk
    simp only [bumpIoo, mem_Ioo] at hi
    rw [lt_div_iff₀ hnR, div_lt_iff₀ hnR] at hi
    have hfl := Nat.floor_le (show 0 ≤ (n : ℝ) * (j / m) by positivity)
    have hfl2 := Nat.lt_floor_add_one ((n : ℝ) * (j / m))
    have hce := Nat.le_ceil ((n : ℝ) / m)
    have e1 : (j : ℝ) / m * n = n * (j / m) := by ring
    have e2 : (j + 1 : ℝ) / m * n = n * (j / m) + n / m := by ring
    have h1 : (k₀ : ℝ) < (i.val + 1 : ℕ) := by push_cast at hi ⊢; linarith
    have h2 : ((i.val + 1 : ℕ) : ℝ) < k₀ + 1 + N := by push_cast at hi ⊢; linarith
    have h1' : k₀ < i.val + 1 := by exact_mod_cast h1
    have h2' : i.val + 1 < k₀ + 1 + N := by exact_mod_cast h2
    simp only [Finset.mem_Ico]
    omega
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_map, Nat.card_Ico, Nat.add_sub_cancel_left] at hcard
  calc ((Finset.univ.filter fun i : Fin n ↦ ((i.val + 1 : ℕ) : ℝ) / n ∈ bumpIoo m j).card : ℝ)
      ≤ N := by exact_mod_cast hcard
    _ ≤ n / m + 1 := (Nat.ceil_lt_add_one (by positivity)).le

/-- For neighbouring patterns `w, w'` (Hamming distance one), the squared Euclidean distance
between the regression means on the design is at most `(n/m + 1) (L (1/m)^β)²`: they differ on
the design points in one cell only, by at most the tent height. -/
private theorem sum_sq_bumpFun_sub_le {β L : ℝ} (hβ : 0 < β) (hL : 0 ≤ L) {n m : ℕ} (hn : 0 < n)
    (hm : 0 < m) (w w' : Fin m → Bool) (hww : hammingDist w w' = 1) :
    ∑ i : Fin n, (bumpFun β L m w' (((i.val + 1 : ℕ) : ℝ) / n) -
      bumpFun β L m w (((i.val + 1 : ℕ) : ℝ) / n)) ^ 2 ≤
      (n / m + 1) * (L * (1 / (m : ℝ)) ^ β) ^ 2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨j₀, hj₀⟩ := Finset.card_eq_one.mp hww
  have hdiff : ∀ j, j ≠ j₀ → w j = w' j := by
    intro j hj
    by_contra h
    have : j ∈ (Finset.univ.filter fun i ↦ w i ≠ w' i) := by simp [h]
    rw [show (Finset.univ.filter fun i ↦ w i ≠ w' i) = {j₀} from hj₀] at this
    exact hj (Finset.mem_singleton.mp this)
  set B := (L * (1 / (m : ℝ)) ^ β) ^ 2
  have hpt : ∀ i : Fin n, (bumpFun β L m w' (((i.val + 1 : ℕ) : ℝ) / n) -
      bumpFun β L m w (((i.val + 1 : ℕ) : ℝ) / n)) ^ 2 ≤
      if ((i.val + 1 : ℕ) : ℝ) / n ∈ bumpIoo m j₀ then B else 0 := by
    intro i
    set x : ℝ := ((i.val + 1 : ℕ) : ℝ) / n
    have hx : x ∈ Icc (0 : ℝ) 1 := by
      refine ⟨by positivity, ?_⟩
      rw [div_le_one hnR]; exact_mod_cast i.isLt
    rcases grid_or_mem_Ioo hm hx with ⟨k, hk⟩ | ⟨j, hj⟩
    · rw [hk, bumpFun_natCast_div hβ hm, bumpFun_natCast_div hβ hm]
      split_ifs <;> simp [B]; positivity
    · rw [bumpFun_of_mem_Ioo hβ w hj, bumpFun_of_mem_Ioo hβ w' hj]
      by_cases hjj : j = j₀
      · subst hjj
        have hmem : x ∈ bumpIoo m j := hj
        simp only [hmem, ↓reduceIte]
        obtain ⟨h0, h1⟩ := tentFun_nonneg_le hβ hL hm hj
        have hB0 : 0 ≤ L * (1 / (m : ℝ)) ^ β := h0.trans h1
        split_ifs <;> simp only [sub_self, sub_zero, zero_sub, neg_sq] <;>
          first | exact pow_le_pow_left₀ h0 h1 2 | (rw [zero_pow two_ne_zero]; exact sq_nonneg _)
      · rw [hdiff j hjj, sub_self]
        have : x ∉ bumpIoo m j₀ := fun h ↦ hjj (Fin.ext (eq_of_mem_Ioo_of_mem_Ioo hj h))
        simp [this]
  refine (Finset.sum_le_sum fun i _ ↦ hpt i).trans ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (card_design_mem_bumpIoo_le hn hm j₀) (sq_nonneg _)

/-- Assouad's bound for the Hölder hypercube: if `(n/m + 1) (L (1/m)^β)² ≤ σ²`, neighbouring
Gaussian laws are at total variation at most `1/2`, and every jointly measurable estimator has
worst-case risk over the Hölder class at least `(m/4) bumpLoss`. -/
private theorem bumpLoss_mul_le_iSup_risk {β L σ : ℝ} (hβ : β ∈ Ioc (0 : ℝ) 1) (hL : 0 ≤ L)
    (hσ : 0 < σ) {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (hTV : (n / m + 1) * (L * (1 / (m : ℝ)) ^ β) ^ 2 ≤ σ ^ 2)
    (T : (Fin n → ℝ) → ℝ → ℝ) (hT : Measurable (Function.uncurry T)) :
    ENNReal.ofReal (m / 4) * bumpLoss β L m ≤
      ⨆ f : holderRegressionClass β L, fixedDesignRegressionRisk f.val σ T := by
  set v : ℝ≥0 := Real.toNNReal (σ ^ 2)
  have hv : (v : ℝ) = σ ^ 2 := Real.coe_toNNReal _ (sq_nonneg σ)
  have hv0 : v ≠ 0 := by
    intro h; rw [h] at hv; simp at hv; exact hσ.ne' (by simpa using hv.symm)
  set P : (Fin m → Bool) → Measure (Fin n → ℝ) :=
    fun w ↦ fixedDesignRegressionLaw n (bumpFun β L m w) σ
  have hP : ∀ w, P w = Measure.pi fun i : Fin n ↦
      gaussianReal (bumpFun β L m w (((i.val + 1 : ℕ) : ℝ) / n)) v := fun w ↦ rfl
  have hprob : ∀ w, IsProbabilityMeasure (P w) := fun w ↦ by rw [hP]; infer_instance
  have hnear : ∀ w w', hammingDist w w' = 1 → totalVariationDistance (P w) (P w') ≤ 1 / 2 := by
    intro w w' hww
    rw [hP, hP]
    refine (totalVariationDistance_pi_gaussianReal_le _ _ hv0).trans ?_
    rw [show (1 / 2 : ℝ) = Real.sqrt (1 / 4) by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_le_sqrt
    have := (sum_sq_bumpFun_sub_le hβ.1 hL hn hm w w' hww).trans hTV
    rw [hv, div_le_iff₀ (by positivity)]
    linarith
  set D : (Fin n → ℝ) → (Fin m → Bool) := fun y ↦ regDecode β L m (T y)
  have hD : Measurable D := measurable_regDecode_comp hβ.1 hT
  have hA := mul_one_sub_div_two_le_sSup_integral_hammingDist m P (1 / 2) hnear D hD
  obtain ⟨w₀, hw₀⟩ := (Set.range_nonempty fun w ↦ ∫ x, (hammingDist (D x) w : ℝ) ∂P w).csSup_mem
    (Set.finite_range _)
  rw [← hw₀] at hA
  have hHm : Measurable fun y ↦ (hammingDist (D y) w₀ : ℝ) :=
    (measurable_of_countable (fun v ↦ (hammingDist v w₀ : ℝ))).comp hD
  have hint : Integrable (fun y ↦ (hammingDist (D y) w₀ : ℝ)) (P w₀) := by
    refine Integrable.of_bound (C := m) hHm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact_mod_cast hammingDist_le_card_fintype.trans (by simp)
  refine le_trans ?_ (le_iSup (fun f : holderRegressionClass β L ↦
    fixedDesignRegressionRisk f.val σ T) ⟨_, bumpFun_mem_holderRegressionClass hβ hL hm w₀⟩)
  calc ENNReal.ofReal (m / 4) * bumpLoss β L m
      ≤ ENNReal.ofReal (∫ y, (hammingDist (D y) w₀ : ℝ) ∂P w₀) * bumpLoss β L m := by
        gcongr
        have : (m : ℝ) * (1 - 1 / 2) / 2 = m / 4 := by ring
        rw [← this]; exact hA
    _ = ∫⁻ y, (hammingDist (D y) w₀ : ℝ≥0∞) * bumpLoss β L m ∂P w₀ := by
        rw [ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun _ ↦
          by positivity)]
        have hmeas : Measurable fun y ↦ ENNReal.ofReal (hammingDist (D y) w₀ : ℝ) :=
          ENNReal.measurable_ofReal.comp hHm
        rw [← lintegral_mul_const _ hmeas]
        simp only [ENNReal.ofReal_natCast]
    _ ≤ fixedDesignRegressionRisk (bumpFun β L m w₀) σ T := by
        unfold fixedDesignRegressionRisk
        exact lintegral_mono fun y ↦ hammingDist_regDecode_mul_le hβ.1 hL
          (hT.comp measurable_prodMk_left) w₀

/-- Lower half of GAPS 103.22: for `0 < β ≤ 1`, the fixed-design Hölder minimax mean integrated
squared risk is at least `c n^(-2β/(2β+1))`. The proof applies Assouad's lemma to
`m ≍ n^(1/(2β+1))` Hölder tents with Gaussian total variation bounds. -/
theorem holderRegressionMinimaxRisk_ge (β L σ : ℝ)
    (hβ : β ∈ Ioc (0 : ℝ) 1) (hL : 0 < L) (hσ : 0 < σ) :
    ∃ c > (0 : ℝ), ∀ n : ℕ, 0 < n →
      ENNReal.ofReal (c * Real.rpow (n : ℝ) (-2 * β / (2 * β + 1))) ≤
        holderRegressionMinimaxRisk n β L σ := by
  obtain ⟨hβ0, hβ1⟩ := hβ
  set A : ℝ := max 1 ((2 * L ^ 2 / σ ^ 2) ^ (1 / (2 * β)))
  have hA1 : 1 ≤ A := le_max_left _ _
  have hA0 : 0 < A := by linarith
  have hA2 : 2 * L ^ 2 / σ ^ 2 ≤ A ^ (2 * β) := by
    have h := Real.rpow_le_rpow (by positivity) (le_max_right 1
      ((2 * L ^ 2 / σ ^ 2) ^ (1 / (2 * β)))) (by positivity : (0 : ℝ) ≤ 2 * β)
    rwa [← Real.rpow_mul (by positivity), one_div_mul_cancel (by positivity),
      Real.rpow_one] at h
  set c : ℝ := L ^ 2 * ((1 / (8 * A)) ^ β) ^ 2 / 32
  refine ⟨c, by positivity, fun n hn ↦ ?_⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : (0 : ℝ) < 2 * β + 1 := by linarith
  set r : ℝ := (n : ℝ) ^ (1 / (2 * β + 1))
  have hr1 : 1 ≤ r := Real.one_le_rpow hn1 (by positivity)
  have hr0 : 0 < r := by linarith
  have hrn : r ^ (2 * β + 1) = n := by
    rw [← Real.rpow_mul hnR.le, one_div_mul_cancel hp.ne', Real.rpow_one]
  set m : ℕ := ⌈A * r⌉₊
  have hmge : A * r ≤ m := Nat.le_ceil _
  have hmlt : (m : ℝ) < A * r + 1 := Nat.ceil_lt_add_one (by positivity)
  have hmR : (0 : ℝ) < m := lt_of_lt_of_le (by positivity) hmge
  have hm : 0 < m := by exact_mod_cast hmR
  have hm2 : (m : ℝ) ≤ 2 * (A * r) := by nlinarith
  -- the total variation condition
  have hTV : (n / m + 1) * (L * (1 / (m : ℝ)) ^ β) ^ 2 ≤ σ ^ 2 := by
    set x : ℝ := 1 / m
    set y : ℝ := 1 / (A * r)
    have hx0 : 0 < x := by positivity
    have hxy : x ≤ y := one_div_le_one_div_of_le (by positivity) hmge
    have hy1 : y ≤ 1 / A := one_div_le_one_div_of_le hA0 (by nlinarith)
    have hsq : (L * x ^ β) ^ 2 = L ^ 2 * x ^ (2 * β) := by
      rw [mul_pow, ← Real.rpow_mul_natCast hx0.le, mul_comm β]; norm_num
    have h1 : (n : ℝ) / m * x ^ (2 * β) ≤ 1 / A ^ (2 * β) := by
      have e : (n : ℝ) / m * x ^ (2 * β) = n * x ^ (2 * β + 1) := by
        rw [Real.rpow_add hx0, Real.rpow_one]; simp only [x]; ring
      rw [e]
      have hy : n * y ^ (2 * β + 1) = 1 / A ^ (2 * β + 1) := by
        simp only [y]
        rw [Real.div_rpow zero_le_one (by positivity), Real.one_rpow,
          Real.mul_rpow hA0.le hr0.le, hrn]
        field_simp
      calc (n : ℝ) * x ^ (2 * β + 1) ≤ n * y ^ (2 * β + 1) :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hx0.le hxy hp.le) hnR.le
        _ = 1 / A ^ (2 * β + 1) := hy
        _ ≤ 1 / A ^ (2 * β) := one_div_le_one_div_of_le (by positivity)
            (Real.rpow_le_rpow_of_exponent_le hA1 (by linarith))
    have h2 : x ^ (2 * β) ≤ 1 / A ^ (2 * β) := by
      calc x ^ (2 * β) ≤ (1 / A) ^ (2 * β) :=
            Real.rpow_le_rpow hx0.le (hxy.trans hy1) (by positivity)
        _ = 1 / A ^ (2 * β) := by rw [Real.div_rpow zero_le_one hA0.le, Real.one_rpow]
    rw [hsq]
    have hA2' : 2 * L ^ 2 ≤ σ ^ 2 * A ^ (2 * β) := by
      have := (div_le_iff₀ (by positivity)).mp hA2; linarith
    have hApos : 0 < A ^ (2 * β) := by positivity
    calc ((n : ℝ) / m + 1) * (L ^ 2 * x ^ (2 * β))
        = L ^ 2 * ((n : ℝ) / m * x ^ (2 * β) + x ^ (2 * β)) := by ring
      _ ≤ L ^ 2 * (1 / A ^ (2 * β) + 1 / A ^ (2 * β)) := by gcongr
      _ = 2 * L ^ 2 / A ^ (2 * β) := by ring
      _ ≤ σ ^ 2 := by rw [div_le_iff₀ hApos]; exact hA2'
  unfold holderRegressionMinimaxRisk
  refine le_iInf fun T ↦ le_trans ?_ (bumpLoss_mul_le_iSup_risk ⟨hβ0, hβ1⟩ hL.le hσ hn hm hTV
    T.val T.property)
  rw [bumpLoss, ENNReal.div_eq_inv_mul, show (4 : ℝ≥0∞)⁻¹ = ENNReal.ofReal 4⁻¹ by
      rw [ENNReal.ofReal_inv_of_pos (by norm_num)]; simp,
    ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  -- arithmetic
  have hq : (1 / (8 * A * r)) ^ β ≤ (1 / (4 * m : ℝ)) ^ β :=
    Real.rpow_le_rpow (by positivity) (one_div_le_one_div_of_le (by positivity) (by linarith))
      hβ0.le
  have hsplit : (1 / (8 * A * r)) ^ β = (1 / (8 * A)) ^ β * (1 / r) ^ β := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]; congr 1; field_simp
  have hrpow : ((1 / r) ^ β) ^ 2 = Real.rpow (n : ℝ) (-2 * β / (2 * β + 1)) := by
    rw [Real.rpow_eq_pow, Real.div_rpow zero_le_one hr0.le, Real.one_rpow, ← Real.rpow_natCast,
      Real.div_rpow zero_le_one (by positivity), Real.one_rpow, ← Real.rpow_mul hr0.le,
      ← Real.rpow_mul hnR.le, one_div, ← Real.rpow_neg hnR.le]
    congr 1; push_cast; field_simp
  have hsq := pow_le_pow_left₀ (by positivity) hq 2
  rw [hsplit, mul_pow, hrpow] at hsq
  have e : (m : ℝ) / 4 * ((4 : ℝ)⁻¹ * (L ^ 2 * ((1 / (4 * m : ℝ)) ^ β) ^ 2 * (1 / (2 * m)))) =
      L ^ 2 * ((1 / (4 * m : ℝ)) ^ β) ^ 2 / 32 := by field_simp; ring
  rw [e]
  simp only [c]
  have hL2 : 0 ≤ L ^ 2 / 32 := by positivity
  calc L ^ 2 * ((1 / (8 * A)) ^ β) ^ 2 / 32 * Real.rpow (n : ℝ) (-2 * β / (2 * β + 1))
      = L ^ 2 / 32 * (((1 / (8 * A)) ^ β) ^ 2 * Real.rpow (n : ℝ) (-2 * β / (2 * β + 1))) := by
        ring
    _ ≤ L ^ 2 / 32 * ((1 / (4 * m : ℝ)) ^ β) ^ 2 := mul_le_mul_of_nonneg_left hsq hL2
    _ = _ := by ring

/-- GAPS 103.22: the fixed-design `L²` Hölder minimax rate for orders at most one.
This states both bounds; sup-norm risk and higher local-polynomial orders are not asserted. -/
theorem holderRegressionMinimaxRisk_bounds (β L σ : ℝ)
    (hβ : β ∈ Ioc (0 : ℝ) 1) (hL : 0 < L) (hσ : 0 < σ) :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ n : ℕ, 0 < n →
      ENNReal.ofReal (c * Real.rpow (n : ℝ) (-2 * β / (2 * β + 1))) ≤
        holderRegressionMinimaxRisk n β L σ ∧
      holderRegressionMinimaxRisk n β L σ ≤
        ENNReal.ofReal (C * Real.rpow (n : ℝ) (-2 * β / (2 * β + 1))) := by
  obtain ⟨c, hc, hlow⟩ := holderRegressionMinimaxRisk_ge β L σ hβ hL hσ
  obtain ⟨C, hC, hup⟩ := holderRegressionMinimaxRisk_le β L σ hβ hL hσ
  exact ⟨c, hc, C, hC, fun n hn ↦ ⟨hlow n hn, hup n hn⟩⟩

end CKSD
