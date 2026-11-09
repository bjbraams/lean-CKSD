module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.MeasureTheory.Measure.LevyConvergence
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Independence.CharacteristicFunction
import TauCeti.Algebra.Order.BigOperators.ProdSubProd

/-!
# The Lindeberg–Feller central limit theorem

Row sums of a triangular array of independent, centred, square-integrable real random variables
whose variances sum to `v` in the limit and which satisfy Lindeberg's condition converge in
distribution to the centred Gaussian law with variance `v`.

The proof is the characteristic-function argument: the second-order Taylor remainder of
`x ↦ exp (i x)` is bounded by `min (|x|³ / 3) (2 x²)`, which bounds the distance between the
characteristic function of each summand and `1 - σ² t² / 2`; the telescoping inequality for
products of complex numbers in the unit disc (TauCeti's
`TauCeti.norm_prod_sub_prod_le_sum_norm_sub`) then compares the characteristic function of the
row sum with `exp (-(∑ σ²) t² / 2)`, and Lévy's continuity theorem
(`MeasureTheory.TendstoInDistribution.of_tendsto_charFun`) concludes.

## Main results

* `CKSD.norm_cexp_ofReal_mul_I_sub_le`: `‖exp (i x) - (1 + i x - x² / 2)‖ ≤ |x|³ / 3` and
  `≤ 2 x²`.
* `CKSD.norm_cexp_ofReal_mul_I_sub_le_lindeberg`: the truncated form of this bound.
* `CKSD.norm_charFun_map_sub_one_sub_le`: Lindeberg's bound for one centred variable.
* `CKSD.tendstoInDistribution_sum_of_lindeberg`: the Lindeberg–Feller central limit theorem.
* `CKSD.tendstoInDistribution_sum_of_lindeberg_of_iIndepFun`: the same for rows that are
  independent sequences.

## References

* J. W. Lindeberg, “Eine neue Herleitung des Exponentialgesetzes in der
  Wahrscheinlichkeitsrechnung,” *Mathematische Zeitschrift* 15 (1922), 211–225.
* P. Billingsley, *Probability and Measure*, 3rd ed., Wiley, 1995, Theorem 27.2.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Complex
open scoped Topology

namespace CKSD


/-- The quartic bound `cos x - 1 + x² / 2 ≤ x⁴ / 24`, from `1 - cos x = 2 sin² (x / 2)` and
`|y - sin y| ≤ |y|³ / 6`. -/
private theorem cos_sub_one_add_sq_div_two_le_pow_four (x : ℝ) :
    Real.cos x - 1 + x ^ 2 / 2 ≤ x ^ 4 / 24 := by
  have hc : Real.cos x = 1 - 2 * Real.sin (x / 2) ^ 2 := by
    have h2 := Real.cos_two_mul (x / 2)
    have h3 := Real.sin_sq_add_cos_sq (x / 2)
    rw [show 2 * (x / 2) = x by ring] at h2
    linarith
  have hs := Real.abs_sub_sin_le (x / 2)
  have hs2 := Real.abs_sin_le_abs (x := x / 2)
  have hy : |x / 2| ^ 2 - |Real.sin (x / 2)| ^ 2 ≤ |x / 2| ^ 4 / 3 := by
    have h1 : |x / 2| - |Real.sin (x / 2)| ≤ |x / 2| ^ 3 / 6 :=
      (abs_sub_abs_le_abs_sub _ _).trans hs
    have h0 : 0 ≤ |x / 2| - |Real.sin (x / 2)| := by linarith
    nlinarith [abs_nonneg (Real.sin (x / 2)), abs_nonneg (x / 2)]
  rw [sq_abs, sq_abs] at hy
  have : |x / 2| ^ 4 = x ^ 4 / 16 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs]; ring
  rw [hc]; nlinarith

/-- The second-order Taylor remainder of `x ↦ exp (i x)` has real part
`cos x - 1 + x² / 2`, which lies between `0` and `min (|x|³ / 6) (x² / 2)`. -/
private theorem cos_sub_one_add_sq_div_two_bounds (x : ℝ) :
    0 ≤ Real.cos x - 1 + x ^ 2 / 2 ∧ Real.cos x - 1 + x ^ 2 / 2 ≤ |x| ^ 3 / 6 ∧
      Real.cos x - 1 + x ^ 2 / 2 ≤ x ^ 2 / 2 := by
  have h0 := Real.one_sub_sq_div_two_le_cos (x := x)
  have h1 := Real.cos_le_one x
  have h4 := cos_sub_one_add_sq_div_two_le_pow_four x
  refine ⟨by linarith, ?_, by linarith⟩
  have hx2 : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
  have hx4 : x ^ 4 = |x| ^ 4 := (pow_abs x 4).symm ▸ by rw [abs_of_nonneg (by positivity)]
  rcases le_or_gt |x| 4 with h | h
  · have : x ^ 4 / 24 ≤ |x| ^ 3 / 6 := by
      rw [hx4]; nlinarith [abs_nonneg x, pow_nonneg (abs_nonneg x) 3]
    linarith
  · have : x ^ 2 / 2 ≤ |x| ^ 3 / 6 := by
      rw [hx2]; nlinarith [abs_nonneg x, pow_nonneg (abs_nonneg x) 2]
    linarith

/-- The quadratic bound `|sin x - x| ≤ x²` for all real `x`. -/
private theorem abs_sin_sub_le_sq (x : ℝ) : |Real.sin x - x| ≤ x ^ 2 := by
  have hs : |Real.sin x - x| ≤ |x| ^ 3 / 6 := by rw [abs_sub_comm]; exact Real.abs_sub_sin_le x
  have hx2 : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
  rcases le_or_gt |x| 2 with h | h
  · rw [hx2]; nlinarith [abs_nonneg x, pow_nonneg (abs_nonneg x) 2]
  · have := Real.abs_sin_le_one x
    have h3 : |Real.sin x - x| ≤ |Real.sin x| + |x| := abs_sub _ _
    rw [hx2]; nlinarith

/-- The second-order Taylor remainder of `x ↦ exp (i x)`:
`‖exp (i x) - (1 + i x - x² / 2)‖ ≤ min (|x|³ / 3) (2 x²)`. -/
theorem norm_cexp_ofReal_mul_I_sub_le (x : ℝ) :
    ‖cexp (x * I) - (1 + x * I - x ^ 2 / 2)‖ ≤ |x| ^ 3 / 3 ∧
      ‖cexp (x * I) - (1 + x * I - x ^ 2 / 2)‖ ≤ 2 * x ^ 2 := by
  set z := cexp (x * I) - (1 + x * I - x ^ 2 / 2)
  have hre : z.re = Real.cos x - 1 + x ^ 2 / 2 := by
    simp only [z, sub_re, exp_ofReal_mul_I_re, add_re, one_re, mul_re, ofReal_re, I_re,
      ofReal_im, I_im]
    norm_cast; simp; ring
  have him : z.im = Real.sin x - x := by
    simp only [z, sub_im, exp_ofReal_mul_I_im, add_im, one_im, mul_im, ofReal_re, I_re,
      ofReal_im, I_im]
    norm_cast; simp
  have hn := Complex.norm_le_abs_re_add_abs_im z
  rw [hre, him] at hn
  obtain ⟨c0, c3, c2⟩ := cos_sub_one_add_sq_div_two_bounds x
  rw [abs_of_nonneg c0] at hn
  have s3 : |Real.sin x - x| ≤ |x| ^ 3 / 6 := by rw [abs_sub_comm]; exact Real.abs_sub_sin_le x
  have s2 := abs_sin_sub_le_sq x
  constructor <;> nlinarith [sq_nonneg x]

/-- The truncated form of the Taylor bound used in Lindeberg's argument: for `ε ≥ 0`,
`‖exp (i t x) - (1 + i t x - (t x)² / 2)‖ ≤ |t|³ ε x² / 3 + 2 t² x² 1{|x| > ε}`. -/
theorem norm_cexp_ofReal_mul_I_sub_le_lindeberg {ε : ℝ} (hε : 0 ≤ ε) (t x : ℝ) :
    ‖cexp (↑(t * x) * I) - (1 + ↑(t * x) * I - ↑(t * x) ^ 2 / 2)‖ ≤
      |t| ^ 3 * ε / 3 * x ^ 2 + 2 * t ^ 2 * (if ε < |x| then x ^ 2 else 0) := by
  obtain ⟨b3, b2⟩ := norm_cexp_ofReal_mul_I_sub_le (t * x)
  split_ifs with hxε
  · refine b2.trans ?_
    have : 0 ≤ |t| ^ 3 * ε / 3 * x ^ 2 := by positivity
    nlinarith
  · replace hxε := not_lt.mp hxε
    refine b3.trans ?_
    rw [abs_mul, mul_pow]
    have : |x| ^ 3 ≤ ε * x ^ 2 := by
      rw [pow_succ, ← sq_abs x, mul_comm]
      exact mul_le_mul_of_nonneg_right hxε (sq_nonneg _)
    have : 0 ≤ |t| ^ 3 := by positivity
    nlinarith

/-- For `a ≥ 0`, `|exp (-a) - (1 - a)| ≤ a²`. -/
theorem Real.abs_exp_neg_sub_one_sub_le_sq {a : ℝ} (ha : 0 ≤ a) :
    |Real.exp (-a) - (1 - a)| ≤ a ^ 2 := by
  rcases le_or_gt a 1 with h | h
  · have := Real.abs_exp_sub_one_sub_id_le (x := -a) (by rw [abs_neg, abs_of_nonneg ha]; exact h)
    rw [neg_sq] at this
    convert this using 2; ring
  · have h1 := Real.one_sub_le_exp_neg a
    have h2 : Real.exp (-a) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    rw [abs_of_nonneg (by linarith)]
    nlinarith


/-- Lindeberg's bound for one centred square-integrable variable `Y`: for every `ε ≥ 0`,
`‖φ_Y(t) - (1 - 𝔼[Y²] t² / 2)‖ ≤ |t|³ ε 𝔼[Y²] / 3 + 2 t² 𝔼[Y² ; |Y| > ε]`. -/
theorem norm_charFun_map_sub_one_sub_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {Y : Ω → ℝ} (hY : MemLp Y 2 μ) (h0 : ∫ ω, Y ω ∂μ = 0)
    {ε : ℝ} (hε : 0 ≤ ε) (t : ℝ) :
    ‖charFun (μ.map Y) t - (1 - ((∫ ω, Y ω ^ 2 ∂μ : ℝ) : ℂ) * t ^ 2 / 2)‖ ≤
      |t| ^ 3 * ε / 3 * ∫ ω, Y ω ^ 2 ∂μ +
        2 * t ^ 2 * ∫ ω, (if ε < |Y ω| then Y ω ^ 2 else 0) ∂μ := by
  have hYm := hY.aemeasurable
  have hY1 : Integrable Y μ := hY.integrable one_le_two
  have hY2 : Integrable (fun ω ↦ Y ω ^ 2) μ := hY.integrable_sq
  let T : ℝ → ℝ := fun x ↦ if ε < |x| then x ^ 2 else 0
  have hTm : Measurable T := Measurable.ite (measurableSet_lt measurable_const
    continuous_abs.measurable) (by fun_prop) measurable_const
  have hT : Integrable (fun ω ↦ T (Y ω)) μ := by
    refine hY2.mono' (hTm.comp_aemeasurable hYm).aestronglyMeasurable (ae_of_all _ fun ω ↦ ?_)
    simp only [T, Real.norm_eq_abs]
    split_ifs
    · rw [abs_of_nonneg (sq_nonneg _)]
    · simp [sq_nonneg]
  let g : Ω → ℂ := fun ω ↦
    cexp (↑(t * Y ω) * I) - (1 + ↑(t * Y ω) * I - ↑(t * Y ω) ^ 2 / 2)
  have hE : Integrable (fun ω ↦ cexp (↑(t * Y ω) * I)) μ := by
    refine Integrable.of_bound ?_ 1 (ae_of_all _ fun ω ↦ ?_)
    · exact ((by fun_prop : Measurable fun x : ℝ ↦ cexp (↑x * I)).comp_aemeasurable
        (hYm.const_mul t)).aestronglyMeasurable
    · rw [norm_exp_ofReal_mul_I]
  have hP1 : Integrable (fun ω ↦ (↑(t * Y ω) : ℂ) * I) μ :=
    ((hY1.const_mul t).ofReal (𝕜 := ℂ)).mul_const I
  have hP2 : Integrable (fun ω ↦ (↑(t * Y ω) : ℂ) ^ 2 / 2) μ := by
    have := ((hY2.const_mul (t ^ 2)).ofReal (𝕜 := ℂ)).div_const 2
    refine this.congr (ae_of_all _ fun ω ↦ ?_)
    show ((t ^ 2 * Y ω ^ 2 : ℝ) : ℂ) / 2 = _
    push_cast; ring
  have hP12 : Integrable (fun ω ↦ (1 : ℂ) + ↑(t * Y ω) * I) μ := (integrable_const _).add hP1
  have hP : Integrable (fun ω ↦ (1 : ℂ) + ↑(t * Y ω) * I - ↑(t * Y ω) ^ 2 / 2) μ :=
    hP12.sub hP2
  have hpoly : ∫ ω, ((1 : ℂ) + ↑(t * Y ω) * I - ↑(t * Y ω) ^ 2 / 2) ∂μ =
      1 - ((∫ ω, Y ω ^ 2 ∂μ : ℝ) : ℂ) * t ^ 2 / 2 := by
    rw [integral_sub hP12 hP2, integral_add (integrable_const _) hP1, integral_mul_const,
      integral_div, integral_const, integral_complex_ofReal]
    have h1 : ∫ ω, t * Y ω ∂μ = 0 := by rw [integral_const_mul, h0, mul_zero]
    have h2 : ∫ ω, (↑(t * Y ω) : ℂ) ^ 2 ∂μ = ↑(∫ ω, Y ω ^ 2 ∂μ) * ↑t ^ 2 := by
      have hc : ∀ ω, (↑(t * Y ω) : ℂ) ^ 2 = ↑(t ^ 2 * Y ω ^ 2) := fun ω ↦ by push_cast; ring
      simp_rw [hc]
      rw [integral_complex_ofReal, integral_const_mul]
      push_cast; ring
    rw [h1, h2]
    simp
  have hkey : charFun (μ.map Y) t - (1 - ((∫ ω, Y ω ^ 2 ∂μ : ℝ) : ℂ) * t ^ 2 / 2) =
      ∫ ω, g ω ∂μ := by
    rw [charFun_apply_real, integral_map hYm (by fun_prop)]
    simp only [g]
    rw [integral_sub hE hP, hpoly]
    simp only [ofReal_mul]
  rw [hkey]
  refine (norm_integral_le_of_norm_le ((hY2.const_mul (|t| ^ 3 * ε / 3)).add
    (hT.const_mul (2 * t ^ 2)))
    (ae_of_all _ fun ω ↦ ?_)).trans_eq ?_
  · exact norm_cexp_ofReal_mul_I_sub_le_lindeberg hε t (Y ω)
  · simp only [Pi.add_apply]
    rw [integral_add (hY2.const_mul _) (hT.const_mul _), integral_const_mul, integral_const_mul]


/-- The truncated second moment `ω ↦ Y² 1{|Y| > ε}` of a square-integrable variable is
integrable. -/
theorem integrable_ite_lt_abs_sq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {Y : Ω → ℝ} (hY : MemLp Y 2 μ) (ε : ℝ) :
    Integrable (fun ω ↦ if ε < |Y ω| then Y ω ^ 2 else 0) μ := by
  have hTm : Measurable fun x : ℝ ↦ if ε < |x| then x ^ 2 else 0 :=
    Measurable.ite (measurableSet_lt measurable_const continuous_abs.measurable) (by fun_prop)
      measurable_const
  refine hY.integrable_sq.mono' (hTm.comp_aemeasurable hY.aemeasurable).aestronglyMeasurable
    (ae_of_all _ fun ω ↦ ?_)
  simp only [Real.norm_eq_abs]
  split_ifs
  · rw [abs_of_nonneg (sq_nonneg _)]
  · simp [sq_nonneg]

/-- The second moment is at most `ε² + 𝔼[Y² ; |Y| > ε]`. -/
theorem integral_sq_le_sq_add_integral_ite {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {Y : Ω → ℝ} (hY : MemLp Y 2 μ) (ε : ℝ) :
    ∫ ω, Y ω ^ 2 ∂μ ≤ ε ^ 2 + ∫ ω, (if ε < |Y ω| then Y ω ^ 2 else 0) ∂μ := by
  have hT := integrable_ite_lt_abs_sq hY ε
  calc ∫ ω, Y ω ^ 2 ∂μ ≤ ∫ ω, (ε ^ 2 + if ε < |Y ω| then Y ω ^ 2 else 0) ∂μ := by
        refine integral_mono hY.integrable_sq ((integrable_const _).add hT) fun ω ↦ ?_
        simp only
        split_ifs with h
        · nlinarith [sq_nonneg ε]
        · rw [add_zero, ← sq_abs (Y ω)]
          exact pow_le_pow_left₀ (abs_nonneg _) (not_lt.mp h) 2
    _ = _ := by rw [integral_add (integrable_const _) hT, integral_const]; simp

/-- Lindeberg's bound for one row of a triangular array: for centred square-integrable
variables `Y j`, `j ∈ s`, with variances `σⱼ²`, every `ε ≥ 0` and every `t`,
`‖∏ⱼ φ_{Yⱼ}(t) - exp (-(∑ⱼ σⱼ²) t² / 2)‖` is at most
`|t|³ ε (∑ σⱼ²) / 3 + 2 t² Lₛ(ε) + t⁴ (∑ σⱼ²) (ε² + Lₛ(ε)) / 4`, where
`Lₛ(ε) = ∑ⱼ 𝔼[Yⱼ² ; |Yⱼ| > ε]`. -/
theorem norm_prod_charFun_sub_exp_le {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (s : Finset ι) (Y : ι → Ω → ℝ) (h2 : ∀ j ∈ s, MemLp (Y j) 2 μ)
    (h0 : ∀ j ∈ s, ∫ ω, Y j ω ∂μ = 0) {ε : ℝ} (hε : 0 ≤ ε) (t : ℝ) :
    ‖∏ j ∈ s, charFun (μ.map (Y j)) t -
        (Real.exp (-((∑ j ∈ s, ∫ ω, Y j ω ^ 2 ∂μ) * t ^ 2 / 2)) : ℂ)‖ ≤
      |t| ^ 3 * ε / 3 * (∑ j ∈ s, ∫ ω, Y j ω ^ 2 ∂μ) +
        2 * t ^ 2 * (∑ j ∈ s, ∫ ω, (if ε < |Y j ω| then Y j ω ^ 2 else 0) ∂μ) +
        t ^ 4 / 4 * (∑ j ∈ s, ∫ ω, Y j ω ^ 2 ∂μ) *
          (ε ^ 2 + ∑ j ∈ s, ∫ ω, (if ε < |Y j ω| then Y j ω ^ 2 else 0) ∂μ) := by
  set σ2 : ι → ℝ := fun j ↦ ∫ ω, Y j ω ^ 2 ∂μ with hσ2
  set Lj : ι → ℝ := fun j ↦ ∫ ω, (if ε < |Y j ω| then Y j ω ^ 2 else 0) ∂μ with hLj
  have hσ0 : ∀ j, 0 ≤ σ2 j := fun j ↦ integral_nonneg fun ω ↦ sq_nonneg _
  have hL0 : ∀ j, 0 ≤ Lj j := fun j ↦ integral_nonneg fun ω ↦ by
    simp only; split_ifs <;> positivity
  let a : ι → ℝ := fun j ↦ σ2 j * t ^ 2 / 2
  have ha0 : ∀ j, 0 ≤ a j := fun j ↦ by have := hσ0 j; positivity
  have hexp : (Real.exp (-((∑ j ∈ s, σ2 j) * t ^ 2 / 2)) : ℂ) =
      ∏ j ∈ s, (Real.exp (-a j) : ℂ) := by
    rw [← ofReal_prod, ← Real.exp_sum, Finset.sum_neg_distrib]
    congr 3
    simp only [a, Finset.sum_mul, Finset.sum_div]
  rw [hexp]
  have hφ : ∀ j ∈ s, ‖charFun (μ.map (Y j)) t‖ ≤ 1 := fun j _ ↦ norm_charFun_le_one t
  have hw : ∀ j ∈ s, ‖(Real.exp (-a j) : ℂ)‖ ≤ 1 := fun j _ ↦ by
    rw [norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (by linarith [ha0 j])
  refine (TauCeti.norm_prod_sub_prod_le_sum_norm_sub s hφ hw).trans ?_
  have hterm : ∀ j ∈ s, ‖charFun (μ.map (Y j)) t - (Real.exp (-a j) : ℂ)‖ ≤
      |t| ^ 3 * ε / 3 * σ2 j + 2 * t ^ 2 * Lj j + t ^ 4 / 4 * σ2 j *
        (ε ^ 2 + ∑ i ∈ s, Lj i) := by
    intro j hj
    have h1 := norm_charFun_map_sub_one_sub_le (h2 j hj) (h0 j hj) hε t
    have h3 : ‖((1 - a j : ℝ) : ℂ) - (Real.exp (-a j) : ℂ)‖ ≤ a j ^ 2 := by
      rw [← ofReal_sub, norm_real, Real.norm_eq_abs, abs_sub_comm]
      exact Real.abs_exp_neg_sub_one_sub_le_sq (ha0 j)
    have hcast : ((1 - a j : ℝ) : ℂ) = 1 - ((σ2 j : ℝ) : ℂ) * t ^ 2 / 2 := by
      simp only [a]; push_cast; ring
    rw [hcast] at h3
    have hσle : σ2 j ≤ ε ^ 2 + ∑ i ∈ s, Lj i :=
      (integral_sq_le_sq_add_integral_ite (h2 j hj) ε).trans
        (add_le_add_right (Finset.single_le_sum (fun i _ ↦ hL0 i) hj) _)
    have ha2 : a j ^ 2 ≤ t ^ 4 / 4 * σ2 j * (ε ^ 2 + ∑ i ∈ s, Lj i) := by
      have : a j ^ 2 = t ^ 4 / 4 * σ2 j * σ2 j := by simp only [a]; ring
      rw [this]
      exact mul_le_mul_of_nonneg_left hσle (by have := hσ0 j; positivity)
    calc _ ≤ ‖charFun (μ.map (Y j)) t - (1 - ((σ2 j : ℝ) : ℂ) * t ^ 2 / 2)‖ +
          ‖(1 - ((σ2 j : ℝ) : ℂ) * t ^ 2 / 2) - (Real.exp (-a j) : ℂ)‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ _ := by linarith
  refine (Finset.sum_le_sum hterm).trans_eq ?_
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]

/-- **Lindeberg–Feller central limit theorem** for triangular arrays of real random
variables. Let `X n 0, …, X n (k n - 1)` be independent, centred and square integrable for
each `n`. If `∑ⱼ 𝔼[X_{n,j}²] → v` and the Lindeberg condition
`∑ⱼ 𝔼[X_{n,j}² ; |X_{n,j}| > ε] → 0` holds for every `ε > 0`, then the row sums
`∑ⱼ X_{n,j}` converge in distribution to `N(0, v)`. -/
theorem tendstoInDistribution_sum_of_lindeberg {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → ℕ → Ω → ℝ) (k : ℕ → ℕ)
    (h2 : ∀ n j, MemLp (X n j) 2 μ) (h0 : ∀ n j, ∫ ω, X n j ω ∂μ = 0)
    (hind : ∀ n, iIndepFun (fun j : Finset.range (k n) ↦ X n j) μ) (v : ℝ)
    (hvar : Tendsto (fun n ↦ ∑ j ∈ Finset.range (k n), ∫ ω, X n j ω ^ 2 ∂μ) atTop (𝓝 v))
    (hlin : ∀ ε > 0, Tendsto (fun n ↦ ∑ j ∈ Finset.range (k n),
      ∫ ω, (if ε < |X n j ω| then X n j ω ^ 2 else 0) ∂μ) atTop (𝓝 0)) :
    TendstoInDistribution (fun n ω ↦ ∑ j ∈ Finset.range (k n), X n j ω) atTop id
      (fun _ ↦ μ) (gaussianReal 0 v.toNNReal) := by
  have hm : ∀ n j, AEMeasurable (X n j) μ := fun n j ↦ (h2 n j).aemeasurable
  refine TendstoInDistribution.of_tendsto_charFun
    (fun n ↦ Finset.aemeasurable_fun_sum _ fun j _ ↦ hm n j) aemeasurable_id fun t ↦ ?_
  set s : ℕ → ℝ := fun n ↦ ∑ j ∈ Finset.range (k n), ∫ ω, X n j ω ^ 2 ∂μ with hs
  set L : ℝ → ℕ → ℝ := fun ε n ↦ ∑ j ∈ Finset.range (k n),
    ∫ ω, (if ε < |X n j ω| then X n j ω ^ 2 else 0) ∂μ with hL
  have hs0 : ∀ n, 0 ≤ s n := fun n ↦
    Finset.sum_nonneg fun j _ ↦ integral_nonneg fun ω ↦ sq_nonneg _
  have hv0 : 0 ≤ v := ge_of_tendsto' hvar hs0
  have hprod : ∀ n, charFun (μ.map fun ω ↦ ∑ j ∈ Finset.range (k n), X n j ω) t =
      ∏ j ∈ Finset.range (k n), charFun (μ.map (X n j)) t := fun n ↦ by
    rw [(hind n).charFun_map_fun_finsetSum_eq_prod (fun j _ ↦ hm n j), Finset.prod_apply]
  have hlim : charFun ((gaussianReal 0 v.toNNReal).map id) t =
      (Real.exp (-(v * t ^ 2 / 2)) : ℂ) := by
    rw [Measure.map_id, charFun_gaussianReal, ofReal_exp, Real.coe_toNNReal _ hv0]
    push_cast; ring_nf
  simp only [hprod, hlim]
  -- the Gaussian factors converge
  have hG : Tendsto (fun n ↦ (Real.exp (-(s n * t ^ 2 / 2)) : ℂ)) atTop
      (𝓝 (Real.exp (-(v * t ^ 2 / 2)) : ℂ)) :=
    (continuous_ofReal.tendsto _).comp ((hvar.mul_const (t ^ 2)).div_const 2).neg.rexp
  -- the difference tends to zero
  have hD : Tendsto (fun n ↦ ∏ j ∈ Finset.range (k n), charFun (μ.map (X n j)) t -
      (Real.exp (-(s n * t ^ 2 / 2)) : ℂ)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine Metric.tendsto_nhds.2 fun δ hδ ↦ ?_
    let B : ℝ → ℝ := fun ε ↦ |t| ^ 3 * ε / 3 * v + t ^ 4 / 4 * v * ε ^ 2
    have hB : Tendsto B (𝓝[>] 0) (𝓝 0) := by
      have : Tendsto B (𝓝 0) (𝓝 (B 0)) := (by fun_prop : Continuous B).continuousAt.tendsto
      simpa [B] using this.mono_left nhdsWithin_le_nhds
    obtain ⟨ε, hεδ, hε0⟩ := ((hB.eventually (gt_mem_nhds hδ)).and self_mem_nhdsWithin).exists
    have hε0' : (0 : ℝ) < ε := hε0
    have hBn : Tendsto (fun n ↦ |t| ^ 3 * ε / 3 * s n + 2 * t ^ 2 * L ε n +
        t ^ 4 / 4 * s n * (ε ^ 2 + L ε n)) atTop (𝓝 (B ε)) := by
      have := ((hvar.const_mul (|t| ^ 3 * ε / 3)).add ((hlin ε hε0').const_mul (2 * t ^ 2))).add
        ((hvar.const_mul (t ^ 4 / 4)).mul ((hlin ε hε0').const_add (ε ^ 2)))
      convert this using 2
      simp only [B]; ring
    filter_upwards [hBn.eventually (gt_mem_nhds hεδ)] with n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
    exact (norm_prod_charFun_sub_exp_le _ (X n) (fun j _ ↦ h2 n j) (fun j _ ↦ h0 n j)
      hε0'.le t).trans_lt hn
  simpa using hD.add hG

/-- The Lindeberg–Feller central limit theorem for rows that are independent sequences: if
each row `X n` is an independent family, the row sums over `j < k n` converge in distribution to
`N(0, v)` under the hypotheses of `CKSD.tendstoInDistribution_sum_of_lindeberg`. -/
theorem tendstoInDistribution_sum_of_lindeberg_of_iIndepFun {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → ℕ → Ω → ℝ) (k : ℕ → ℕ)
    (h2 : ∀ n j, MemLp (X n j) 2 μ) (h0 : ∀ n j, ∫ ω, X n j ω ∂μ = 0)
    (hind : ∀ n, iIndepFun (X n) μ) (v : ℝ)
    (hvar : Tendsto (fun n ↦ ∑ j ∈ Finset.range (k n), ∫ ω, X n j ω ^ 2 ∂μ) atTop (𝓝 v))
    (hlin : ∀ ε > 0, Tendsto (fun n ↦ ∑ j ∈ Finset.range (k n),
      ∫ ω, (if ε < |X n j ω| then X n j ω ^ 2 else 0) ∂μ) atTop (𝓝 0)) :
    TendstoInDistribution (fun n ω ↦ ∑ j ∈ Finset.range (k n), X n j ω) atTop id
      (fun _ ↦ μ) (gaussianReal 0 v.toNNReal) :=
  tendstoInDistribution_sum_of_lindeberg μ X k h2 h0
    (fun n ↦ (hind n).precomp Subtype.val_injective) v hvar hlin

end CKSD
