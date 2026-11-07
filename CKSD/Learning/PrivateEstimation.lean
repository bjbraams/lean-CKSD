module

public import CKSD.Learning.Basic
public import Mathlib.Probability.Moments.Variance
public import TauCeti.Probability.Distributions.Laplace.Basic

/-!
# Private estimation of a bounded mean

Data sets are vectors in `ℝⁿ`, neighbouring when they differ in at most one coordinate. A
central mechanism is a Markov kernel from data sets to real releases. The clipped Laplace
mechanism releases the mean of the data clipped to `[-1,1]` plus Laplace noise of scale
`2 / (n ε)`. Local mechanisms are noninteractive: individual `i` releases `Zᵢ ∼ Qᵢ(· | Xᵢ)`
through an `ε`-locally private kernel to the real line, and an estimator is a measurable
function of the releases. The target is the mean of an unknown law on `[-1,1]` and the risk is
the mean squared error.

The Laplace law and its moments are TauCeti's (`TauCeti.Probability.laplaceMeasure`).
Source: GAPS 107.66.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- Data sets in `ℝⁿ` are neighbouring when they differ in at most one coordinate. -/
def IsHammingNeighbor {n : ℕ} (d d' : Fin n → ℝ) : Prop :=
  (Finset.univ.filter fun i ↦ d i ≠ d' i).card ≤ 1

/-- Clipping to `[-1,1]`. -/
def clipUnit (x : ℝ) : ℝ := max (-1) (min 1 x)

/-- Mean of a data set clipped to `[-1,1]`. -/
def clippedMean {n : ℕ} (d : Fin n → ℝ) : ℝ := (∑ i, clipUnit (d i)) / n

/-- The clipped Laplace mean mechanism with noise scale `2 / (n ε)`. -/
def laplaceMeanMechanism (n : ℕ) (ε : ℝ) : Kernel (Fin n → ℝ) ℝ where
  toFun d := TauCeti.Probability.laplaceMeasure (clippedMean d) (2 / (n * ε))
  measurable' := by
    have hc : Measurable fun d : Fin n → ℝ ↦ clippedMean d := by
      unfold clippedMean clipUnit
      fun_prop
    exact TauCeti.Probability.measurable_laplaceMeasure.comp (hc.prodMk measurable_const)

/-- Mean squared error of a central mechanism for the mean of `P`, from `n` observations. -/
def centralMeanRisk {n : ℕ} (M : Kernel (Fin n → ℝ) ℝ) (P : Measure ℝ) : ℝ :=
  ∫ d, ∫ y, (y - ∫ x, x ∂P) ^ 2 ∂M d ∂Measure.pi fun _ : Fin n ↦ P

/-- Mean squared error of a noninteractive local protocol with release kernels `Q` and
estimator `est`, for the mean of `P`. -/
def localMeanRisk {n : ℕ} (Q : Fin n → Kernel ℝ ℝ) (est : (Fin n → ℝ) → ℝ) (P : Measure ℝ) :
    ℝ :=
  ∫ z, (est z - ∫ x, x ∂P) ^ 2 ∂Measure.pi fun i ↦ Q i ∘ₘ P

/-- Changing one coordinate moves the clipped mean by at most `2 / n`. -/
theorem abs_clippedMean_sub_le {n : ℕ} {d d' : Fin n → ℝ} (h : IsHammingNeighbor d d') :
    |clippedMean d - clippedMean d'| ≤ 2 / n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [clippedMean]
  have hclip : ∀ x, clipUnit x ∈ Icc (-1 : ℝ) 1 := fun x ↦
    ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
  have hnr : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hsum : |∑ i, (clipUnit (d i) - clipUnit (d' i))| ≤ 2 := by
    let S := Finset.univ.filter fun i ↦ d i ≠ d' i
    calc |∑ i, (clipUnit (d i) - clipUnit (d' i))|
        ≤ ∑ i, |clipUnit (d i) - clipUnit (d' i)| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i ∈ S, |clipUnit (d i) - clipUnit (d' i)| := by
        refine (Finset.sum_subset (Finset.subset_univ _) fun i _ hi ↦ ?_).symm
        have : d i = d' i := by simpa [S] using hi
        simp [this]
      _ ≤ ∑ _i ∈ S, (2 : ℝ) := Finset.sum_le_sum fun i _ ↦ by
        have h1 := hclip (d i); have h2 := hclip (d' i)
        rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
      _ = 2 * S.card := by rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ 2 * 1 := by
        have : (S.card : ℝ) ≤ 1 := by exact_mod_cast h
        linarith
      _ = 2 := by norm_num
  unfold clippedMean
  rw [← sub_div, ← Finset.sum_sub_distrib, abs_div, abs_of_pos hnr]
  exact div_le_div_of_nonneg_right hsum hnr.le

/-- Shifting the location of a Laplace density by `δ` changes it by at most `e^{|δ|/b}`. -/
theorem laplacePDF_le_exp_mul {b : ℝ} (hb : 0 < b) (m m' x : ℝ) :
    TauCeti.Probability.laplacePDF m b x ≤
      ENNReal.ofReal (Real.exp (|m - m'| / b)) * TauCeti.Probability.laplacePDF m' b x := by
  rw [TauCeti.Probability.laplacePDF_of_pos hb, TauCeti.Probability.laplacePDF_of_pos hb,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  apply ENNReal.ofReal_le_ofReal
  have htri : |x - m'| ≤ |x - m| + |m - m'| := by
    calc |x - m'| = |(x - m) + (m - m')| := by ring_nf
      _ ≤ _ := abs_add_le _ _
  have hexp : Real.exp (-|x - m| / b) ≤ Real.exp (|m - m'| / b) * Real.exp (-|x - m'| / b) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    rw [← add_div, div_le_div_iff_of_pos_right hb]
    linarith
  have h2b : 0 ≤ (2 * b)⁻¹ := by positivity
  calc (2 * b)⁻¹ * Real.exp (-|x - m| / b)
      ≤ (2 * b)⁻¹ * (Real.exp (|m - m'| / b) * Real.exp (-|x - m'| / b)) :=
        mul_le_mul_of_nonneg_left hexp h2b
    _ = _ := by ring

/-- GAPS 107.66: the clipped Laplace mean mechanism is `ε`-differentially private. -/
theorem isDifferentiallyPrivate_laplaceMeanMechanism (n : ℕ) (hn : 0 < n) (ε : ℝ)
    (hε : 0 < ε) :
    IsDifferentiallyPrivate IsHammingNeighbor ε 0 (laplaceMeanMechanism n ε) := by
  intro d d' hdd' A _
  have hnr : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  set b : ℝ := 2 / (n * ε) with hb_def
  have hb : 0 < b := by positivity
  have hratio : |clippedMean d - clippedMean d'| / b ≤ ε := by
    rw [div_le_iff₀ hb, hb_def]
    calc |clippedMean d - clippedMean d'| ≤ 2 / n := abs_clippedMean_sub_le hdd'
      _ = ε * (2 / (n * ε)) := by field_simp
  have hk : ∀ e : Fin n → ℝ, laplaceMeanMechanism n ε e =
      volume.withDensity (TauCeti.Probability.laplacePDF (clippedMean e) b) := fun e ↦
    TauCeti.Probability.laplaceMeasure_eq_withDensity _ _
  rw [ENNReal.ofReal_zero, add_zero, hk, hk, withDensity_apply' _ A, withDensity_apply' _ A,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun x ↦ ?_
  calc TauCeti.Probability.laplacePDF (clippedMean d) b x
      ≤ ENNReal.ofReal (Real.exp (|clippedMean d - clippedMean d'| / b)) *
          TauCeti.Probability.laplacePDF (clippedMean d') b x := laplacePDF_le_exp_mul hb _ _ x
    _ ≤ ENNReal.ofReal (Real.exp ε) * TauCeti.Probability.laplacePDF (clippedMean d') b x := by
      gcongr

/-- Mean squared deviation of a Laplace law from a point: squared bias plus variance `2b²`. -/
theorem integral_sq_sub_laplaceMeasure {b : ℝ} (hb : 0 < b) (m θ : ℝ) :
    ∫ y, (y - θ) ^ 2 ∂TauCeti.Probability.laplaceMeasure m b = (m - θ) ^ 2 + 2 * b ^ 2 := by
  have := TauCeti.Probability.isProbabilityMeasure_laplaceMeasure hb m
  have h2 := TauCeti.Probability.integral_pow_abs_sub_laplaceMeasure hb m 2
  have hi2 := TauCeti.Probability.integrable_pow_abs_sub_laplaceMeasure (b := b) m 2
  have hi1 := TauCeti.Probability.integrable_sub_const_laplaceMeasure (b := b) m
  have h1 := TauCeti.Probability.integral_sub_const_laplaceMeasure (b := b) m
  simp only [sq_abs] at h2 hi2
  have hpt : ∀ y : ℝ, (y - θ) ^ 2 = ((y - m) ^ 2 + 2 * (m - θ) * (y - m)) + (m - θ) ^ 2 := by
    intro y; ring
  rw [show (fun y : ℝ ↦ (y - θ) ^ 2) = fun y ↦
    ((y - m) ^ 2 + 2 * (m - θ) * (y - m)) + (m - θ) ^ 2 from funext hpt]
  rw [integral_add (f := fun y ↦ (y - m) ^ 2 + 2 * (m - θ) * (y - m))
      (g := fun _ ↦ (m - θ) ^ 2) (hi2.add (hi1.const_mul _)) (integrable_const _),
    integral_add (f := fun y ↦ (y - m) ^ 2) (g := fun y ↦ 2 * (m - θ) * (y - m)) hi2
      (hi1.const_mul _), integral_const_mul, h1, h2, integral_const]
  simp only [probReal_univ, one_smul, Nat.factorial_two, Nat.cast_ofNat, mul_zero, add_zero]
  ring

/-- On laws supported by `[-1,1]` the clipped sample mean has mean squared error at most
`1/n`. -/
theorem integral_clippedMean_sub_sq_le (n : ℕ) (hn : 0 < n) (P : Measure ℝ)
    [IsProbabilityMeasure P] (hP : P (Icc (-1) 1)ᶜ = 0) :
    ∫ d, (clippedMean d - ∫ x, x ∂P) ^ 2 ∂Measure.pi (fun _ : Fin n ↦ P) ≤ 1 / n := by
  set π : Measure (Fin n → ℝ) := Measure.pi fun _ : Fin n ↦ P
  have hnr : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hclipm : Measurable clipUnit := by unfold clipUnit; fun_prop
  have hclip : ∀ x, clipUnit x ∈ Icc (-1 : ℝ) 1 := fun x ↦
    ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
  have hae : ∀ᵐ x ∂P, clipUnit x = x := by
    have hmem : ∀ᵐ x ∂P, x ∈ Icc (-1 : ℝ) 1 := measure_eq_zero_iff_ae_notMem.mp hP |>.mono
      fun x hx ↦ by simpa using hx
    filter_upwards [hmem] with x hx
    simp only [clipUnit, min_eq_right hx.2, max_eq_right hx.1]
  have hθ : ∫ x, clipUnit x ∂P = ∫ x, x ∂P := integral_congr_ae hae
  set Y : Fin n → (Fin n → ℝ) → ℝ := fun i d ↦ clipUnit (d i)
  have hYm : ∀ i, Measurable (Y i) := fun i ↦ hclipm.comp (measurable_pi_apply i)
  have hYb : ∀ i d, ‖Y i d‖ ≤ 1 := fun i d ↦ by
    rw [Real.norm_eq_abs, abs_le]; exact ⟨(hclip _).1, (hclip _).2⟩
  have hYL : ∀ i, MemLp (Y i) 2 π := fun i ↦
    MemLp.of_bound (hYm i).aestronglyMeasurable 1 (Eventually.of_forall (hYb i))
  have hYint : ∀ i, ∫ d, Y i d ∂π = ∫ x, x ∂P := by
    intro i
    have hp := measurePreserving_eval (fun _ : Fin n ↦ P) i
    have := integral_map (μ := π) hp.measurable.aemeasurable (f := clipUnit)
      hclipm.aestronglyMeasurable
    rw [hp.map_eq] at this
    rw [← hθ, this]
  have hmean_eq : (fun d ↦ clippedMean d) = fun d ↦ (n : ℝ)⁻¹ * (∑ i, Y i) d := by
    funext d
    simp only [clippedMean, Finset.sum_apply, Y]
    rw [div_eq_inv_mul]
  have hsumL : MemLp (∑ i, Y i) 2 π := memLp_finsetSum' _ fun i _ ↦ hYL i
  have hEmean : ∫ d, clippedMean d ∂π = ∫ x, x ∂P := by
    rw [hmean_eq, integral_const_mul]
    simp only [Finset.sum_apply]
    rw [integral_finsetSum _ fun i _ ↦ (hYL i).integrable one_le_two]
    simp only [hYint, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hvar_eq : ∫ d, (clippedMean d - ∫ x, x ∂P) ^ 2 ∂π = ProbabilityTheory.variance (fun d ↦ clippedMean d) π := by
    rw [variance_eq_integral (by rw [hmean_eq]; exact (hsumL.aemeasurable.const_mul _)), hEmean]
  have hindep : Set.Pairwise (↑(Finset.univ : Finset (Fin n))) fun i j ↦ Y i ⟂ᵢ[π] Y j := by
    intro i _ j _ hij
    exact (iIndepFun_pi (X := fun _ : Fin n ↦ clipUnit)
      (fun _ ↦ hclipm.aemeasurable)).indepFun hij
  have hvsum : ProbabilityTheory.variance (∑ i, Y i) π = ∑ i, ProbabilityTheory.variance (Y i) π :=
    IndepFun.variance_sum (fun i _ ↦ hYL i) hindep
  have hvY : ∀ i, ProbabilityTheory.variance (Y i) π ≤ 1 := by
    intro i
    have := variance_le_sq_of_bounded (μ := π) (a := -1) (b := 1)
      (Eventually.of_forall fun d ↦ hclip (d i)) (hYm i).aemeasurable
    norm_num at this
    exact this
  rw [hvar_eq, hmean_eq, variance_const_mul, hvsum]
  calc ((n : ℝ)⁻¹) ^ 2 * ∑ i, ProbabilityTheory.variance (Y i) π ≤ ((n : ℝ)⁻¹) ^ 2 * ∑ _i : Fin n, (1 : ℝ) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ ↦ hvY i) (by positivity)
    _ = 1 / n := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
        field_simp

/-- GAPS 107.66: on laws supported by `[-1,1]`, the clipped Laplace mean mechanism has mean
squared error at most `1/n + 8/(n ε)²`. -/
theorem centralMeanRisk_laplaceMeanMechanism_le (n : ℕ) (hn : 0 < n) (ε : ℝ) (hε : 0 < ε)
    (P : Measure ℝ) [IsProbabilityMeasure P] (hP : P (Icc (-1) 1)ᶜ = 0) :
    centralMeanRisk (laplaceMeanMechanism n ε) P ≤ 1 / n + 8 / (n * ε) ^ 2 := by
  have hnr : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  set b : ℝ := 2 / (n * ε) with hb_def
  have hb : 0 < b := by positivity
  have hinner : ∀ d : Fin n → ℝ, ∫ y, (y - ∫ x, x ∂P) ^ 2 ∂laplaceMeanMechanism n ε d =
      (clippedMean d - ∫ x, x ∂P) ^ 2 + 2 * b ^ 2 := fun d ↦
    integral_sq_sub_laplaceMeasure hb _ _
  have hclipm : Measurable clipUnit := by unfold clipUnit; fun_prop
  have hcm : Measurable fun d : Fin n → ℝ ↦ clippedMean d := by
    unfold clippedMean; fun_prop
  have hbdd : ∀ d : Fin n → ℝ, ‖(clippedMean d - ∫ x, x ∂P) ^ 2‖ ≤ (1 + |∫ x, x ∂P|) ^ 2 := by
    intro d
    have hc : |clippedMean d| ≤ 1 := by
      unfold clippedMean
      rw [abs_div, abs_of_pos hnr, div_le_one hnr]
      calc |∑ i, clipUnit (d i)| ≤ ∑ i, |clipUnit (d i)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum fun i _ ↦ by
          rw [abs_le]
          exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
        _ = n := by simp
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have := abs_sub (clippedMean d) (∫ x, x ∂P)
    nlinarith [abs_nonneg (clippedMean d - ∫ x, x ∂P), sq_abs (clippedMean d - ∫ x, x ∂P)]
  have hint : Integrable (fun d : Fin n → ℝ ↦ (clippedMean d - ∫ x, x ∂P) ^ 2)
      (Measure.pi fun _ : Fin n ↦ P) :=
    Integrable.of_bound ((hcm.sub_const _).pow_const 2).aestronglyMeasurable _
      (Eventually.of_forall hbdd)
  unfold centralMeanRisk
  simp_rw [hinner]
  rw [integral_add hint (integrable_const _), integral_const]
  simp only [probReal_univ, one_smul]
  have h1 := integral_clippedMean_sub_sq_le n hn P hP
  have h2 : 2 * b ^ 2 = 8 / (n * ε) ^ 2 := by rw [hb_def]; field_simp; ring
  linarith

/-- The clipped Laplace mean mechanism is a Markov kernel for positive `n` and `ε`. -/
theorem isMarkovKernel_laplaceMeanMechanism (n : ℕ) (hn : 0 < n) (ε : ℝ) (hε : 0 < ε) :
    IsMarkovKernel (laplaceMeanMechanism n ε) := by
  have hnr : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  refine ⟨fun d ↦ ?_⟩
  exact TauCeti.Probability.isProbabilityMeasure_laplaceMeasure (by positivity) _

/-- The mean of a law supported by `[-1,1]` lies in `[-1,1]`. -/
theorem abs_integral_le_one_of_support (P : Measure ℝ) [IsProbabilityMeasure P]
    (hP : P (Icc (-1) 1)ᶜ = 0) : |∫ x, x ∂P| ≤ 1 := by
  have hmem : ∀ᵐ x ∂P, x ∈ Icc (-1 : ℝ) 1 := measure_eq_zero_iff_ae_notMem.mp hP |>.mono
    fun x hx ↦ by simpa using hx
  have h := norm_integral_le_of_norm_le_const (C := 1) (hmem.mono fun x hx ↦ by
    rw [Real.norm_eq_abs, abs_le]; exact hx)
  simpa [Real.norm_eq_abs] using h

/-- GAPS 107.66, central minimax upper bound: for `0 < ε ≤ 1` some `ε`-differentially private
mechanism (the clipped Laplace mean, or the constant release `0` when `1` is the smaller
rate) has mean squared error at most `8 min(1, 1/n + 1/(nε)²)` for every law on `[-1,1]`. -/
theorem exists_centralMeanRisk_le (n : ℕ) (hn : 0 < n) (ε : ℝ) (hε : ε ∈ Ioc (0 : ℝ) 1) :
    ∃ M : Kernel (Fin n → ℝ) ℝ, IsMarkovKernel M ∧
      IsDifferentiallyPrivate IsHammingNeighbor ε 0 M ∧
      ∀ P : Measure ℝ, IsProbabilityMeasure P → P (Icc (-1) 1)ᶜ = 0 →
        centralMeanRisk M P ≤ 8 * min 1 (1 / n + 1 / (n * ε) ^ 2) := by
  have hnr : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  by_cases hsmall : 1 ≤ 1 / n + 1 / (n * ε) ^ 2
  · refine ⟨Kernel.const _ (Measure.dirac 0), inferInstance, ?_, fun P hP1 hP ↦ ?_⟩
    · intro d d' _ A _
      simp only [Kernel.const_apply, ENNReal.ofReal_zero, add_zero]
      calc (Measure.dirac (0 : ℝ)) A = 1 * (Measure.dirac (0 : ℝ)) A := (one_mul _).symm
        _ ≤ ENNReal.ofReal (Real.exp ε) * (Measure.dirac (0 : ℝ)) A := by
          gcongr
          rw [← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal (Real.one_le_exp hε.1.le)
    · rw [min_eq_left hsmall]
      unfold centralMeanRisk
      simp only [Kernel.const_apply, integral_dirac, zero_sub, even_two, Even.neg_pow,
        integral_const, probReal_univ, one_smul]
      have := abs_integral_le_one_of_support P hP
      nlinarith [abs_nonneg (∫ x, x ∂P), sq_abs (∫ x, x ∂P)]
  · push Not at hsmall
    refine ⟨laplaceMeanMechanism n ε, isMarkovKernel_laplaceMeanMechanism n hn ε hε.1,
      isDifferentiallyPrivate_laplaceMeanMechanism n hn ε hε.1, fun P hP1 hP ↦ ?_⟩
    rw [min_eq_right hsmall.le]
    have h := centralMeanRisk_laplaceMeanMechanism_le n hn ε hε.1 P hP
    have h8 : 8 / (n * ε) ^ 2 = 8 * (1 / (n * ε) ^ 2) := by ring
    have hpos : 0 ≤ 1 / (n : ℝ) := by positivity
    linarith

/-- GAPS 107.66, central minimax lower bound: there is an absolute `c > 0` such that for
`0 < ε ≤ 1` every `ε`-differentially private mechanism has mean squared error at least
`c min(1, 1/n + 1/(nε)²)` for the mean of some law on `[-1,1]`. -/
theorem exists_centralMeanRisk_ge :
    ∃ c > (0 : ℝ), ∀ n : ℕ, 0 < n → ∀ ε ∈ Ioc (0 : ℝ) 1, ∀ M : Kernel (Fin n → ℝ) ℝ,
      IsMarkovKernel M → IsDifferentiallyPrivate IsHammingNeighbor ε 0 M →
      ∃ P : Measure ℝ, IsProbabilityMeasure P ∧ P (Icc (-1) 1)ᶜ = 0 ∧
        c * min 1 (1 / n + 1 / (n * ε) ^ 2) ≤ centralMeanRisk M P := by
  sorry

/-- GAPS 107.66, local minimax rate: there are absolute `c, C > 0` such that for `0 < ε ≤ 1`
every noninteractive protocol with `ε`-locally private release kernels and every measurable
estimator has mean squared error at least `c min(1, 1/(nε²))` for some law on `[-1,1]`, and some
such protocol has error at most `C min(1, 1/(nε²))` for every law on `[-1,1]`. -/
theorem localMeanRisk_minimax_order :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ n : ℕ, 0 < n → ∀ ε ∈ Ioc (0 : ℝ) 1,
      (∀ Q : Fin n → Kernel ℝ ℝ, (∀ i, IsMarkovKernel (Q i)) →
        (∀ i, IsDifferentiallyPrivate (fun _ _ : ℝ ↦ True) ε 0 (Q i)) →
        ∀ est : (Fin n → ℝ) → ℝ, Measurable est →
        ∃ P : Measure ℝ, IsProbabilityMeasure P ∧ P (Icc (-1) 1)ᶜ = 0 ∧
          c * min 1 (1 / (n * ε ^ 2)) ≤ localMeanRisk Q est P) ∧
      ∃ Q : Fin n → Kernel ℝ ℝ, (∀ i, IsMarkovKernel (Q i)) ∧
        (∀ i, IsDifferentiallyPrivate (fun _ _ : ℝ ↦ True) ε 0 (Q i)) ∧
        ∃ est : (Fin n → ℝ) → ℝ, Measurable est ∧
          ∀ P : Measure ℝ, IsProbabilityMeasure P → P (Icc (-1) 1)ᶜ = 0 →
            localMeanRisk Q est P ≤ C * min 1 (1 / (n * ε ^ 2)) := by
  sorry

end CKSD
